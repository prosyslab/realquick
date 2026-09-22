import Lean
import RealQuick.TimeM
import RealQuick.Instrumentation.Registry
import RealQuick.Instrumentation.CostModel
import RealQuick.Instrumentation.Computability
import RealQuick.Instrumentation.Context
import RealQuick.Instrumentation.Translate
import RealQuick.Instrumentation.WF

/-!
# TimeM instrumentation

`#instrument f as f_timed` translates a pure definition into `TimeM`.
This also generates `f_timed_value : ∀ args, TimeM.value (f_timed args) = f args`.
For well-founded recursion, `f_eq_def` is also generated.

This module follows the fail-fast policy. If the instrumentation fails,
it should abort, not silently producing zero-cost function.
-/

open Lean Meta Elab Command Compiler
open RealQuick.TimeM

namespace RealQuick.Instrumentation

private def printing (m : MetaM α) : MetaM α :=
  withOptions (fun o => o.setBool `pp.all false |>.setBool `pp.explicit false
    |>.setBool `pp.notation true |>.setBool `pp.match true
    |>.setBool `pp.fieldNotation false |>.setBool `pp.proofs true
    |>.setBool `pp.universes false |>.setBool `pp.natLit true) m

/-- Instrument a supported pure declaration. Unsupported work is an error, never free. -/
elab "#instrument " source:ident " as " target:ident : command => do
  let saved ← get
  try
    let sourceName ← liftTermElabM <| resolveGlobalConstNoOverload source
    let targetName := (← getCurrNamespace) ++ target.getId
    if (← getEnv).contains targetName then throwError "declaration `{targetName}` already exists"
    let isWF ← liftTermElabM do
      return (← isRecursiveDefinition sourceName) && (← getStructuralRecArgPos? sourceName).isNone
    if isWF then
      liftTermElabM <| WF.instrumentWF sourceName targetName
      let theoremName := targetName.appendAfter "_value"
      modifyEnv fun env => Registry.register env sourceName targetName theoremName
      logInfo m!"Instrumented `{sourceName}` as `{targetName}`; value theorem: `{theoremName}`"
      return
    let (ty, body, params, recPos?, levels, unfolded) ← liftTermElabM do
      let .defnInfo info ← getConstInfo sourceName
        | throwError "instrumentation requires a transparent definition"
      unless info.safety == .safe do throwError "unsafe or partial sources are unsupported"
      if info.value.hasSorry then throwError "sorry-backed sources are unsupported"
      checkAxioms sourceName
      checkComputable sourceName
      let recPos? ← getStructuralRecArgPos? sourceName
      if (← isRecursiveDefinition sourceName) && recPos?.isNone then
        throwError "only structural recursion is supported"
      let sourceExpr := mkConst sourceName (info.levelParams.map Level.param)
      let body ← if let some eqn ← getUnfoldEqnFor? sourceName then do
          let eqnInfo ← getConstInfo eqn
          forallTelescope eqnInfo.type fun xs eq => do
            let some (_, lhs, rhs) := eq.eq? | throwError "malformed unfold equation"
            unless lhs == mkAppN sourceExpr xs do throwError "unsupported unfold equation telescope"
            mkLambdaFVars xs rhs
        else pure info.value
      forallTelescope info.type fun xs result => do
        -- Equation-compiler binders can share the same inaccessible user name.
        -- Rename the local declarations before delaborating either type or body,
        -- and reuse these names in the structural termination telescope.
        withUniqueParameterNames xs do
          for x in xs do
            let ty ← inferType x
            unless (← isProp ty) || (← isType x) do firstOrderResult ty
          firstOrderResult result
          if xs.any (fun x => result.containsFVar x.fvarId!) then
            throwError "dependent results are unsupported"
          if let some pos := recPos? then
            let argTy ← whnf (← inferType xs[pos]!)
            unless ← supportedInductive argTy do
              throwError "only nonindexed, nonmutual inductive structural recursion is supported"
          let timedType ← mkForallFVars xs (← mkAppM ``TimeM #[result])
          withLocalDeclD target.getId timedType fun self => do
            let unfolded ← IO.mkRef ({} : NameSet)
            -- Do not unfold `Nat.log2`'s internal recursor; model its source declaration
            -- as the same one-tick primitive application used at call sites.
            let translated ← if sourceName == ``Nat.log2 then
                mkStep (← mkRet (mkAppN (mkConst ``Nat.log2) xs))
              else mkStep (← translate { source := sourceName, self, unfolded }
                (← applyParameters body xs))
            let translated ← mkLambdaFVars xs translated
            let params ← xs.mapM fun x => return mkIdent (← x.fvarId!.getDecl).userName
            return (← printing (PrettyPrinter.delab timedType),
              ← printing (PrettyPrinter.delab translated), params, recPos?,
              info.levelParams.toArray.map mkIdent, (← unfolded.get).toArray)
    let decl ← `(declId| $target:ident.{$levels:ident,*})
    let cmd ← if let some pos := recPos? then
        `(def $decl:declId : $ty := $body
          termination_by structural $params* => $(params[pos]!))
      else `(def $decl:declId : $ty := $body)
    elabCommand cmd
    let errors := ((← get).messages.toList.drop saved.messages.toList.length).filter (·.severity == .error)
    unless errors.isEmpty do
      let details := MessageData.joinSep (errors.map (·.data)) (m!"\n")
      throwError "generated declaration failed:\n{cmd}\n{details}"
    let theoremName := targetName.appendAfter "_value"
    liftTermElabM do
      let info ← getConstInfo sourceName
      let timedInfo ← getConstInfo targetName
      if timedInfo.value?.any Expr.hasSorry then throwError "generated instrumentation failed to elaborate"
      forallTelescope info.type fun xs _ => do
        withUniqueParameterNames xs do
          let original := mkAppN (mkConst sourceName (info.levelParams.map Level.param)) xs
          let timed := mkAppN (mkConst targetName (info.levelParams.map Level.param)) xs
          -- Projection form makes the certificate usable even after value unfolds.
          let goal ← mkEq (.proj ``Prod 0 timed) original
          let originalStx ← printing (PrettyPrinter.delab original)
          let src ← `(Lean.Parser.Tactic.simpLemma| $(mkIdent sourceName):term)
          let dst ← `(Lean.Parser.Tactic.simpLemma| $(mkIdent targetName):term)
          let helperNames := Registry.valueTheorems (← getEnv) ++ unfolded
          let helpers ← helperNames.mapM fun name =>
            `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):term)
          let proofStx ← if recPos?.isSome then
              `(by
                fun_induction $originalStx
                all_goals simp_all [$src, $dst, TimeM.value, TimeM.fst_done, TimeM.fst_step, TimeM.fst_seq,
                  TimeM.fst_ite, Bool.cond_eq_ite, nat_beq_value, int_neg_value, intEq, natEq, intLe,
                  natLe, intLt, natLt, arrayRead?, $helpers,*]
                all_goals try rfl
                all_goals try (constructor <;> rfl))
            else `(by
              solve
              | simp [$src, $dst, TimeM.value, TimeM.fst_done, TimeM.fst_step, TimeM.fst_seq, TimeM.fst_ite,
                  Bool.cond_eq_ite, nat_beq_value, int_neg_value, intEq, natEq, intLe, natLe,
                  intLt, natLt, arrayRead?, $helpers,*] <;> try rfl
              | fun_cases $originalStx <;> simp_all [$src, $dst, TimeM.value, TimeM.fst_done, TimeM.fst_step, TimeM.fst_seq, TimeM.fst_ite,
                  Bool.cond_eq_ite, nat_beq_value, int_neg_value, intEq, natEq, intLe, natLe,
                  intLt, natLt, arrayRead?, $helpers,*] <;> try rfl)
          let proof ← Term.elabTermEnsuringType proofStx goal
          Term.synthesizeSyntheticMVarsNoPostponing
          let proof ← instantiateMVars (← mkLambdaFVars xs proof)
          if proof.hasSorry || proof.hasExprMVar then
            let errors := (← Core.getMessageLog).toList.filter (·.severity == .error)
            let details := MessageData.joinSep (errors.map (·.data)) (m!"\n")
            throwError "value-preservation proof failed:\n{details}"
          let theoremType ← mkForallFVars xs goal
          addDecl (.thmDecl {
            name := theoremName
            levelParams := info.levelParams
            type := theoremType
            value := proof
          })
    liftTermElabM do
      checkComputable targetName
      checkAxioms targetName
      checkAxioms theoremName
    modifyEnv fun env => Registry.register env sourceName targetName theoremName
    logInfo m!"Instrumented `{sourceName}` as `{targetName}`; value theorem: `{theoremName}`"
  catch ex =>
    set saved
    throw ex

end RealQuick.Instrumentation
