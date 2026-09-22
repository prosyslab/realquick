import Lean
import RealQuick.TimeM
import RealQuick.Instrumentation.Registry
import RealQuick.Instrumentation.CostModel
import RealQuick.Instrumentation.Computability
import RealQuick.Instrumentation.Context
import RealQuick.Instrumentation.Translate

open RealQuick.TimeM

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

/-- Translate the kernel fixpoint, retaining its relation and erased decrease proofs. -/
private def instrumentWF (sourceName targetName : Name) : MetaM Unit :=
    withOptions (Elab.async.set · false) <| withTransparency .all do
  let info ← getConstInfoDefn sourceName
  unless info.safety == .safe && !info.value.hasSorry do
    throwError "unsafe, partial, or sorry-backed sources are unsupported"
  checkAxioms sourceName
  checkComputable sourceName
  let some eqns := Elab.WF.eqnInfoExt.find? (← getEnv) sourceName
    | throwError "well-founded recursion metadata is unavailable"
  unless eqns.declNames.size == 1 do throwError "mutual well-founded recursion is unsupported"
  let helper ← getConstInfoDefn eqns.declNameNonRec
  let workerName := targetName.appendAfter "_certified"
  if (← getEnv).contains workerName then throwError "declaration `{workerName}` already exists"
  let levels := info.levelParams.map Level.param
  let helperValue := helper.value.instantiateLevelParams helper.levelParams levels
  let (workerType, workerValue) ← lambdaBoundedTelescope helperValue eqns.fixedParamPerms.numFixed fun fixed fix => do
    let args := fix.getAppArgs
    let natFix := fix.getAppFn.isConstOf ``WellFounded.Nat.fix
    unless (natFix && args.size == 4) || (fix.getAppFn.isConstOf ``WellFounded.fix && args.size == 5) do
      throwError "unsupported well-founded fixpoint representation"
    let domain := args[0]!
    let pureFn := mkAppN (mkConst eqns.declNameNonRec levels) fixed
    let functional := args.back!
    let relation ← if natFix then do
        let wfRel ← mkAppM ``invImage #[args[2]!, mkConst ``Nat.lt_wfRel]
        pure (mkProj ``WellFoundedRelation 0 wfRel)
      else pure args[2]!
    let unfolded ← IO.mkRef ({} : NameSet)
    let baseCtx : Ctx := { source := sourceName, self := pureFn, unfolded := unfolded, wf? := some { domain, pureFn, relation, arity := eqns.argsPacker.varNamess[0]!.size, unpackRemaining := eqns.argsPacker.varNamess[0]!.size - 1 } }
    let newMotive ← withLocalDeclD `input domain fun x => do
      let result ← whnf (← inferType (mkApp pureFn x))
      firstOrderResult result
      unless !result.containsFVar x.fvarId! do throwError "dependent results are unsupported"
      mkLambdaFVars #[x] (← mkAppM ``WF.Certified #[pureFn, x])
    let newFunctional ← lambdaBoundedTelescope functional 1 fun xs body => do
      let x := xs[0]!
      let .lam name recTy recBody bi := body.consumeMData
        | throwError "malformed well-founded recursive functional"
      let some (pureRec, certTy) ← wfCallback? baseCtx recTy
        | throwError "unsupported well-founded recursive callback"
      withLetDecl name recTy pureRec fun original => do
        withLocalDecl name bi certTy fun timed => do
          let wf := baseCtx.wf?.get!
          let ctx := { baseCtx with wf? := some { wf with recs := #[(original, timed)] } }
          let originalBody := recBody.instantiate1 original
          let translated ← step (← translate ctx originalBody)
          let valueProof ← wfProve ctx (← mkEq (mkProj ``Prod 0 translated) originalBody)
          let fixEqName := if natFix then ``WellFounded.Nat.fix_eq else ``WellFounded.fix_eq
          let fixEq := mkAppN (mkConst fixEqName fix.getAppFn.constLevels!) (args.push x)
          let proof ← mkEqTrans valueProof (← mkEqSymm fixEq)
          let cert ← mkAppOptM ``Subtype.mk #[some (← mkAppM ``TimeM #[← inferType originalBody]),
            some (← withLocalDeclD `result (← inferType translated) fun r => do
              mkLambdaFVars #[r] (← mkEq (mkProj ``Prod 0 r) (mkApp pureFn x))),
            some translated, some proof]
          mkLambdaFVars xs (← mkLambdaFVars #[timed] (← mkLetFVars #[original] cert))
    let newFix ← if natFix then
        mkAppOptM ``WellFounded.Nat.fix #[some domain, some newMotive, some args[2]!, some newFunctional]
      else
        mkAppOptM ``WellFounded.fix #[some domain, some newMotive, some relation, some args[3]!, some newFunctional]
    return (← mkForallFVars fixed (← inferType newFix), ← mkLambdaFVars fixed newFix)
  if workerValue.hasSorry || workerValue.hasExprMVar then throwError "incomplete certified worker"
  addAndCompile (.defnDecl { name := workerName, levelParams := info.levelParams, type := workerType, value := workerValue, hints := .regular 0, safety := .safe }) (logCompileErrors := false)
  forallTelescope info.type fun xs result => do
    for x in xs do
      unless (← isProp (← inferType x)) || (← isType x) do firstOrderResult (← inferType x)
    firstOrderResult result
    if xs.any (fun x => result.containsFVar x.fvarId!) then throwError "dependent results are unsupported"
    let fixed := eqns.fixedParamPerms.perms[0]!.pickFixed xs
    let varying := eqns.fixedParamPerms.perms[0]!.pickVarying xs
    let worker := mkAppN (mkConst workerName levels) fixed
    let workerTy ← whnf (← inferType worker)
    let packed ← eqns.argsPacker.pack workerTy.bindingDomain! 0 varying
    let cert := mkApp worker packed
    let value := mkProj ``Subtype 0 cert
    addAndCompile (.defnDecl { name := targetName, levelParams := info.levelParams, type := ← mkForallFVars xs (← mkAppM ``TimeM #[result]), value := ← mkLambdaFVars xs value, hints := .regular 0, safety := .safe }) (logCompileErrors := false)
    let timed := mkAppN (mkConst targetName levels) xs
    let theoremType ← mkForallFVars xs (← mkEq (mkProj ``Prod 0 timed) (mkAppN (mkConst sourceName levels) xs))
    let proof ← mkLambdaFVars xs (mkProj ``Subtype 1 cert)
    addDecl (.thmDecl { name := targetName.appendAfter "_value", levelParams := info.levelParams, type := theoremType, value := proof })
    -- An explicit one-step equation supports cost proofs without unfolding the fixpoint implementation.
    let fix ← applyParameters workerValue fixed
    let fixArgs := fix.getAppArgs
    let functional := fixArgs.back!
    let recTy := (← inferType (mkApp functional packed)).bindingDomain!
    let callback ← forallBoundedTelescope recTy (some 2) fun ys _ =>
      mkLambdaFVars ys (mkApp worker ys[0]!)
    let mut body ← applyParameters functional #[packed, callback]
    -- These outer lets bind only the erased original recursive callback.
    while let .letE _ _ value rest _ := body do
      body := rest.instantiate1 value
    unless body.isAppOfArity ``Subtype.mk 4 do throwError "malformed certified result"
    let rhs := body.getAppArgs[2]!
    let eqName := if fix.getAppFn.isConstOf ``WellFounded.Nat.fix then
        ``WellFounded.Nat.fix_eq else ``WellFounded.fix_eq
    let fixEq := mkAppN (mkConst eqName fix.getAppFn.constLevels!) (fixArgs.push packed)
    let projection ← withLocalDeclD `result (← inferType cert) fun r =>
      mkLambdaFVars #[r] (mkProj ``Subtype 0 r)
    let eqProof ← mkCongrArg projection fixEq
    addDecl (.thmDecl { name := targetName.appendAfter "_eq_def", levelParams := info.levelParams, type := ← mkForallFVars xs (← mkEq timed rhs), value := ← mkLambdaFVars xs eqProof })
  checkComputable targetName
  checkAxioms targetName
  checkAxioms (targetName.appendAfter "_value")

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
      liftTermElabM <| instrumentWF sourceName targetName
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
                step (← ret (mkAppN (mkConst ``Nat.log2) xs))
              else step (← translate { source := sourceName, self, unfolded }
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
