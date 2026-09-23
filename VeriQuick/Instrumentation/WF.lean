import Lean
import VeriQuick.TimeM
import VeriQuick.Instrumentation.Context
import VeriQuick.Instrumentation.Translate

open Lean Meta Elab Command Compiler
open VeriQuick.TimeM

namespace VeriQuick.Instrumentation.WF

/-- Translate the kernel fixpoint, retaining its relation and erased decrease proofs. -/
def instrumentWF (sourceName targetName : Name) : MetaM Unit :=
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
          let translated ← mkStep (← translate ctx originalBody)
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

end VeriQuick.Instrumentation.WF
