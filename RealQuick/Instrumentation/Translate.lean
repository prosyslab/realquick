import Lean

import RealQuick.TimeM
import RealQuick.Instrumentation.Registry
import RealQuick.Instrumentation.CostModel
import RealQuick.Instrumentation.Computability
import RealQuick.Instrumentation.Context

open Lean Meta Elab Command Compiler
open RealQuick.TimeM

namespace RealQuick.Instrumentation

def ret (e : Expr) : MetaM Expr := mkAppM ``TimeM.done #[e]
def step (e : Expr) : MetaM Expr := mkAppM ``TimeM.step #[e]

structure FnAppView where
  expr: Expr
  fn: Expr
  args: Array Expr
  name?: Option Name
  levels : List Level

namespace FnAppView

def fromExpr (e : Expr) : FnAppView :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const name levels =>
    ⟨e, fn, args, name, levels⟩
  | _ => ⟨e, fn, args, none, []⟩

end FnAppView

/-- Avoid introducing aliases for already evaluated values (important for termination). -/
private def sequence (comp : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  if comp.isAppOfArity ``TimeM.done 2 then
    return ← k comp.getAppArgs[1]!
  let ty ← inferType comp
  let ty ← whnf ty
  unless ty.isAppOfArity ``Prod 2 do throwError "internal instrumentation error: expected TimeM"
  withLocalDeclD (← mkFreshUserName `value) ty.getAppArgs[0]! fun x => do
    let body ← k x
    mkAppM ``TimeM.seq #[comp, ← mkLambdaFVars #[x] body]

/-- Substitute only known declaration parameters. `headBeta` would also reduce
executable beta-redexes in the body and could erase expensive unused arguments. -/
def applyParameters (body : Expr) (args : Array Expr) : MetaM Expr := do
  args.foldlM (fun body arg => do
    let .lam _ _ body _ := body.consumeMData
      | throwError "unsupported function body: expected a parameter lambda"
    pure (body.instantiate1 arg)) body

/-- Direct nonindexed inductives have ordinary constant-cost branch selection.
Array's logical constructor exposes a list conversion, so it is deliberately
excluded here and handled only through its explicit costed operations. -/
def supportedInductive (ty : Expr) : MetaM Bool := do
  let .const name _ := ty.getAppFn | return false
  if name == ``Array then return false
  let .inductInfo info ← getConstInfo name | return false
  return info.numIndices == 0 && info.all.length == 1

/-- A multi-pattern matcher may carry an accumulator without inspecting it.
Check its uninstantiated alternative types so an Array accumulator is allowed,
without treating Array's logical list-destructuring as a free RAM operation. -/
private def passesDiscriminant (matcher : MatcherApp) (i : Nat) : MetaM Bool := do
  let info ← getConstInfo matcher.matcherName
  forallTelescope info.type fun binders _ => do
    for j in [:matcher.numAlts] do
      let alt := binders[matcher.numParams + 1 + matcher.numDiscrs + j]!
      let pass ← forallTelescope (← inferType alt) fun fields result => do
        unless result.getAppFn == binders[matcher.numParams]! do return false
        let some arg := result.getAppArgs[i]? | return false
        return fields.contains arg
      unless pass do return false
    return true

def withUniqueParameterNames {m : Type → Type} [Monad m]
    [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (xs : Array Expr) (action : m α) : m α := do
  let mut lctx ← (getLCtx : MetaM LocalContext)
  for i in [:xs.size] do
    lctx := lctx.setUserName xs[i]!.fvarId! (Name.mkSimple s!"instrumentArg{i}")
  withLCtx lctx (← (getLocalInstances : MetaM LocalInstances)) action


/-- Proof automation only: simplification must never normalize executable source code. -/
private def wfSimpContext (ctx : Ctx) : MetaM Simp.Context := do
  let mut thms ← getSimpTheorems
  for name in #[``TimeM.fst_done, ``TimeM.fst_step, ``TimeM.fst_seq,
      ``WF.fst_seqEq, ``WF.fst_certified, ``Bool.cond_eq_ite,
      ``nat_beq_value, ``int_neg_value, ``intEq, ``natEq, ``intLe, ``natLe,
      ``intLt, ``natLt, ``arrayRead?] do
    thms ← if ← isProp (← getConstInfo name).type then thms.addConst name (post := false) else thms.addDeclToUnfold name
  for theoremName in Registry.valueTheorems (← getEnv) do
    thms ← thms.addConst theoremName (post := false)
  for name in (← ctx.unfolded.get).toArray do
    thms ← thms.addDeclToUnfold name
  return ← Simp.mkContext (config := { zetaDelta := true, failIfUnchanged := false }) (simpTheorems := #[thms])

private partial def wfSolve (ctx : Ctx) (goal : MVarId) (fuel : Nat := 64) : MetaM Unit :=
  goal.withContext do
    if fuel == 0 then throwError "well-founded proof search exhausted its branch limit"
    if let some next ← substSomeVar? goal then
      wfSolve ctx next (fuel - 1)
      return
    let some goal := (← simpAll goal (← wfSimpContext ctx)).1 | return
    try goal.refl; return catch _ => pure ()
    try goal.assumption; return catch _ => pure ()
    if fuel == 0 then throwError "well-founded value/termination proof failed:{indentExpr (← goal.getType)}"
    let target ← goal.getType
    if target.isAppOfArity ``Iff 2 && (← isDefEq target.getAppArgs[0]! target.getAppArgs[1]!) then
      goal.assign (← mkAppM ``Iff.refl #[target.getAppArgs[0]!])
      return
    if let some e ← findSplit? target .match then
      if let some matcher ← matchMatcherApp? e then
        for discr in matcher.discrs do
          let env ← getEnv
          let candidates := if discr.isFVar then #[discr] else
            if env.isConstructor discr.getAppFn.constName! then discr.getAppArgs.reverse else #[]
          for candidate in candidates do
            if candidate.isFVar && (← supportedInductive (← inferType candidate)) then
              let goals ← goal.cases candidate.fvarId!
              for g in goals do wfSolve ctx g.mvarId (fuel - 1)
              return
    if let some goals ← splitTarget? goal (useNewSemantics := true) then
      for g in goals do wfSolve ctx g (fuel - 1)
    else
      for decl in (← getLCtx) do
        if !decl.isLet && decl.type.isAppOfArity ``PSigma 2 then
          let goals ← goal.cases decl.fvarId
          for g in goals do wfSolve ctx g.mvarId (fuel - 1)
          return
      throwError "well-founded value/termination proof failed:\n{goal}"

def wfProve (ctx : Ctx) (type : Expr) : MetaM Expr := do
  let proof ← mkFreshExprSyntheticOpaqueMVar type
  wfSolve ctx proof.mvarId!
  instantiateMVars proof

private def adaptProof (ctx : Ctx) (proof type : Expr) : MetaM Expr := do
  let actual ← inferType proof
  if ← isDefEq actual type then return proof
  unless ctx.wf?.isSome do throwError "dependent proof arguments are unsupported"
  mkEqMP (← wfProve ctx (← mkEq actual type)) proof

/-- Eta-expand dependent matcher alternatives, transporting only their erased proof binders. -/
private partial def adaptAlternative (ctx : Ctx) (alt expected : Expr) : MetaM Expr := do
  let actual ← inferType alt
  if ← isDefEq actual expected then return alt
  let .forallE n dom body bi ← whnf expected
    | throwError "dependent matcher data results are unsupported"
  let .forallE _ oldDom _ _ ← whnf actual
    | throwError "malformed dependent matcher alternative"
  withLocalDecl n bi dom fun x => do
    let arg ← if ← isProp dom then adaptProof ctx x oldDom else do
      unless ← isDefEq dom oldDom do throwError "dependent matcher data binders are unsupported"
      pure x
    let result ← adaptAlternative ctx (mkApp alt arg) (body.instantiate1 x)
    mkLambdaFVars #[x] result

/-- Preserve a value equality in the continuation so original decrease proofs can be reused. -/
private def sequenceWith (ctx : Ctx) (comp : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  if ctx.wf?.isNone then return ← sequence comp k
  if comp.isAppOfArity ``TimeM.done 2 then return ← k comp.getAppArgs[1]!
  let value := mkProj ``Prod 0 comp
  let (r, _) ← simp value (← wfSimpContext ctx)
  let h ← r.getProof
  let ty ← inferType value
  withLocalDeclD (← mkFreshUserName `value) ty fun x => do
    withLocalDeclD (← mkFreshUserName `value_eq) (← mkEq x r.expr) fun hx => do
      let body ← k x
      mkAppM ``WF.seqEq #[comp, r.expr, h, ← mkLambdaFVars #[x, hx] body]

/-- Recognize only the compiler's smaller-argument callback, not general higher-order code. -/
def wfCallback? (ctx : Ctx) (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let some wf := ctx.wf? | return none
  forallBoundedTelescope ty (some 2) fun xs result => do
    unless xs.size == 2 do return none
    unless ← isDefEq (← inferType xs[0]!) wf.domain do return none
    unless ← isProp (← inferType xs[1]!) do return none
    let prop ← inferType xs[1]!
    let parent := prop.getAppArgs.back!
    unless ← isDefEq prop (mkApp2 wf.relation xs[0]! parent) do return none
    unless ← isDefEq result (← inferType (mkApp wf.pureFn xs[0]!)) do return none
    let pureRec ← mkLambdaFVars xs (mkApp wf.pureFn xs[0]!)
    let certTy ← mkForallFVars xs (← mkAppM ``WF.Certified #[wf.pureFn, xs[0]!])
    return some (pureRec, certTy)

private partial def wfResultType (ctx : Ctx) (ty : Expr) : MetaM Expr := do
  if let .forallE n dom body bi := ty then
    if let some (_, certTy) ← wfCallback? ctx dom then
      withLocalDecl n bi certTy fun x => do
        unless !body.hasLooseBVar 0 do throwError "dependent recursive callbacks are unsupported"
        mkForallFVars #[x] (← wfResultType ctx (body.instantiate1 x))
    else if ← isProp dom then
      withLocalDecl n bi dom fun x => do mkForallFVars #[x] (← wfResultType ctx (body.instantiate1 x))
    else throwError "unsupported higher-order well-founded result"
  else
    firstOrderResult ty
    mkAppM ``TimeM #[ty]

mutual
  /-- let x : type := value; body -/
  partial def translateLet (ctx : Ctx) (name : Name) (type value body : Expr) : MetaM Expr := do
    if (← isProp type) || (← isType value) then
      -- Proposition/Type has no runtime cost
      translate ctx (body.instantiate1 value)
    else
      -- Otherwise, `value` is instrumented
      let value_inst ← translate ctx value
      sequenceWith ctx value_inst (fun value =>
        withLetDecl name type value fun x => do
          let body_inst ← translate ctx (body.instantiate1 x)
          mkLetFVars #[x] body_inst)

  partial def translateProj (ctx : Ctx) (name : Name) (index : Nat) (value : Expr) : MetaM Expr := do
    let e := .proj name index value
    firstOrderResult (← inferType e)
    sequenceWith ctx (← translate ctx value) fun value => do
      if name == ``Array then
        let size ← mkAppM ``Array.size #[value]
        mkAppM ``charge #[← mkAppM ``Nat.succ #[size], .proj name index value]
      else
        step (← ret (.proj name index value))

  partial def translate (ctx : Ctx) (e : Expr) : MetaM Expr := do
    let e := e.consumeMData
    match e with
    | .fvar _ | .lit _ =>
      firstOrderResult (← inferType e)
      ret e
    | .letE name type value body _ => translateLet ctx name type value body
    | .proj name index value => translateProj ctx name index value
    | .app .. | .const .. => translateApp ctx e
    | _ => throwError "unsupported executable expression in instrumentation:{indentExpr e}"

  private partial def arguments (ctx : Ctx) (fn : Expr) (args : Array Expr)
      (k : Array Expr → MetaM Expr) : MetaM Expr := do
    go (← inferType fn) 0 #[]
  where
    go (ty : Expr) (i : Nat) (out : Array Expr) : MetaM Expr := do
      if i == args.size then return ← k out
      let .forallE _ dom body _ ← whnf ty
        | throwError "unsupported application in instrumentation"
      let arg := args[i]!
      if (← isProp dom) || (← isType arg) then
        let arg ← if ← isProp dom then adaptProof ctx arg dom else pure arg
        go (body.instantiate1 arg) (i + 1) (out.push arg)
      else
        firstOrderResult dom
        sequenceWith ctx (← translate ctx arg) fun value =>
          go (body.instantiate1 value) (i + 1) (out.push value)

  private partial def translateApp (ctx : Ctx) (e : Expr) : MetaM Expr := do
    firstOrderResult (← inferType e)
    let app := FnAppView.fromExpr e
    let fn := app.fn
    let args := app.args
    if let some wf := ctx.wf? then
      if let some (_, timed) := wf.recs.find? (fun (original, _) => original == fn) then
        unless args.size == 2 do throwError "partially applied recursive callback is unsupported"
        return ← sequenceWith ctx (← translatePacked ctx args[0]! wf.arity) fun value => do
          let expected := (← inferType (mkApp timed value)).bindingDomain!
          let proof ← adaptProof ctx args[1]! expected
          pure (mkProj ``Subtype 0 (mkApp2 timed value proof))
    let some name := app.name?
      | throwError "higher-order calls are unsupported:{indentExpr e}"
    let levels := app.levels
    if name == ctx.source then
      return ← arguments ctx fn args fun args => pure (mkAppN ctx.self args)
    if let some timed := Registry.timedForSource? (← getEnv) name then
      return ← arguments ctx fn args fun args => pure (mkAppN (mkConst timed levels) args)
    if let some matcher ← matchMatcherApp? e (alsoCasesOn := ctx.wf?.isSome) then
      -- A nested pattern can expose Array.toList even when its outer
      -- discriminant is an ordinary structure/tree. Such conversion must not
      -- disappear into the matcher's otherwise constant-cost branch selection.
      let matcherInfo ← getConstInfo matcher.matcherName
      if matcherInfo.value?.any (fun body => (body.find? fun
          | .proj ``Array _ _ => true
          | .const n _ => [``Array.rec, ``Array.casesOn, ``Array.toList].contains n
          | _ => false).isSome) then
        throwError "array destructuring in patterns is unsupported; use explicit Array.toList"
      if ctx.wf?.isSome then return ← translateWFMatch ctx matcher
      unless matcher.remaining.isEmpty do throwError "partially applied matches are unsupported"
      let motive ← lambdaTelescope matcher.motive fun xs result => do
        if xs.any (fun x => result.containsFVar x.fvarId!) then
          throwError "dependent matches are unsupported"
        mkLambdaFVars xs (← mkAppM ``TimeM #[result])
      let alts ← matcher.alts.mapM fun alt => lambdaTelescope alt fun xs body => do
        mkLambdaFVars xs (← translate ctx body)
      let rec discrs (i : Nat) (out : Array Expr) : MetaM Expr := do
        if i == matcher.discrs.size then
          return ← step ({ matcher with motive, alts, discrs := out }.toExpr)
        let discr := matcher.discrs[i]!
        let ty ← whnf (← inferType discr)
        unless (← supportedInductive ty) || (← passesDiscriminant matcher i) do
          throwError "unsupported match discriminant type:{indentExpr ty}"
        sequenceWith ctx (← translate ctx discr) fun value => discrs (i + 1) (out.push value)
      return ← discrs 0 #[]
    if name == ``dite && ctx.wf?.isSome then
      unless args.size == 5 do throwError "malformed dependent conditional"
      let decision ← translateDecision ctx args[1]! args[2]!
      return ← sequenceWith ctx decision fun b => do
        let prop ← mkEq b (mkConst ``Bool.true)
        let yes ← withLocalDeclD `condition prop fun h => do
          let originalProof ← wfProve ctx args[1]!
          mkLambdaFVars #[h] (← translate ctx (← applyParameters args[3]! #[originalProof]))
        let no ← withLocalDeclD `condition (mkNot prop) fun h => do
          let originalProof ← wfProve ctx (mkNot args[1]!)
          mkLambdaFVars #[h] (← translate ctx (← applyParameters args[4]! #[originalProof]))
        step (← mkAppOptM ``dite #[some (← mkAppM ``TimeM #[args[0]!]), some prop, none, some yes, some no])
    if name == ``ite then
      unless args.size == 5 do throwError "malformed conditional"
      -- Account for executable decision procedures, not the erased proposition itself.
      let decision ← translateDecision ctx args[1]! args[2]!
      return ← sequenceWith ctx decision fun b => do
        let yes ← translate ctx args[3]!
        let no ← translate ctx args[4]!
        -- Bool elimination avoids re-synthesizing a potentially hostile Decidable
        -- instance when the generated expression is delaborated and elaborated.
        step (← mkAppM ``cond #[b, yes, no])
    -- Allocation/conversion is linear. Push conservatively includes reallocation;
    -- writes/pop above are abstract RAM primitives under exclusive ownership.
    if let some measure := CostModel.linearArrayMeasure? name then
      return ← arguments ctx fn args fun values => do
        let size ← match measure with
          | .capacity => pure values[1]!
          | .listLength => mkAppM ``List.length #[values[1]!]
          | .arraySize => mkAppM ``Array.size #[values[1]!]
        mkAppM ``charge #[← mkAppM ``Nat.succ #[size], mkAppN fn values]
    if name == ``GetElem.getElem || name == ``GetElem?.getElem? then
      let required := name == ``GetElem.getElem
      unless args.size == (if required then 8 else 7) &&
          args[0]!.isAppOfArity ``Array 1 && args[1]!.isConstOf ``Nat do
        throwError "only canonical Nat-indexed array reads are supported"
      let instName := if required then
        ``Array.instGetElemNatLtSize else ``Array.instGetElem?NatLtSize
      let expected := mkApp (mkConst instName [levels[0]!]) args[2]!
      unless args[4]! == expected do
        throwError "custom array access instances are unsupported"
      -- The validity predicate is erased; the instance has just been checked.
      return ← arguments ctx (mkAppN fn (args.extract 0 5)) (args.extract 5 args.size) fun values => do
        if required then
          step (← ret (← mkAppM ``Array.getInternal values))
        else
          step (← ret (← mkAppM ``arrayRead? values))
    if CostModel.unitCostPrimitive name || CostModel.unitCostArrayOperation name ||
        (← getEnv).isConstructor name then
      return ← arguments ctx fn args fun args => do step (← ret (mkAppN fn args))
    -- Match canonical instances syntactically: normalizing an arbitrary instance
    -- could execute (and thereby erase) work before we have accounted for it.
    if name == ``OfNat.ofNat then
      unless args.size == 3 && args[1]!.isRawNatLit do
        throwError "only canonical Nat/Int literals are supported"
      if args[0]!.isConstOf ``Nat && args[2]! == mkApp (mkConst ``instOfNatNat) args[1]! then
        return ← ret args[1]!
      if args[0]!.isConstOf ``Int && args[2]! == mkApp (mkConst ``instOfNat) args[1]! then
        return ← ret (mkApp (mkConst ``Int.ofNat) args[1]!)
      throwError "only canonical Nat/Int literals are supported"
    if name == ``BEq.beq then
      unless args.size == 4 do throwError "malformed equality test"
      let isNat := args[0]!.isConstOf ``Nat
      let expected := mkAppN (mkConst ``instBEqOfDecidableEq [.zero])
        #[args[0]!, mkConst (if isNat then ``instDecidableEqNat else ``Int.instDecidableEq)]
      unless (isNat || args[0]!.isConstOf ``Int) && args[1]! == expected do
        throwError "only canonical Nat BEq is supported"
      if isNat then
        return ← translate ctx (mkAppN (mkConst ``Nat.beq) (args.extract 2 4))
      return ← arguments ctx (mkAppN fn (args.extract 0 2)) (args.extract 2 4) fun values => do
        step (← ret (← mkAppM ``intEq values))
    if name == ``Neg.neg then
      unless args.size == 3 && args[0]!.isConstOf ``Int && args[1]!.isConstOf ``Int.instNegInt do
        throwError "only canonical Int negation is supported"
      return ← translate ctx (mkApp (mkConst ``Int.neg) args[2]!)
    if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod].contains name then
      unless args.size == 6 do throwError "malformed arithmetic application"
      let isNat := args[0]!.isConstOf ``Nat
      let tyName := if isNat then ``Nat else ``Int
      let (wrapper, instanceName, op) :=
        if name == ``HAdd.hAdd then
          (``instHAdd, if isNat then ``instAddNat else ``Int.instAdd, if isNat then ``Nat.add else ``Int.add)
        else if name == ``HSub.hSub then
          (``instHSub, if isNat then ``instSubNat else ``Int.instSub, if isNat then ``Nat.sub else ``Int.sub)
        else if name == ``HMul.hMul then
          (``instHMul, if isNat then ``instMulNat else ``Int.instMul, if isNat then ``Nat.mul else ``Int.mul)
        else if name == ``HDiv.hDiv then
          (``instHDiv, if isNat then ``Nat.instDiv else ``Int.instDiv, if isNat then ``Nat.div else ``Int.ediv)
        else
          (``instHMod, if isNat then ``Nat.instMod else ``Int.instMod, if isNat then ``Nat.mod else ``Int.emod)
      let expected := mkAppN (mkConst wrapper [.zero]) #[mkConst tyName, mkConst instanceName]
      unless (args.extract 0 3).all (·.isConstOf tyName) && args[3]! == expected do
        throwError "only canonical Nat/Int arithmetic instances are supported"
      return ← translate ctx (mkAppN (mkConst op) (args.extract 4 6))
    if let some projection := (← getEnv).getProjectionFnInfo? name then
      unless projection.fromClass do
        unless args.size == projection.numParams + 1 do
          throwError "partially applied or functional projections are unsupported"
        return ← arguments ctx fn args fun values => do
          step (← ret (mkAppN fn values))
    if ctx.active.contains name then throwError "recursive helper `{name}` must be instrumented first"
    if ← isRecursiveDefinition name then
      throwError "recursive helper `{name}` must be instrumented first with #instrument"
    let .defnInfo info ← getConstInfo name
      | throwError "no approved cost model for `{name}`"
    unless info.safety == .safe do throwError "unsafe or partial helper `{name}` is unsupported"
    if info.value.hasSorry then throwError "sorry-backed helper `{name}` is unsupported"
    checkComputable name
    ctx.unfolded.modify (·.insert name)
    -- Evaluate arguments once before unfolding a transparent first-order helper.
    arguments ctx fn args fun values => do
      step (← translate { ctx with active := name :: ctx.active }
        (← applyParameters (info.value.instantiateLevelParams info.levelParams levels) values))

  /-- Only the equation compiler's argument packing is free. User computations in
  each argument still go through the ordinary translator. -/
  private partial def translatePacked (ctx : Ctx) (e : Expr) (arity : Nat) : MetaM Expr := do
    if arity ≤ 1 then return ← translate ctx e
    unless e.isAppOfArity ``PSigma.mk 4 do throwError "unsupported packed recursive argument"
    let args := (FnAppView.fromExpr e).args
    sequenceWith ctx (← translate ctx args[2]!) fun first => do
      sequenceWith ctx (← translatePacked ctx args[3]! (arity - 1)) fun rest =>
        ret (mkAppN e.getAppFn #[args[0]!, args[1]!, first, rest])

  /-- Transform matcher binders introduced by the well-founded equation compiler. -/
  private partial def translateWFLambda (ctx : Ctx) (e : Expr) : MetaM Expr := do
    if let .lam n ty body bi := e.consumeMData then
      if let some (pureRec, certTy) ← wfCallback? ctx ty then
        withLetDecl n ty pureRec fun original => do
          withLocalDecl n bi certTy fun timed => do
            let wf := ctx.wf?.get!
            let body ← translateWFLambda { ctx with wf? := some { wf with recs := wf.recs.push (original, timed) } }
              (body.instantiate1 original)
            mkLambdaFVars #[timed] (← mkLetFVars #[original] body)
      else
        withLocalDecl n bi ty fun x => do
          mkLambdaFVars #[x] (← translateWFLambda ctx (body.instantiate1 x))
    else translate ctx e

  private partial def translateWFMatch (ctx : Ctx) (matcher : MatcherApp) : MetaM Expr := do
    -- PSigma is used solely for the compiler's packed argument telescope.
    let packing := matcher.matcherName == ``PSigma.casesOn
    let wf := ctx.wf?.get!
    if packing && wf.unpackRemaining == 0 then
      throwError "user PSigma elimination is unsupported"
    let branchCtx := if packing then
        { ctx with wf? := some { wf with unpackRemaining := wf.unpackRemaining - 1 } }
      else ctx
    let motive ← lambdaTelescope matcher.motive fun xs result => do
      mkLambdaFVars xs (← wfResultType ctx result)
    let alts ← matcher.alts.mapM (translateWFLambda branchCtx)
    let rec discrs (i : Nat) (out : Array Expr) : MetaM Expr := do
      if i == matcher.discrs.size then
        let mut result := mkAppN (mkApp (mkAppN (mkConst matcher.matcherName matcher.matcherLevels.toList)
          matcher.params) motive) out
        for alt in alts do
          let .forallE _ dom _ _ ← whnf (← inferType result)
            | throwError "malformed well-founded matcher alternative"
          result := mkApp result (← adaptAlternative ctx alt dom)
        for arg in matcher.remaining do
          let .forallE _ dom _ _ ← whnf (← inferType result)
            | throwError "malformed well-founded matcher"
          let arg ← if ← isProp dom then adaptProof ctx arg dom else do
            let wf := ctx.wf?.get!
            let some (_, timed) := wf.recs.find? (fun (original, _) => original == arg)
              | throwError "unsupported well-founded matcher argument:{indentExpr arg}"
            pure timed
          result := mkApp result arg
        if packing then return result else return ← step result
      let discr := matcher.discrs[i]!
      let ty ← whnf (← inferType discr)
      unless packing || (← supportedInductive ty) || (← passesDiscriminant matcher i) do
        throwError "unsupported match discriminant type:{indentExpr ty}"
      if packing then return ← discrs (i + 1) (out.push discr)
      sequenceWith ctx (← translate ctx discr) fun value => discrs (i + 1) (out.push value)
    discrs 0 #[]

  private partial def translateDecision (ctx : Ctx) (prop inst : Expr) : MetaM Expr := do
    let pfn := prop.getAppFn
    let pargs := prop.getAppArgs
    let eq := pfn.isConstOf ``Eq
    let le := pfn.isConstOf ``LE.le
    let lt := pfn.isConstOf ``LT.lt
    if (eq && pargs.size == 3 || (le || lt) && pargs.size == 4) &&
        (pargs[0]!.isConstOf ``Nat || pargs[0]!.isConstOf ``Int) then
      let isNat := pargs[0]!.isConstOf ``Nat
      let decName := if eq then
          (if isNat then ``instDecidableEqNat else ``Int.instDecidableEq)
        else if le then (if isNat then ``Nat.decLe else ``Int.decLe)
        else (if isNat then ``Nat.decLt else ``Int.decLt)
      if !eq then
        let opInst := if le then (if isNat then ``instLENat else ``Int.instLEInt)
          else (if isNat then ``instLTNat else ``Int.instLTInt)
        unless pargs[1]!.isConstOf opInst do
          throwError "custom comparison instances are unsupported"
      let offset := if eq then 1 else 2
      unless inst == mkAppN (mkConst decName) (pargs.extract offset pargs.size) do
        throwError "custom decision procedures are unsupported"
      return ← sequenceWith ctx (← translate ctx pargs[offset]!) fun lhs => do
        sequenceWith ctx (← translate ctx pargs[offset + 1]!) fun rhs => do
          let test := if eq then (if isNat then ``natEq else ``intEq)
            else if le then (if isNat then ``natLe else ``intLe)
            else (if isNat then ``natLt else ``intLt)
          step (← ret (mkAppN (mkConst test) #[lhs, rhs]))
    -- The Bool coercion also requires its canonical decision procedure.
    unless prop.isAppOfArity ``Eq 3 && prop.getAppArgs[0]!.isConstOf ``Bool &&
        prop.getAppArgs[2]!.isConstOf ``Bool.true do
      throwError "unsupported condition: use a Bool test with approved operations"
    let canonical := mkAppN (mkConst ``instDecidableEqBool)
      #[prop.getAppArgs[1]!, mkConst ``Bool.true]
    unless inst == canonical do
      throwError "custom decision procedures are unsupported"
    translate ctx prop.getAppArgs[1]!
end

end RealQuick.Instrumentation
