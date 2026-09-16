import Lean
import RealQuick.TimeM
import RealQuick.Instrumentation.Registry
import RealQuick.Instrumentation.CostModel
import RealQuick.Instrumentation.Computability

open RealQuick.TimeM

/-!
# TimeM instrumentation

`#instrument f as f_timed` translates a pure definition into `TimeM`.
This also generates `f_timed_value : ∀ args, TimeM.value (f_timed args) = f args`.
For well-founded recursion, `f_eq_def` is also generated.

This module follows the fail-fast policy. If the instrumentation fails,
it should abort, not silently producing zero-cost function.

This initial, fail-closed frontend supports nondependent first-order code in `Type`,
structural recursion on direct nonindexed inductives (including Nat/List/trees),
structures/projections, Nat/Int/Bool primitives,
and selected array operations, with `Nat.log2` treated as a unit-cost primitive.
Conditionals require canonical Bool or Nat/Int comparison decision procedures.
Dependent conditionals, higher-order iteration,
and general well-founded recursion remain unsupported.

The `Type` restriction follows the existing `TimeM.step`/`TimeM.value` API; this
module does not change that API. Value preservation is kernel checked (the generated
statement uses the definitionally equal `.1` projection). Cost adequacy still trusts
this translator, Lean's elaboration machinery, and the primitive policy below.
nStrict gating of the legacy `#analyze` command and a formal cost-adequacy theorem are
separate milestones, not provided by this module.
-/

open Lean Meta Elab Command Compiler
open RealQuick.TimeM

namespace RealQuick.Instrumentation.WF

open RealQuick.TimeM

universe u v

variable {α : Type u} {β : Type v}

/-- A timed result certified to agree with the original function at its input. -/
def Certified (f : α → β) (x : α) :=
  {result : TimeM β // result.1 = f x}

/-- Recover the original value without unfolding the certified computation. -/
@[simp]
theorem fst_certified {f : α → β} {x : α} (c : Certified f x) :
    (c.val).1 = f x :=
  c.property

/-- Reuse the standard one-tick function-entry charge, with the same universe
restriction as `RealQuick.TimeM.TimeM.step`. -/
abbrev step {α : Type} (comp : TimeM α) : TimeM α := TimeM.step comp

/-- Sequence a timed computation, giving the continuation its value and a proof
that it agrees with the original value. The computation and continuation are
both evaluated once; their costs are added in sequencing order. -/
def seqEq (comp : TimeM α) (original : α) (h : comp.1 = original)
    (k : (value : α) → value = original → TimeM β) : TimeM β :=
  let result := k comp.1 h
  (result.1, comp.2 + result.2)

/-- The direct value projection, retaining the computed value and its proof. -/
theorem fst_seqEq_apply (comp : TimeM α) (original : α)
    (h : comp.1 = original) (k : (value : α) → value = original → TimeM β) :
    (seqEq comp original h k).1 = (k comp.1 h).1 := rfl

/-- Normalize values to the original input; equality proofs are irrelevant. -/
@[simp]
theorem fst_seqEq (comp : TimeM α) (original : α)
    (h : comp.1 = original) (k : (value : α) → value = original → TimeM β) :
    (seqEq comp original h k).1 = (k original rfl).1 := by
  cases h
  rfl

/-- Sequencing adds costs without introducing an entry charge.
This is deliberately not a simp lemma, so cost expansion remains explicit. -/
theorem snd_seqEq (comp : TimeM α) (original : α)
    (h : comp.1 = original) (k : (value : α) → value = original → TimeM β) :
    (seqEq comp original h k).2 = comp.2 + (k comp.1 h).2 := rfl

end RealQuick.Instrumentation.WF


namespace RealQuick.Instrumentation

variable {α : Type}

/-- Closed wrappers keep approved instances from being re-synthesized under a
caller's local instances when generated terms are delaborated and elaborated. -/
def intEq (a b : Int) : Bool := decide (a = b)
def natEq (a b : Nat) : Bool := decide (a = b)
def intLe (a b : Int) : Bool := decide (a ≤ b)
def natLe (a b : Nat) : Bool := decide (a ≤ b)
def intLt (a b : Int) : Bool := decide (a < b)
def natLt (a b : Nat) : Bool := decide (a < b)
def arrayRead? (xs : Array α) (i : Nat) : Option α := xs[i]?

/-- Primitive implementations need normalization before congruence simplification:
Nat.beq is not definitionally equal to the canonical BEq implementation, and
simplifying containers first can bury Int.neg beneath a disjunction. -/
theorem nat_beq_value (x y : Nat) : Nat.beq x y = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  simp [Nat.beq_eq]

theorem int_neg_value (x : Int) : Int.neg x = -x := rfl

private def ret (e : Expr) : MetaM Expr := mkAppM ``TimeM.done #[e]
private def step (e : Expr) : MetaM Expr := mkAppM ``TimeM.step #[e]

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
private def applyParameters (body : Expr) (args : Array Expr) : MetaM Expr := do
  args.foldlM (fun body arg => do
    let .lam _ _ body _ := body.consumeMData
      | throwError "unsupported function body: expected a parameter lambda"
    pure (body.instantiate1 arg)) body

private structure WFCtx where
  domain : Expr
  pureFn : Expr
  relation : Expr
  arity : Nat := 1
  unpackRemaining : Nat := 0
  recs : Array (Expr × Expr) := #[]
  deriving Inhabited

private structure Ctx where
  source : Name
  self : Expr
  active : List Name := []
  unfolded : IO.Ref NameSet
  wf? : Option WFCtx := none

/-- Direct nonindexed inductives have ordinary constant-cost branch selection.
Array's logical constructor exposes a list conversion, so it is deliberately
excluded here and handled only through its explicit costed operations. -/
private def supportedInductive (ty : Expr) : MetaM Bool := do
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

private def withUniqueParameterNames {m : Type → Type} [Monad m]
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

private def wfProve (ctx : Ctx) (type : Expr) : MetaM Expr := do
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
private def wfCallback? (ctx : Ctx) (ty : Expr) : MetaM (Option (Expr × Expr)) := do
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
  private partial def translate (ctx : Ctx) (e : Expr) : MetaM Expr := do
    let e := e.consumeMData
    match e with
    | .fvar _ | .lit _ =>
      firstOrderResult (← inferType e)
      ret e
    | .letE n ty val body _ =>
      if (← isProp ty) || (← isType val) then
        -- Only erased bindings may be substituted without accounting for evaluation.
        translate ctx (body.instantiate1 val)
      else
        sequenceWith ctx (← translate ctx val) fun val =>
          withLetDecl n ty val fun x => do
            let body ← translate ctx (body.instantiate1 x)
            mkLetFVars #[x] body
    | .proj name idx value =>
      firstOrderResult (← inferType e)
      sequenceWith ctx (← translate ctx value) fun value => do
        if name == ``Array then
          let size ← mkAppM ``Array.size #[value]
          mkAppM ``charge #[← mkAppM ``Nat.succ #[size], .proj name idx value]
        else step (← ret (.proj name idx value))
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
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let some wf := ctx.wf? then
      if let some (_, timed) := wf.recs.find? (fun (original, _) => original == fn) then
        unless args.size == 2 do throwError "partially applied recursive callback is unsupported"
        return ← sequenceWith ctx (← translatePacked ctx args[0]! wf.arity) fun value => do
          let expected := (← inferType (mkApp timed value)).bindingDomain!
          let proof ← adaptProof ctx args[1]! expected
          pure (mkProj ``Subtype 0 (mkApp2 timed value proof))
    let .const name levels := fn
      | throwError "higher-order calls are unsupported:{indentExpr e}"
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
    let args := e.getAppArgs
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
