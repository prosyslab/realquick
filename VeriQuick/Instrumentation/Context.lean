import Lean

import VeriQuick.TimeM
import VeriQuick.Instrumentation.CostModel

open Lean
open VeriQuick.TimeM

namespace VeriQuick.Instrumentation.WF

open VeriQuick.TimeM

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
restriction as `VeriQuick.TimeM.TimeM.step`. -/
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

end VeriQuick.Instrumentation.WF


namespace VeriQuick.Instrumentation

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


structure WFCtx where
  domain : Expr
  pureFn : Expr
  relation : Expr
  arity : Nat := 1
  unpackRemaining : Nat := 0
  recs : Array (Expr × Expr) := #[]
  deriving Inhabited

structure Ctx where
  /-- the source function being instrumented -/
  source : Name
  /-- the generated timed function -/
  self : Expr
  active : List Name := []
  unfolded : IO.Ref NameSet
  wf? : Option WFCtx := none

end VeriQuick.Instrumentation
