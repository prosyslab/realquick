import VeriQuick.Complexity
import Algorithms.ModExp.Impl

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.ModExp.Impl

namespace Algorithms.ModExp.Complexity

/-- The loop exits in four ticks once the exponent reaches zero. -/
theorem loop_timed_zero (m acc base : Nat) : (loop_timed m acc base 0).cost = 4 := by
  rw [loop_timed_eq_def]
  rfl

/-- An iteration on an odd exponent costs twelve ticks. -/
theorem loop_timed_odd (m acc base e : Nat) (he : e ≠ 0) (hodd : lowBit e = 1) :
    (loop_timed m acc base e).cost = (loop_timed m (acc * base % m) (base * base % m) (e / 2)).cost + 12 := by
  have hlow : lowBit_timed e = (lowBit e, 2) := rfl
  rw [loop_timed_eq_def]
  simp +arith only [TimeM.cost, TimeM.step, bind, TimeM.tick, VeriQuick.Instrumentation.WF.seqEq,
    TimeM.done, VeriQuick.Instrumentation.natEq, he, decide_false, Bool.false_eq_true, ↓reduceDIte,
    hlow, hodd, decide_true, Nat.mul_eq, VeriQuick.Instrumentation.WF.fst_certified]
  rfl

/-- An iteration on an even exponent costs ten ticks. -/
theorem loop_timed_even (m acc base e : Nat) (he : e ≠ 0) (heven : lowBit e ≠ 1) :
    (loop_timed m acc base e).cost = (loop_timed m acc (base * base % m) (e / 2)).cost + 10 := by
  have hlow : lowBit_timed e = (lowBit e, 2) := rfl
  rw [loop_timed_eq_def]
  simp +arith only [TimeM.cost, TimeM.step, bind, TimeM.tick, VeriQuick.Instrumentation.WF.seqEq,
    TimeM.done, VeriQuick.Instrumentation.natEq, he, decide_false, Bool.false_eq_true, ↓reduceDIte,
    hlow, heven, Nat.mul_eq, VeriQuick.Instrumentation.WF.fst_certified]
  rfl

/-- Each loop iteration costs at most 12 ticks and halves `e`, so the loop runs
`Nat.log2 e + 1` times for `e > 0`. -/
theorem loop_timed_bound (m acc base e : Nat) :
    (loop_timed m acc base e).cost ≤ 12 * (Nat.log2 e + 1) + 4 := by
  -- Halving either ends the loop or lowers `Nat.log2` by one.
  have hlog (e : Nat) : e / 2 = 0 ∨ Nat.log2 e = Nat.log2 (e / 2) + 1 := by
    by_cases h2 : 2 ≤ e
    · exact .inr (by rw [Nat.log2_def, if_pos h2])
    · exact .inl (by omega)
  fun_induction loop m acc base e with
  | case1 acc base =>
    rw [loop_timed_zero]
    omega
  | case2 acc base e h hodd ih =>
    rw [loop_timed_odd m acc base e h hodd]
    rcases hlog e with he | he
    · rw [he, loop_timed_zero]
      omega
    · omega
  | case3 acc base e h heven ih =>
    rw [loop_timed_even m acc base e h heven]
    rcases hlog e with he | he
    · rw [he, loop_timed_zero]
      omega
    · omega

/-- `modExp` adds two ticks on top of the loop: its own call and reducing the
base. -/
theorem modExp_timed_cost (b e m : Nat) :
    (modExp_timed b e m).cost = (loop_timed m 1 (b % m) e).cost + 2 := by
  simp only [modExp_timed, TimeM.cost, TimeM.snd_step, TimeM.snd_seq, TimeM.fst_step,
    TimeM.snd_done, TimeM.fst_done, show b.mod m = b % m from rfl]
  omega

/-- The explicit `O(log e)` bound for modular exponentiation. -/
theorem modExp_timed_bound (b e m : Nat) :
    (modExp_timed b e m).cost ≤ 12 * (Nat.log2 e + 1) + 6 := by
  have h := loop_timed_bound m 1 (b % m) e
  rw [modExp_timed_cost]
  omega

structure Input where
  base : Nat
  exp : Nat
  modulus : Nat

instance : Size Input where
  size x := x.exp

/-- Logarithmic bound in the exponent. -/
def Bound (n : Nat) : Nat := Nat.log2 n

/-- Instrumented modular exponentiation is `O(log e)`. -/
def complexity : Prop :=
  Asymptotic (fun (x : Input) => modExp_timed x.base x.exp x.modulus) (.some Bound)

/-- For `e ≥ 2`, `Nat.log2 e ≥ 1` absorbs the additive constants. -/
theorem modExp_timed_isLogarithmic : complexity := by
  refine ⟨30, 2, by decide, ?_⟩
  rintro ⟨b, e, m⟩
  dsimp only [Size.size, Bound]
  intro he
  have hlog : 1 ≤ Nat.log2 e :=
    (Nat.le_log2 (by omega)).2 (by simpa only [Nat.pow_one] using he)
  have h := modExp_timed_bound b e m
  omega

end Algorithms.ModExp.Complexity
