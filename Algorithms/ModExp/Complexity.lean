import VeriQuick.Complexity
import Algorithms.ModExp.Impl

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.ModExp.Impl

namespace Algorithms.ModExp.Complexity

/-- The loop exits in four ticks once the exponent reaches zero. -/
theorem loop_timed_zero (modulus acc base : Nat) :
    (loop_timed modulus acc base 0).cost = 4 := by
  rw [loop_timed_eq_def]
  rfl

/-- An iteration on an odd exponent costs twelve ticks. -/
theorem loop_timed_odd (modulus acc base exponent : Nat) (he : exponent ≠ 0)
    (hodd : lowBit exponent = 1) :
    (loop_timed modulus acc base exponent).cost =
      (loop_timed modulus (acc * base % modulus) (base * base % modulus) (exponent / 2)).cost +
        12 := by
  have hlow : lowBit_timed exponent = (lowBit exponent, 2) := rfl
  rw [loop_timed_eq_def]
  simp +arith only [TimeM.cost, TimeM.step, bind, TimeM.tick, VeriQuick.Instrumentation.WF.seqEq,
    TimeM.done, VeriQuick.Instrumentation.natEq, he, decide_false, Bool.false_eq_true, ↓reduceDIte,
    hlow, hodd, decide_true, Nat.mul_eq, VeriQuick.Instrumentation.WF.fst_certified]
  rfl

/-- An iteration on an even exponent costs ten ticks. -/
theorem loop_timed_even (modulus acc base exponent : Nat) (he : exponent ≠ 0)
    (heven : lowBit exponent ≠ 1) :
    (loop_timed modulus acc base exponent).cost =
      (loop_timed modulus acc (base * base % modulus) (exponent / 2)).cost + 10 := by
  have hlow : lowBit_timed exponent = (lowBit exponent, 2) := rfl
  rw [loop_timed_eq_def]
  simp +arith only [TimeM.cost, TimeM.step, bind, TimeM.tick, VeriQuick.Instrumentation.WF.seqEq,
    TimeM.done, VeriQuick.Instrumentation.natEq, he, decide_false, Bool.false_eq_true, ↓reduceDIte,
    hlow, heven, Nat.mul_eq, VeriQuick.Instrumentation.WF.fst_certified]
  rfl

/-- Each loop iteration costs at most 12 ticks and halves `exponent`, so the
loop runs `Nat.log2 exponent + 1` times for `exponent > 0`. -/
theorem loop_timed_bound (modulus acc base exponent : Nat) :
    (loop_timed modulus acc base exponent).cost ≤ 12 * (Nat.log2 exponent + 1) + 4 := by
  -- Halving either ends the loop or lowers `Nat.log2` by one.
  have hlog (exponent : Nat) :
      exponent / 2 = 0 ∨ Nat.log2 exponent = Nat.log2 (exponent / 2) + 1 := by
    by_cases h2 : 2 ≤ exponent
    · exact .inr (by rw [Nat.log2_def, if_pos h2])
    · exact .inl (by omega)
  fun_induction loop modulus acc base exponent with
  | case1 acc base =>
    rw [loop_timed_zero]
    omega
  | case2 acc base exponent h hodd ih =>
    rw [loop_timed_odd modulus acc base exponent h hodd]
    rcases hlog exponent with he | he
    · rw [he, loop_timed_zero]
      omega
    · omega
  | case3 acc base exponent h heven ih =>
    rw [loop_timed_even modulus acc base exponent h heven]
    rcases hlog exponent with he | he
    · rw [he, loop_timed_zero]
      omega
    · omega

/-- `modExp` adds two ticks on top of the loop: its own call and reducing the
base. -/
theorem modExp_timed_cost (base exponent modulus : Nat) :
    (modExp_timed base exponent modulus).cost =
      (loop_timed modulus 1 (base % modulus) exponent).cost + 2 := by
  simp only [modExp_timed, TimeM.cost, TimeM.snd_step, TimeM.snd_seq, TimeM.fst_step,
    TimeM.snd_done, TimeM.fst_done, show base.mod modulus = base % modulus from rfl]
  omega

/-- The explicit `O(log exponent)` bound for modular exponentiation. -/
theorem modExp_timed_bound (base exponent modulus : Nat) :
    (modExp_timed base exponent modulus).cost ≤ 12 * (Nat.log2 exponent + 1) + 6 := by
  have h := loop_timed_bound modulus 1 (base % modulus) exponent
  rw [modExp_timed_cost]
  omega

structure Input where
  base : Nat
  exponent : Nat
  modulus : Nat

instance : Size Input where
  size x := x.exponent

/-- Logarithmic bound in the exponent. -/
def Bound (n : Nat) : Nat := Nat.log2 n

/-- Instrumented modular exponentiation is `O(log exponent)`. -/
def complexity : Prop :=
  Asymptotic (fun (x : Input) => modExp_timed x.base x.exponent x.modulus) (.some Bound)

/-- For `exponent ≥ 2`, `Nat.log2 exponent ≥ 1` absorbs the additive constants. -/
theorem modExp_timed_isLogarithmic : complexity := by
  refine ⟨30, 2, by decide, ?_⟩
  rintro ⟨base, exponent, modulus⟩
  dsimp only [Size.size, Bound]
  intro he
  have hlog : 1 ≤ Nat.log2 exponent :=
    (Nat.le_log2 (by omega)).2 (by simpa only [Nat.pow_one] using he)
  have h := modExp_timed_bound base exponent modulus
  omega

end Algorithms.ModExp.Complexity
