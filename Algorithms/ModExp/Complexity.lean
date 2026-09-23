import VeriQuick.Complexity
import Algorithms.ModExp.Impl

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.ModExp.Impl

namespace Algorithms.ModExp.Complexity

/-- One bit costs at most seven ticks: five when the bit = zero, seven when
it = one -/
theorem absorbBit_timed_cost (m base e acc : Nat) : (absorbBit_timed m base e acc).cost ≤ 7 := by
  simp only [absorbBit_timed, TimeM.cost, TimeM.snd_seq, TimeM.snd_step, TimeM.snd_done]
  have hlow : (lowBit_timed e).2 = 2 := rfl
  cases ((lowBit_timed e).seq
      fun v => (TimeM.done (VeriQuick.Instrumentation.natEq v 1)).step).1 <;>
    simp only [cond_true, cond_false, TimeM.snd_step, TimeM.snd_seq, TimeM.snd_done] <;> omega

/-- The loop exits in four ticks once the exponent reaches zero. -/
theorem loop_timed_zero (m acc base : Nat) : (loop_timed m acc base 0).cost = 4 := by
  rw [loop_timed_eq_def]
  rfl

/-- One iteration costs its `absorbBit` call plus six ticks. -/
theorem loop_timed_succ (m acc base e : Nat) (he : e ≠ 0) :
    (loop_timed m acc base e).cost =
      (loop_timed m (absorbBit m base e acc) (base * base % m) (e / 2)).cost +
        (absorbBit_timed m base e acc).cost + 6 := by
  have hrec : (loop_timed_certified m
      ⟨(absorbBit_timed m base e acc).1, ⟨(base * base).mod m, e.div 2⟩⟩).1 =
      loop_timed m (absorbBit m base e acc) (base * base % m) (e / 2) :=
    congrArg (fun v => (loop_timed_certified m ⟨v, ⟨(base * base).mod m, e.div 2⟩⟩).1)
      (absorbBit_timed_value m base e acc)
  rw [loop_timed_eq_def]
  simp only [TimeM.cost, TimeM.step, bind, TimeM.tick, VeriQuick.Instrumentation.WF.seqEq,
    TimeM.done, VeriQuick.Instrumentation.natEq, he, decide_false, Nat.zero_add,
    Bool.false_eq_true, ↓reduceDIte, Nat.add_zero, VeriQuick.Instrumentation.WF.fst_certified,
    Nat.add_right_cancel_iff]
  change 1 + ((absorbBit_timed m base e acc).cost + 3 +
      (loop_timed_certified m
        ⟨(absorbBit_timed m base e acc).1, ⟨(base * base).mod m, e.div 2⟩⟩).1.cost + 1) =
    (loop_timed m (absorbBit m base e acc) (base * base % m) (e / 2)).cost +
      (absorbBit_timed m base e acc).cost + 5
  rw [hrec]
  omega

/-- Each loop iteration costs at most 13 ticks and halves `e`, so the loop runs
`Nat.log2 e + 1` times for `e > 0`. -/
theorem loop_timed_bound (m acc base e : Nat) :
    (loop_timed m acc base e).cost ≤ 13 * (Nat.log2 e + 1) + 4 := by
  fun_induction loop m acc base e with
  | case1 acc base =>
    rw [loop_timed_zero]
    omega
  | case2 acc base e h ih =>
    rw [loop_timed_succ m acc base e h]
    have habsorb := absorbBit_timed_cost m base e acc
    by_cases h2 : 2 ≤ e
    · have hlog : Nat.log2 e = Nat.log2 (e / 2) + 1 := by
        rw [Nat.log2_def, if_pos h2]
      omega
    · have he : e / 2 = 0 := by omega
      rw [he, loop_timed_zero]
      omega

/-- `modExp` adds two ticks on top of the loop: its own call and reducing the
base. -/
theorem modExp_timed_cost (b e m : Nat) :
    (modExp_timed b e m).cost = (loop_timed m 1 (b % m) e).cost + 2 := by
  simp only [modExp_timed, TimeM.cost, TimeM.snd_step, TimeM.snd_seq, TimeM.fst_step,
    TimeM.snd_done, TimeM.fst_done, show b.mod m = b % m from rfl]
  omega

/-- The explicit `O(log e)` bound for modular exponentiation. -/
theorem modExp_timed_bound (b e m : Nat) :
    (modExp_timed b e m).cost ≤ 13 * (Nat.log2 e + 1) + 6 := by
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
  refine ⟨32, 2, by decide, ?_⟩
  rintro ⟨b, e, m⟩
  dsimp only [Size.size, Bound]
  intro he
  have hlog : 1 ≤ Nat.log2 e :=
    (Nat.le_log2 (by omega)).2 (by simpa only [Nat.pow_one] using he)
  have h := modExp_timed_bound b e m
  omega

end Algorithms.ModExp.Complexity
