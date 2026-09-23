import VeriQuick.TimeM
import VeriQuick.Instrumentation

import Algorithms.Euclidean.Correctness
open Algorithms.Euclidean.Correctness

open VeriQuick.TimeM

namespace Algorithms.Euclidean.Impl

def gcd (a b : Nat) : Nat :=
  if _h : b = 0 then
    a
  else
    gcd b (a % b)
termination_by b
decreasing_by
  exact Nat.mod_lt a (Nat.pos_of_ne_zero _h)

#eval gcd 48 18 -- 6

theorem euclidean_correct : Correct gcd := by
  intro a b
  fun_induction gcd a b with
  | case1 a =>
    simp
  | case2 a b h ih =>
    calc
      gcd b (a % b) = Nat.gcd b (a % b) := ih
      _ = Nat.gcd (a % b) b := Nat.gcd_comm _ _
      _ = Nat.gcd b a := (Nat.gcd_rec b a).symm
      _ = Nat.gcd a b := Nat.gcd_comm _ _

#instrument gcd as gcd_timed

/-- proof time for base case:
T(a, 0) = 3
-/
theorem gcd_timed_base (a : Nat) :
    (gcd_timed a 0).cost = 3 := by
  rw [gcd_timed_eq_def]
  rfl

/-- proof time for each recursive step
T(a, b) = 4 + T(b, a % b)
-/
theorem gcd_timed_step (a b : Nat) (hb : b ≠ 0) :
    (gcd_timed a b).cost = (gcd_timed b (a % b)).cost + 4 := by
  rw [gcd_timed_eq_def]
  dsimp [TimeM.cost, TimeM.step, TimeM.tick, TimeM.done,
    VeriQuick.Instrumentation.WF.seqEq, VeriQuick.Instrumentation.natEq,
    Bind.bind, Pure.pure, instMonadTimeM]
  simp only [hb, decide_false, Bool.false_eq_true, ↓reduceDIte]
  change 1 + (1 + (gcd_timed b (a % b)).cost + 1) + 1 = (gcd_timed b (a % b)).cost + 4
  omega

/-- proof total step satisfies: k <= O(log2 n) -/
private theorem remainder_halves (b r : Nat)
    (hr : 0 < r) (hrb : r < b) :
    2 * (b % r) < b := by
  have hs := Nat.mod_lt b hr
  by_cases h : 2 * r ≤ b
  · omega
  · have heq : b % r = b - r := by
      rw [Nat.mod_eq_sub_mod (Nat.le_of_lt hrb)]
      exact Nat.mod_eq_of_lt (by omega)
    omega

/-- total cost bounds in: 8*k + 3 -/
private theorem gcd_timed_cost_lt_pow (k : Nat) :
    ∀ a b : Nat, b < 2 ^ k →
      (gcd_timed a b).cost ≤ 8 * k + 3 := by
  induction k with
  | zero =>
    intro a b hb
    have hb0 : b = 0 := by simpa using hb
    subst b
    rw [gcd_timed_base]
    omega
  | succ k ih =>
    intro a b hb
    by_cases hb0 : b = 0
    · subst b
      rw [gcd_timed_base]
      omega
    · rw [gcd_timed_step a b hb0]
      by_cases hr0 : a % b = 0
      · rw [hr0, gcd_timed_base]
        omega
      · rw [gcd_timed_step b (a % b) hr0]
        have hhalf : 2 * (b % (a % b)) < b :=
          remainder_halves b (a % b)
            (Nat.pos_of_ne_zero hr0)
            (Nat.mod_lt a (Nat.pos_of_ne_zero hb0))
        have hs : b % (a % b) < 2 ^ k := by
          rw [Nat.pow_succ] at hb
          omega
        have hcost := ih (a % b) (b % (a % b)) hs
        omega

theorem gcd_timed_logarithmic (a b : Nat) :
    (gcd_timed a b).cost ≤ 8 * Nat.log2 b + 11 := by
  have h := gcd_timed_cost_lt_pow (Nat.log2 b + 1) a b
    (Nat.lt_log2_self (n := b))
  omega

theorem gcd_timed_total_time :
    ∃ c : Nat, 0 < c ∧ ∃ n₀ : Nat, ∀ a b : Nat,
      n₀ ≤ b → (gcd_timed a b).cost ≤ c * Nat.log2 b := by
  refine ⟨20, by decide, 2, ?_⟩
  intro a b hb
  have hlog : 1 ≤ Nat.log2 b :=
    (Nat.le_log2 (by omega : b ≠ 0)).2 (by simpa using hb)
  have hcost := gcd_timed_logarithmic a b
  omega

end Algorithms.Euclidean.Impl
