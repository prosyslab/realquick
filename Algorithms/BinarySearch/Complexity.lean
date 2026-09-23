import VeriQuick.Complexity
import Algorithms.BinarySearch.Impl

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.BinarySearch.Impl

namespace Algorithms.BinarySearch.Complexity

/-!
`lowerBound_timed key a` costs at most `40 * (log₂ n + 1) + 11` ticks, where
`n = a.size`, so it is `O(log n)` uniformly in `key`. -/

/-- Logarithmic cost bound with a nonzero value at input size zero. -/
def Bound (n : Nat) : Nat := Nat.log2 n + 1

theorem midpoint_timed_cost (lo hi : Nat) : (midpoint_timed lo hi).2 = 4 := rfl

theorem readAt?_timed_cost (a : Array Nat) (i : Nat) : (readAt?_timed a i).2 = 2 := rfl

theorem active_timed_cost (lo hi : Nat) : (active_timed lo hi).2 = 3 := rfl

/-- One interval update costs at most 16 ticks. -/
theorem nextBounds_cost (a : Array Nat) (key lo hi : Nat) :
    (nextBounds_timed a key lo hi).cost ≤ 16 := by
  simp only [nextBounds_timed, TimeM.cost, TimeM.snd_step, TimeM.snd_seq, TimeM.fst_seq,
    midpoint_timed_value, readAt?_timed_value, midpoint_timed_cost, readAt?_timed_cost]
  split
  · cases VeriQuick.Instrumentation.natLt _ key <;>
      simp only [TimeM.snd_step, TimeM.snd_seq, TimeM.fst_step, TimeM.fst_done, TimeM.snd_done,
        cond_true, cond_false, midpoint_timed_cost] <;> omega
  · simp only [TimeM.snd_step, TimeM.snd_done]
    omega

/-- The loop costs at most 40 ticks per unit of fuel, plus 6. -/
theorem loop_cost (a : Array Nat) (key fuel lo hi : Nat) :
    (loop_timed a key fuel lo hi).cost ≤ 40 * fuel + 6 := by
  fun_induction loop a key fuel lo hi with
  | case1 lo hi =>
    rw [loop_timed]
    simp only [TimeM.cost, TimeM.snd_step, TimeM.snd_done]
    omega
  | case2 fuel lo hi hact ih =>
    rw [loop_timed]
    have hnext := nextBounds_cost a key lo hi
    simp only [TimeM.cost, TimeM.snd_step, TimeM.snd_seq, TimeM.fst_seq, TimeM.fst_step,
      TimeM.fst_done, TimeM.snd_done, active_timed_value, nextBounds_timed_value, hact,
      active_timed_cost] at hnext ih ⊢
    omega
  | case3 fuel lo hi hact =>
    rw [loop_timed]
    simp only [TimeM.cost, TimeM.snd_step, TimeM.snd_seq, active_timed_value, hact,
      active_timed_cost, TimeM.snd_done]
    omega

/-- Explicit tick bound for the whole search. -/
theorem lowerBound_cost (key : Nat) (a : Array Nat) :
    (lowerBound_timed key a).cost ≤ 40 * Bound a.size + 11 := by
  have h := loop_cost a key (Nat.log2 a.size + 1) 0 a.size
  simp only [lowerBound_timed, Bound, TimeM.cost, TimeM.snd_step, TimeM.snd_seq, TimeM.fst_seq,
    TimeM.fst_step, TimeM.fst_done, TimeM.snd_done, Nat.add_eq] at h ⊢
  omega

/-- For each key, the search cost is `O(log n)` in the array size. -/
theorem lowerBound_asymptotic (key : Nat) :
    Asymptotic (lowerBound_timed key) (.some Bound) := by
  refine ⟨51, 0, by omega, fun a _ => ?_⟩
  have h := lowerBound_cost key a
  have : 1 ≤ Bound a.size := Nat.le_add_left 1 _
  change (lowerBound_timed key a).cost ≤ 51 * Bound a.size
  omega

end Algorithms.BinarySearch.Complexity
