import VeriQuick.TimeM
import VeriQuick.Instrumentation
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

import Algorithms.MergeSort.Correctness
open Algorithms.MergeSort.Correctness

open VeriQuick.TimeM

namespace Algorithms.MergeSort.Impl

def split : List Int → (List Int × List Int)
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: xs =>
    let s := split xs
    (x :: s.1, y :: s.2)

#eval split [1,2,3,4]

/-- `split` returns lists whose lengths differ by at most one. -/
theorem split_balanced (xs : List Int) :
  let (s1, s2) := split xs
  s1.length - s2.length ≤ 1 ∧ s2.length - s1.length ≤ 1 := by
  match xs with
  | [] => simp [split]
  | [x] => simp [split]
  | x :: y :: xs =>
    simp [split]
    have ih := split_balanced xs
    simp at ih
    omega

theorem split_preserves_length (xs : List Int) :
  let (s1, s2) := split xs
  s1.length + s2.length = xs.length := by
  match xs with
  | [] => simp [split]
  | [x] => simp [split]
  | x :: y :: xs =>
    simp [split]
    have ih := split_preserves_length xs
    simp at ih
    omega

/-- `split` produces two list of length ⌈n/2⌉ and ⌊n/2⌋ -/
theorem split_lengths (xs : List Int) (a b : List Int) (h : split xs = (a, b)) :
    a.length = (xs.length + 1) / 2 ∧ b.length = xs.length / 2 := by
  fun_induction split xs generalizing a b with
  | case1 => rcases h; decide
  | case2 x => rcases h; simp
  | case3 x y xs s ih =>
    rcases h
    subst s
    have h_ih := ih (split xs).1 (split xs).2 rfl
    simp only [List.length_cons]
    omega

theorem split_reduces_length
    (x y : Int) (xs : List Int)
    (h : split (x :: y :: xs) = (a, b)) :
    a.length < (x :: y :: xs).length ∧ b.length < (x :: y :: xs).length := by
  have hsum := split_preserves_length (x :: y :: xs)
  have hbalanced := split_balanced (x :: y :: xs)
  simp [h] at hsum hbalanced ⊢
  omega

def merge : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys

def mergeSort : List Int → List Int
  | [] => []
  | [x] => [x]
  | x :: y :: xs =>
    match h : split (x :: y :: xs) with
    | (a, b) =>
      let a' := mergeSort a
      let b' := mergeSort b
      merge a' b'
termination_by xs => xs.length
decreasing_by
  all_goals
    have hlt := split_reduces_length x y xs h
    first | exact hlt.1 | exact hlt.2

#eval mergeSort [1,4,2,9,8]

#instrument split as split_timed
#instrument merge as merge_timed
#instrument mergeSort as mergeSort_timed

/-- split preserves the elements: the output is a permutation of the input -/
theorem split_perm (xs : List Int) :
    ((split xs).1 ++ (split xs).2).Perm xs := by
  fun_induction split xs with
  | case1 => rfl
  | case2 x => rfl
  | case3 x y xs s ih =>
    -- ih : ((split xs).1 ++ (split xs).2).Perm xs
    simp
    have h : (s.fst ++ y :: s.snd).Perm (y :: s.fst ++ s.snd) := by
      exact List.perm_middle
    -- (y :: s.fst ++ s.snd) ~ (y :: xs)
    apply h.trans
    -- s.fst ++ s.snd ~ xs (this is the IH)
    exact ih.cons y

/-- `merge` preserves permutation relation -/
theorem merge_perm (xs ys : List Int) :
    (merge xs ys).Perm (xs ++ ys) := by
  fun_induction merge xs ys with
  | case1 => rfl
  | case2 => simp
  | case3 x xs y ys h ih =>
    apply List.Perm.cons
    simpa
  | case4 x xs y ys h ih =>
    have ih_y := ih.cons y
    apply ih_y.trans
    exact List.perm_middle.symm

/-- `merge` preserves sortedness -/
theorem merge_sorted (xs ys : List Int)
    (hxs : Sorted xs) (hys : Sorted ys) : Sorted (merge xs ys) := by
  revert hxs hys
  fun_induction merge xs ys with
  | case1 =>
    intro _ hys
    exact hys
  | case2 =>
    intro hxs _
    exact hxs
  | case3 x xs y ys h ih =>
    intro hxs hys
    -- ih : Sorted xs → Sorted (y :: ys) → Sorted (merge xs (y :: ys))

    -- From Sorted (x :: xs), we know `x` is the least element of `x :: xs`,
    -- and `xs` is sorted.
    obtain ⟨hx, hxs_sorted⟩ := List.pairwise_cons.mp hxs
    -- From Sorted (y :: ys), we know `y` is the least element of `y :: ys`,
    -- and `ys` is sorted.
    obtain ⟨hy, hys_sorted⟩ := List.pairwise_cons.mp hys
    have htail : Sorted (merge xs (y :: ys)) := ih hxs_sorted hys
    -- From the fact that `y` is the least element of `y :: ys` and `h : x ≤ y`,
    -- we deduce that `x` is smaller than `y :: ys`.
    have hx_le_y_ys : ∀ y' ∈ y :: ys, x ≤ y' := by
      intro y' hy'
      rcases List.mem_cons.mp hy' with rfl | hy'
      · exact h
      · have h1 := hy y' hy'
        exact Int.le_trans h h1
    -- From that `x` is the less than any of `xs` and `y :: ys`,
    -- we can say `x` is the least of `merge xs (y :: ys)`.
    have hx_le_merge_xs_y_ys : ∀ z ∈ merge xs (y :: ys), x ≤ z := by
      intro z hz
      have hz := (merge_perm xs (y :: ys)).mem_iff.mp hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hx z hz
      · exact hx_le_y_ys z hz
    
    -- Then we know
    -- (1) x is the least element of `xs` and `y :: ys`.
    -- (2) The main goal is `Sorted (x :: merge xs (y :: ys))`
    -- (3) Then we can reduce the goal to `Sorted (merge xs (y :: ys))`
    exact List.pairwise_cons.mpr ⟨hx_le_merge_xs_y_ys, htail⟩ 
  | case4 x xs y ys h ih =>
    intro hxs hys
    -- ih : Sorted (x :: xs) → Sorted ys → Sorted (merge (x :: xs) ys)
    obtain ⟨hx, hxs_sorted⟩ := List.pairwise_cons.mp hxs
    obtain ⟨hy, hys_sorted⟩ := List.pairwise_cons.mp hys
    have htail := ih hxs hys_sorted
    have hy_lt_x_xs : ∀ z ∈ x :: xs, y < z := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · omega -- automatically use ¬(x ≤ y)
      · have hx_le_z := hx z hz
        omega -- automatically use ¬(x ≤ y) and x ≤ z ⇒ y < z

    -- Every element of the merged tail comes from `x :: xs` or `ys`,
    -- and `y` is at most every element of either input.
    have hy_le_merge_x_xs_ys : ∀ z ∈ merge (x :: xs) ys, y ≤ z := by
      intro z hz
      have hz := (merge_perm (x :: xs) ys).mem_iff.mp hz
      rcases List.mem_append.mp hz with hz | hz
      · exact Int.le_of_lt (hy_lt_x_xs z hz)
      · exact hy z hz
    exact List.pairwise_cons.mpr ⟨hy_le_merge_x_xs_ys, htail⟩


theorem mergeSort_correct_sorted (xs : List Int) :
  Sorted (mergeSort xs) := by
  fun_induction mergeSort xs with
  | case1 => simp [Sorted]
  | case2 x => simp [Sorted]
  | case3 x y xs a b h a' b' ih_a ih_b =>
    -- The induction hypotheses say that both recursively sorted halves are sorted.
    exact merge_sorted a' b' ih_a ih_b

theorem mergeSort_correct_perm (xs : List Int) :
  (mergeSort xs).Perm xs := by
  fun_induction mergeSort xs with
  | case1 => rfl
  | case2 x => rfl
  | case3 x y xs a b h a' b' ih_a ih_b =>
    -- Merging preserves the elements of the two recursively sorted halves.
    apply (merge_perm a' b').trans
    -- The induction hypotheses recover the original halves.
    apply (ih_a.append ih_b).trans
    -- Splitting preserved the elements of the original input.
    have hsplit := split_perm (x :: y :: xs)
    rw [h] at hsplit
    exact hsplit

theorem mergeSort_correct : Correct mergeSort := by
  intro xs
  constructor
  · exact mergeSort_correct_sorted xs
  · exact mergeSort_correct_perm xs

#eval split_timed [] -- 0 => 5
#eval split_timed [1] -- 1 => 6 (+1)
#eval split_timed [1,2] -- 2 => 12 (+6)
#eval split_timed [1,2,3] -- 3 => 13 (+1)
#eval split_timed [1,2,3,4] -- 4 ==> 19 (+6)
#eval split_timed [1,2,3,4,5] -- 4 ==> 20 (+1)

theorem split_timed_linear (xs : List Int) :
  TimeM.cost (split_timed xs) ≤ 4 * xs.length + 5 := by
  fun_induction split xs with
  | case1 =>
    change 5 ≤ 5
    omega
  | case2 =>
    change 6 ≤ 9
    omega
  | case3 x y xs s ih =>
    -- Note: split (x :: y :: xs) = (x :: (split xs).1, y :: (split xs).2)
    change (split_timed xs).cost + 7 ≤ 4 * xs.length + 13
    omega

#eval merge_timed [] [] -- T(0, 0) = 2
#eval merge_timed [1] [] -- T(1, 0) = 2
#eval merge_timed [1] [2] -- T(1, 1) = 8
#eval merge_timed [1,3] [2] -- T(2, 1) = 14 = T(1, 1) + 6
#eval merge_timed [1] [2,3] -- T(1, 2) = 8
#eval merge_timed [1,3] [2,4] -- T(2, 2) = 20 = T(2, 1) + 6
#eval merge_timed [5,6] [1,2,3]

#check merge_timed_certified

/- NOTE: TimeM instrumentation is leaking abstractions. I had to manually unfold low-level
   instrumentation internals: WellFounded.fix, seqEq, TimeM.tick, ...
   we must provide a cleaner layer so that users can focus on algebraic inequalities ..
   we could extend the instrumention to generate useful cost lemmas to skip those parts,
   and make a dedicated tactic.
-/
theorem merge_timed_linear (xs ys : List Int) :
  TimeM.cost (merge_timed xs ys) ≤ 6 * (xs.length + ys.length) + 2 := by
  fun_induction merge xs ys with
  | case1 ys =>
    rw [merge_timed_eq_def]
    simp [TimeM.step, TimeM.done, TimeM.cost]
    change 2 ≤ 6 * ys.length + 2
    omega
  | case2 xs =>
    rw [merge_timed_eq_def]
    simp [TimeM.step, TimeM.done, TimeM.cost]
    change 2 ≤ 6 * xs.length + 2
    omega
  | case3 x xs y ys h ih =>
    rw [merge_timed_eq_def]
    simp [VeriQuick.Instrumentation.intLe, decide_eq_true h] -- TODO: clean up
    simp [VeriQuick.Instrumentation.WF.seqEq, TimeM.step, bind]
    simp only [List.length_cons] at ih ⊢
    dsimp [merge_timed, TimeM.cost] at ih
    omega
  | case4 x xs y ys h ih =>
    rw [merge_timed_eq_def]
    simp [VeriQuick.Instrumentation.intLe, decide_eq_false h]
    simp [VeriQuick.Instrumentation.WF.seqEq, TimeM.step, bind]
    simp only [List.length_cons] at ih ⊢
    dsimp [merge_timed, TimeM.cost] at ih
    omega


theorem List.length_mergeSort (xs : List Int) : (mergeSort xs).length = xs.length :=
  (mergeSort_correct_perm xs).length_eq

/-- The time taken for mergeSort is bounded by
    the sum of split time, merge time, and two mergeSort times. -/
theorem mergeSort_timed_step (x y : Int) (xs : List Int) (a b : List Int)
  (h : split (x :: y :: xs) = (a, b)) :
  (mergeSort_timed (x :: y :: xs)).cost ≤
    (split_timed (x :: y :: xs)).cost +
    (mergeSort_timed a).cost + (mergeSort_timed b).cost +
    (merge_timed (mergeSort a) (mergeSort b)).cost + 5 := by
  rw [mergeSort_timed_eq_def]
  have hcert (l : List Int) : (mergeSort_timed_certified l).1 = mergeSort_timed l := rfl
  simp [VeriQuick.Instrumentation.WF.seqEq, TimeM.step, TimeM.done, bind, hcert ?_]
  -- TODO: tidier way to prove this ...
  have hsplit_val : (split_timed (x :: y :: xs)).fst = (a, b) := by
    simp [split_timed_value, h]  
  rw [hsplit_val]
  dsimp [Prod.fst, Prod.snd]
  -- The main goal still has (mergeSort_timed a).fst.
  -- `omega` can't reason that it is equal to (mergeSort a),
  have hmergeSort_val : ∀ a, (mergeSort_timed a).1 = mergeSort a := by
    simp [mergeSort_timed_value]
  
  simp [hmergeSort_val a, hmergeSort_val b]
  omega

/-- We show the amount of work in one mergeSort level is linear -/
theorem mergeSort_timed_recurrence
  (x y : Int) (xs : List Int) (a b : List Int) (h : split (x :: y :: xs) = (a, b)) :
  (mergeSort_timed (x :: y :: xs)).cost ≤
    (mergeSort_timed a).cost + (mergeSort_timed b).cost +
    10 * (x :: y :: xs).length + 12 := by
  have hstep := mergeSort_timed_step x y xs a b h
  have hsplit := split_timed_linear (x :: y :: xs)
  have hmerge := merge_timed_linear (mergeSort a) (mergeSort b)
  rw [List.length_mergeSort a, List.length_mergeSort b] at hmerge
  have hsum : a.length + b.length = (x :: y :: xs).length := by
    simpa [h] using split_preserves_length (x :: y :: xs)
  omega

-- A merge-sort call does linear work, then recurses on the two halves.
-- The logarithmic budget below accounts for repeatedly halving the input.

/-- The recursive calls have enough logarithmic slack to pay for one floor
    half of the input. -/
private theorem balanced_halves_core (a b n : Nat)
    (ha : a = (n + 1) / 2) (hb : b = n / 2) (hn : 2 ≤ n) :
    a * (a.log2 + 1) + b * (b.log2 + 1) + b ≤
      n * (n.log2 + 1) := by
  subst a
  subst b
  have hleft_log : ((n + 1) / 2).log2 ≤ n.log2 := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    apply Nat.log_mono_right
    omega
  have hright_log : (n / 2).log2 + 1 = n.log2 := by
    have hlog : (n / 2).log2 = n.log2 - 1 := by
      simp only [Nat.log2_eq_log_two]
      exact Nat.log_div_base 2 n
    have hlog_pos : 1 ≤ n.log2 := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_pos (by omega) hn
    rw [hlog, Nat.sub_add_cancel hlog_pos]
  have hleft :
      (n + 1) / 2 * (((n + 1) / 2).log2 + 1) ≤
        (n + 1) / 2 * (n.log2 + 1) :=
    Nat.mul_le_mul_left _ (Nat.succ_le_succ hleft_log)
  have hsum : (n + 1) / 2 + n / 2 = n := by omega
  calc
    (n + 1) / 2 * (((n + 1) / 2).log2 + 1) +
          n / 2 * ((n / 2).log2 + 1) + n / 2
      ≤ (n + 1) / 2 * (n.log2 + 1) + n / 2 * n.log2 + n / 2 := by
        rw [hright_log]
        simpa only [Nat.add_assoc] using
          Nat.add_le_add_right hleft (n / 2 * n.log2 + n / 2)
    _ = n * (n.log2 + 1) := by
      calc
        (n + 1) / 2 * (n.log2 + 1) + n / 2 * n.log2 + n / 2 =
            ((n + 1) / 2 + n / 2) * (n.log2 + 1) := by ring
        _ = n * (n.log2 + 1) := by rw [hsum]

/-- One merge-sort level: the balanced recursive work plus its affine overhead
    fits in the `n * log2 n` budget. -/
private theorem balanced_halves_nlogn (a b n : Nat)
    (ha : a = (n + 1) / 2) (hb : b = n / 2) (hn : 2 ≤ n) :
    50 * a * (a.log2 + 1) + 50 * b * (b.log2 + 1) + 10 * n + 16 ≤
      50 * n * (n.log2 + 1) := by
  have hcore := balanced_halves_core a b n ha hb hn
  have hwork : 10 * n + 16 ≤ 50 * b := by
    rw [hb]
    omega
  calc
    50 * a * (a.log2 + 1) + 50 * b * (b.log2 + 1) + 10 * n + 16
      ≤ 50 * a * (a.log2 + 1) + 50 * b * (b.log2 + 1) + 50 * b :=
        Nat.add_le_add_left hwork _
    _ = 50 * (a * (a.log2 + 1) + b * (b.log2 + 1) + b) := by ring
    _ ≤ 50 * (n * (n.log2 + 1)) := Nat.mul_le_mul_left 50 hcore
    _ = 50 * n * (n.log2 + 1) := by ring

#eval mergeSort_timed [] -- 3
#eval mergeSort_timed [1] -- 4
#eval mergeSort_timed [2,1] -- 33
#eval mergeSort_timed [3,2,1] -- 69

theorem mergeSort_timed_nlogn (l : List Int) :
  TimeM.cost (mergeSort_timed l) ≤ 50 * l.length * (Nat.log2 l.length + 1) + 4 := by
  fun_induction mergeSort l with
  | case1 =>
    simp only [TimeM.cost, List.length_nil, mul_zero, Nat.log2_zero, zero_add, mul_one]
    decide
  | case2 x =>
    simp only [TimeM.cost, List.length_cons, List.length_nil, zero_add, mul_one]
    change 4 ≤ 54
    omega
  | case3 x y xs a b h a' b' ih_a ih_b =>
    have hlengths := split_lengths (x :: y :: xs) a b h
    have hn : 2 ≤ (x :: y :: xs).length := by simp
    have hrecurrence := mergeSort_timed_recurrence x y xs a b h
    calc
      TimeM.cost (mergeSort_timed (x :: y :: xs))
        ≤ TimeM.cost (mergeSort_timed a) + TimeM.cost (mergeSort_timed b) +
            10 * (x :: y :: xs).length + 12 := hrecurrence
      _ ≤ 50 * a.length * (a.length.log2 + 1) +
            50 * b.length * (b.length.log2 + 1) +
            10 * (x :: y :: xs).length + 20 := by omega
      _ ≤ 50 * (x :: y :: xs).length * ((x :: y :: xs).length.log2 + 1) + 4 := by
        have hbalanced := balanced_halves_nlogn a.length b.length
          (x :: y :: xs).length hlengths.1 hlengths.2 hn
        omega
    
    

end Algorithms.MergeSort.Impl
