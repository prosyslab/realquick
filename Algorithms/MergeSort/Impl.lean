import RealQuick.TimeM
import RealQuick.Instrumentation

import Algorithms.MergeSort.Correctness
open Algorithms.MergeSort.Correctness

open RealQuick.TimeM

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

private theorem split_lt_length_of_length_ge_two
    (xs : List Int) (hxs : 2 ≤ xs.length) :
    (split xs).1.length < xs.length ∧
      (split xs).2.length < xs.length := by
  have hsum := split_preserves_length xs
  have hbalanced := split_balanced xs
  dsimp at hbalanced
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
    have hlt := split_lt_length_of_length_ge_two (x :: y :: xs) (by simp)
    rw [h] at hlt
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
    simp [RealQuick.Instrumentation.intLe, decide_eq_true h]
    simp [RealQuick.Instrumentation.WF.seqEq, TimeM.step, bind]
    simp only [List.length_cons] at ih ⊢
    dsimp [merge_timed, TimeM.cost] at ih
    omega
  | case4 x xs y ys h ih =>
    rw [merge_timed_eq_def]
    simp [RealQuick.Instrumentation.intLe, decide_eq_false h]
    simp [RealQuick.Instrumentation.WF.seqEq, TimeM.step, bind]
    simp only [List.length_cons] at ih ⊢
    dsimp [merge_timed, TimeM.cost] at ih
    omega

end Algorithms.MergeSort.Impl
