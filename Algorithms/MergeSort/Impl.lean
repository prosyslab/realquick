import RealQuick.TimeM
import RealQuick.Instrumentation

import Algorithms.MergeSort.Correctness
open Algorithms.MergeSort.Correctness

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

-- #instrument mergeSort as mergeSort_timed

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

theorem merge_perm (xs ys : List Int) :
    (merge xs ys).Perm (xs ++ ys) := by
  match xs, ys with
  | [], ys => simp [merge]
  | x :: xs, [] => simp [merge]
  | x :: xs, y :: ys =>
    by_cases h : x ≤ y
    · simpa [merge, h] using (merge_perm xs (y :: ys)).cons x
    · simpa [merge, h] using
        ((merge_perm (x :: xs) ys).cons y).trans List.perm_middle.symm

private theorem merge_sorted (xs ys : List Int)
    (hxs : Sorted xs) (hys : Sorted ys) : Sorted (merge xs ys) := by
  match xs, ys with
  | [], ys => simpa [merge] using hys
  | x :: xs, [] => simpa [merge] using hxs
  | x :: xs, y :: ys =>
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hxs
    obtain ⟨hy, hys⟩ := List.pairwise_cons.mp hys
    by_cases h : x ≤ y
    · simp only [merge, h, ↓reduceIte, Sorted, List.pairwise_cons]
      constructor
      · intro z hz
        have hz := (merge_perm xs (y :: ys)).mem_iff.mp hz
        simp only [List.mem_append, List.mem_cons] at hz
        rcases hz with hz | rfl | hz
        · exact hx z hz
        · exact h
        · exact Int.le_trans h (hy z hz)
      · exact merge_sorted xs (y :: ys) hxs (List.pairwise_cons.mpr ⟨hy, hys⟩)
    · simp only [merge, h, ↓reduceIte, Sorted, List.pairwise_cons]
      constructor
      · intro z hz
        have hz := (merge_perm (x :: xs) ys).mem_iff.mp hz
        simp only [List.mem_append, List.mem_cons] at hz
        rcases hz with (rfl | hz) | hz
        · omega
        · exact Int.le_trans (by omega : y ≤ x) (hx z hz)
        · exact hy z hz
      · exact merge_sorted (x :: xs) ys (List.pairwise_cons.mpr ⟨hx, hxs⟩) hys

theorem mergeSort_correct_sorted (xs : List Int) :
  Sorted (mergeSort xs) := by
  match xs with
  | [] => simp [mergeSort, Sorted]
  | [x] => simp [mergeSort, Sorted]
  | x :: y :: xs =>
    rw [mergeSort]
    exact merge_sorted _ _
      (mergeSort_correct_sorted (split (x :: y :: xs)).1)
      (mergeSort_correct_sorted (split (x :: y :: xs)).2)
termination_by xs.length
decreasing_by
  all_goals
    have hlt := split_lt_length_of_length_ge_two (x :: y :: xs) (by simp)
    first | exact hlt.1 | exact hlt.2

theorem mergeSort_correct_perm (xs : List Int) :
  (mergeSort xs).Perm xs := by
  match xs with
  | [] => simp [mergeSort]
  | [x] => simp [mergeSort]
  | x :: y :: xs =>
    rw [mergeSort]
    exact (merge_perm _ _).trans
      (((mergeSort_correct_perm (split (x :: y :: xs)).1).append
        (mergeSort_correct_perm (split (x :: y :: xs)).2)).trans
        (split_perm (x :: y :: xs)))
termination_by xs.length
decreasing_by
  all_goals
    have hlt := split_lt_length_of_length_ge_two (x :: y :: xs) (by simp)
    first | exact hlt.1 | exact hlt.2

theorem mergeSort_correct : Correct mergeSort := by
  intro xs
  constructor
  · exact mergeSort_correct_sorted xs
  · exact mergeSort_correct_perm xs

end Algorithms.MergeSort.Impl
