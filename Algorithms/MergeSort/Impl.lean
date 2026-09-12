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

theorem mergeSort_correct_sorted (xs : List Int) :
  Sorted (mergeSort xs) := by sorry

theorem mergeSort_correct_perm (xs : List Int) :
  (mergeSort xs).Perm xs := by sorry

theorem mergeSort_correct : Correct mergeSort := by
  intro xs
  constructor
  · exact mergeSort_correct_sorted xs
  · exact mergeSort_correct_perm xs

end Algorithms.MergeSort.Impl
