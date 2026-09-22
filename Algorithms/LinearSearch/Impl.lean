import VeriQuick.Instrumentation
import Algorithms.LinearSearch.Correctness

open Algorithms.LinearSearch.Correctness

namespace Algorithms.LinearSearch.Impl

/-- Search a list from left to right for the first value equal to `x`. -/
def linearSearch (x : Nat) (xs : List Nat) : Bool :=
  match xs with
  | [] => false
  | hd :: tl =>
    if x = hd then true
    else linearSearch x tl

/-- `linearSearch` returns `true` exactly when the target occurs in the list. -/
theorem linearSearch_correct : Correct linearSearch := by
  intro x xs
  induction xs with
  | nil => simp [linearSearch]
  | cons hd tl ih =>
    simp [linearSearch, ih]

#instrument linearSearch as linearSearch_timed

end Algorithms.LinearSearch.Impl
