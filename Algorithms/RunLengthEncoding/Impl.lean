import RealQuick.Instrumentation
import Algorithms.RunLengthEncoding.Correctness

open Algorithms.RunLengthEncoding.Correctness

namespace Algorithms.RunLengthEncoding.Impl

/-- Encode consecutive equal values as positive `(count, value)` runs. -/
def encode : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs =>
    match encode xs with
    | [] => [(1, x)]
    | (count, value) :: runs =>
      if x = value then (count + 1, value) :: runs
      else (1, x) :: (count, value) :: runs

#instrument encode as encode_timed

/-- The encoder is lossless and produces canonical runs. -/
theorem encode_correct : Correct encode := by
  intro xs
  induction xs with
  | nil => simp [encode, decode, Canonical, PositiveRuns, AdjacentDistinct]
  | cons x xs ih =>
    rcases ih with ⟨hdecode, hcanonical⟩
    cases henc : encode xs with
    | nil =>
      have hxs : xs = [] := by
        simpa [henc, decode] using hdecode.symm
      subst xs
      simp [encode, decode, Canonical, PositiveRuns, AdjacentDistinct]
    | cons run runs =>
      rcases run with ⟨count, value⟩
      rw [henc] at hdecode hcanonical
      rcases hcanonical with ⟨hpositive, hadjacent⟩
      by_cases h : x = value
      · subst x
        rw [encode, henc]
        simp only [↓reduceIte]
        change
          decode ((count + 1, value) :: runs) = value :: xs ∧
            Canonical ((count + 1, value) :: runs)
        constructor
        · change value :: (List.replicate count value ++ decode runs) = value :: xs
          congr 1
        · change
            PositiveRuns ((count + 1, value) :: runs) ∧
              AdjacentDistinct ((count + 1, value) :: runs)
          constructor
          · intro run hrun
            rcases List.mem_cons.mp hrun with rfl | hrest
            · omega
            · exact hpositive run (List.mem_cons_of_mem _ hrest)
          · cases runs with
            | nil => trivial
            | cons next runs =>
              rcases next with ⟨nextCount, nextValue⟩
              simpa [AdjacentDistinct] using hadjacent
      · rw [encode, henc]
        simp only [h, ↓reduceIte]
        change
          decode ((1, x) :: (count, value) :: runs) = x :: xs ∧
            Canonical ((1, x) :: (count, value) :: runs)
        constructor
        · change x :: (List.replicate count value ++ decode runs) = x :: xs
          congr 1
        · change
            PositiveRuns ((1, x) :: (count, value) :: runs) ∧
              AdjacentDistinct ((1, x) :: (count, value) :: runs)
          constructor
          · intro run hrun
            rcases List.mem_cons.mp hrun with rfl | hrest
            · simp
            · exact hpositive run hrest
          · exact ⟨h, hadjacent⟩

end Algorithms.RunLengthEncoding.Impl
