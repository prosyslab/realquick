import RealQuick.Instrumentation
import Algorithms.RunLengthEncoding.Correctness

open Algorithms.RunLengthEncoding.Correctness

namespace Algorithms.RunLengthEncoding.Impl

/-- Count and drop the leading elements equal to `x`. -/
def takeRun (x : Nat) : List Nat → Nat × List Nat
  | [] => (0, [])
  | y :: ys =>
    if x = y then
      let r := takeRun x ys
      (r.1 + 1, r.2)
    else (0, y :: ys)

/-- `takeRun` splits its input into `count` copies of `x` and the rest. -/
theorem takeRun_length (x : Nat) (xs : List Nat) :
    (takeRun x xs).1 + (takeRun x xs).2.length = xs.length := by
  induction xs with
  | nil => simp [takeRun]
  | cons y ys ih =>
    by_cases h : x = y
    · subst h
      simp only [takeRun, ↓reduceIte, List.length_cons]
      omega
    · simp [takeRun, h]

#instrument takeRun as takeRun_timed

/-- The consumed prefix is exactly `count` copies of `x`. -/
theorem takeRun_append (x : Nat) (xs : List Nat) :
    List.replicate (takeRun x xs).1 x ++ (takeRun x xs).2 = xs := by
  induction xs with
  | nil => simp [takeRun]
  | cons y ys ih =>
    by_cases h : x = y
    · subst h
      simp [takeRun, List.replicate_succ, ih]
    · simp [takeRun, h]

/-- The rest does not start with `x`. -/
theorem takeRun_head (x : Nat) (xs : List Nat) :
    (takeRun x xs).2.head? ≠ some x := by
  induction xs with
  | nil => simp [takeRun]
  | cons y ys ih =>
    by_cases h : x = y
    · subst h
      simpa [takeRun] using ih
    · simp [takeRun, h, Ne.symm h]

/-- Encode consecutive equal values as positive `(count, value)` runs. -/
def encode : List Nat → List (Nat × Nat)
  | [] => []
  | x :: xs =>
    match h : takeRun x xs with
    | (count, rest) => (count + 1, x) :: encode rest
termination_by xs => xs.length
decreasing_by
  have hlen := takeRun_length x xs
  rw [h] at hlen
  simp only [List.length_cons] at hlen ⊢
  omega

#instrument encode as encode_timed

/-- The first run carries the first input value. -/
theorem encode_head (xs : List Nat) :
    (encode xs).head?.map Prod.snd = xs.head? := by
  cases xs with
  | nil => simp [encode]
  | cons x xs => simp [encode]

/-- The encoder is lossless and produces canonical runs. -/
theorem encode_correct : Correct encode := by
  intro xs
  fun_induction encode xs with
  | case1 => simp [decode, Canonical, PositiveRuns, AdjacentDistinct]
  | case2 x xs count rest h ih =>
    rcases ih with ⟨hdecode, hpositive, hadjacent⟩
    have happend := takeRun_append x xs
    have hhead := takeRun_head x xs
    have hfirst := encode_head rest
    rw [h] at happend hhead
    refine ⟨?_, ?_, ?_⟩
    · simp [decode, hdecode, List.replicate_succ, happend]
    · intro run hrun
      rcases List.mem_cons.mp hrun with rfl | hrest
      · simp
      · exact hpositive run hrest
    · cases hrest : encode rest with
      | nil => trivial
      | cons next runs =>
        rw [hrest] at hadjacent hfirst
        refine ⟨?_, hadjacent⟩
        intro hx
        apply hhead
        simp [← hfirst, ← hx]

end Algorithms.RunLengthEncoding.Impl
