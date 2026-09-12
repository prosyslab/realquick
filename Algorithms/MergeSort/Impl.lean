namespace Algorithms.MergeSort.Impl

def splitAlt : Bool → List Int → (List Int × List Int)
  | _, [] => ([], [])
  | alt, x :: xs =>
    let s := splitAlt (!alt) xs
    if alt then (x :: s.1, s.2)
    else (s.1, x :: s.2)

#eval splitAlt false [1,2,3,4]

/-- The length difference of `splitAlt`-returned lists is bounded by 1 -/
private theorem splitAlt_balanced_oriented (xs : List Int) :
  ∀ b,
    let (s1, s2) := splitAlt b xs
    if b then s2.length ≤ s1.length ∧ s1.length ≤ s2.length + 1
    else s1.length ≤ s2.length ∧ s2.length ≤ s1.length + 1 := by
  induction xs with
  | nil =>
    intro b
    simp [splitAlt]
  | cons hd tl ih =>
    intro b
    cases b with
    | false =>
      simp [splitAlt]
      have h := ih true
      simp at h
      omega
    | true =>
      simp [splitAlt]
      have h := ih false
      simp at h
      omega

/-- `splitAlt` always returns two lists of balanced-lengths -/
theorem splitAlt_balanced (xs : List Int) :
  ∀ (b : Bool),
    let (s1, s2) := splitAlt b xs
    s1.length - s2.length ≤ 1 ∧ s2.length - s1.length ≤ 1 := by
  intro b
  simp
  have h := splitAlt_balanced_oriented xs b
  cases b <;> simp at h <;> omega

theorem splitAlt_preserves_length (b : Bool) (xs : List Int) :
  let (s1, s2) := splitAlt b xs
  s1.length + s2.length = xs.length := by
  induction xs generalizing b with
  | nil =>
    simp [splitAlt]
  | cons x xs ih =>
    cases b with
    | false =>
      simp [splitAlt]
      have h := ih true
      omega
    | true =>
      simp [splitAlt]
      have h := ih false
      omega

private theorem splitAlt_lt_length_of_length_ge_two
    (b : Bool) (xs : List Int) (hxs : 2 ≤ xs.length) :
    (splitAlt b xs).1.length < xs.length ∧
      (splitAlt b xs).2.length < xs.length := by
  have hsum := splitAlt_preserves_length b xs
  have hbalanced := splitAlt_balanced xs b
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
    match h : splitAlt true (x :: y :: xs) with
    | (a, b) =>
      let a' := mergeSort a
      let b' := mergeSort b
      merge a' b'
termination_by xs => xs.length
decreasing_by
  all_goals
    have hlt := splitAlt_lt_length_of_length_ge_two true (x :: y ::xs) (by simp)
    rw [h] at hlt
    first | exact hlt.1 | exact hlt.2

end Algorithms.MergeSort.Impl
