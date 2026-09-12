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

end Algorithms.MergeSort.Impl
