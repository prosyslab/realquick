namespace Algorithms.LinearSearch.Correctness

/-- A linear-search implementation is correct exactly when it reports `true`
if and only if the target occurs in the input list. -/
def Correct (impl : Nat → List Nat → Bool) : Prop :=
  ∀ x xs, impl x xs = true ↔ x ∈ xs

end Algorithms.LinearSearch.Correctness
