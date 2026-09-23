namespace Algorithms.RunLengthEncoding.Correctness

/-- A run of `count` copies of `value`. Empty runs are ruled out by construction. -/
structure Run where
  count : Nat
  value : Nat
  count_pos : 0 < count

/-- Expand a run-length encoding back into its underlying list. -/
def decode : List Run → List Nat
  | [] => []
  | run :: runs => List.replicate run.count run.value ++ decode runs

/-- No two neighboring runs share a value.
For example, `[(1, 5), (1, 5)]` must be written as `[(2, 5)]`. -/
def AdjacentDistinct : List Run → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
    first.value ≠ second.value ∧ AdjacentDistinct (second :: rest)

/-- An encoder is correct when decoding recovers the input and no two
neighboring runs share a value. -/
def Correct (impl : List Nat → List Run) : Prop :=
  ∀ xs, decode (impl xs) = xs ∧ AdjacentDistinct (impl xs)

end Algorithms.RunLengthEncoding.Correctness
