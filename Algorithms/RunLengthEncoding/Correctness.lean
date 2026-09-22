namespace Algorithms.RunLengthEncoding.Correctness

/-- A run is represented by its positive count and repeated value. -/
abbrev Run := Nat × Nat

/-- Expand a run-length encoding back into its underlying list. -/
def decode : List Run → List Nat
  | [] => []
  | (count, value) :: runs =>
    List.replicate count value ++ decode runs

/-- Every run in a well-formed encoding has a positive count. -/
def PositiveRuns (runs : List Run) : Prop :=
  ∀ run ∈ runs, 0 < run.1

/-- Neighboring runs in a canonical encoding carry different values. -/
def AdjacentDistinct : List Run → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
    first.2 ≠ second.2 ∧ AdjacentDistinct (second :: rest)

/-- A canonical encoding has positive counts and no mergeable adjacent runs. -/
def Canonical (runs : List Run) : Prop :=
  PositiveRuns runs ∧ AdjacentDistinct runs

/-- An encoder is correct when decoding recovers the input and its output is
canonical. -/
def Correct (impl : List Nat → List Run) : Prop :=
  ∀ xs, decode (impl xs) = xs ∧ Canonical (impl xs)

end Algorithms.RunLengthEncoding.Correctness
