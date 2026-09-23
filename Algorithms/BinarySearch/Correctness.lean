namespace Algorithms.BinarySearch.Correctness

def Sorted (a : Array Nat) : Prop :=
  ∀ i j (hij : i < j) (hj : j < a.size), a[i] ≤ a[j]

def Correct (impl : Nat → Array Nat → Nat) : Prop :=
  ∀ key a, Sorted a →
    impl key a ≤ a.size ∧ ∀ i (hi : i < a.size), (i < impl key a ↔ a[i] < key)

end Algorithms.BinarySearch.Correctness
