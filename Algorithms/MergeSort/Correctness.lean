import RealQuick.TimeM

open RealQuick.TimeM

namespace Algorithms.MergeSort.Correctness

def Sorted (xs : List Int) : Prop := xs.Pairwise (fun x y => x ≤ y)

def Correct (impl : List Int → List Int) : Prop :=
  ∀ xs, Sorted (impl xs) ∧ (impl xs).Perm xs

end Algorithms.MergeSort.Correctness
