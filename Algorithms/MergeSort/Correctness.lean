import RealQuick.TimeM

open RealQuick.TimeM

namespace Algorithms.MergeSort.Correctness

def Sorted (xs : List Int) : Prop := xs.Pairwise (fun x y => x ≤ y)

def Correct (impl : List Int → TimeM (List Int)) : Prop :=
  ∀ xs, Sorted (impl xs).value ∧ (impl xs).value.Perm xs

end Algorithms.MergeSort.Correctness
