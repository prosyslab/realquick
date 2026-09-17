import Algorithms.Complexity
import Algorithms.MergeSort.Impl

open RealQuick.TimeM
open Algorithms.Complexity
open Algorithms.MergeSort.Impl

namespace Algorithms.MergeSort.Complexity

def Bound (n : Nat) := (n + 1) * (Nat.log2 (n + 1))

abbrev Algorithm (α β : Type) := α → TimeM β

def complexity :=
  Asymptotic mergeSort_timed
    .some (fun n => (n + 1) * (Nat.log2 (n + 1))

end Algorithms.MergeSort.Complexity
