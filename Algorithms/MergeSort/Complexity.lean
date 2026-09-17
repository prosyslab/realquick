import RealQuick.Complexity
import Algorithms.MergeSort.Impl

open RealQuick.TimeM
open RealQuick.Complexity
open Algorithms.MergeSort.Impl

namespace Algorithms.MergeSort.Complexity

def Bound (n : Nat) := (n + 1) * (Nat.log2 (n + 1))

abbrev Algorithm (α β : Type) := α → TimeM β

def complexity : Prop :=
  Asymptotic mergeSort_timed (.some Bound)

end Algorithms.MergeSort.Complexity
