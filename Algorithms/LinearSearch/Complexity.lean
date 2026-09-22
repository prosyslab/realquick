import VeriQuick.Complexity
import Algorithms.LinearSearch.Impl

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.LinearSearch.Impl

namespace Algorithms.LinearSearch.Complexity

/-- Worst-case linear-search cost, measured by the input-list length. -/
def Bound (n : Nat) : Nat := n + 1

/-- Instrumented linear search performs at most four ticks per list element,
plus three ticks for the empty-list case. -/
theorem linearSearch_timed_linear (x : Nat) (xs : List Nat) :
    (linearSearch_timed x xs).cost ≤ 4 * xs.length + 3 := by
  fun_induction linearSearch x xs with
  | case1 =>
    change 3 ≤ 3
    omega
  | case2 tl =>
    simp [linearSearch_timed, VeriQuick.Instrumentation.natEq, cond, TimeM.cost,
      TimeM.step, TimeM.tick, TimeM.done, TimeM.seq, Bind.bind]
    omega
  | case3 hd tl h ih =>
    cases htimed : linearSearch_timed x tl with
    | mk value cost =>
      simp [linearSearch_timed, VeriQuick.Instrumentation.natEq, cond, h, htimed,
        TimeM.cost, TimeM.step, TimeM.tick, TimeM.done, TimeM.seq, Bind.bind] at ih ⊢
      omega

/-- For every fixed target, instrumented linear search is O(n) in the list
length. -/
def complexity (x : Nat) : Prop :=
  Asymptotic (linearSearch_timed x) (.some Bound)

theorem linearSearch_timed_isLinear (x : Nat) : complexity x := by
  refine ⟨4, 0, by decide, ?_⟩
  intro xs
  dsimp [Size.size, Bound]
  intro _
  change (linearSearch_timed x xs).cost ≤ 4 * (xs.length + 1)
  have h := linearSearch_timed_linear x xs
  omega

end Algorithms.LinearSearch.Complexity
