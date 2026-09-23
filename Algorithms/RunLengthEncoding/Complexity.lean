import RealQuick.Complexity
import Algorithms.RunLengthEncoding.Impl

open RealQuick.TimeM
open RealQuick.Instrumentation (natEq)
open RealQuick.Complexity
open Algorithms.RunLengthEncoding.Impl

namespace Algorithms.RunLengthEncoding.Complexity

/-!
`decode` is specification machinery. Its running time is proportional to the
sum of run counts (the expanded output length), not merely the number of runs,
so the list-length `Size` instance is intentionally used only for `encode`.
-/

/-- Linear cost bound with a nonzero value at input size zero. -/
def Bound (n : Nat) : Nat := n + 1

/-- Consuming a run of length `count` costs at most `8 * count + 6` ticks. -/
theorem takeRun_timed_linear (x : Nat) (xs : List Nat) :
    (takeRun_timed x xs).cost ≤ 8 * (takeRun x xs).1 + 6 := by
  induction xs with
  | nil =>
    change 4 ≤ 6
    omega
  | cons y ys ih =>
    by_cases h : x = y
    · subst h
      simp [takeRun_timed, takeRun, natEq, cond, TimeM.step, TimeM.seq, Bind.bind] at ih ⊢
      omega
    · simp [takeRun_timed, takeRun, h, natEq, cond, TimeM.step, TimeM.seq, Bind.bind]

/-- One encoding step costs the run scan, the recursive call, and six ticks. -/
theorem encode_timed_step (x : Nat) (xs : List Nat) :
    (encode_timed (x :: xs)).cost ≤
      (takeRun_timed x xs).cost + (encode_timed (takeRun x xs).2).cost + 6 := by
  rw [encode_timed_eq_def]
  have hcert (l : List Nat) : (encode_timed_certified l).1 = encode_timed l := rfl
  simp [RealQuick.Instrumentation.WF.seqEq, TimeM.step, TimeM.done, TimeM.cost, bind,
    hcert, takeRun_timed_value]
  omega

/-- The instrumented encoder has a linear pointwise cost bound. -/
theorem encode_timed_linear (xs : List Nat) :
    (encode_timed xs).cost ≤ 12 * xs.length + 3 := by
  fun_induction encode xs with
  | case1 =>
    change 3 ≤ 3
    omega
  | case2 x xs count rest h ih =>
    have hstep := encode_timed_step x xs
    have hscan := takeRun_timed_linear x xs
    have hlen := takeRun_length x xs
    rw [h] at hstep hscan hlen
    dsimp only at hstep hscan hlen
    simp only [List.length_cons]
    omega

/-- Instrumented run-length encoding is O(n) in the input-list length. -/
def complexity : Prop :=
  Asymptotic encode_timed (.some Bound)

theorem encode_timed_isLinear : complexity := by
  refine ⟨12, 0, by decide, ?_⟩
  intro xs
  dsimp [Size.size, Bound]
  intro _
  change (encode_timed xs).cost ≤ 12 * (xs.length + 1)
  have h := encode_timed_linear xs
  omega

end Algorithms.RunLengthEncoding.Complexity
