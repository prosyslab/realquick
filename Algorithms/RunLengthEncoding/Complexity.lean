import RealQuick.Complexity
import Algorithms.RunLengthEncoding.Impl

open RealQuick.TimeM
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

/-- Encoding one additional input element adds at most nine ticks. -/
theorem encode_timed_step (x : Nat) (xs : List Nat) :
    (encode_timed (x :: xs)).cost ≤ (encode_timed xs).cost + 9 := by
  cases htimed : encode_timed xs with
  | mk encoded tailCost =>
    have hvalue : encoded = encode xs := by
      have h := encode_timed_value xs
      simpa [htimed] using h
    subst encoded
    cases henc : encode xs with
    | nil =>
      simp [encode_timed, htimed, henc, TimeM.cost, TimeM.step, TimeM.tick,
        TimeM.done, TimeM.seq, Bind.bind]
    | cons run runs =>
      rcases run with ⟨count, value⟩
      by_cases h : x = value
      · simp [encode_timed, htimed, henc, h, RealQuick.Instrumentation.natEq,
          cond, TimeM.cost, TimeM.step, TimeM.tick, TimeM.done, TimeM.seq,
          Bind.bind]
      · simp [encode_timed, htimed, henc, h, RealQuick.Instrumentation.natEq,
          cond, TimeM.cost, TimeM.step, TimeM.tick, TimeM.done, TimeM.seq,
          Bind.bind]

/-- The instrumented encoder has a linear pointwise cost bound. -/
theorem encode_timed_linear (xs : List Nat) :
    (encode_timed xs).cost ≤ 9 * xs.length + 3 := by
  induction xs with
  | nil =>
    change 3 ≤ 3
    omega
  | cons x xs ih =>
    have hstep := encode_timed_step x xs
    simp only [List.length_cons]
    omega

/-- Instrumented run-length encoding is O(n) in the input-list length. -/
def complexity : Prop :=
  Asymptotic encode_timed (.some Bound)

theorem encode_timed_isLinear : complexity := by
  refine ⟨9, 0, by decide, ?_⟩
  intro xs
  dsimp [Size.size, Bound]
  intro _
  change (encode_timed xs).cost ≤ 9 * (xs.length + 1)
  have h := encode_timed_linear xs
  omega

end Algorithms.RunLengthEncoding.Complexity
