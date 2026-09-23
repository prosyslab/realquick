import Mathlib.Data.Nat.Log
import VeriQuick.Instrumentation
import Algorithms.BinarySearch.Correctness

open Algorithms.BinarySearch.Correctness

namespace Algorithms.BinarySearch.Impl

/-!
Lower-bound binary search over the half-open interval `[lo, hi)`.
-/

/-! ## Helpers

These exist so that `#instrument` can prove value preservation.
-/

def midpoint (lo hi : Nat) : Nat := lo + (hi - lo) / 2

#instrument midpoint as midpoint_timed

def readAt? (a : Array Nat) (i : Nat) : Option Nat := a[i]?

#instrument readAt? as readAt?_timed

/-- Whether the half-open interval `[lo, hi)` is nonempty. -/
def active (lo hi : Nat) : Bool := Nat.ble (lo + 1) hi

#instrument active as active_timed

/-! ## Search -/

/-- Actual search step: compute the next bounds based on the midpoint comparison. -/
def nextBounds (a : Array Nat) (key lo hi : Nat) : Nat × Nat :=
  match readAt? a (midpoint lo hi) with
  | some value =>
    if value < key then (midpoint lo hi + 1, hi)
    else (lo, midpoint lo hi)
  | none => (lo, hi)

#instrument nextBounds as nextBounds_timed

/-- Fuel-bounded lower-bound search over `[lo, hi)`. -/
def loop (a : Array Nat) (key : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    match active lo hi with
    | true =>
      -- Active: Interval is nonempty, continue the search.
      loop a key fuel
        (nextBounds a key lo hi).1
        (nextBounds a key lo hi).2
    | false =>
      -- Inactive: Interval is empty, return the lower bound.
      lo

#instrument loop as loop_timed

/-- Lower-bound binary search: return the first array position whose value is at least `key`. -/
def lowerBound (key : Nat) (a : Array Nat) : Nat :=
  loop a key (Nat.log2 a.size + 1) 0 a.size

#instrument lowerBound as lowerBound_timed

/-! ## Correctness proof -/

/--
Invariant for the lower-bound search which is our goal for the correctness:
1. `lo ≤ hi ≤ a.size`
2. every element before `lo` is below `key`
3. every element from `hi` on is at least `key`. -/
def Inv (a : Array Nat) (key lo hi : Nat) : Prop :=
  lo ≤ hi ∧ hi ≤ a.size ∧
    (∀ i (h : i < a.size), i < lo → a[i] < key) ∧
    (∀ i (h : i < a.size), hi ≤ i → key ≤ a[i])

-- In sorted array, if `i ≤ j` then `a[i] ≤ a[j]`.
theorem sorted_le {a : Array Nat} (hs : Sorted a) {i j : Nat} (hij : i ≤ j)
    (hj : j < a.size) : a[i] ≤ a[j] := by
  obtain h | rfl := Nat.lt_or_eq_of_le hij
  exacts [hs i j h hj, Nat.le_refl _]

-- interval is nonempty == active == `lo < hi`
theorem active_eq_true (lo hi : Nat) : active lo hi = true ↔ lo < hi := by
  simp only [active, Nat.ble_eq]
  omega

-- We can use `nextBounds` without `Option` with this theorem.
theorem nextBounds_eq (a : Array Nat) (key lo hi : Nat) (h : midpoint lo hi < a.size) :
    nextBounds a key lo hi =
      if a[midpoint lo hi] < key then (midpoint lo hi + 1, hi)
      else (lo, midpoint lo hi) := by
  simp only [nextBounds, readAt?, Array.getElem?_eq_getElem h]

/-- A step on a nonempty interval preserves `Inv`. -/
theorem nextBounds_inv {a : Array Nat} {key lo hi : Nat} (hs : Sorted a)
    (h : Inv a key lo hi) (hlt : lo < hi) :
    Inv a key (nextBounds a key lo hi).1 (nextBounds a key lo hi).2 := by
  obtain ⟨_, hhi, hbelow, habove⟩ := h
  have hm : midpoint lo hi < a.size := by unfold midpoint; omega
  rw [nextBounds_eq a key lo hi hm]
  split <;> dsimp only
  · refine ⟨by unfold midpoint; omega, hhi, fun i hi hlt' => ?_, habove⟩
    exact Nat.lt_of_le_of_lt (sorted_le hs (by omega) hm) ‹_›
  · refine ⟨by unfold midpoint; omega, by omega, hbelow, fun i hi hle => ?_⟩
    exact Nat.le_trans (by omega) (sorted_le hs hle hi)

/-- A step on a nonempty interval at least halves its length. -/
theorem nextBounds_halves (a : Array Nat) (key lo hi : Nat) (hlt : lo < hi)
    (hhi : hi ≤ a.size) :
    2 * ((nextBounds a key lo hi).2 - (nextBounds a key lo hi).1) ≤ hi - lo := by
  have hm : midpoint lo hi < a.size := by unfold midpoint; omega
  rw [nextBounds_eq a key lo hi hm]
  split <;> simp only [midpoint] <;> omega

/-- With enough fuel, `loop` returns a point `r` with `Inv a key r r`. -/
theorem loop_inv (a : Array Nat) (key fuel lo hi : Nat) (hs : Sorted a)
    (h : Inv a key lo hi) (hfuel : hi - lo < 2 ^ fuel) :
    Inv a key (loop a key fuel lo hi) (loop a key fuel lo hi) := by
  fun_induction loop a key fuel lo hi with
  | case1 lo hi =>
    obtain rfl : hi = lo := by have := h.1; omega
    exact h
  | case2 fuel lo hi hact ih =>
    rw [active_eq_true] at hact
    apply ih (nextBounds_inv hs h hact)
    have := nextBounds_halves a key lo hi hact h.2.1
    rw [Nat.pow_succ] at hfuel
    omega
  | case3 fuel lo hi hact =>
    rw [← Bool.not_eq_true, active_eq_true] at hact
    obtain rfl : hi = lo := by have := h.1; omega
    exact h

theorem lowerBound_correct : Correct lowerBound := by
  intro key a hs

  -- Invariant holds initially.
  have hinit : Inv a key 0 a.size :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ _ _ => by omega, fun _ _ _ => by omega⟩

  -- Fuel is enough to cover the whole array. (`n < 2 ^ (Nat.log2 n + 1)`)
  -- So the result `r` satisfies `Inv a key r r`.
  obtain ⟨_, hsize, hbelow, habove⟩ :=
    loop_inv a key (Nat.log2 a.size + 1) 0 a.size hs hinit
      (by simpa only [Nat.sub_zero] using Nat.lt_log2_self (n := a.size))

  -- `r ≤ a.size`, and `i < r → a[i] < key` is the forward direction.
  refine ⟨hsize, fun i hi => ⟨hbelow i hi, fun hv => ?_⟩⟩

  -- Backward direction: if `r ≤ i`, then `key ≤ a[i]`, contradicting `a[i] < key`.
  exact Nat.lt_of_not_le fun hle => Nat.not_lt_of_le (habove i hi hle) hv

end Algorithms.BinarySearch.Impl
