import VeriQuick.Instrumentation
import Algorithms.ModExp.Correctness

open VeriQuick.TimeM
open Algorithms.ModExp.Correctness

namespace Algorithms.ModExp.Impl

/-- The lowest bit of `e`. If e is odd, 1; otherwise 0. -/
def lowBit (e : Nat) : Nat := e % 2

#instrument lowBit as lowBit_timed

/-- Multiply the accumulator by `base` modulo `m` when the lowest bit of `e`
is set; otherwise keep it unchanged. Need to Right-to-left square-and-multiply method. -/
def absorbBit (m base e acc : Nat) : Nat :=
  if lowBit e = 1 then acc * base % m else acc

#instrument absorbBit as absorbBit_timed

/-- Right-to-left square-and-multiply: consume `e` one bit at a time, starting
from the lowest, squaring `base` after each bit. -/
def loop (m acc base e : Nat) : Nat :=
  if _h : e = 0 then
    -- Base case: Do modulo because we are relying on Lean's `Nat.mod` arithmetic:
    -- m = 1, e = 0 => acc % 1 = 0
    acc % m
  else
    -- Recursive case: consume the lowest bit of `e`, square `base`, and continue.
    loop m (absorbBit m base e acc) (base * base % m) (e / 2)
termination_by e
decreasing_by omega

#instrument loop as loop_timed

/-- Modular exponentiation `b ^ e % m` by the right-to-left binary method. -/
def modExp (b e m : Nat) : Nat := loop m 1 (b % m) e

#instrument modExp as modExp_timed

/-- Up to `m`, `absorbBit` multiplies the accumulator by `base ^ (e % 2)`. -/
theorem absorbBit_mod (m base e acc : Nat) :
    absorbBit m base e acc % m = acc * base ^ (e % 2) % m := by
  unfold absorbBit lowBit
  split
  · next h => simp only [h, Nat.pow_one, Nat.mod_mod]
  · next h =>
    have h0 : e % 2 = 0 := by omega
    simp only [h0, Nat.pow_zero, Nat.mul_one]

/-- The loop invariant: `loop` returns `acc * base ^ e` modulo `m`. -/
theorem loop_eq (m acc base e : Nat) :
    loop m acc base e = acc * base ^ e % m := by
  fun_induction loop m acc base e with
  | case1 acc base =>
    simp only [Nat.pow_zero, Nat.mul_one]
  | case2 acc base e h ih =>
    rw [ih, Nat.mul_mod, absorbBit_mod, ← Nat.pow_mod, ← Nat.mul_mod,
      ← Nat.pow_two, ← Nat.pow_mul, Nat.mul_assoc, ← Nat.pow_add,
      Nat.mod_add_div]

theorem modExp_correct : Correct modExp := by
  intro b e m
  rw [modExp, loop_eq, Nat.one_mul, ← Nat.pow_mod]

end Algorithms.ModExp.Impl
