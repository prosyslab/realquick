import VeriQuick.Instrumentation
import Algorithms.ModExp.Correctness

open VeriQuick.TimeM
open Algorithms.ModExp.Correctness

namespace Algorithms.ModExp.Impl

/-- The lowest bit of `e`. If e is odd, 1; otherwise 0. -/
def lowBit (e : Nat) : Nat := e % 2

#instrument lowBit as lowBit_timed

/-- Right-to-left square-and-multiply: consume `e` one bit at a time, starting
from the lowest, squaring `base` after each bit. -/
def loop (m acc base e : Nat) : Nat :=
  if _h : e = 0 then
    -- Base case: Do modulo because we are relying on Lean's `Nat.mod` arithmetic:
    -- m = 1, e = 0 => acc % 1 = 0
    acc % m
  else if lowBit e = 1 then
    -- Lowest bit set: multiply `acc` by `base`, square `base`, drop the bit.
    loop m (acc * base % m) (base * base % m) (e / 2)
  else
    -- Lowest bit clear: keep `acc`, square `base`, drop the bit.
    loop m acc (base * base % m) (e / 2)
termination_by e

#instrument loop as loop_timed

/-- Modular exponentiation `b ^ e % m` by the right-to-left binary method. -/
def modExp (b e m : Nat) : Nat := loop m 1 (b % m) e

#instrument modExp as modExp_timed

/-- The loop invariant: `loop` returns `acc * base ^ e` modulo `m`. -/
theorem loop_eq (m acc base e : Nat) :
    loop m acc base e = acc * base ^ e % m := by
  fun_induction loop m acc base e with
  | case1 acc base =>
    simp only [Nat.pow_zero, Nat.mul_one]
  | case2 acc base e h hodd ih =>
    unfold lowBit at hodd
    have hpow : base ^ e = base * (base * base) ^ (e / 2) := by
      rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ']
      congr 1
      omega
    rw [ih, hpow, Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod, Nat.mul_assoc]
  | case3 acc base e h heven ih =>
    unfold lowBit at heven
    have hpow : base ^ e = (base * base) ^ (e / 2) := by
      rw [← Nat.pow_two, ← Nat.pow_mul]
      congr 1
      omega
    rw [ih, hpow, Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]

theorem modExp_correct : Correct modExp := by
  intro b e m
  rw [modExp, loop_eq, Nat.one_mul, ← Nat.pow_mod]

end Algorithms.ModExp.Impl
