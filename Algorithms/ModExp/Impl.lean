import VeriQuick.Instrumentation
import Algorithms.ModExp.Correctness

open VeriQuick.TimeM
open Algorithms.ModExp.Correctness

namespace Algorithms.ModExp.Impl

/-- The lowest bit of `exponent`: `1` if `exponent` is odd, `0` otherwise. -/
def lowBit (exponent : Nat) : Nat := exponent % 2

#instrument lowBit as lowBit_timed

/-- Right-to-left square-and-multiply: consume `exponent` one bit at a time,
starting from the lowest, squaring `base` after each bit. -/
def loop (modulus acc base exponent : Nat) : Nat :=
  if _h : exponent = 0 then
    -- Base case: Do modulo because we are relying on Lean's `Nat.mod` arithmetic:
    -- modulus = 1, exponent = 0 => acc % 1 = 0
    acc % modulus
  else if lowBit exponent = 1 then
    -- Lowest bit set: multiply `acc` by `base`, square `base`, drop the bit.
    loop modulus (acc * base % modulus) (base * base % modulus) (exponent / 2)
  else
    -- Lowest bit clear: keep `acc`, square `base`, drop the bit.
    loop modulus acc (base * base % modulus) (exponent / 2)
termination_by exponent

#instrument loop as loop_timed

/-- Modular exponentiation `base ^ exponent % modulus` by the right-to-left
binary method. -/
def modExp (base exponent modulus : Nat) : Nat :=
  loop modulus 1 (base % modulus) exponent

#instrument modExp as modExp_timed

/-- The loop invariant: `loop` returns `acc * base ^ exponent` modulo `modulus`. -/
theorem loop_eq (modulus acc base exponent : Nat) :
    loop modulus acc base exponent = acc * base ^ exponent % modulus := by
  fun_induction loop modulus acc base exponent with
  | case1 acc base =>
    simp only [Nat.pow_zero, Nat.mul_one]
  | case2 acc base exponent h hodd ih =>
    unfold lowBit at hodd
    have hpow : base ^ exponent = base * (base * base) ^ (exponent / 2) := by
      rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ']
      congr 1
      omega
    rw [ih, hpow, Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod,
      Nat.mul_assoc]
  | case3 acc base exponent h heven ih =>
    unfold lowBit at heven
    have hpow : base ^ exponent = (base * base) ^ (exponent / 2) := by
      rw [← Nat.pow_two, ← Nat.pow_mul]
      congr 1
      omega
    rw [ih, hpow, Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]

theorem modExp_correct : Correct modExp := by
  intro base exponent modulus
  rw [modExp, loop_eq, Nat.one_mul, ← Nat.pow_mod]

end Algorithms.ModExp.Impl
