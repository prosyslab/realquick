namespace Algorithms.ModExp.Correctness

/-!
Modular exponentiation computes `base ^ exponent % modulus` without first
building `base ^ exponent`.

The specification follows Lean's `Nat.mod`, which is total:
- `modulus = 0`: `x % 0 = x`, so the result is `base ^ exponent` itself (no
  reduction).
- `modulus = 1`: every number is `0` modulo `1`, so the result is `0`, even for
  `exponent = 0` (where `base ^ 0 = 1`).
-/

/-- An implementation is correct when it returns `base ^ exponent % modulus`
for every `base`, `exponent` and `modulus`, including `modulus = 0` and
`modulus = 1`. -/
def Correct (impl : Nat → Nat → Nat → Nat) : Prop :=
  ∀ base exponent modulus, impl base exponent modulus = base ^ exponent % modulus

end Algorithms.ModExp.Correctness
