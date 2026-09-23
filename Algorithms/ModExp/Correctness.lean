namespace Algorithms.ModExp.Correctness

/-!
Modular exponentiation computes `b ^ e % m` without first building `b ^ e`.

The specification follows Lean's `Nat.mod`, which is total:
- `m = 0`: `x % 0 = x`, so the result is `b ^ e` itself (no reduction).
- `m = 1`: every number is `0` modulo `1`, so the result is `0`, even for
  `e = 0` (where `b ^ 0 = 1`).
-/

/-- An implementation is correct when it returns `b ^ e % m` for every base
`b`, exponent `e` and modulus `m`, including `m = 0` and `m = 1`. -/
def Correct (impl : Nat → Nat → Nat → Nat) : Prop :=
  ∀ b e m, impl b e m = b ^ e % m

end Algorithms.ModExp.Correctness
