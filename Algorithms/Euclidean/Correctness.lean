import VeriQuick.TimeM

open VeriQuick.TimeM

namespace Algorithms.Euclidean.Correctness

def Correct (impl : Nat → Nat → Nat) : Prop :=
  ∀ a b, impl a b = Nat.gcd a b

end Algorithms.Euclidean.Correctness
