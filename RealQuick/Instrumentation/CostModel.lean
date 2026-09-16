import RealQuick.TimeM

open Lean
open RealQuick.TimeM

namespace RealQuick.Instrumentation

variable {α β : Type}

def charge (cost : Nat) (value : α) : TimeM α := (value, cost)

@[simp] theorem fst_charge (cost : Nat) (value : α) : (charge cost value).1 = value := rfl
@[simp] theorem snd_charge (cost : Nat) (value : α) : (charge cost value).2 = cost := rfl

namespace CostModel

/-- These implementations, not arbitrary instances of the same operation, are approved.
Nat/Int arithmetic, including division, is unit-cost (not bit complexity). -/
def unitCostPrimitive (n : Name) : Bool :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.log2, ``Nat.beq, ``Nat.ble,
   ``Int.add, ``Int.sub, ``Int.mul, ``Int.ediv, ``Int.emod, ``Int.neg,
   ``Int.natAbs, ``Int.toNat, ``Bool.not, ``Bool.and, ``Bool.or].contains n

/-- Array operations under the unit-cost RAM model. -/
def unitCostArrayOperation (n : Name) : Bool :=
  [``Array.size, ``Array.getInternal, ``Array.getD,
   ``Array.set, ``Array.set!, ``Array.setIfInBounds, ``Array.pop].contains n

end CostModel
end RealQuick.Instrumentation
