import RealQuick.TimeM

open RealQuick.TimeM

namespace RealQuick.Complexity

class Size (α : Type) where
  size : α → Nat

export Size (size)

-- Size Instances for common types

instance : Size (List α) where
  size := List.length

instance : Size (Array α) where
  size := Array.size

instance : Size String where
  size := String.length

instance [Size α] [Size β] : Size (α × β) where
  size p := size p.1 + size p.2


def Asymptotic {α β : Type} [Size α]
  (impl : α → TimeM β) (bound : Option (Nat → Nat)) : Prop :=
  match bound with
  | none => True
  | some bound =>
    ∃ (c n₀ : Nat), 0 < c ∧ ∀ (x : α),
     let n := size x
     n₀ ≤ n → (impl x).cost ≤ c * (bound n)

end RealQuick.Complexity
