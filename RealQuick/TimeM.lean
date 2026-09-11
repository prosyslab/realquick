namespace RealQuick.TimeM

/-- A computation augmented with a `time` variable, -/
def TimeM (α : Type u) := α × Nat

instance : Monad TimeM where
  pure a := (a, 0)
  bind comp cont :=
    let (a, t) := comp -- this computation takes t' ticks
    let (b, t') := cont a -- cont takes t'' ticks
    (b, t' + t)

namespace TimeM

/- Simple equalities for easier proofs of timed functions -/

/-- An explicit `TimeM` return used by generated instrumentation terms. -/
@[simp]
def done (a : α) : TimeM α := (a, 0)

/-- Projection forms simplify generated `TimeM.done` terms after `value` or
`cost` has been unfolded. -/
@[simp]
theorem fst_done (a : α) : (done a).1 = a := rfl

@[simp]
theorem snd_done (a : α) : (done a).2 = 0 := rfl

@[simp]
def tick : TimeM Unit := ((), 1)

@[simp]
def value (comp : TimeM α) := comp.1

@[simp]
def cost (comp : TimeM α) := comp.2

/-- Charge one tick before returning the supplied timed computation. -/
def step (comp : TimeM α) : TimeM α := do
  tick
  comp

@[simp]
theorem value_pure (a : α) : value (pure a : TimeM α) = a := rfl

@[simp]
theorem value_bind (comp : TimeM α) (cont : α → TimeM β) :
  value (do
    let a ← comp
    cont a) = value (cont (value comp)) := by
  cases comp
  rfl

@[simp]
theorem value_step (comp : TimeM α) : value (step comp) = value comp := by
  cases comp
  rfl

@[simp]
theorem cost_step (comp : TimeM α) : cost (step comp) = cost comp + 1 := by
  cases comp
  rfl

@[simp]
theorem cost_pure (a : α) : cost (pure a) = 0 := rfl

@[simp]
theorem cost_tick : cost tick = 1 := rfl

@[simp]
theorem cost_bind (comp : TimeM α) (cont : α → TimeM β) :
  cost (do
      let a ← comp
      cont a) = cost (cont (value comp)) + cost comp :=
  rfl

/-- Explicit sequencing used by generated instrumentation terms. -/
def seq (x : TimeM α) (k : α → TimeM β) : TimeM β :=
  let y := k x.1
  (y.1, x.2 + y.2)

@[simp]
theorem value_seq (x : TimeM α) (k : α → TimeM β) :
    value (seq x k) = value (k (value x)) := rfl

/-- Projection forms also simplify after `TimeM.value` has been unfolded. -/
@[simp]
theorem fst_step (x : TimeM α) : (step x).1 = x.1 :=
  TimeM.value_step x

@[simp]
theorem fst_seq (x : TimeM α) (k : α → TimeM β) :
    (seq x k).1 = (k x.1).1 := rfl

@[simp]
theorem snd_step (x : TimeM α) : (TimeM.step x).2 = x.2 + 1 :=
  cost_step x

@[simp]
theorem snd_seq (x : TimeM α) (k : α → TimeM β) :
    (seq x k).2 = x.2 + (k x.1).2 := rfl

@[simp]
theorem fst_ite (p : Prop) [Decidable p] (x y : TimeM α) :
    (if p then x else y).1 = if p then x.1 else y.1 := by
  split <;> rfl

end TimeM

abbrev CostBound := Nat → Nat

def Meets (bound : CostBound) (obligation: (Nat → Nat) → Prop) : Prop :=
  obligation bound

end RealQuick.TimeM 
