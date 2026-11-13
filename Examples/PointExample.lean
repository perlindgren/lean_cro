import Examples.AmountCounter

namespace PointExample

structure Point where
  x : Int := 0
  y : Int := 0
  deriving Repr, DecidableEq

-- Reuse the DSL counter from AmountCounter.lean, rather than define a new one.
-- The friend is immutable; only the stored Point is mutable.
structure PointObject (s : Type) (n : Nat) where
  private mk ::
  private contents : ST.Ref s Point
  friend : AmountCounter.Object s n

namespace PointObject

def new (friend : AmountCounter.Object s n) (initial : Point := {}) :
    ST s (PointObject s n) := do
  let contents ← ST.mkRef initial
  return ⟨contents, friend⟩

def value (self : PointObject s n) : ST s Point := self.contents.get

-- Execute the existing counter's increase immediately, then read its result.
-- Its original behavior (decreasing its friend and queuing feedback) is retained.
def increase_x (self : PointObject s n) (amount : Int := 1) : ST s Int := do
  sync self.friend.increase amount
  let x ← sync self.friend.value
  let point ← self.contents.get
  self.contents.set { point with x := x }
  return x

def decrease_y (self : PointObject s n) (amount : Int := 1) : ST s Int := do
  let y ← sync self.friend.decrease amount
  let point ← self.contents.get
  self.contents.set { point with y := y }
  return y

end PointObject

def exampleResult : Point × Point × Int × Int := runST fun _ => do
  let counters ← AmountCounters.new
  let point ← PointObject.new counters.ca
  let _ ← point.increase_x 7
  let first ← point.value              -- { x := 7, y := 0 }
  let _ ← point.decrease_y 2
  let second ← point.value             -- { x := 7, y := 5 }
  return (first, second, ← counters.ca.value, ← counters.cb.value)

#eval exampleResult -- ({ x := 7, y := 0 }, { x := 7, y := 5 }, 5, -7)

example : exampleResult = ({ x := 7, y := 0 }, { x := 7, y := 5 }, 5, -7) :=
  by native_decide

-- The point holds the actual supplied instance: external changes are visible.
example : (runST fun _ => do
    let counters ← AmountCounters.new
    let point ← PointObject.new counters.ca
    let _ ← counters.ca.decrease (-4)
    let _ ← point.increase_x
    return (← point.value, ← counters.ca.value, ← counters.cb.value))
    = ({ x := 5, y := 0 }, 5, -1) := by native_decide

-- The reused counter's feedback message is still executable on its own queue.
example : (runST fun _ => do
    let counters ← AmountCounters.new
    let point ← PointObject.new counters.ca
    let _ ← point.increase_x 7
    let executed ← counters.ca.run 1
    return (executed, ← counters.ca.value, ← counters.cb.value, ← point.value))
    = (1, 0, 0, { x := 7, y := 0 }) := by native_decide

end PointExample
