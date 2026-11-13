import Examples.ReactiveExample
import Examples.AmountCounter

-- Payloads stay queued, preserve order, and survive feedback to the friend.
example : (runST fun _ => do
    let counters ← AmountCounters.new
    counters.ca.enqueue (.increase 7)
    counters.ca.enqueue (.increase (-2))
    let before ← counters.ca.value
    let _ ← counters.ca.run 2
    let a ← counters.ca.value
    let b ← counters.cb.value
    let _ ← counters.ca.run 1
    return (before, a, b, ← counters.ca.value, ← counters.cb.value))
    = (0, 5, -5, -2, 2) := by native_decide

example : (runST fun _ => do
    let counters ← AmountCounters.new
    let a ← sync counters.ca.decrease (-4)
    let b ← sync counters.ca.decrease 0
    return (a, b)) = (4, 4) := by native_decide

-- Enqueuing changes no state; one step updates both objects and queues work.
example : (runST fun _ => do
    let counters ← Counters.new
    counters.ca.enqueue .increase
    let before ← counters.ca.value
    let first ← counters.ca.run 1
    let a ← counters.ca.value
    let b ← counters.cb.value
    let second ← counters.cb.run 1
    return (before, first, a, b, second, ← counters.ca.value, ← counters.cb.value))
    = (0, 1, 1, -1, 1, 0, 0) := by native_decide

example : (runST fun _ => do
    let counters ← Counters.new
    counters.ca.enqueue .increase
    let executed ← counters.ca.run 0
    return (executed, ← counters.ca.value)) = (0, 0) := by native_decide

reactive Fifo where
  state : List Nat := []
  request value : List Nat := self.get
  action first := do self.set ((← self.get) ++ [1])
  action second := do self.set ((← self.get) ++ [2])

network Single where
  only := Fifo()

example : (runST fun _ => do
    let system ← Single.new
    system.only.enqueue .first
    system.only.enqueue .second
    let executed ← system.only.run 10
    return (← system.only.value, executed)) = ([1, 2], 2) := by native_decide

-- Constructor parameters are named, ordered, and need not be called `friend`.
reactive Linked (left : Linked) (right : Linked) where
  state : Int := 0
  request value : Int := state
  request increment : Int := do
    write (← state) + 1
    state
  action visit := do
    let _ ← sync left.increment
    let _ ← sync right.increment
    pure ()

network Triangle where
  a := Linked(b, c)
  b := Linked(a, c)
  c := Linked(a, b)

example : (runST fun _ => do
    let objects ← Triangle.new
    objects.a.enqueue .visit
    let _ ← objects.a.run 1
    return (← objects.a.value, ← objects.b.value, ← objects.c.value))
    = (0, 1, 1) := by native_decide
