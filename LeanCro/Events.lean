import Std

namespace Events

-- A thunk delays the closure's execution until it is dispatched.
abbrev Action (s : Type) (α : Type) := Unit → ST s α

-- Async actions have no immediate result to return to their sender.
structure Dispatcher (s : Type) where
  private mk ::
  private pending : ST.Ref s (List (Action s Unit))

namespace Dispatcher

def new : ST s (Dispatcher s) := do
  let pending ← ST.mkRef []
  return ⟨pending⟩

def sync (_dispatcher : Dispatcher s) (action : Action s α) : ST s α :=
  action ()

-- Enqueue only; the action does not execute here.
def async (dispatcher : Dispatcher s) (action : Action s Unit) : ST s Unit := do
  let queue ← dispatcher.pending.get
  dispatcher.pending.set (queue ++ [action])

-- Remove the action before executing it, so it can safely enqueue more work.
def runNext (dispatcher : Dispatcher s) : ST s Bool := do
  match ← dispatcher.pending.get with
  | [] => return false
  | action :: rest =>
    dispatcher.pending.set rest
    action ()
    return true

-- Process at most `steps` actions in FIFO order; return the number executed.
def run (dispatcher : Dispatcher s) : Nat → ST s Nat
  | 0 => pure 0
  | steps + 1 => do
    if ← dispatcher.runNext then
      return 1 + (← dispatcher.run steps)
    else
      return 0

end Dispatcher

end Events
