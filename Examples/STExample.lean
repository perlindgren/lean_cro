import Std

namespace STExample

-- There are exactly two valid identities, so partner links cannot dangle.
inductive CounterId where
  | ca
  | cb
  deriving DecidableEq, Repr

private structure CounterStore (s : Type) where
  caState : ST.Ref s Int
  cbState : ST.Ref s Int

-- Only the counts are mutable. Identity and partner identity are immutable.
structure Counter (s : Type) where
  private mk ::
  private store : CounterStore s
  id : CounterId
  partnerId : CounterId

namespace Counter

private def state (counter : Counter s) : ST.Ref s Int :=
  match counter.id with
  | .ca => counter.store.caState
  | .cb => counter.store.cbState

def decrease (counter : Counter s) : ST s Int := do
  let value ← counter.state.get
  counter.state.set (value - 1)
  counter.state.get

-- Resolve the permanent link to another handle into the same store.
-- This creates no new mutable state.
def partner (counter : Counter s) : Counter s :=
  ⟨counter.store, counter.partnerId, counter.id⟩

-- Increasing this counter also decreases its friend.
def increase (counter : Counter s) : ST s Int := do
  let value ← counter.state.get
  counter.state.set (value + 1)
  let _ ← counter.partner.decrease
  counter.state.get

-- Both handles share one store and are fully linked from creation.
def newPair (initialA : Int := 0) (initialB : Int := 0) :
    ST s (Counter s × Counter s) := do
  let caState ← ST.mkRef initialA
  let cbState ← ST.mkRef initialB
  let store : CounterStore s := ⟨caState, cbState⟩
  return (⟨store, .ca, .cb⟩, ⟨store, .cb, .ca⟩)

end Counter

def linkedCountersExample : List Int := runST fun _ => do
  let (ca, cb) ← Counter.newPair 0 10
  let a ← ca.increase          -- ca = 1, cb = 9
  let b ← ca.partner.increase  -- cb = 10, ca = 0
  let c ← cb.decrease          -- cb = 9
  let d ← cb.partner.decrease  -- ca = -1
  return [a, b, c, d]

#eval linkedCountersExample -- [1, 10, 9, -1]

example : linkedCountersExample = [1, 10, 9, -1] := by native_decide

-- Check both stored values immediately after increasing ca.
example : (runST fun _ => do
    let (ca, cb) ← Counter.newPair 0 10
    let _ ← ca.increase
    return (← ca.state.get, ← cb.state.get)) = (1, 9) := by native_decide

-- `s` identifies the region in which this mutable reference may be used.
def addToCounter (counter : ST.Ref s Nat) (amount : Nat) : ST s Unit := do
  let current ← counter.get
  counter.set (current + amount)

-- `runST` keeps mutation local and returns an ordinary, pure value.
def sumWithST (numbers : List Nat) : Nat := runST fun _ => do
  let counter ← ST.mkRef 0
  for number in numbers do
    addToCounter counter number
  counter.get

#eval sumWithST [10, 20, 30] -- 60

example : sumWithST [10, 20, 30] = 60 := by native_decide

end STExample
