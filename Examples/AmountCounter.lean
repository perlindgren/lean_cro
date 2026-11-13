import LeanCro.Reactive

reactive AmountCounter (friend : AmountCounter) where
  state : Int := 0

  request value : Int := state

  request decrease (amount : Int) : Int := do
    write (← state) - amount
    state

  action increase (amount : Int) := do
    write (← state) + amount
    let _ ← sync friend.decrease amount
    async friend (.increase amount)

network AmountCounters where
  ca := AmountCounter(cb)
  cb := AmountCounter(ca)

def amountCounterExample : Int × Int × Nat := runST fun _ => do
  let counters ← AmountCounters.new
  counters.ca.enqueue (.increase 7)
  let executed ← counters.ca.run 1
  return (← counters.ca.value, ← counters.cb.value, executed)

#eval amountCounterExample -- (7, -7, 1)

example : amountCounterExample = (7, -7, 1) := by native_decide
