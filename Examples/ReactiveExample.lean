import LeanCro.Reactive

reactive Counter (friend : Counter) where
  state : Int := 0

  request value : Int := state

  request decrease : Int := do
    write (← state) - 1
    state

  action increase := do
    write (← state) + 1
    let _ ← sync friend.decrease
    async friend .increase

network Counters where
  ca := Counter(cb)
  cb := Counter(ca)

def reactiveExample : Int × Int × Nat := runST fun _ => do
  let counters ← Counters.new
  let ca := counters.ca
  let cb := counters.cb
  ca.enqueue .increase
  let executed ← ca.run 5
  return (← ca.value, ← cb.value, executed)

#eval reactiveExample -- (1, -1, 5); another message is still pending.

example : reactiveExample = (1, -1, 5) := by native_decide
