import LeanCro.Events

namespace Events

def exampleResults : Int × Int × Int × Nat := runST fun s => do
  let dispatcher : Dispatcher s ← Dispatcher.new
  let count : ST.Ref s Int ← ST.mkRef 0
  let immediate ← dispatcher.sync fun () => do
    count.set 1
    count.get
  dispatcher.async fun () => do
    count.set ((← count.get) + 10)
  dispatcher.async fun () => do
    count.set ((← count.get) * 2)
  let beforeQueue ← count.get
  let executed ← dispatcher.run 10
  let afterQueue ← count.get
  return (immediate, beforeQueue, afterQueue, executed)

#eval exampleResults -- (1, 1, 22, 2)

example : exampleResults = (1, 1, 22, 2) := by native_decide

end Events
