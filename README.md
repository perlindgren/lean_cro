# Lean reactive objects

A first Timber-inspired DSL, implemented in `LeanCro/Reactive.lean`, with a
runnable example in `Examples/ReactiveExample.lean`.

```lean
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
```

`state` reads the current object's state as an ST computation; `write` replaces
it. The state type can also be a user-defined record. `self` is the current
object. `(friend : Counter)` explicitly declares an immutable, non-optional
constructor parameter. `Counter(cb)` supplies it when creating `ca`, and the
handler can use `friend` directly (or `self.friend`). No friend exists unless
the class declares it. Multiple references, with arbitrary names, are supported:
`reactive Node (left : Node) (right : Node) where ...`, instantiated as
`Node(otherA, otherB)`. A class with no parameters is instantiated as `Class()`.
Arguments are positional and their count is checked by Lean.

Requests return typed results. `sync` executes an ordinary method call
immediately; its result can be bound with `←`. All handlers are emitted in a
Lean `mutual` block, so forward calls work and synchronous recursive cycles
must pass Lean's termination checker. `sync` is notation, not a separate
execution mechanism. Direct method calls also execute immediately, including
direct calls to action implementations.

`async target .actionName` queues a typed action message and
returns without executing the handler. Queues hold data rather than recursive
closures. Only actions have message constructors; requests cannot be queued.
The scheduler removes each message before running its handler.

```lean
def demo : Int × Int × Nat := runST fun _ => do
  let counters ← Counters.new
  counters.ca.enqueue .increase
  let executed ← counters.ca.run 5
  return (← counters.ca.value, ← counters.cb.value, executed)

#eval demo -- (1, -1, 5)
```

The run executes five messages, then returns with the next message still
pending. Either handle runs the same shared FIFO queue. `run 0` executes
nothing; an empty queue stops early. Each run terminates for safe, total Lean
handlers, while asynchronous feedback can continue across arbitrarily many
runs. This does not prove eventual idleness, fairness under an external driver,
or real-time deadlines.

Network declarations validate names, allocate independent mutable state for
each object, and resolve all explicit constructor references before returning
handles. This supports forward and circular references without mutable
initialization placeholders. This
first version supports homogeneous networks, zero or more explicitly declared same-type references,
typed method arguments, and one initial-state expression per class. It has no
timers, deadlines, interrupts, heterogeneous object interfaces, or automatic
forever-running driver. The list queue is unbounded and enqueue is linear in
queue length; this is a semantic prototype rather than an embedded runtime.
Handler bodies are ordinary Lean, so this is an embedded DSL rather than a
restricted standalone language.

Validation:

```sh
lake build
lake env lean Tests/Reactive.lean
python3 Tests/check_reactive.py
```

The checks cover deferred execution, shared friend state, bounded feedback,
FIFO ordering, empty queues, zero-step runs, and rejection of synchronous
cycles, unknown friends, unknown messages, missing or extra constructor
arguments, and access to undeclared references. Multiple constructor references
are checked using a three-object network.

## Counter with an amount

`Examples/AmountCounter.lean` adds a second counter class:

```lean
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
```

Enqueue with `counters.ca.enqueue (.increase 7)`. One step leaves the counts
at `(7, -7)` and queues the same amount for the friend. Direct requests use
`sync counters.ca.decrease 3`. Negative amounts are allowed and reverse the
arithmetic. Action arguments are stored in the typed message until execution;
Lean checks both request arguments and message payloads. Parenthesize a message
application after `async`, as in `async friend (.increase amount)`.

## Project layout

- `LeanCro/`: reusable DSL and event-dispatcher implementation.
- `Examples/`: counter, point, and dispatcher example programs.
- `Tests/`: behavioral checks and compiler rejection checks.

`import LeanCro` loads only the library. `import Examples` loads the example
programs. `lake build LeanCro` builds the library alone; `lake build Examples`
builds the examples. The default `lake build` builds both and the executable.
