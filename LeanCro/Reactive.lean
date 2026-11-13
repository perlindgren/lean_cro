import Lean

namespace Reactive

-- All handles share this store. Links are immutable, counts are mutable.
structure Handle (s : Type) (State Message : Type) (n k : Nat) where
  states : ST.Ref s (Vector State n)
  pending : ST.Ref s (List (Fin n × Message))
  links : Fin n → Vector (Fin n) k
  id : Fin n

namespace Handle

def get (self : Handle s State Message n k) : ST s State := do
  return (← self.states.get)[self.id]

def set (self : Handle s State Message n k) (value : State) : ST s Unit := do
  self.states.set ((← self.states.get).set self.id value)

def linked (self : Handle s State Message n k) (index : Fin k) : Handle s State Message n k :=
  { self with id := (self.links self.id)[index] }

def enqueue (self : Handle s State Message n k) (message : Message) : ST s Unit := do
  self.pending.set ((← self.pending.get) ++ [(self.id, message)])

def pop (self : Handle s State Message n k) :
    ST s (Option (Handle s State Message n k × Message)) := do
  match ← self.pending.get with
  | [] => return none
  | (id, message) :: rest =>
    self.pending.set rest
    return some ({ self with id }, message)

end Handle

open Lean Macro

declare_syntax_cat methodParam
syntax "(" ident " : " term ")" : methodParam
declare_syntax_cat reactiveMember
syntax "request " ident methodParam* " : " term " := " term : reactiveMember
syntax "action " ident methodParam* " := " term : reactiveMember
declare_syntax_cat reactiveParam
syntax "(" ident " : " ident ")" : reactiveParam
syntax (name := reactiveDecl) "reactive " ident reactiveParam* " where "
  "state " " : " term " := " term reactiveMember* : command

-- A message constructor (rather than a function) is queued.
syntax "async " term:max term:max : doElem
macro_rules
  | `(doElem| async $target:term $message:term) =>
    `(doElem| ($target).enqueue $message)

-- State notation is scoped by the generated handler's explicit `self` binder.
syntax "state" : term
syntax (name := writeState) "write " term : doElem
macro_rules
  | `(term| state) => do
    let self := mkIdent `self
    `(($self).get)
macro_rules (kind := writeState)
  | `(writeState| write $value:term) => do
    let self := mkIdent `self
    `(doElem| ($self).set $value)

macro_rules
  | `(reactive $name:ident $params:reactiveParam* where state : $stateType:term := $initial:term
        $members:reactiveMember*) => do
    let self := mkIdent `self
    let arity := Syntax.mkNumLit (toString params.size)
    let mut parameterNames : Array (TSyntax `ident) := #[]
    for param in params do
      let `(reactiveParam| ($field:ident : $type:ident)) := param
        | Macro.throwErrorAt param "expected an object parameter"
      if type.getId != name.getId then
        Macro.throwErrorAt type "constructor references currently must have the enclosing object type"
      if parameterNames.any (fun n => n.getId == field.getId) then
        Macro.throwErrorAt field "duplicate constructor parameter"
      parameterNames := parameterNames.push field
    let bindParameters := fun (body : TSyntax `term) => do
      let mut result := body
      for field in parameterNames.reverse do
        result ← `(let $field:ident := ($self).$field:ident; $result)
      pure result
    let mut constructors : Array (TSyntax `Lean.Parser.Command.ctor) := #[]
    let mut handlers : Array (TSyntax `command) := #[]
    let mut branches : Array (TSyntax `Lean.Parser.Term.matchAltExpr) := #[]
    let methodBinders := fun (params : Array (TSyntax `methodParam)) => do
      let mut binders : Array (TSyntax `Lean.Parser.Term.bracketedBinderF) := #[]
      let mut args : Array (TSyntax `ident) := #[]
      for param in params do
        let `(methodParam| ($arg:ident : $type:term)) := param
          | Macro.throwErrorAt param "expected a typed method argument"
        binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| ($arg : $type)))
        args := args.push arg
      pure (binders, args)
    for member in members do
      match member with
      | `(reactiveMember| request $method:ident $params:methodParam* : $result:term := $body:term) =>
        let (binders, _) ← methodBinders params
        let body ← bindParameters body
        handlers := handlers.push (← `(command|
          def $method:ident ($self : Object s n) $binders:bracketedBinder* : ST s $result := $body))
      | `(reactiveMember| action $method:ident $params:methodParam* := $body:term) =>
        let (binders, args) ← methodBinders params
        constructors := constructors.push (← `(Lean.Parser.Command.ctor|
          | $method:ident $binders:bracketedBinder*))
        let body ← bindParameters body
        handlers := handlers.push (← `(command|
          def $method:ident ($self : Object s n) $binders:bracketedBinder* : ST s Unit := $body))
        let mut pattern ← `(.$method:ident)
        let mut call ← `(target.$method:ident)
        for arg in args do
          pattern ← `($pattern $arg:ident)
          call ← `($call $arg:ident)
        branches := branches.push (← `(Lean.Parser.Term.matchAltExpr|
          | $pattern:term => $call))
      | _ => Macro.throwErrorAt member "expected a request or action"
    if constructors.isEmpty then
      Macro.throwError "a reactive object needs at least one action"
    let mut commands : Array (TSyntax `command) := #[]
    commands := commands.push (← `(command| namespace $name))
    commands := commands.push (← `(command| abbrev State := $stateType))
    commands := commands.push (← `(command| def initialState : State := $initial))
    commands := commands.push (← `(command|
      inductive Message where
        $constructors:ctor*))
    commands := commands.push (← `(command|
      structure Object (s : Type) (n : Nat) where
        private mk ::
        private handle : Reactive.Handle s State Message n $arity))
    commands := commands.push (← `(command| namespace Object))
    commands := commands.push (← `(command|
      def get ($self : Object s n) : ST s State := ($self).handle.get))
    commands := commands.push (← `(command|
      def set ($self : Object s n) (value : State) : ST s Unit :=
        ($self).handle.set value))
    for i in [:parameterNames.size] do
      let field := parameterNames[i]!
      let index := Syntax.mkNumLit (toString i)
      commands := commands.push (← `(command|
        def $field:ident ($self : Object s n) : Object s n :=
          ⟨($self).handle.linked $index⟩))
    commands := commands.push (← `(command|
      def enqueue ($self : Object s n) (message : Message) : ST s Unit :=
        ($self).handle.enqueue message))
    commands := commands.push (← `(command|
      mutual
        $handlers:command*
      end))
    commands := commands.push (← `(command|
      def step ($self : Object s n) : ST s Bool := do
        match ← ($self).handle.pop with
        | none => return false
        | some (handle, message) =>
          let target : Object s n := ⟨handle⟩
          let task : ST s Unit := (match message with $branches:matchAlt*)
          task
          return true))
    commands := commands.push (← `(command|
      def run ($self : Object s n) : Nat → ST s Nat
        | 0 => pure 0
        | steps + 1 => do
          if ← ($self).step then
            return 1 + (← ($self).run steps)
          else return 0))
    commands := commands.push (← `(command| end Object))
    commands := commands.push (← `(command|
      def newNetwork (links : Fin n → Vector (Fin n) $arity) : ST s (Fin n → Object s n) := do
        let states ← ST.mkRef (Vector.replicate n initialState)
        let pending ← ST.mkRef []
        return fun id => ⟨⟨states, pending, links, id⟩⟩))
    commands := commands.push (← `(command| end $name))
    -- These declarations intentionally expose their names and the `self` binder.
    let expose := fun (stx : Syntax) => stx.rewriteBottomUp fun node =>
      match node with
      | .ident info raw value _ => .ident info raw value.eraseMacroScopes []
      | other => other
    return mkNullNode (commands.map (fun command => expose command.raw))

-- `sync` documents the immediate-call boundary; ordinary method calls work too.
syntax "sync " term : term
macro_rules
  | `(sync $call:term) => `($call)

declare_syntax_cat reactiveInstance
syntax ident " := " ident "(" ident,* ")" : reactiveInstance
syntax "network " ident " where " reactiveInstance+ : command

macro_rules
  | `(network $name:ident where $instances:reactiveInstance*) => do
    let count := Syntax.mkNumLit (toString instances.size)
    let mut names : Array (TSyntax `ident) := #[]
    let mut classes : Array (TSyntax `ident) := #[]
    let mut arguments : Array (Array (TSyntax `ident)) := #[]
    for entry in instances do
      let `(reactiveInstance| $source:ident := $className:ident ($args:ident,*)) := entry
        | Macro.throwErrorAt entry "expected an object instantiation"
      if names.any (fun n => n.getId == source.getId) then
        Macro.throwErrorAt source "duplicate object name"
      names := names.push source
      classes := classes.push className
      arguments := arguments.push args.getElems
    let className := classes[0]!
    for type in classes do
      if type.getId != className.getId then
        Macro.throwErrorAt type "heterogeneous networks are not supported yet"
    let objectType := mkIdent (className.getId ++ `Object)
    let allocator := mkIdent (className.getId ++ `newNetwork)
    let mut fields : Array (TSyntax `Lean.Parser.Command.structSimpleBinder) := #[]
    let mut values : Array (TSyntax `term) := #[]
    let mut edges : Array (TSyntax `term) := #[]
    for i in [:names.size] do
      let field := names[i]!
      let index := Syntax.mkNumLit (toString i)
      fields := fields.push (← `(Lean.Parser.Command.structSimpleBinder|
        $field:ident : $objectType s $count))
      values := values.push (← `(objects $index))
      let mut refs : Array (TSyntax `term) := #[]
      for target in arguments[i]! do
        let some destination := names.findIdx? (fun n => n.getId == target.getId)
          | Macro.throwErrorAt target "unknown friend in network"
        let destination := Syntax.mkNumLit (toString destination)
        refs := refs.push (← `(($destination : Fin $count)))
      edges := edges.push (← `(#v[$refs,*]))
    let commands ← `(command|
      structure $name (s : Type) where
        $[$fields:structSimpleBinder]*)
    let constructor := mkIdent (name.getId ++ `new)
    let allocation ← `(command|
      def $constructor : ST s ($name s) := do
        let objects ← $allocator:ident (fun id => (#v[$edges,*])[id])
        return ⟨$values,*⟩)
    let expose := fun (stx : Syntax) => stx.rewriteBottomUp fun node =>
      match node with
      | .ident info raw value _ => .ident info raw value.eraseMacroScopes []
      | other => other
    return mkNullNode #[expose commands.raw, expose allocation.raw]

end Reactive
