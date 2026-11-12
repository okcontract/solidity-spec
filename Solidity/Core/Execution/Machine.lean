/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.MachineHelpers
import Solidity.Core.Execution.ErrorPayloads
import Solidity.Core.Execution.ValueOperations
import Solidity.Core.Execution.Constructors
import Solidity.Core.Execution.PacketTransfers
import Solidity.Policy
import Solidity.Frontend.Assignment

/-! One continuation machine for expressions, captured places, scopes, loops
and internal source calls. Every eager child group makes independent choices;
short-circuit and statement sequencing retain their required order. -/
namespace Solidity.Execution.Machine
open Static
open Core (ArithmeticMode)
open Aggregates (Result Failure)

abbrev StepResult (σ : Type) (Key : SType → Type) :=
  Result (Progress (Config σ Key) (Observation σ))

def next (config : Config σ Key) (task : Task Key)
    (state : MachineState σ := config.state) (stack : List (Frame Key) := config.stack) : StepResult σ Key :=
  .ok (.next {config with task, state, stack})

def gather (config : Config σ Key) (values : List (Expr Key)) (finish : Completion) : StepResult σ Key :=
  next config (.collect (values.zipIdx.map fun (value, index) => (index, value)) [] finish)

def finishCall (config : Config σ Key) (locals : Locals) (mode : ArithmeticMode)
    (returns : List Binder) (stack : List (Frame Key)) : StepResult σ Key := do
  let values ← collectResults config.state.locals returns
  next config (.value (Datum.ofPacket values)) {config.state with locals, mode} stack

def invoke (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (config : Config σ Key) (signature : FunctionSignature) (function : Value)
    (arguments : Packet) : StepResult σ Key := do
  let function ← Effects.scalarCast .implicit signature.type function
  let handle ← match function with
    | ⟨.function .internal mutability parameters returns, value⟩ => do
        if (⟨mutability, parameters, returns⟩ : FunctionSignature) != signature then
          throw (.invalidContext "internal call signature differs from resolved function value")
        pure (value : Option Nat)
    | _ => throw (.invalidContext "internal call operand is not an internal function value")
  let (arguments, prepared) ← prepareArguments registry limits config.state (typesList signature.parameters) arguments
  let some handle := handle | throw (.panic 0x51)
  let definition ← program.lookup handle
  if !definition.signature.accepts signature then
    throw (.invalidContext "internal handle selects a different signature")
  let entered := {prepared with locals := Locals.empty, mode := .checked}
  let entered ← bindArguments backend registry limits entered definition.parameters arguments
  let entered ← definition.returns.foldlM (declareReturn registry limits) entered
  next config (.exec definition.body) entered
    (.call config.state.locals config.state.mode definition.returns :: config.stack)

def commit (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (config : Config σ Key) (target : Target Key) (right : Datum) (compound : Option BinaryCode)
    (stack : List (Frame Key)) : StepResult σ Key := do
  let right ← right.asAtom
  let written ← match compound with
    | none => pure right
    | some code => do
        if !Frontend.Inference.compoundToken code then throw .rejected
        Effects.binary config.state.mode code (← readTarget backend registry limits config.state target) right
  let state ← writeTarget backend registry limits config.state target written
  let value ← assignmentResult registry limits state target written
  next config (.value (.atom value)) state stack

def update (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (config : Config σ Key) (target : Target Key) (code : UpdateCode)
    (stack : List (Frame Key)) : StepResult σ Key := do
  match target with
  | .captured captured =>
      let (value, locals, heap, remaining) ← Effects.updateCaptured registry limits.aggregateFuel
        config.state.materializationRemaining config.state.mode config.state.locals config.state.heap captured code
      next config (.value (match value with | none => .tuple [] | some value => .atom value))
        {config.state with locals, heap, materializationRemaining := remaining} stack
  | .external (type := type) key =>
      match code with
      | .delete =>
          if !Aggregates.Mutation.deletable type then throw .rejected
          let (zero, heap, remaining) ← Aggregates.Mutation.deleteValue registry limits.aggregateFuel
            config.state.materializationRemaining config.state.heap type
          if same : zero.type = type then
            let external ← backend.write config.state.external key (same ▸ zero.value)
            next config (.value (.tuple [])) {config.state with external, heap, materializationRemaining := remaining} stack
          else throw (.invalidContext "delete default changed its type")
      | _ =>
          let old ← readTarget backend registry limits config.state target
          let changed ← Effects.scalarUpdate config.state.mode code old
          let state ← writeTarget backend registry limits config.state target changed.next
          next config (.value (match changed.result with | none => .tuple [] | some value => .atom value)) state stack

def apply (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (config : Config σ Key) (finish : Completion) (values : Packet) : StepResult σ Key := do
  let state := config.state
  let fuel := limits.aggregateFuel
  let budget := state.materializationRemaining
  match finish, values with
  | .tuple, values => next config (.value (.tuple values))
  | .structConstructor identity order, arguments =>
      let arguments ← ArgumentOrder.select order arguments
      let (root, types, state) ← Constructors.allocateStruct registry limits state identity
      if types.length != arguments.length then throw .rejected
      next config (.structFields root 0 types arguments) state
  | .wrap identity base, [source] => next config (.value (.atom (← ValueOperations.wrap identity base (← source.asAtom))))
  | .unwrap identity base, [source] => next config (.value (.atom (← ValueOperations.unwrap identity base (← source.asAtom))))
  | .functionAddress, [source] => next config (.value (.atom (← ValueOperations.functionAddress (← source.asAtom))))
  | .functionSelector, [source] => next config (.value (.atom (← ValueOperations.functionSelector (← source.asAtom))))
  | .unary code, [value] =>
      next config (.value (.atom (← Effects.unary state.mode code (← value.asAtom))))
  | .binary code type, [left, right] =>
      let value ← Effects.binary state.mode code (← left.asAtom) (← right.asAtom)
      next config (.value (← typed type (.atom value)))
  | .cast mode target, [source] =>
      let (value, heap, remaining) ← PacketTransfers.transfer registry fuel budget state.heap mode target source
      next config (.value value) {state with heap, materializationRemaining := remaining}
  | .referenceCast target, [source] =>
      let (value, heap, remaining) ← Effects.convert registry fuel budget state.heap (.explicit .ordinary)
        target (← source.asAtom)
      next config (.value (.atom value)) {state with heap, materializationRemaining := remaining}
  | .call signature, function :: arguments => invoke backend registry limits program config signature (← function.asAtom) arguments
  | .namedCall signature order, function :: arguments =>
      invoke backend registry limits program config signature (← function.asAtom) (← ArgumentOrder.select order arguments)
  | .assert_, [condition] =>
      if ← boolean condition then next config (.value (.tuple [])) else throw (.panic 0x01)
  | .require_ encoding, condition :: arguments =>
      if ← boolean condition then next config (.value (.tuple []))
      else throw (.revert (← ErrorPayloads.encode registry fuel budget state.heap encoding (← arguments.mapM Datum.asAtom)))
  | .revertWith encoding, arguments =>
      throw (.revert (← ErrorPayloads.encode registry fuel budget state.heap encoding (← arguments.mapM Datum.asAtom)))
  | .newArray element, [count] =>
      let (value, heap, remaining) ← Effects.newArray registry fuel budget state.heap element (← count.asAtom)
      next config (.value (.atom value)) {state with heap, materializationRemaining := remaining}
  | .newBytes string, [count] =>
      let (value, heap, remaining) ← Effects.newBytes budget state.heap string (← count.asAtom)
      next config (.value (.atom value)) {state with heap, materializationRemaining := remaining}
  | .length, [source] => next config (.value (.atom (← Effects.length registry fuel state.heap (← source.asAtom))))
  | .slice hasStart hasStop, source :: bounds =>
      let source ← source.asAtom
      let (start, bounds) ← if hasStart then
        match bounds with
        | value :: rest => pure (← Effects.unsignedNat (← value.asAtom), rest)
        | _ => throw (.invalidContext "missing slice start operand")
        else pure (0, bounds)
      let stop ← if hasStop then
        match bounds with
        | [value] => Effects.unsignedNat (← value.asAtom)
        | _ => throw (.invalidContext "missing slice stop operand")
        else do
          if !bounds.isEmpty then throw (.invalidContext "extra slice operand")
          Effects.unsignedNat (← Effects.length registry fuel state.heap source)
      next config (.value (.atom (← Effects.slice registry fuel state.heap source start stop)))
  | .push, [source, value] =>
      let (heap, remaining) ← Effects.push registry fuel budget state.heap (← source.asAtom) (← value.asAtom)
      next config (.value (.tuple [])) {state with heap, materializationRemaining := remaining}
  | .pop, [source] =>
      let (heap, remaining) ← Effects.pop registry fuel budget state.heap (← source.asAtom)
      next config (.value (.tuple [])) {state with heap, materializationRemaining := remaining}
  | .field type index, [source] =>
      next config (.target (← checkedTarget type (← Effects.field registry fuel state.heap (← source.asAtom) index)))
  | .index type, [source, index] =>
      next config (.target (← checkedTarget type (← Effects.index registry fuel state.heap (← source.asAtom) (← index.asAtom))))
  | .readIndex type, [source, index] =>
      next config (.value (← typed type (.atom (← Effects.readIndex registry fuel state.locals state.heap
        (← source.asAtom) (← index.asAtom)))))
  | .mapping type, [source, key] =>
      let (place, remaining) ← Effects.mapping registry fuel budget state.heap (← source.asAtom) (← key.asAtom)
      next config (.target (← checkedTarget type place)) {state with materializationRemaining := remaining}
  | .pushZero type, [source] =>
      let (target, heap, remaining) ← Effects.capturePushZero registry fuel budget state.heap (← source.asAtom)
      if target.type != type then throw (.invalidContext "push lvalue result type mismatch")
      next config (.target (.captured target)) {state with heap, materializationRemaining := remaining}
  | .emit topicCount, values =>
      if values.length < topicCount then throw (.invalidContext "missing event operands")
      let topics ← (values.take topicCount).mapM Datum.asAtom
      let data ← (values.drop topicCount).mapM Datum.asAtom
      let heap ← Effects.emitWords state.heap topics data
      next config (.resume .next) {state with heap}
  | _, _ => throw (.invalidContext "resolved operation operand count mismatch")

def transition (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (choice : Nat) (config : Config σ Key) : StepResult σ Key := do
  let state := config.state
  let stack := config.stack
  match config.task with
  | .eval expression => match expression with
    | .literal value => next config (.value (.atom value))
    | .bytesLiteral string bytes =>
        let type : SType := if string then .string .memory true else .bytes .memory true
        let (value, heap, remaining) ← Aggregates.Copy.materializeMemory registry limits.aggregateFuel
          state.materializationRemaining state.heap type (.bytes string bytes)
        next config (.value (.atom value)) {state with heap, materializationRemaining := remaining}
    | .local id type => next config (.value (.atom (← Effects.readCaptured registry limits.aggregateFuel state.locals state.heap (.local id type))))
    | .externalRead key => next config (.value (.atom ⟨_, ← backend.read state.external key⟩))
    | .read target => next config (.capture target) state (.readTarget :: stack)
    | .arithmetic mode value => next config (.eval value) {state with mode} (.mode state.mode :: stack)
    | .cast mode type arg => gather config [arg] (.cast mode type)
    | .referenceCast type arg => gather config [arg] (.referenceCast type)
    | .unary code arg => gather config [arg] (.unary code)
    | .wrap identity base arg => gather config [arg] (.wrap identity base)
    | .unwrap identity base arg => gather config [arg] (.unwrap identity base)
    | .functionAddress arg => gather config [arg] .functionAddress
    | .functionSelector arg => gather config [arg] .functionSelector
    | .binary .and _ left right => next config (.eval left) state (.lazy false right :: stack)
    | .binary .or _ left right => next config (.eval left) state (.lazy true right :: stack)
    | .binary code type left right => gather config [left, right] (.binary code type)
    | .conditional test yes no => next config (.eval test) state (.select yes no :: stack)
    | .tuple values => gather config values .tuple
    | .inlineArray element elements =>
        let (root, state) ← Constructors.allocateArray registry limits state element elements.length
        next config (.inlineElements root (Aggregates.atLocation element .memory false)
          (elements.zipIdx.map fun (value, index) => (index, value))) state
    | .structConstructor identity arguments order => gather config arguments (.structConstructor identity order)
    | .assign target value =>
        if choice % 2 = 0 then next config (.eval value) state (.assignRight target none :: stack)
        else next config (.capture target) state (.assignLeft value none :: stack)
    | .compound code target value =>
        if choice % 3 = 0 then next config (.eval value) state (.assignRight target (some code) :: stack)
        else if choice % 3 = 1 then next config (.capture target) state (.compoundReadFirst value code :: stack)
        else next config (.capture target) state (.assignLeft value (some code) :: stack)
    | .update code target => next config (.capture target) state (.update code :: stack)
    | .tupleAssign pattern value =>
        if choice % 2 = 0 then next config (.eval value) state (.tupleCapture pattern :: stack)
        else next config (.pattern pattern) state (.tupleRight value :: stack)
    | .call signature function arguments => gather config (function :: arguments) (.call signature)
    | .namedCall signature function arguments order => gather config (function :: arguments) (.namedCall signature order)
    | .assert_ condition => gather config [condition] .assert_
    | .require_ encoding condition arguments => gather config (condition :: arguments) (.require_ encoding)
    | .revertWith encoding arguments => gather config arguments (.revertWith encoding)
    | .newArray element count => gather config [count] (.newArray element)
    | .newBytes string count => gather config [count] (.newBytes string)
    | .length source => gather config [source] .length
    | .index type source index => gather config [source, index] (.readIndex type)
    | .slice source start stop => gather config ([source] ++ start.toList ++ stop.toList) (.slice start.isSome stop.isSome)
    | .push source value => gather config [source, value] .push
    | .pop source => gather config [source] .pop
  | .capture target => match target with
    | .local id type =>
        if (← state.locals.typeOf id) != type then throw (.invalidContext "captured local type mismatch")
        next config (.target (.captured (.local id type)))
    | .heap place =>
        Aggregates.Access.validate state.heap place
        next config (.target (.captured (.heap place)))
    | .external key => next config (.target (.external key))
    | .field type base index => gather config [base] (.field type index)
    | .index type base index => gather config [base, index] (.index type)
    | .mapping type base key => gather config [base, key] (.mapping type)
    | .pushZero type base => gather config [base] (.pushZero type)
  | .collect pending values finish =>
      match pick choice pending with
      | none => next config (.apply finish (ordered values))
      | some ((index, expression), rest) => next config (.eval expression) state (.collect index rest values finish :: stack)
  | .apply finish values => apply backend registry limits program config finish values
  | .inlineElements root element pending =>
      match pick choice pending with
      | none => next config (.value (.atom (← root.asValue)))
      | some ((index, expression), rest) =>
          next config (.eval expression) state (.initializeElement root element index rest :: stack)
  | .structFields root _ [] [] => next config (.value (.atom (← root.asValue)))
  | .structFields root index (type :: types) (value :: values) =>
      next config (.structFields root (index + 1) types values)
        (← Constructors.writeCell registry limits state root index type (← value.asAtom))
  | .structFields _ _ _ _ => throw .rejected
  | .pattern pattern => match pattern with
    | .hole => next config (.patternValue .hole)
    | .target target => next config (.capture target) state (.patternTarget :: stack)
    | .tuple patterns => next config (.patterns (patterns.zipIdx.map fun (value, index) => (index, value)) [])
  | .patterns pending values =>
      match pick choice pending with
      | none => next config (.patternValue (.tuple (ordered values)))
      | some ((index, pattern), rest) => next config (.pattern pattern) state (.patternItem index rest values :: stack)
  | .patternValue pattern => match stack with
    | .patternItem index rest values :: stack => next config (.patterns rest ((index, pattern) :: values)) state stack
    | .tupleRight right :: stack => next config (.eval right) state (.tupleCommitPattern pattern :: stack)
    | .tupleCommitValue value :: stack => next config (.writes (Policy.Solc0836.tupleCommit (← patternWrites pattern value))) state stack
    | _ => throw (.invalidContext "captured tuple pattern escaped its continuation")
  | .writes [] => next config (.value (.tuple []))
  | .writes ((target, value) :: rest) =>
      next config (.writes rest) (← writeTarget backend registry limits state target value)
  | .target target => match stack with
    | .readTarget :: stack => next config (.value (.atom (← readTarget backend registry limits state target))) state stack
    | .update code :: stack => update backend registry limits config target code stack
    | .assignLeft right compound :: stack => next config (.eval right) state (.commitTarget target compound :: stack)
    | .commitValue value compound :: stack => commit backend registry limits config target value compound stack
    | .compoundReadFirst right code :: stack =>
        let old ← readTarget backend registry limits state target
        next config (.eval right) state (.commitOld target code old :: stack)
    | .patternTarget :: stack => next config (.patternValue (.target target)) state stack
    | _ => throw (.invalidContext "captured place escaped its continuation")
  | .value value => match stack with
    | [] => return .done (.returned value.asPacket state)
    | .collect index rest values finish :: stack => next config (.collect rest ((index, value) :: values) finish) state stack
    | .discard :: stack => next config (.resume .next) state stack
    | .returnValue :: stack => next config (.resume (.return_ (some value))) state stack
    | .mode mode :: stack => next config (.value value) {state with mode} stack
    | .select yes no :: stack => next config (.eval (if ← boolean value then yes else no)) state stack
    | .branch yes no :: stack => next config (.exec (if ← boolean value then yes else no)) state stack
    | .lazy terminal right :: stack =>
        if (← boolean value) = terminal then next config (.value (.atom ⟨.bool, terminal⟩)) state stack
        else next config (.eval right) state stack
    | .assignRight target compound :: stack => next config (.capture target) state (.commitValue value compound :: stack)
    | .commitTarget target compound :: stack => commit backend registry limits config target value compound stack
    | .commitOld target code old :: stack =>
        if !Frontend.Inference.compoundToken code then throw .rejected
        let written ← Effects.binary state.mode code old (← value.asAtom)
        let state ← writeTarget backend registry limits state target written
        next config (.value (.atom (← assignmentResult registry limits state target written))) state stack
    | .tupleCapture pattern :: stack => next config (.pattern pattern) state (.tupleCommitValue value :: stack)
    | .tupleCommitPattern pattern :: stack => next config (.writes (Policy.Solc0836.tupleCommit (← patternWrites pattern value))) state stack
    | .declare binders :: stack =>
        next config (.resume .next) (← declareValues backend registry limits state binders value.asPacket) stack
    | .storeExternal key :: stack =>
        let state ← writeTarget backend registry limits state (.external key) (← value.asAtom)
        next config (.resume .next) state stack
    | .loopCondition test body post :: stack =>
        if ← boolean value then next config (.exec body) state (.loopBody test body post :: stack)
        else next config (.resume .next) state stack
    | .doCondition body test :: stack =>
        if ← boolean value then next config (.exec body) state (.doBody body test :: stack)
        else next config (.resume .next) state stack
    | .resultTransfer locals mode returns :: stack => finishCall config locals mode returns stack
    | .initializeElement root element index rest :: stack =>
        next config (.inlineElements root element rest)
          (← Constructors.writeCell registry limits state root index element (← value.asAtom)) stack
    | _ => throw (.invalidContext "expression result reached a statement-only continuation")
  | .exec statement => match statement with
    | .skip => next config (.resume .next)
    | .expr value => next config (.eval value) state (.discard :: stack)
    | .seq first rest => next config (.exec first) state (.next rest :: stack)
    | .block body => next config (.exec body) {state with locals := state.locals.enter} (.scope :: stack)
    | .declare binders (some initializer) => next config (.eval initializer) state (.declare binders :: stack)
    | .declare binders none =>
        let state ← binders.foldlM (fun state binder => do
          let some binder := binder | throw .rejected
          declareDefault registry limits state binder) state
        next config (.resume .next) state
    | .if_ test yes no => next config (.eval test) state (.branch yes no :: stack)
    | .while_ test body => next config (.loopTest test body .skip)
    | .loop test body post => next config (.loopTest test body post)
    | .doWhile body test => next config (.exec body) state (.doBody body test :: stack)
    | .for_ init test post body =>
        let test := test.getD (.literal ⟨.bool, true⟩)
        next config (.exec init) {state with locals := state.locals.enter} (.forInit test body post :: .scope :: stack)
    | .break_ => next config (.resume .break_)
    | .continue_ => next config (.resume .continue_)
    | .return_ none => next config (.resume (.return_ none))
    | .return_ (some value) => next config (.eval value) state (.returnValue :: stack)
    | .arithmetic mode body => next config (.exec body) {state with mode} (.mode state.mode :: stack)
    | .emit topics data => gather config (topics ++ data) (.emit topics.length)
    | .revert bytes => throw (.revert bytes)
    | .storeExternal key value => next config (.eval value) state (.storeExternal key :: stack)
  | .loopTest test body post => next config (.eval test) state (.loopCondition test body post :: stack)
  | .resume signal => match stack with
    | [] => match signal with
      | .next | .return_ none => return .done (.returned [] state)
      | .return_ (some values) => return .done (.returned values.asPacket state)
      | .break_ | .continue_ => throw .rejected
    | .scope :: stack => next config (.resume signal) {state with locals := ← state.locals.leave} stack
    | .mode mode :: stack => next config (.resume signal) {state with mode} stack
    | .next rest :: stack => match signal with
      | .next => next config (.exec rest) state stack
      | _ => next config (.resume signal) state stack
    | .forInit test body post :: stack => match signal with
      | .next => next config (.loopTest test body post) state stack
      | _ => next config (.resume signal) state stack
    | .loopBody test body post :: stack => match signal with
      | .next | .continue_ => next config (.exec post) state (.loopPost test body post :: stack)
      | .break_ => next config (.resume .next) state stack
      | _ => next config (.resume signal) state stack
    | .loopPost test body post :: stack => match signal with
      | .next => next config (.loopTest test body post) state stack
      | _ => next config (.resume signal) state stack
    | .doBody body test :: stack => match signal with
      | .next | .continue_ => next config (.eval test) state (.doCondition body test :: stack)
      | .break_ => next config (.resume .next) state stack
      | _ => next config (.resume signal) state stack
    | .call locals mode returns :: stack => match signal with
      | .next | .return_ none => finishCall config locals mode returns stack
      | .return_ (some values) =>
          next config (.writes (← resultWrites returns values.asPacket)) state (.resultTransfer locals mode returns :: stack)
      | .break_ | .continue_ => throw .rejected
    | _ => throw (.invalidContext "control signal reached an expression-only continuation")

/-- A primitive host limit suspends the exact pre-transition configuration.
Every actual source failure rolls back the invocation checkpoint. -/
def step (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (choice : Nat) (config : Config σ Key) : Progress (Config σ Key) (Observation σ) :=
  match transition backend registry limits program choice config with
  | .ok (.next after) =>
      match limits.hostContinuationLimit with
      | some maximum =>
          if maximum < after.stack.length then .suspended config
          else .next after
      | none => .next after
  | .ok progress => progress
  | .error .exhausted => .suspended config
  | .error failure =>
      if isSourceFailure failure then .done (fail config.entry failure)
      else .done (.inconclusive failure config.state)

/-- An explicit target-resource observation interface. The source continuation
stack is not the EVM operand stack. A target consumer must supply its own
accounting and prove its binding to an artifact; the ideal source step
and its host limits make no target-stack adequacy claim. -/
abbrev TargetPolicy (σ : Type) (Key : SType → Type) :=
  Config σ Key → Config σ Key → Option TargetResource

def targetStep (policy : TargetPolicy σ Key) (backend : Backend σ Key) (registry : Registry)
    (limits : Limits) (program : Program Key) (choice : Nat) (config : Config σ Key) :
    Progress (Config σ Key) (Observation σ) :=
  match step backend registry limits program choice config with
  | .next after => match policy config after with
      | none => .next after
      | some resource => .done (.resourceLimit resource config.entry)
  | progress => progress

def execute (backend : Backend σ Key) (registry : Registry) (limits : Limits) (program : Program Key)
    (fuel : Nat) (choices : List Nat) (config : Config σ Key) : Execution (Config σ Key) (Observation σ) :=
  run (step backend registry limits program) fuel choices config

theorem execute_sound (completed : execute backend registry limits program fuel choices config = .finished result) :
    Executes (step backend registry limits program) config result :=
  run_sound _ _ _ _ _ completed

theorem execute_complete (completed : Executes (step backend registry limits program) config result) :
    ∃ fuel choices, execute backend registry limits program fuel choices config = .finished result :=
  run_complete _ completed

end Solidity.Execution.Machine
