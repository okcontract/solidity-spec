/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.MachineTypes
import Solidity.Core.Execution.Effects

namespace Solidity.Execution.Machine
open Static
open Core (ArithmeticMode)
open Aggregates (Result Failure)

def readTarget (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (state : MachineState σ) : Target Key → Result Value
  | .captured target => Effects.readCaptured registry limits.aggregateFuel state.locals state.heap target
  | .external key => do return ⟨_, ← backend.read state.external key⟩

def writeTarget (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (state : MachineState σ) (target : Target Key) (value : Value) : Result (MachineState σ) := do
  match target with
  | .captured captured =>
      let (locals, heap, remaining) ← Effects.writeCaptured registry limits.aggregateFuel
        state.materializationRemaining state.locals state.heap captured value
      return {state with locals, heap, materializationRemaining := remaining}
  | .external (type := type) key =>
      let (value, heap, remaining) ← Effects.convert registry limits.aggregateFuel
        state.materializationRemaining state.heap .implicit type value
      if same : value.type = type then
        let external ← backend.write state.external key (same ▸ value.value)
        return {state with external, heap, materializationRemaining := remaining}
      else throw (.invalidContext "external write conversion changed its target type")

def assignmentResult (registry : Registry) (limits : Limits)
    (state : MachineState σ) (target : Target Key) (source : Value) : Result Value :=
  match target with
  | .captured target => Effects.assignmentResult registry limits.aggregateFuel state.locals state.heap target source
  | .external (type := type) _ => Effects.scalarCast .implicit type source

def boolean (value : Datum) : Result Bool := do
  let value ← value.asAtom
  match value.type, value.value with
  | .bool, value => return value
  | _, _ => throw (.invalidContext "resolved Boolean expression produced another type")

def typed (expected : SType) (value : Datum) : Result Datum :=
  if value.type = expected then .ok value
  else .error (.invalidContext "resolved expression result type mismatch")

def checkedTarget (expected : SType) (place : Aggregates.Place) : Result (Target Key) :=
  if place.type = expected then .ok (.captured (.heap place))
  else .error (.invalidContext "resolved access result type mismatch")

def pick (choice : Nat) (items : List α) : Option (α × List α) :=
  match items with
  | [] => none
  | _ :: _ =>
      let (before, selected) := items.splitAt (choice % items.length)
      match selected with
      | [] => none
      | value :: rest => some (value, before ++ rest)

/-- Eager groups are generally unary/binary. Structural insertion keeps closed
execution witnesses kernel-computable: Lean's well-founded merge sort gets
stuck behind opaque accessibility proofs during reduction. This ordering costs
quadratic work in group arity and does not evaluate any additional operand. -/
def insertOrdered (item : Nat × α) : List (Nat × α) → List (Nat × α)
  | [] => [item]
  | head :: rest =>
      if item.1 ≤ head.1 then item :: head :: rest
      else head :: insertOrdered item rest

def orderPairs : List (Nat × α) → List (Nat × α)
  | [] => []
  | item :: rest => insertOrdered item (orderPairs rest)

def ordered (items : List (Nat × α)) : List α := (orderPairs items).map Prod.snd

mutual
def patternWrites (pattern : CapturedPattern Key) (value : Datum) :
    Result (List (Target Key × Value)) := do
  match pattern with
  | .hole => return []
  | .target target => return [(target, ← value.asAtom)]
  | .tuple patterns =>
      let .tuple values := value | throw .rejected
      patternListWrites patterns values

def patternListWrites : List (CapturedPattern Key) → Packet → Result (List (Target Key × Value))
  | [], [] => .ok []
  | pattern :: patterns, value :: values => do
      return (← patternWrites pattern value) ++ (← patternListWrites patterns values)
  | _, _ => .error .rejected
end

/-- Default initialization retains unset storage/calldata reference cells.
The checked source boundary proves definite assignment before their use. -/
def declareDefault (registry : Registry) (limits : Limits) (state : MachineState σ)
    (binder : Binder) : Result (MachineState σ) := do
  let (locals, heap, remaining) ← Effects.declareLocal registry limits.aggregateFuel
    state.materializationRemaining state.locals state.heap binder none
  return {state with locals, heap, materializationRemaining := remaining}

def declareUnset (state : MachineState σ) (binder : Binder) : Result (MachineState σ) := do
  return {state with locals := ← state.locals.declare binder}

def declareReturn (registry : Registry) (limits : Limits) (state : MachineState σ)
    (binder : Binder) : Result (MachineState σ) := do
  let (locals, heap, remaining) ← Effects.declareReturn registry limits.aggregateFuel
    state.materializationRemaining state.locals state.heap binder
  return {state with locals, heap, materializationRemaining := remaining}

def bindArguments (backend : Backend σ Key) (registry : Registry) (limits : Limits) :
    MachineState σ → List Binder → Packet → Result (MachineState σ)
  | state, [], [] => .ok state
  | state, binder :: binders, value :: values => do
      let state ← declareUnset state binder
      let state ← writeTarget backend registry limits state (.captured (.local binder.id binder.type))
        (← value.asAtom)
      bindArguments backend registry limits state binders values
  | _, _, _ => .error .rejected

/-- Parameter conversions occur after argument expression effects and before
indirect dispatch, including the null-handle check. Their allocation/panic
behavior is observable even when no callee is ultimately entered. -/
def prepareArguments (registry : Registry) (limits : Limits) :
    MachineState σ → List SType → Packet → Result (Packet × MachineState σ)
  | state, [], [] => .ok ([], state)
  | state, type :: types, value :: values => do
      let (value, heap, remaining) ← Effects.convert registry limits.aggregateFuel
        state.materializationRemaining state.heap .implicit type (← value.asAtom)
      let (values, after) ← prepareArguments registry limits
        {state with heap, materializationRemaining := remaining} types values
      return (.atom value :: values, after)
  | _, _, _ => .error .rejected

def declareValues (backend : Backend σ Key) (registry : Registry) (limits : Limits) :
    MachineState σ → List (Option Binder) → Packet → Result (MachineState σ)
  | state, [], [] => .ok state
  | state, none :: binders, _ :: values => declareValues backend registry limits state binders values
  | state, some binder :: binders, value :: values => do
      let state ← declareUnset state binder
      let state ← writeTarget backend registry limits state (.captured (.local binder.id binder.type))
        (← value.asAtom)
      declareValues backend registry limits state binders values
  | _, _, _ => .error .rejected

def collectResults (locals : Locals) (binders : List Binder) : Result Packet :=
  binders.mapM fun binder => return .atom (← locals.read binder.id binder.type)

def resultWrites : List Binder → Packet → Result (List (Target Key × Value))
  | [], [] => .ok []
  | binder :: binders, value :: values => do
      return (.captured (.local binder.id binder.type), ← value.asAtom) ::
        (← resultWrites binders values)
  | _, _ => .error .rejected

def encodePacket (packet : Packet) : Result (List Contract.Interaction.Word) :=
  packet.mapM fun datum => do
    let value ← datum.asAtom
    Aggregates.encodeMemory value.type value.value

end Solidity.Execution.Machine
