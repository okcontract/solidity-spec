/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.MachineHelpers

/-! Constructor shells allocate only their root. Defaults must not allocate
nested objects that would immediately be overwritten by constructor arguments.
The machine supplies the separate argument-evaluation stages. -/
namespace Solidity.Execution.Constructors
open Static
open Aggregates (Result Place)

def allocateArray (registry : Registry) (limits : Limits) (state : MachineState σ)
    (element : SType) (count : Nat) : Result (Place × MachineState σ) := do
  if count = 0 then throw .rejected
  let type := SType.array (Aggregates.atLocation element .memory false) (some count) .memory true
  Aggregates.eligibleAt registry limits.aggregateFuel (.memory state.heap.invocation) type
  let size ← Aggregates.MemoryOps.arraySize count false false
  let (reference, heap, remaining) ← Aggregates.MemoryOps.allocate state.heap state.materializationRemaining size
  return (⟨type, reference⟩, {state with heap, materializationRemaining := remaining})

def allocateStruct (registry : Registry) (limits : Limits) (state : MachineState σ)
    (identity : Nat) : Result (Place × List SType × MachineState σ) := do
  let type := SType.structType identity .memory true
  Aggregates.eligibleAt registry limits.aggregateFuel (.memory state.heap.invocation) type
  let some fields := registry.structFields identity | throw (.invalidContext "unresolved struct constructor")
  let types := fields.map (fun field => Aggregates.atLocation field.2 .memory false)
  let size ← Aggregates.MemoryOps.arraySize types.length false false
  let (reference, heap, remaining) ← Aggregates.MemoryOps.allocate state.heap state.materializationRemaining size
  return (⟨type, reference⟩, types, {state with heap, materializationRemaining := remaining})

/-- Conversion follows the raw argument evaluation phase. Writing a reference
stores its converted pointer without decoding the previously empty cell. -/
def writeCell (registry : Registry) (limits : Limits) (state : MachineState σ)
    (root : Place) (index : Nat) (type : SType) (source : Value) : Result (MachineState σ) := do
  let (value, heap, remaining) ← Effects.convert registry limits.aggregateFuel
    state.materializationRemaining state.heap .implicit type source
  let cell ← Aggregates.Access.advance root.reference (index * 32)
  let heap ← Aggregates.Defaults.writeMemoryValue heap cell value
  return {state with heap, materializationRemaining := remaining}

theorem writeCell_external
    (written : writeCell registry limits (state : MachineState σ) root index type source = .ok after) :
    after.external = state.external := by
  unfold writeCell at written
  cases converted : Effects.convert registry limits.aggregateFuel state.materializationRemaining state.heap .implicit type source with
  | error failure => simp [converted, Bind.bind, Except.bind] at written
  | ok result =>
      rcases result with ⟨value, heap, remaining⟩
      simp only [converted, Bind.bind, Except.bind] at written
      cases advanced : Aggregates.Access.advance root.reference (index * 32) with
      | error failure => simp [advanced] at written
      | ok cell =>
          simp only [advanced] at written
          cases stored : Aggregates.Defaults.writeMemoryValue heap cell value with
          | error failure => simp [stored] at written
          | ok final => simp [stored, Pure.pure, Except.pure] at written; cases written; rfl

end Solidity.Execution.Constructors
