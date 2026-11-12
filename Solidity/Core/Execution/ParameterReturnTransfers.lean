/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.ParameterTransfers

/-! Complete generic result transfer through the real call continuation.
The transferred values arise from the closed aggregate conversion/alias/copy trace;
they are not caller-supplied postconditions. Arbitrary result types, source
packets, caller scopes and continuation stacks are quantified. -/
namespace Solidity.Execution.ParameterTransfers
open Static Aggregates
open Core (ArithmeticMode)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

variable {σ : Type} {Key : SType → Type}

/-- Explicit returns convert and store their components in declaration order,
read those actual result cells, then restore the saved caller locals and mode.
Reference results retain the actual aggregate alias or physical fresh-copy contracts
in each `Stored.bind` node of the returned trace. -/
theorem explicitReturn_reaches (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (program : Program Key) (state after entry : MachineState σ) (caller : Locals)
    (mode : ArithmeticMode) (binders : List Binder) (source : Datum) (stack : List (Frame Key))
    (transferred : transferResults backend registry limits state binders source.asPacket = .ok after)
    (distinct : (binders.map Binder.id).Nodup) (host : limits.hostContinuationLimit = none) :
    ∃ values,
      Transferred registry limits.aggregateFuel false state binders source.asPacket values after ∧
      Reaches (Machine.step backend registry limits program)
        ⟨.resume (.return_ (some source)), .call caller mode binders :: stack, state, entry⟩
        ⟨.value (Datum.ofPacket (values.map fun item => Datum.atom item.2)), stack,
          {after with locals := caller, mode}, entry⟩ := by
  obtain ⟨values, trace⟩ := transferResults_iff.mp transferred
  obtain ⟨assignments, classified, writes⟩ := resultTransfer_reaches transferred host program
    (.resultTransfer caller mode binders :: stack) entry
  refine ⟨values, trace, ?_⟩
  have beginReturn : Reaches (Machine.step backend registry limits program)
      ⟨.resume (.return_ (some source)), .call caller mode binders :: stack, state, entry⟩
      ⟨.writes assignments, .resultTransfer caller mode binders :: stack, state, entry⟩ := by
    apply Reaches.single (choice := 0)
    simp [Machine.step, Machine.transition, Machine.next, classified, host]
  have finish : Reaches (Machine.step backend registry limits program)
      ⟨.value (.tuple []), .resultTransfer caller mode binders :: stack, after, entry⟩
      ⟨.value (Datum.ofPacket (values.map fun item => Datum.atom item.2)), stack,
        {after with locals := caller, mode}, entry⟩ := by
    apply Reaches.single (choice := 0)
    simp [Machine.step, Machine.transition, Machine.finishCall, Machine.next,
      trace.collectResults distinct, host]
  exact beginReturn.trans (writes.trans finish)

/-- The generic return prefix preserves the shared world, invocation and prior
allocation records. MemoryExtension frames read slices at offsets at least 96
whose endpoints lie below the entry frontier; this excludes the raw free
pointer word. Actual aggregate copy conversions may extend that frontier. -/
theorem explicitReturn_frame (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (program : Program Key) (state after entry : MachineState σ) (caller : Locals)
    (mode : ArithmeticMode) (binders : List Binder) (source : Datum) (stack : List (Frame Key))
    (transferred : transferResults backend registry limits state binders source.asPacket = .ok after)
    (distinct : (binders.map Binder.id).Nodup) (host : limits.hostContinuationLimit = none) :
    ∃ values,
      Transferred registry limits.aggregateFuel false state binders source.asPacket values after ∧
      Reaches (Machine.step backend registry limits program)
        ⟨.resume (.return_ (some source)), .call caller mode binders :: stack, state, entry⟩
        ⟨.value (Datum.ofPacket (values.map fun item => Datum.atom item.2)), stack,
          {after with locals := caller, mode}, entry⟩ ∧
      after.external = state.external ∧ after.mode = state.mode ∧
      after.heap.execution.world = state.heap.execution.world ∧ after.heap.invocation = state.heap.invocation ∧
      Copy.MemoryExtension state.heap.nextMemory state.heap after.heap := by
  obtain ⟨values, trace, reached⟩ := explicitReturn_reaches backend registry limits program state after entry caller mode
    binders source stack transferred distinct host
  exact ⟨values, trace, reached, trace.frame.1, trace.frame.2.1, trace.frame.2.2.1,
    trace.frame.2.2.2, trace.extension⟩

/-- A bare return (or function fallthrough) reads the named cells as they are;
it performs no new conversion, allocation or world update. -/
theorem namedReturn_reaches (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (program : Program Key) (state entry : MachineState σ) (caller : Locals)
    (mode : ArithmeticMode) (binders : List Binder) (packet : Packet) (stack : List (Frame Key))
    (collected : Machine.collectResults state.locals binders = .ok packet)
    (host : limits.hostContinuationLimit = none) :
    Reaches (Machine.step backend registry limits program)
      ⟨.resume (.return_ none), .call caller mode binders :: stack, state, entry⟩
      ⟨.value (Datum.ofPacket packet), stack, {state with locals := caller, mode}, entry⟩ := by
  apply Reaches.single (choice := 0)
  simp [Machine.step, Machine.transition, Machine.finishCall, Machine.next, collected, host]

end Solidity.Execution.ParameterTransfers
