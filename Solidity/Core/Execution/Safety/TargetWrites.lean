/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.SupportedTransfers
import Solidity.Core.Execution.Safety.LocalSteps
import Solidity.Core.Execution.Safety.WordEffects
import Solidity.Core.Execution.Safety.ConfigurationFrames
import Solidity.Core.Execution.Safety.SupportedReads

/-! Constructive writes for represented captured targets. Physical word writes
retain their real read-only exceptional outcome; memory/local assignments use
the existing permitted scalar conversions and canonical memory aliases. -/
namespace Solidity.Execution.Safety.TargetWrites
open Static Aggregates
open SupportedTransfers
open Contract.Interaction (Word wordBytes)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem state_withHeap (represented : StateRep program objects environment state)
    (heapRep : HeapRep heap objects) (invocation : heap.invocation = state.heap.invocation) :
    StateRep program objects environment {state with heap} :=
  ⟨heapRep,represented.cells.extend invocation (fun _ member => member),represented.shape,represented.nonempty⟩

theorem heapTarget_type (target : HeapTargetRep heap objects place) : place.type = .uint 31 := by
  cases target <;> rfl

theorem word_transfer (ready : TransferReady registry source (.uint 31)) :
    source.scalarSupported = true ∧ Static.Implicit source (.uint 31) := by
  obtain ⟨sourceReady,targetReady,kind,rule⟩ := ready
  rcases transfer_classification sourceReady.1 targetReady.1 rule with scalar | ⟨_,_,_,bad,_⟩
  · exact ⟨scalar.1,scalar.2.2.2⟩
  · cases bad

theorem plan_scalar_false (sourceReady : TypeReady registry source) (targetReady : TypeReady registry target)
    (sourceScalar : source.scalarSupported = true) (targetScalar : target.scalarSupported = true)
    (allowed : Static.Implicit source target) (fuel : Nat) :
    planTransfer registry (fuel+2) false source target = .ok .scalarConversion := by
  have selected := (selectTransfer_iff false source target .scalarConversion).mpr
    ⟨scalar_reference_none sourceScalar,scalar_reference_none targetScalar,allowed⟩
  simp only [planTransfer,SupportedEligibility.eligible_total sourceReady fuel,
    SupportedEligibility.eligible_total targetReady fuel,selected,Bind.bind,Except.bind]
  rfl

private theorem heap_conversion (place : Place)
    (planned : planTransfer registry fuel false source.type place.type = .ok .scalarConversion)
    (converted : Copy.convertScalar place.type source = .ok value)
    (identityPlan : planTransfer registry fuel false value.type place.type = .ok .scalarConversion)
    (identity : Copy.convertScalar place.type value = .ok value) :
    Effects.writeCaptured registry fuel budget locals heap (.heap place) source =
      Effects.writeCaptured registry fuel budget locals heap (.heap place) value := by
  simp only [Effects.writeCaptured,Copy.assign]
  cases valid : Access.validate heap place with
  | error failure => simp
  | ok _ => simp [planned,converted,identityPlan,identity]

theorem heap_write_total (backend : Backend Unit EmptyKey)
    (stateRep : StateRep program objects environment state)
    (target : HeapTargetRep state.heap objects place)
    (sourceRep : ValueRep program state.heap objects source)
    (ready : TransferReady registry source.type (.uint 31)) (fuel : Nat) :
    Machine.writeTarget backend registry ⟨fuel+2,none⟩ state (.captured (.heap place)) source =
        .error .exceptional ∨
    ∃ after,
      Machine.writeTarget backend registry ⟨fuel+2,none⟩ state (.captured (.heap place)) source = .ok after ∧
      StateRep program objects environment after ∧ after.heap.invocation = state.heap.invocation ∧
      after.materializationRemaining = state.materializationRemaining := by
  obtain ⟨support,allowed⟩ := word_transfer ready
  obtain ⟨converted,conversion,convertedRep⟩ := scalar_value_total program state.heap objects source (.uint 31)
    support rfl allowed (scalar_closed sourceRep support)
  have convertedType := Copy.convertScalar_type conversion
  rcases converted with ⟨type,value⟩
  dsimp only at convertedType
  cases convertedType
  have planned := plan_scalar_false ready.1 ready.2.1 support rfl allowed fuel
  have write := heap_conversion (registry := registry) (fuel := fuel+2)
    (budget := state.materializationRemaining) (locals := state.locals) (heap := state.heap) place
    (by rw [heapTarget_type target]; exact planned)
    (by rw [heapTarget_type target]; exact conversion)
    (by rw [heapTarget_type target]; exact WordEffects.plan_word registry (fuel+1) false)
    (by rw [heapTarget_type target]; rfl)
  cases target with
  | persistent owner address =>
      have physical := WordEffects.write_persistent (registry := registry) (fuel := fuel+1)
        (budget := state.materializationRemaining) (locals := state.locals) state.heap owner address value
      dsimp only [WordEffects.persistent] at physical
      rw [← write] at physical
      by_cases readOnly : state.heap.execution.context.readOnly = true
      · exact Or.inl (by simp [Machine.writeTarget,physical,Slot.write,readOnly])
      · let heap := {state.heap with execution := {state.heap.execution with
          world := state.heap.execution.world.store (owner.setWidth 256) address value}}
        refine Or.inr ⟨{state with heap},?_,state_withHeap stateRep (WordEffects.HeapRep.withWorld stateRep.heap _) rfl,rfl,rfl⟩
        simp [Machine.writeTarget,physical,Slot.write,readOnly,heap]
  | transient owner address =>
      have physical := WordEffects.write_transient (registry := registry) (fuel := fuel+1)
        (budget := state.materializationRemaining) (locals := state.locals) state.heap owner address value
      dsimp only [WordEffects.transient] at physical
      rw [← write] at physical
      by_cases readOnly : state.heap.execution.context.readOnly = true
      · exact Or.inl (by simp [Machine.writeTarget,physical,Slot.write,readOnly])
      · let heap := {state.heap with execution := {state.heap.execution with
          world := state.heap.execution.world.tstore (owner.setWidth 256) address value}}
        refine Or.inr ⟨{state with heap},?_,state_withHeap stateRep (WordEffects.HeapRep.withWorld stateRep.heap _) rfl,rfl,rfl⟩
        simp [Machine.writeTarget,physical,Slot.write,readOnly,heap]
  | cell object member index inside =>
      have physical := WordEffects.write_cell (registry := registry) (fuel := fuel+1)
        (budget := state.materializationRemaining) (locals := state.locals)
        (stateRep.heap.arena.represented object member) inside value
      rw [← write] at physical
      let heap := MemoryOps.snapshotCopy state.heap (object.offset index) (wordBytes value)
      refine Or.inr ⟨{state with heap},?_,state_withHeap stateRep (WordEffects.HeapRep.store_cell stateRep.heap member inside value) rfl,rfl,rfl⟩
      simp [Machine.writeTarget,physical,heap]

/-- A represented captured write cannot yield a model-admission marker. The
only non-success is the actual persistent/transient read-only exception. -/
theorem writeTarget_total (backend : Backend Unit EmptyKey)
    (stateRep : StateRep program objects environment state)
    (target : TargetRep registry state.heap objects environment destination type)
    (sourceRep : ValueRep program state.heap objects source)
    (ready : TransferReady registry source.type type) (fuel : Nat) :
    Machine.writeTarget backend registry ⟨fuel+2,none⟩ state destination source = .error .exceptional ∨
    ∃ after,
      Machine.writeTarget backend registry ⟨fuel+2,none⟩ state destination source = .ok after ∧
      StateRep program objects environment after ∧ after.heap.invocation = state.heap.invocation ∧
      after.materializationRemaining = state.materializationRemaining := by
  cases target with
  | @«local» localId type bound typeReady =>
      obtain ⟨value,converted,valueRep,valueType⟩ := bind_total program registry fuel state.materializationRemaining
        state.heap objects source type ready stateRep.heap sourceRep
      obtain ⟨locals,written,represented⟩ := local_write_total stateRep bound valueRep valueType
      have current : state.locals.typeOf localId = .ok type := by
        have read := bound
        rw [← stateRep.shape,environment_find] at read
        cases selected : state.locals.find localId with
        | none => simp [selected] at read
        | some cell =>
            simp only [selected,Option.map_some,Option.some.injEq] at read
            simp [Execution.Locals.typeOf,selected,read]
      exact Or.inr ⟨{state with locals},by simp [Machine.writeTarget,Effects.writeCaptured,current,converted,written],represented,rfl,rfl⟩
  | heap physical => exact heap_write_total backend stateRep physical sourceRep ready fuel

theorem readTarget_total (backend : Backend Unit EmptyKey)
    (stateRep : StateRep program objects environment state)
    (target : TargetRep registry state.heap objects environment destination type) (fuel : Nat) :
    ∃ value,
      Machine.readTarget backend registry ⟨fuel+2,none⟩ state destination = .ok value ∧
      ValueRep program state.heap objects value ∧ value.type = type := by
  cases target with
  | «local» bound ready => exact SupportedReads.local_total stateRep bound ready
  | heap physical =>
      cases physical with
      | persistent owner address =>
          exact ⟨_,WordEffects.read_persistent (locals := state.locals) _ _ _,ValueRep.word _ _ _ _,rfl⟩
      | transient owner address =>
          exact ⟨_,WordEffects.read_transient (locals := state.locals) _ _ _,ValueRep.word _ _ _ _,rfl⟩
      | cell object member index inside =>
          exact ⟨_,WordEffects.read_cell (locals := state.locals) (stateRep.heap.arena.represented object member) inside,
            ValueRep.word _ _ _ _,rfl⟩

theorem scalar_transfer (ready : TransferReady registry source target) (scalar : target.scalarSupported = true) :
    source.scalarSupported = true ∧ Static.Implicit source target := by
  obtain ⟨sourceReady,targetReady,kind,rule⟩ := ready
  rcases transfer_classification sourceReady.1 targetReady.1 rule with scalar | ⟨_,_,_,rfl,_⟩
  · exact ⟨scalar.1,scalar.2.2.2⟩
  · cases scalar

theorem scalarCast_total (sourceRep : ValueRep program heap objects source)
    (ready : TransferReady registry source.type type) (scalar : type.scalarSupported = true) :
    ∃ value, Effects.scalarCast .implicit type source = .ok value ∧
      ValueRep program heap objects value ∧ value.type = type := by
  obtain ⟨supported,allowed⟩ := scalar_transfer ready scalar
  obtain ⟨value,converted⟩ := implicit_convert_total source.type type source.value supported scalar allowed
  exact ⟨⟨type,value⟩,scalar_cast_of_conversion converted,
    .scalar scalar (conversion_closed program source type value (scalar_closed sourceRep supported) allowed converted),rfl⟩

/-- Assignment results are actual readable represented values after a write.
Reference locals reload their new binding; scalar results perform the native
implicit conversion of the RHS. -/
theorem assignmentResult_total (stateRep : StateRep program objects environment state)
    (target : TargetRep registry state.heap objects environment destination type)
    (sourceRep : ValueRep program state.heap objects source)
    (ready : TransferReady registry source.type type) (fuel : Nat) :
    ∃ value, Machine.assignmentResult registry ⟨fuel+2,none⟩ state destination source = .ok value ∧
      ValueRep program state.heap objects value ∧ value.type = type := by
  cases target with
  | «local» bound typeReady =>
      rcases typeReady.1 with scalar | ⟨pointer,rfl⟩
      · obtain ⟨value,casted,represented,typeEq⟩ := scalarCast_total sourceRep ready scalar
        exact ⟨value,by simp [Machine.assignmentResult,Effects.assignmentResult,Captured.type,isReference,
          scalar_reference_none scalar,casted],represented,typeEq⟩
      · obtain ⟨value,read,represented,typeEq⟩ := SupportedReads.local_total stateRep bound typeReady
        exact ⟨value,by simpa only [Machine.assignmentResult,Effects.assignmentResult,WordArena.arrayType,
          isReference,referenceLocation,Option.isSome_some,↓reduceIte] using read,represented,typeEq⟩
  | heap physical =>
      obtain ⟨value,casted,represented,typeEq⟩ := scalarCast_total sourceRep ready rfl
      exact ⟨value,by simp [Machine.assignmentResult,Effects.assignmentResult,Captured.type,heapTarget_type physical,
        isReference,referenceLocation,casted],represented,typeEq⟩

end Solidity.Execution.Safety.TargetWrites
