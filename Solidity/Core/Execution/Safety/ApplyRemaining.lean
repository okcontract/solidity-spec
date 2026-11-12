/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ApplySteps
import Solidity.Core.Execution.Safety.TargetWrites

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

/-- Only internal dispatch is excluded here; it has its own call-frame proof. -/
def NoncallCompletion (completion : Completion) : Prop :=
  (∀ signature, completion ≠ .call signature) ∧
    (∀ signature order, completion ≠ .namedCall signature order)

private theorem scalar_convert_progress
    (sourceRep : ValueRep program heap objects source)
    (sourceSupport : source.type.scalarSupported = true) (targetSupport : target.scalarSupported = true)
    (sourceFormed : Static.wellFormed registry source.type = true)
    (targetFormed : Static.wellFormed registry target = true)
    (physical : HeapRep heap objects) (allowed : Static.Allowed mode source.type target) :
    (∃ value, Effects.convert registry (fuel+2) budget heap mode target source = .ok (value,heap,budget) ∧
      value.type = target ∧ ValueRep program heap objects value) ∨
    (∃ failure, Effects.convert registry (fuel+2) budget heap mode target source = .error failure ∧
      isSourceFailure failure = true) := by
  cases mode with
  | implicit =>
      have permission : TransferRule true source.type target .scalarConversion :=
        ⟨SupportedTransfers.scalar_reference_none sourceSupport,
          SupportedTransfers.scalar_reference_none targetSupport,allowed⟩
      obtain ⟨value,converted,represented,typed⟩ := SupportedTransfers.bind_total program registry fuel budget heap objects
        source target ⟨⟨.inl sourceSupport,sourceFormed⟩,⟨.inl targetSupport,targetFormed⟩,.scalarConversion,permission⟩
        physical sourceRep
      exact .inl ⟨value,converted,typed,represented⟩
  | explicit kind =>
      have noReference := SupportedReads.scalar_reference_none sourceSupport
      rcases ScalarRepresentation.cast_progress (.explicit kind) target source sourceRep sourceSupport targetSupport allowed with
        ⟨value,converted,typed,represented⟩ | ⟨failure,failed,isSource⟩
      · refine .inl ⟨value,?_,typed,represented⟩
        cases kind <;> simp [Effects.convert,noReference,converted]
      · refine .inr ⟨failure,?_,isSource⟩
        cases kind <;> simp [Effects.convert,noReference,failed]

theorem apply_cast_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value target))
    (sourceRep : ValueRep program state.heap objects source)
    (sourceSupport : source.type.scalarSupported = true) (targetSupport : target.scalarSupported = true)
    (allowed : Static.Allowed mode source.type target)
    (sourceFormed : Static.wellFormed registry source.type = true)
    (targetFormed : Static.wellFormed registry target = true) :
    StepRep registry program ⟨.apply (.cast mode target) [.atom source],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.cast mode target) [.atom source],stack,state,entry⟩) := by
  rcases scalar_convert_progress (fuel := fuel) (budget := state.materializationRemaining)
      sourceRep sourceSupport targetSupport sourceFormed targetFormed
      context.stateRep.heap allowed with ⟨value,converted,typed,represented⟩ | ⟨failure,failed,isSource⟩
  · apply stepRep_next (after := ⟨.value (.atom value),stack,state,entry⟩)
    · apply step_of_transition
      simp [Machine.transition,Machine.apply,PacketTransfers.transfer,converted,Machine.next]
    · exact context.value (by simpa only [typed] using (DatumRep.atom represented))
    · rfl
    · simp
  · apply stepRep_source (failure := failure) _ isSource
    simp [Machine.transition,Machine.apply,PacketTransfers.transfer,failed]

theorem apply_assert_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.tuple .nil)))
    (condition : Bool) :
    StepRep registry program ⟨.apply .assert_ [.atom ⟨.bool,condition⟩],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply .assert_ [.atom ⟨.bool,condition⟩],stack,state,entry⟩) := by
  cases condition with
  | false =>
      apply stepRep_source (failure := .panic 0x01) _ rfl
      rfl
  | true => exact stepRep_next rfl (context.value (.tuple .nil)) rfl (by simp)

theorem apply_require_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.tuple .nil)))
    (condition : Bool) :
    StepRep registry program ⟨.apply (.require_ .empty) [.atom ⟨.bool,condition⟩],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.require_ .empty) [.atom ⟨.bool,condition⟩],stack,state,entry⟩) := by
  cases condition with
  | false =>
      apply stepRep_source (failure := .revert []) _ rfl
      rfl
  | true => exact stepRep_next rfl (context.value (.tuple .nil)) rfl (by simp)

theorem apply_revert_progress :
    StepRep registry program ⟨.apply (.revertWith .empty) [],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.revertWith .empty) [],stack,state,entry⟩) := by
  apply stepRep_source (failure := .revert []) _ rfl
  rfl

private theorem capture_index_eq (heap : Heap) (reference : Reference) (pointer : Bool)
    {width : Core.Width} (index : BitVec width.bits) :
    Effects.captureIndex registry fuel heap ⟨WordArena.arrayType pointer,reference⟩ ⟨.uint width,index⟩ =
      (Effects.index registry fuel heap ⟨WordArena.arrayType pointer,reference⟩ ⟨.uint width,index⟩).map Captured.heap := by
  simp [Effects.captureIndex,Effects.index,Effects.indexNumber,Effects.unsignedNat,Defaults.asPlace,
    Value.reference,WordArena.arrayType,Except.map]

private theorem index_total {width : Core.Width} (index : BitVec width.bits)
    (physical : HeapRep heap objects)
    (source : ValueRep program heap objects ⟨WordArena.arrayType pointer,reference⟩) :
    (∃ place, Effects.index registry (fuel+2) heap ⟨WordArena.arrayType pointer,reference⟩ ⟨.uint width,index⟩ =
      .ok place ∧ HeapTargetRep heap objects place) ∨
    Effects.index registry (fuel+2) heap ⟨WordArena.arrayType pointer,reference⟩ ⟨.uint width,index⟩ =
      .error (.panic 0x32) := by
  cases source with
  | scalar support _ => simp [WordArena.arrayType,SType.scalarSupported] at support
  | array _ object member =>
      have represented := physical.arena.represented object member
      by_cases inside : index.toNat < object.length
      · exact .inl ⟨object.cell heap index.toNat,WordEffects.index_inside represented inside pointer,
          .cell object member index.toNat inside⟩
      · exact .inr (WordEffects.index_outside represented (Nat.le_of_not_gt inside) pointer)
  | emptyArray _ => exact .inr (WordEffects.index_outside physical.empty (Nat.zero_le _) pointer)

theorem apply_index_progress {width : Core.Width} (index : BitVec width.bits)
    (context : EvaluationContext registry program objects environment state entry stack (.target (.uint 31)))
    (source : ValueRep program state.heap objects ⟨WordArena.arrayType pointer,reference⟩) :
    StepRep registry program
      ⟨.apply (.index (.uint 31)) [.atom ⟨WordArena.arrayType pointer,reference⟩,.atom ⟨.uint width,index⟩],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.index (.uint 31)) [.atom ⟨WordArena.arrayType pointer,reference⟩,.atom ⟨.uint width,index⟩],stack,state,entry⟩) := by
  rcases index_total (registry := registry) (fuel := fuel) index context.stateRep.heap source with
    ⟨place,indexed,represented⟩ | failed
  · apply stepRep_next (after := ⟨.target (.captured (.heap place)),stack,state,entry⟩)
    · apply step_of_transition
      simp [Machine.transition,Machine.apply,Datum.asAtom,indexed,Machine.checkedTarget,
        TargetWrites.heapTarget_type represented,Machine.next]
    · exact context.configuration (.target (.heap represented))
    · rfl
    · simp
  · apply stepRep_source (failure := .panic 0x32) _ rfl
    simp [Machine.transition,Machine.apply,Datum.asAtom,failed]

theorem apply_readIndex_progress {width : Core.Width} (index : BitVec width.bits)
    (context : EvaluationContext registry program objects environment state entry stack (.value (.uint 31)))
    (source : ValueRep program state.heap objects ⟨WordArena.arrayType pointer,reference⟩) :
    StepRep registry program
      ⟨.apply (.readIndex (.uint 31)) [.atom ⟨WordArena.arrayType pointer,reference⟩,.atom ⟨.uint width,index⟩],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.readIndex (.uint 31)) [.atom ⟨WordArena.arrayType pointer,reference⟩,.atom ⟨.uint width,index⟩],stack,state,entry⟩) := by
  have captured := capture_index_eq (registry := registry) (fuel := fuel+2) state.heap reference pointer index
  rcases index_total (registry := registry) (fuel := fuel) index context.stateRep.heap source with
    ⟨place,indexed,represented⟩ | failed
  · obtain ⟨value,read,valueRep,typed⟩ := TargetWrites.readTarget_total physicalBackend context.stateRep
      (TargetRep.heap (registry := registry) (environment := environment) represented) (fuel := fuel)
    change Effects.readCaptured registry (fuel+2) state.locals state.heap (.heap place) = .ok value at read
    rw [indexed] at captured
    simp only [Except.map] at captured
    have computed : Effects.readIndex registry (fuel+2) state.locals state.heap
        ⟨WordArena.arrayType pointer,reference⟩ ⟨.uint width,index⟩ = .ok value := by
      change (do
        let _ ← Effects.indexNumber ⟨.uint width,index⟩
        Effects.readCaptured registry (fuel+2) state.locals state.heap
          (← Effects.captureIndex registry (fuel+2) state.heap
            ⟨WordArena.arrayType pointer,reference⟩ ⟨.uint width,index⟩)) = .ok value
      simp [Effects.indexNumber,captured,read]
    apply stepRep_next (after := ⟨.value (.atom value),stack,state,entry⟩)
    · apply step_of_transition
      simp [Machine.transition,Machine.apply,Datum.asAtom,computed,Machine.typed,Datum.type,typed,Machine.next]
    · exact context.value (by simpa only [typed] using DatumRep.atom valueRep)
    · rfl
    · simp
  · rw [failed] at captured
    simp only [Except.map] at captured
    have failed : Effects.readIndex registry (fuel+2) state.locals state.heap
        ⟨WordArena.arrayType pointer,reference⟩ ⟨.uint width,index⟩ = .error (.panic 0x32) := by
      change (do
        let _ ← Effects.indexNumber ⟨.uint width,index⟩
        Effects.readCaptured registry (fuel+2) state.locals state.heap
          (← Effects.captureIndex registry (fuel+2) state.heap
            ⟨WordArena.arrayType pointer,reference⟩ ⟨.uint width,index⟩)) = .error (.panic 0x32)
      simp [Effects.indexNumber,captured]
    apply stepRep_source (failure := .panic 0x32) _ rfl
    simp [Machine.transition,Machine.apply,Datum.asAtom,failed]

private theorem typed_atom {type : SType} (represented : DatumRep program heap objects datum type)
    (supported : Supported type) :
    ∃ value : type.Value, datum = .atom ⟨type,value⟩ ∧ ValueRep program heap objects ⟨type,value⟩ := by
  obtain ⟨⟨actual,value⟩,rfl,same,represented⟩ := represented.atom_of_supported supported
  dsimp only at same
  subst actual
  exact ⟨value,rfl,represented⟩

/-- Every represented completion except internal dispatch advances or produces
an actual source failure. The only potentially materializing case is new-array
construction, bounded explicitly by the one-step resource allowance. -/
theorem apply_noncall_progress
    (context : EvaluationContext registry program objects environment state entry stack kind)
    (packet : PacketRep program state.heap objects values (Types.ofList types))
    (completion : CompletionRep registry finish types kind)
    (noncall : NoncallCompletion finish)
    (budget : materializationStepBound ≤ state.materializationRemaining) :
    StepRep registry program ⟨.apply finish values,stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply finish values,stack,state,entry⟩) := by
  cases completion with
  | tuple types => exact apply_tuple_progress context packet
  | unary supported allowed =>
      cases packet with
      | cons head rest =>
          cases rest
          obtain ⟨value,rfl,_⟩ := typed_atom head (.inl supported)
          exact apply_unary_progress context rfl allowed
  | binary leftSupport rightSupport _ allowed =>
      cases packet with
      | cons left rest =>
          cases rest with
          | cons right rest =>
              cases rest
              obtain ⟨a,rfl,_⟩ := typed_atom left (.inl leftSupport)
              obtain ⟨b,rfl,_⟩ := typed_atom right (.inl rightSupport)
              exact apply_binary_progress context leftSupport rightSupport allowed
  | cast sourceSupport targetSupport allowed sourceFormed targetFormed =>
      cases packet with
      | cons head rest =>
          cases rest
          obtain ⟨value,rfl,represented⟩ := typed_atom head (.inl sourceSupport)
          exact apply_cast_progress context represented sourceSupport targetSupport allowed sourceFormed targetFormed
  | call _ _ _ => exact False.elim (noncall.1 _ rfl)
  | namedCall _ _ _ _ => exact False.elim (noncall.2 _ _ rfl)
  | length pointer =>
      cases packet with
      | cons head rest =>
          cases rest
          obtain ⟨reference,rfl,represented⟩ := typed_atom head (.inr ⟨pointer,rfl⟩)
          exact apply_length_progress context represented
  | index pointer width =>
      cases packet with
      | cons source rest =>
          cases rest with
          | cons index rest =>
              cases rest
              obtain ⟨reference,rfl,represented⟩ := typed_atom source (.inr ⟨pointer,rfl⟩)
              obtain ⟨offset,rfl,_⟩ := typed_atom index (.inl rfl)
              exact apply_index_progress offset context represented
  | readIndex pointer width =>
      cases packet with
      | cons source rest =>
          cases rest with
          | cons index rest =>
              cases rest
              obtain ⟨reference,rfl,represented⟩ := typed_atom source (.inr ⟨pointer,rfl⟩)
              obtain ⟨offset,rfl,_⟩ := typed_atom index (.inl rfl)
              exact apply_readIndex_progress offset context represented
  | newArray width =>
      cases packet with
      | cons head rest =>
          cases rest
          obtain ⟨count,rfl,_⟩ := typed_atom head (.inl rfl)
          exact apply_newArray_progress count context budget
  | assert_ =>
      cases packet with
      | cons head rest =>
          cases rest
          obtain ⟨condition,rfl,_⟩ := typed_atom head (.inl rfl)
          exact apply_assert_progress context condition
  | require_ =>
      cases packet with
      | cons head rest =>
          cases rest
          obtain ⟨condition,rfl,_⟩ := typed_atom head (.inl rfl)
          exact apply_require_progress context condition
  | revertWith => cases packet; exact apply_revert_progress

end Solidity.Execution.Safety
