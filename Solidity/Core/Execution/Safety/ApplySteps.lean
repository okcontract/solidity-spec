/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.StepLaws
import Solidity.Core.Execution.Safety.ScalarRepresentation
import Solidity.Core.Execution.Safety.SupportedTransfers
import Solidity.Core.Execution.Safety.WordEffects

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem apply_tuple_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.tuple types)))
    (valuesRep : PacketRep program state.heap objects values types) :
    StepRep registry program ⟨.apply .tuple values,stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice ⟨.apply .tuple values,stack,state,entry⟩) := by
  apply stepRep_next (after := ⟨.value (.tuple values),stack,state,entry⟩)
  · rfl
  · exact context.value (.tuple valuesRep)
  · rfl
  · dsimp; omega

theorem apply_unary_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (same : value.type = type)
    (allowed : (checkUnary code type).isSome = true) :
    StepRep registry program ⟨.apply (.unary code) [.atom value],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.unary code) [.atom value],stack,state,entry⟩) := by
  have permitted : (checkUnary code value.type).isSome = true := by rw [same]; exact allowed
  rcases ScalarRepresentation.unary_checked_progress (program := program) (heap := state.heap) (objects := objects)
      state.mode code value permitted with
    ⟨result,computed,typed,represented⟩ | ⟨failure,failed,isSource⟩
  · apply stepRep_next (after := ⟨.value (.atom result),stack,state,entry⟩)
    · apply step_of_transition
      simp [Machine.transition,Machine.apply,Datum.asAtom,computed,Machine.next]
    · exact context.value (by simpa only [typed,same] using (DatumRep.atom represented))
    · rfl
    · dsimp; omega
  · apply stepRep_source (failure := failure) _ isSource
    simp [Machine.transition,Machine.apply,Datum.asAtom,failed]

theorem apply_binary_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value resultType))
    (leftSupport : left.type.scalarSupported = true) (rightSupport : right.type.scalarSupported = true)
    (allowed : Admission.BinaryAllowed code left.type right.type resultType) :
    StepRep registry program ⟨.apply (.binary code resultType) [.atom left,.atom right],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.binary code resultType) [.atom left,.atom right],stack,state,entry⟩) := by
  rcases ScalarRepresentation.binary_progress (program := program) (heap := state.heap) (objects := objects)
      state.mode code left right allowed leftSupport rightSupport with
    ⟨result,computed,typed,represented⟩ | ⟨failure,failed,isSource⟩
  · apply stepRep_next (after := ⟨.value (.atom result),stack,state,entry⟩)
    · apply step_of_transition
      simp [Machine.transition,Machine.apply,Datum.asAtom,computed,Machine.typed,Datum.type,typed,Machine.next]
    · exact context.value (by simpa only [typed] using (DatumRep.atom represented))
    · rfl
    · dsimp; omega
  · apply stepRep_source (failure := failure) _ isSource
    simp [Machine.transition,Machine.apply,Datum.asAtom,failed]

theorem apply_length_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value (.uint 31)))
    (source : ValueRep program state.heap objects ⟨WordArena.arrayType pointer,reference⟩) :
    StepRep registry program ⟨.apply .length [.atom ⟨WordArena.arrayType pointer,reference⟩],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply .length [.atom ⟨WordArena.arrayType pointer,reference⟩],stack,state,entry⟩) := by
  obtain ⟨object,represented,rfl⟩ := source.array_object context.stateRep.heap
  have length := WordEffects.length (registry := registry) (fuel := fuel+2) represented pointer
  apply stepRep_next (after := ⟨.value (.atom ⟨.uint 31,BitVec.ofNat 256 object.length⟩),stack,state,entry⟩)
  · apply step_of_transition
    simp [Machine.transition,Machine.apply,Datum.asAtom,length,Machine.next]
  · exact context.value (.atom (ValueRep.word _ _ _ _))
  · rfl
  · dsimp; omega

theorem apply_newArray_progress {width : Core.Width} (count : BitVec width.bits)
    (context : EvaluationContext registry program objects environment state entry stack (.value (WordArena.arrayType true)))
    (budget : materializationStepBound ≤ state.materializationRemaining) :
    StepRep registry program ⟨.apply (.newArray (.uint 31)) [.atom ⟨.uint width,count⟩],stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.newArray (.uint 31)) [.atom ⟨.uint width,count⟩],stack,state,entry⟩) := by
  have countCost := unsigned_cost_bound count
  have enough : WordArrayResources.cost count.toNat ≤ state.materializationRemaining := Nat.le_trans countCost budget
  rcases WordArrayResources.newArray_total registry fuel state.materializationRemaining count.toNat state.heap objects
      context.stateRep.heap enough with failed | ⟨heap,allocated,physical,world,invocation,frame⟩
  · apply stepRep_source (failure := .panic 0x41) _ rfl
    simp [Machine.transition,Machine.apply,Datum.asAtom,Effects.newArray,Effects.unsignedNat,Effects.indexNumber,failed]
  · let newObjects := WordArrayResources.freshObject state.heap count.toNat :: objects
    let afterState := {state with heap,materializationRemaining := state.materializationRemaining-WordArrayResources.cost count.toNat}
    let result : Value := ⟨WordArena.arrayType true,(WordArrayResources.freshObject state.heap count.toNat).reference heap⟩
    have members : ∀ object ∈ objects, object ∈ newObjects := fun _ member => List.mem_cons_of_mem _ member
    have nextContext := context.extend_heap physical invocation members afterState.materializationRemaining
    apply stepRep_next (after := ⟨.value (.atom result),stack,afterState,entry⟩)
    · apply step_of_transition
      simp [Machine.transition,Machine.apply,Datum.asAtom,Effects.newArray,Effects.unsignedNat,Effects.indexNumber,
        allocated,Machine.next,afterState,result]
    · exact nextContext.value (.atom (.array true _ (by simp)))
    · rfl
    · dsimp only [afterState]
      omega

end Solidity.Execution.Safety
