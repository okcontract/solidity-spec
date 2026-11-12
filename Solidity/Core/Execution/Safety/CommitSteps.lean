/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.PrimitiveSteps
import Solidity.Core.Execution.Safety.TargetWrites
import Solidity.Core.Execution.Safety.ScalarRepresentation

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem TargetRep.ready {heap : Heap} (represented : TargetRep registry heap objects environment target type) : TypeReady registry type := by
  cases represented with
  | «local» _ ready => exact ready
  | heap _ => exact ⟨.inl rfl,rfl⟩

/-- The post-conversion store and actual assignment-result readback. -/
theorem written_value_progress (config : Config Unit EmptyKey)
    (context : EvaluationContext registry program objects environment config.state config.entry stack (.value type))
    (target : TargetRep registry config.state.heap objects environment destination type)
    (source : ValueRep program config.state.heap objects value)
    (ready : TransferReady registry value.type type) :
    PrimitiveRep registry program config (do
      let state ← Machine.writeTarget physicalBackend registry ⟨fuel+2,none⟩ config.state destination value
      let value ← Machine.assignmentResult registry ⟨fuel+2,none⟩ state destination value
      Machine.next config (.value (.atom value)) state stack) := by
  rcases TargetWrites.writeTarget_total physicalBackend context.stateRep target source ready fuel with
    failed | ⟨after,written,stateRep,invocation,budget⟩
  · simp only [failed,Bind.bind,Except.bind,PrimitiveRep]
    rfl
  · have targetAfter := target.extend invocation (fun _ member => member)
    have sourceAfter := source.extend invocation (fun _ member => member)
    obtain ⟨result,readback,represented,typeEq⟩ := TargetWrites.assignmentResult_total
      (fuel := fuel) stateRep targetAfter sourceAfter ready
    simp only [written,Bind.bind,Except.bind,readback,Machine.next,PrimitiveRep,StepRep]
    refine ⟨(context.replace_state stateRep invocation).value ?_,by trivial,?_⟩
    · simpa only [typeEq] using (DatumRep.atom represented)
    · dsimp; omega

theorem commit_plain_progress (config : Config Unit EmptyKey)
    (context : EvaluationContext registry program objects environment config.state config.entry stack (.value type))
    (target : TargetRep registry config.state.heap objects environment destination type)
    (right : DatumRep program config.state.heap objects datum source)
    (ready : TransferReady registry source type) :
    PrimitiveRep registry program config
      (Machine.commit physicalBackend registry ⟨fuel+2,none⟩ config destination datum none stack) := by
  obtain ⟨value,rfl,typeEq,represented⟩ := right.atom_of_supported ready.1.1
  have ready' : TransferReady registry value.type type := by rw [typeEq]; exact ready
  simpa only [Machine.commit,Datum.asAtom,Bind.bind,Except.bind,Pure.pure,Except.pure] using
    written_value_progress config context target represented ready'

/-- Arithmetic can fail before the store. The successful branch uses the
actual converted result and physical store/frame contract. -/
theorem compound_written_progress (config : Config Unit EmptyKey)
    (context : EvaluationContext registry program objects environment config.state config.entry stack (.value type))
    (target : TargetRep registry config.state.heap objects environment destination type)
    (typeReady : TypeReady registry type)
    (oldType : old.type = type) (rightType : right.type = source)
    (leftSupported : type.scalarSupported = true) (rightSupported : source.scalarSupported = true)
    (allowed : Admission.BinaryAllowed code type source type) :
    PrimitiveRep registry program config (do
      let written ← Effects.binary config.state.mode code old right
      let state ← Machine.writeTarget physicalBackend registry ⟨fuel+2,none⟩ config.state destination written
      let value ← Machine.assignmentResult registry ⟨fuel+2,none⟩ state destination written
      Machine.next config (.value (.atom value)) state stack) := by
  have permission : Admission.BinaryAllowed code old.type right.type type := by rw [oldType,rightType]; exact allowed
  rcases ScalarRepresentation.binary_progress (program := program) (heap := config.state.heap) (objects := objects)
      config.state.mode code old right permission (by rw [oldType];exact leftSupported)
        (by rw [rightType];exact rightSupported) with
    ⟨written,computed,typeEq,represented⟩ | ⟨failure,failed,sourceFailure⟩
  · simp only [computed,Bind.bind,Except.bind]
    have ready : TransferReady registry written.type type := by rw [typeEq];exact SupportedTransfers.self_ready typeReady
    exact written_value_progress config context target represented ready
  · simpa only [failed,Bind.bind,Except.bind,PrimitiveRep] using sourceFailure

theorem commit_compound_progress (config : Config Unit EmptyKey)
    (context : EvaluationContext registry program objects environment config.state config.entry stack (.value type))
    (target : TargetRep registry config.state.heap objects environment destination type)
    (typeReady : TypeReady registry type)
    (right : DatumRep program config.state.heap objects datum source)
    (leftSupported : type.scalarSupported = true) (rightSupported : source.scalarSupported = true)
    (token : Frontend.Inference.compoundToken code = true)
    (allowed : Admission.BinaryAllowed code type source type) :
    PrimitiveRep registry program config
      (Machine.commit physicalBackend registry ⟨fuel+2,none⟩ config destination datum (some code) stack) := by
  obtain ⟨right,rfl,rightType,rightRep⟩ := right.atom_of_supported (.inl rightSupported)
  obtain ⟨old,read,oldRep,oldType⟩ := TargetWrites.readTarget_total physicalBackend context.stateRep target fuel
  simpa only [Machine.commit,Datum.asAtom,token,Bool.not_true,read,Bind.bind,Except.bind,Pure.pure,Except.pure] using
    compound_written_progress config context target typeReady oldType rightType leftSupported rightSupported allowed

end Solidity.Execution.Safety
