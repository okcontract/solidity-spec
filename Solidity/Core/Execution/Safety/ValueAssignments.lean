/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.TargetSteps
import Solidity.Core.Execution.Safety.CallSetup

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem value_assignRight_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value target.type))
    (right : DatumRep program state.heap objects datum source)
    (targetCode : TargetCode registry program environment target)
    (ready : TransferReady registry source target.type) :
    StepRep registry program ⟨.value datum,.assignRight target none :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.assignRight target none :: stack,state,entry⟩) := by
  apply stepRep_next (after := ⟨.capture target,.commitValue datum none :: stack,state,entry⟩)
  · rfl
  · exact ⟨⟨context.closed,objects,environment,environment,.target target.type,context.stateRep,.capture targetCode,
      .cons (.commitValue right ready) context.continuation,context.checkpoint⟩⟩
  · rfl
  · dsimp; omega

theorem value_compoundRight_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value target.type))
    (right : DatumRep program state.heap objects datum source)
    (targetCode : TargetCode registry program environment target)
    (leftSupport : target.type.scalarSupported = true) (rightSupport : source.scalarSupported = true)
    (token : Frontend.Inference.compoundToken code = true)
    (allowed : Admission.BinaryAllowed code target.type source target.type) :
    StepRep registry program ⟨.value datum,.assignRight target (some code) :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.assignRight target (some code) :: stack,state,entry⟩) := by
  apply stepRep_next (after := ⟨.capture target,.commitValue datum (some code) :: stack,state,entry⟩)
  · rfl
  · exact ⟨⟨context.closed,objects,environment,environment,.target target.type,context.stateRep,.capture targetCode,
      .cons (.compoundValue right leftSupport rightSupport token allowed) context.continuation,context.checkpoint⟩⟩
  · rfl
  · dsimp; omega

theorem value_commit_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type)
    (right : DatumRep program state.heap objects datum source)
    (ready : TransferReady registry source type) :
    StepRep registry program ⟨.value datum,.commitTarget destination none :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.commitTarget destination none :: stack,state,entry⟩) := by
  apply primitive_step
  exact commit_plain_progress _ context target right ready

theorem value_compoundCommit_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type)
    (right : DatumRep program state.heap objects datum source)
    (leftSupport : type.scalarSupported = true) (rightSupport : source.scalarSupported = true)
    (token : Frontend.Inference.compoundToken code = true)
    (allowed : Admission.BinaryAllowed code type source type) :
    StepRep registry program ⟨.value datum,.commitTarget destination (some code) :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.commitTarget destination (some code) :: stack,state,entry⟩) := by
  apply primitive_step
  exact commit_compound_progress _ context target target.ready right leftSupport rightSupport token allowed

theorem value_commitOld_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type)
    (oldType : old.type = type)
    (right : DatumRep program state.heap objects datum source)
    (leftSupport : type.scalarSupported = true) (rightSupport : source.scalarSupported = true)
    (token : Frontend.Inference.compoundToken code = true)
    (allowed : Admission.BinaryAllowed code type source type) :
    StepRep registry program ⟨.value datum,.commitOld destination code old :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.commitOld destination code old :: stack,state,entry⟩) := by
  obtain ⟨right,rfl,rightType,_⟩ := right.atom_of_supported (.inl rightSupport)
  apply primitive_step
  simpa only [Machine.transition,token,Bool.not_true,Datum.asAtom,Bind.bind,Except.bind,Pure.pure,Except.pure] using
    compound_written_progress _ context target target.ready oldType rightType leftSupport rightSupport allowed

theorem ArgumentsReady.single (ready : ArgumentsReady registry sources [target]) :
    ∃ source,sources = [source] ∧ TransferReady registry source target := by
  cases ready with
  | cons first rest => cases rest;exact ⟨_,rfl,first⟩

theorem PacketRep.single {types : SType} (represented : PacketRep program heap objects values (.cons types .nil)) :
    ∃ datum,values = [datum] ∧ DatumRep program heap objects datum types := by
  cases represented with
  | cons first rest => cases rest;exact ⟨_,rfl,first⟩

/-- Initialized declarations admit exactly one component in this profile. The
actual temporary unset cell is filled by the existing argument/local transfer. -/
theorem value_declare_progress
    (closed : Profile.ClosedProgram registry program)
    (stateRep : StateRep program objects environment state)
    (right : DatumRep program state.heap objects datum source)
    (allowed : ReturnReady registry source [binder])
    (fresh : Environment.find environment binder.id = none)
    (continuation : StackRep registry program state.heap objects (Environment.declare environment binder) .nextOnly stack)
    (checkpoint : ∃ entryObjects entryEnvironment,StateRep program entryObjects entryEnvironment entry) :
    StepRep registry program ⟨.value datum,.declare [some binder] :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.value datum,.declare [some binder] :: stack,state,entry⟩) := by
  obtain ⟨source,sourceTypes,ready⟩ := ArgumentsReady.single allowed
  have packet := right.asPacket_typed
  rw [sourceTypes] at packet
  obtain ⟨component,packetEq,componentRep⟩ := PacketRep.single packet
  obtain ⟨value,rfl,valueType,valueRep⟩ := componentRep.atom_of_supported ready.1.1
  have ready' : TransferReady registry value.type binder.type := by rw [valueType];exact ready
  have absent := fresh
  rw [← stateRep.shape,environment_find] at absent
  have noCell : state.locals.find binder.id = none := by
    cases selected : state.locals.find binder.id <;> simp_all
  cases localsEq : state.locals with
  | nil => exact False.elim (stateRep.nonempty localsEq)
  | cons scope outer =>
      obtain ⟨converted,written,cells⟩ := CallSetup.declare_write_total physicalBackend program registry fuel
        state objects scope outer binder value localsEq noCell ready' stateRep.heap stateRep.cells valueRep
      let after : MachineState Unit := {state with locals := ((binder.id,⟨binder.type,some converted⟩)::scope)::outer}
      have shape : Safety.Locals.environment after.locals = Environment.declare environment binder := by
        rw [← stateRep.shape,localsEq]
        rfl
      have represented : StateRep program objects (Environment.declare environment binder) after :=
        ⟨stateRep.heap,cells,shape,by simp [after]⟩
      apply stepRep_next (after := ⟨.resume .next,stack,after,entry⟩)
      · apply step_of_transition
        have declarations : Machine.declareValues physicalBackend registry ⟨fuel+2,none⟩ state
            [some binder] [.atom value] = .ok after := by
          cases entered : Machine.declareUnset state binder with
          | error failure => simp [entered] at written
          | ok middle =>
              cases stored : Machine.writeTarget physicalBackend registry ⟨fuel+2,none⟩ middle
                  (.captured (.local binder.id binder.type)) value with
              | error failure => simp [entered,stored] at written
              | ok final => simpa [Machine.declareValues,Datum.asAtom,entered,stored,after] using written
        simp [Machine.transition,packetEq,declarations,Machine.next]
      · exact ⟨⟨closed,objects,Environment.declare environment binder,Environment.declare environment binder,
          .nextOnly,represented,.next,continuation,checkpoint⟩⟩
      · rfl
      · dsimp [after];omega

end Solidity.Execution.Safety
