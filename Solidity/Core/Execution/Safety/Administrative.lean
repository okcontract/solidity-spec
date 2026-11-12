/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ConfigurationLaws

/-! Preservation of the actual eager collector and its typed continuations.
Selected children may mutate aliased memory or enter source calls: the packet
invariant concerns positions/types and represented completed values, never a
fixed operand order or a pure-expression restriction. -/
namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def ObservationRep (program : Program EmptyKey) (entry : MachineState Unit) : Observation Unit → Prop
  | .returned values state => ∃ objects environment types,
      StateRep program objects environment state ∧ PacketRep program state.heap objects values types
  | .failed failure state => isSourceFailure failure = true ∧ state = entry
  | .inconclusive _ _ | .resourceLimit _ _ => False

theorem DatumRep.asPacket {type : SType} (represented : DatumRep program heap objects datum type) :
    ∃ types, PacketRep program heap objects datum.asPacket types := by
  cases represented with
  | atom value => exact ⟨.cons _ .nil,.cons (.atom value) .nil⟩
  | tuple members => exact ⟨_,members⟩

theorem pick_none (empty : Machine.pick choice pending = none) : pending = [] := by
  cases pending with
  | nil => rfl
  | cons head tail =>
      have bound : choice % (head :: tail).length < (head :: tail).length :=
        Nat.mod_lt _ (by simp)
      simp only [Machine.pick,List.splitAt_eq] at empty
      rw [List.drop_eq_getElem_cons bound] at empty
      cases empty

theorem step_of_transition (transition : Machine.transition physicalBackend registry
    ⟨fuel,none⟩ program choice config = .ok (.next after)) :
    Machine.step physicalBackend registry ⟨fuel,none⟩ program choice config = .next after := by
  simp [Machine.step,transition]

theorem collector_progress (closed : Profile.ClosedProgram registry program)
    (stateRep : StateRep program objects environment state)
    (packet : TypedPackets.CollectRep program state.heap objects (ExprRep registry program environment)
      types pending completed)
    (operation : CompletionRep registry completion types kind)
    (continuation : StackRep registry program state.heap objects environment kind stack)
    (checkpoint : ∃ entryObjects entryEnvironment, StateRep program entryObjects entryEnvironment entry) :
    ∃ after,
      Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
        ⟨.collect pending completed completion,stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  cases selected : Machine.pick choice pending with
  | none =>
      have empty := pick_none selected
      subst pending
      let after : Config Unit EmptyKey := ⟨.apply completion (Machine.ordered completed),stack,state,entry⟩
      refine ⟨after,step_of_transition ?_,?_,rfl⟩
      · simp [Machine.transition,selected,Machine.next,after]
      · exact ⟨⟨closed,objects,environment,environment,kind,stateRep,
          .apply packet.finish operation,continuation,checkpoint⟩⟩
  | some chosen =>
      rcases chosen with ⟨⟨index,expression⟩,rest⟩
      obtain ⟨child,_,active⟩ := packet.pick selected
      let after : Config Unit EmptyKey :=
        ⟨.eval expression,.collect index rest completed completion :: stack,state,entry⟩
      refine ⟨after,step_of_transition ?_,?_,rfl⟩
      · simp [Machine.transition,selected,Machine.next,after]
      · exact ⟨⟨closed,objects,environment,environment,.value expression.type,stateRep,
          .eval child,.cons (.collect active operation) continuation,checkpoint⟩⟩

theorem collected_value_progress (closed : Profile.ClosedProgram registry program)
    (stateRep : StateRep program objects environment state)
    (value : DatumRep program state.heap objects datum expected)
    (packet : TypedPackets.ActiveRep program state.heap objects (ExprRep registry program environment)
      types index expected pending completed)
    (operation : CompletionRep registry completion types kind)
    (continuation : StackRep registry program state.heap objects environment kind stack)
    (checkpoint : ∃ entryObjects entryEnvironment, StateRep program entryObjects entryEnvironment entry) :
    ∃ after,
      Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
        ⟨.value datum,.collect index pending completed completion :: stack,state,entry⟩ = .next after ∧
      ConfigurationRep registry program after ∧ after.state = state := by
  let after : Config Unit EmptyKey := ⟨.collect pending ((index,datum) :: completed) completion,stack,state,entry⟩
  refine ⟨after,step_of_transition ?_,?_,rfl⟩
  · rfl
  · exact ⟨⟨closed,objects,environment,environment,kind,stateRep,
      .collect (packet.complete value) operation,continuation,checkpoint⟩⟩

theorem returned_value_progress (stateRep : StateRep program objects environment state)
    (value : DatumRep program state.heap objects datum expected) :
    Machine.step physicalBackend registry ⟨fuel,none⟩ program choice
      ⟨.value datum,[],state,entry⟩ = .done (.returned datum.asPacket state) ∧
      ObservationRep program entry (.returned datum.asPacket state) := by
  obtain ⟨types,packet⟩ := value.asPacket
  exact ⟨rfl,objects,environment,types,stateRep,packet⟩

theorem source_failure_progress {failure : Failure} (failed : Machine.transition physicalBackend registry ⟨fuel,none⟩ program
    choice config = .error failure) (source : isSourceFailure failure = true) :
    Machine.step physicalBackend registry ⟨fuel,none⟩ program choice config = .done (fail config.entry failure) ∧
      ObservationRep program config.entry (fail config.entry failure) := by
  constructor
  · cases failure <;> simp_all [Machine.step,isSourceFailure]
  · exact ⟨source,rfl⟩

end Solidity.Execution.Safety
