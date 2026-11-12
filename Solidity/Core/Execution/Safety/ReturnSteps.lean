/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.StepLaws
import Solidity.Core.Execution.Safety.CallSetup

/-! Actual return collection and continuation transfer. Named results are read
from represented initialized cells; explicit returns enqueue the real ordered
write list. Caller restoration keeps the current shared heap and host budget. -/
namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem return_cell_value {localId : LocalId}
    (represented : StateRep program objects environment state)
    (bound : Environment.find environment localId = some type) :
    ∃ data : type.Value, state.locals.read localId type = .ok ⟨type,data⟩ ∧
      ValueRep program state.heap objects ⟨type,data⟩ := by
  rw [← represented.shape,environment_find] at bound
  cases selected : state.locals.find localId with
  | none => simp [selected] at bound
  | some cell =>
      simp only [selected,Option.map_some,Option.some.injEq] at bound
      cases bound
      obtain ⟨data,initialized,valueRep⟩ := represented.cells.find selected
      exact ⟨data,by simp [Execution.Locals.read,selected,initialized],valueRep⟩

theorem collectResults_total (represented : StateRep program objects environment state)
    (returnCells : ∀ binder ∈ returns,Environment.find environment binder.id = some binder.type) :
    ∃ values, Machine.collectResults state.locals returns = .ok values ∧
      PacketRep program state.heap objects values (Types.ofList (returns.map Binder.type)) := by
  induction returns with
  | nil => exact ⟨[],rfl,.nil⟩
  | cons binder returns ih =>
      obtain ⟨data,read,rep⟩ := return_cell_value represented (returnCells binder (by simp))
      obtain ⟨values,collected,packet⟩ := ih (fun next member => returnCells next (by simp [member]))
      refine ⟨.atom ⟨binder.type,data⟩ :: values,?_,.cons (.atom rep) packet⟩
      simpa only [Machine.collectResults,List.mapM_cons,read,Bind.bind,Except.bind,Pure.pure,Except.pure] using
        congrArg (fun result : Aggregates.Result Packet => result.map (.atom ⟨binder.type,data⟩ :: ·)) collected

theorem return_packet_type (returns : List Binder) :
    packetResultType (Types.ofList (returns.map Binder.type)) = Control.resultType ⟨returns,false⟩ := by
  cases returns with
  | nil => rfl
  | cons binder returns => cases returns <;> rfl

/-- This is the actual shared finishCall primitive, usable by both call and
result-transfer frames. No execution equation is an input premise. -/
theorem finishCall_progress (config : Config Unit EmptyKey)
    (closed : Profile.ClosedProgram registry program)
    (represented : StateRep program objects environment config.state)
    (caller : CellsRep program config.state.heap objects callerLocals)
    (callerShape : Safety.Locals.environment callerLocals = callerEnvironment)
    (callerNonempty : callerLocals ≠ [])
    (returnCells : ∀ binder ∈ returns,Environment.find environment binder.id = some binder.type)
    (continuation : StackRep registry program config.state.heap objects callerEnvironment
      (.value (Control.resultType ⟨returns,false⟩)) stack)
    (checkpoint : ∃ entryObjects entryEnvironment,StateRep program entryObjects entryEnvironment config.entry) :
    ∃ after, Machine.finishCall config callerLocals mode returns stack = .ok (.next after) ∧
      ConfigurationRep registry program after ∧ after.entry = config.entry ∧
      after.state.heap = config.state.heap ∧ after.state.locals = callerLocals ∧ after.state.mode = mode ∧
      after.state.materializationRemaining = config.state.materializationRemaining := by
  obtain ⟨values,collected,packet⟩ := collectResults_total represented returnCells
  let state := {config.state with locals := callerLocals,mode}
  let after : Config Unit EmptyKey := ⟨.value (Datum.ofPacket values),stack,state,config.entry⟩
  have value : DatumRep program config.state.heap objects (Datum.ofPacket values)
      (Control.resultType ⟨returns,false⟩) := by
    rw [← return_packet_type]
    exact packet.ofPacket
  refine ⟨after,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · simp [Machine.finishCall,collected,Machine.next,after,state]
  · exact ⟨⟨closed,objects,callerEnvironment,callerEnvironment,.value _,
      ⟨represented.heap,caller,callerShape,callerNonempty⟩,.value value,continuation,checkpoint⟩⟩

theorem resultWrites_total (packet : PacketRep program heap objects values (Types.ofList sourceTypes))
    (allowed : ArgumentsReady registry sourceTypes (returns.map Binder.type))
    (returnCells : ∀ binder ∈ returns,Environment.find environment binder.id = some binder.type) :
    ∃ writes, Machine.resultWrites returns values = .ok writes ∧
      WritesRep registry program heap objects environment writes := by
  induction returns generalizing sourceTypes values with
  | nil => cases allowed; cases packet; exact ⟨[],rfl,.nil⟩
  | cons binder returns ih =>
      cases allowed with
      | cons first rest =>
          cases packet with
          | cons head tail =>
              obtain ⟨value,rfl,typeEq,represented⟩ := head.atom_of_supported first.1.1
              obtain ⟨writes,written,writesRep⟩ := ih tail rest
                (fun next member => returnCells next (by simp [member]))
              have ready : TransferReady registry value.type binder.type := by rw [typeEq]; exact first
              exact ⟨(.captured (.local binder.id binder.type),value) :: writes,
                by simp [Machine.resultWrites,Datum.asAtom,written],
                .cons (.local (returnCells binder (by simp)) first.2.1) represented ready writesRep⟩

/-- Explicit return first captures the actual ordered result writes. The
ordinary writes task performs permitted conversions and aliases afterward. -/
theorem explicitReturn_progress
    (context : EvaluationContext registry program objects environment state entry
      (.call callerLocals mode returns :: stack) (.signal ⟨returns,false⟩))
    (represented : DatumRep program state.heap objects datum type)
    (allowed : ReturnReady registry type returns) :
    StepRep registry program
      ⟨.resume (.return_ (some datum)),.call callerLocals mode returns :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.resume (.return_ (some datum)),.call callerLocals mode returns :: stack,state,entry⟩) := by
  cases context.continuation with
  | cons frame continuation =>
      cases frame with
      | call caller callerShape callerNonempty returnCells returnReady =>
          obtain ⟨writes,written,writesRep⟩ := resultWrites_total represented.asPacket_typed allowed returnCells
          let after : Config Unit EmptyKey :=
            ⟨.writes writes,.resultTransfer callerLocals mode returns :: stack,state,entry⟩
          apply stepRep_next (after := after)
          · apply step_of_transition
            simp [Machine.transition,written,Machine.next,after]
          · exact ⟨⟨context.closed,objects,environment,environment,.value (.tuple .nil),context.stateRep,
              .writes writesRep,.cons (.resultTransfer caller callerShape callerNonempty returnCells returnReady)
                continuation,context.checkpoint⟩⟩
          · rfl
          · simp only [after]
            omega

end Solidity.Execution.Safety
