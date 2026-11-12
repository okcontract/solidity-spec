/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.CommitSteps

/-! Increment/decrement use the actual captured read, scalar update and store.
The scalar result distinguishes prefix/postfix values; arithmetic panics and
read-only word-store failures retain the real source-failure path. -/
namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem update_captured_form (config : Config Unit EmptyKey) (captured : Captured)
    (nondelete : code ≠ .delete) :
    Machine.update physicalBackend registry limits config (.captured captured) code stack =
      (do
        let old ← Machine.readTarget physicalBackend registry limits config.state (.captured captured)
        let changed ← Effects.scalarUpdate config.state.mode code old
        let state ← Machine.writeTarget physicalBackend registry limits config.state (.captured captured) changed.next
        Machine.next config (.value (match changed.result with | none => .tuple [] | some value => .atom value)) state stack) := by
  have expanded : Effects.updateCaptured registry limits.aggregateFuel config.state.materializationRemaining
      config.state.mode config.state.locals config.state.heap captured code =
      (do
        let old ← Effects.readCaptured registry limits.aggregateFuel config.state.locals config.state.heap captured
        let changed ← Effects.scalarUpdate config.state.mode code old
        let (locals,heap,remaining) ← Effects.writeCaptured registry limits.aggregateFuel
          config.state.materializationRemaining config.state.locals config.state.heap captured changed.next
        return (changed.result,locals,heap,remaining)) := by
    cases code <;> simp_all [Effects.updateCaptured]
  unfold Machine.update
  dsimp only
  rw [expanded]
  simp only [Machine.readTarget,Machine.writeTarget]
  cases read : Effects.readCaptured registry limits.aggregateFuel config.state.locals config.state.heap captured with
  | error failure => simp
  | ok old =>
      cases changed : Effects.scalarUpdate config.state.mode code old with
      | error failure => simp [changed]
      | ok result =>
          cases written : Effects.writeCaptured registry limits.aggregateFuel config.state.materializationRemaining
              config.state.locals config.state.heap captured result.next with
          | error failure => simp [changed,written]
          | ok after =>
              rcases after with ⟨locals,heap,remaining⟩
              simp [changed,written]
              rfl

private theorem update_target_captured
    (target : TargetRep registry heap objects environment destination type) :
    ∃ captured,destination = .captured captured := by
  cases target <;> exact ⟨_,rfl⟩

theorem update_primitive_progress (config : Config Unit EmptyKey)
    (context : EvaluationContext registry program objects environment config.state config.entry stack (.value type))
    (target : TargetRep registry config.state.heap objects environment destination type)
    (nondelete : code ≠ .delete) (allowed : Static.UpdateAllowed code type true) :
    PrimitiveRep registry program config
      (Machine.update physicalBackend registry ⟨fuel+2,none⟩ config destination code stack) := by
  obtain ⟨captured,rfl⟩ := update_target_captured target
  rw [update_captured_form config captured nondelete]
  obtain ⟨old,read,_,oldType⟩ := TargetWrites.readTarget_total physicalBackend context.stateRep target fuel
  rw [read]
  simp only [Bind.bind,Except.bind]
  have permission : Static.UpdateAllowed code old.type true := by rw [oldType]; exact allowed
  rcases ScalarRepresentation.update_progress (program := program) (heap := config.state.heap) (objects := objects)
      config.state.mode code old nondelete permission with
    ⟨changed,result,computed,nextType,nextRep,present,resultType,resultRep⟩ | ⟨failure,failed,sourceFailure⟩
  · rw [computed]
    simp only [present]
    have ready : TransferReady registry changed.next.type type := by
      rw [nextType,oldType]
      exact SupportedTransfers.self_ready target.ready
    rcases TargetWrites.writeTarget_total physicalBackend context.stateRep target nextRep ready fuel with
      failed | ⟨after,written,stateRep,invocation,budget⟩
    · simp only [failed,PrimitiveRep]
      rfl
    · simp only [written,Machine.next,PrimitiveRep,StepRep]
      refine ⟨(context.replace_state stateRep invocation).value ?_,by trivial,?_⟩
      · have typed : result.type = type := resultType.trans oldType
        simpa only [typed] using DatumRep.atom (resultRep.extend invocation (fun _ member => member))
      · dsimp
        omega
  · simpa only [failed,Bind.bind,Except.bind,PrimitiveRep] using sourceFailure

theorem update_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value type))
    (target : TargetRep registry state.heap objects environment destination type)
    (nondelete : code ≠ .delete) (allowed : Static.UpdateAllowed code type true) :
    StepRep registry program ⟨.target destination,.update code :: stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.target destination,.update code :: stack,state,entry⟩) := by
  apply primitive_step
  exact update_primitive_progress _ context target nondelete allowed

end Solidity.Execution.Safety
