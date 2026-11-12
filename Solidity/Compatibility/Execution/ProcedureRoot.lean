/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Procedures

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def rootTranslation (body : Core.Procedure Ref Place returns vars) : Translation (Key Ref Place) :=
  let compiled := procedure 1 body
  ⟨compiled.body,
    (0, ⟨.nonpayable, parameterBinders vars, returnBinders 0 returns, compiled.body⟩) :: compiled.functions,
    compiled.nextHandle⟩

def procedureProgram (body : Core.Procedure Ref Place returns vars) : Program (Key Ref Place) :=
  program (rootTranslation body)

/-- Invocation begins with the resolved handle and already evaluated scalar
argument packet. Subsequent parameter/return conversion and body execution
are all ordinary shared-machine transitions. -/
def procedureConfig (_body : Core.Procedure Ref Place returns vars) (state : MachineState State)
    (environment : Core.Env vars) : Config State (Key Ref Place) :=
  ⟨.apply (.call (signature vars returns))
    (.atom ⟨(signature vars returns).type, some 0⟩ :: environmentPacket environment), [], state, state⟩

theorem rootTranslation_region (body : Core.Procedure Ref Place returns vars) :
    TableRegion 0 (rootTranslation body).nextHandle (rootTranslation body).functions :=
  (procedure_table body 1).prepend _ (function_bindings _ _ _)
    (by change Mutability.nonpayable ≠ .payable; decide)

theorem procedureProgram_valid (body : Core.Procedure Ref Place returns vars) : (procedureProgram body).valid = true := by
  have region := rootTranslation_region body
  have erase : ((rootTranslation body).functions.map Prod.fst).eraseDups =
      (rootTranslation body).functions.map Prod.fst := by
    exact eraseDups_nodup _ region.distinct
  simp only [procedureProgram, program, Program.valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  constructor
  · rw [erase]
    simp
  · intro entry member
    obtain ⟨bindings, mutability⟩ := region.bindings entry member
    simp [bindings, mutability]

theorem procedureProgram_contains (body : Core.Procedure Ref Place returns vars) :
    ContainsTranslation (procedureProgram body) (procedure 1 body) := by
  intro entry member
  exact lookup_member (rootTranslation body) (procedureProgram_valid body) (rootTranslation_region body)
    (List.mem_cons_of_mem _ member)

theorem procedureProgram_root (body : Core.Procedure Ref Place returns vars) :
    (procedureProgram body).lookup 0 = .ok
      ⟨.nonpayable, parameterBinders vars, returnBinders 0 returns, (procedure 1 body).body⟩ :=
  lookup_member (rootTranslation body) (procedureProgram_valid body) (rootTranslation_region body) (by simp [rootTranslation])

/-- The universal finite-procedure endpoint has no caller-supplied helper
execution or typed-state restriction. Its concrete emitted table is valid;
actual invocation initializes scalar parameters and named returns. -/
theorem procedure_machine (store : Core.Store Ref Place State) (registry : Registry)
    (emitter : BitVec 160) (body : Core.Procedure Ref Place returns vars)
    (state : MachineState State) (environment : Core.Env vars)
    (writable : state.heap.execution.context.readOnly = false)
    (self : state.heap.execution.context.self = emitter.setWidth 256)
    (logs : state.heap.execution.world.logs = []) :
    ∃ observed,
      Executes (transition (backend store) registry (procedureProgram body)) (procedureConfig body state environment) observed ∧
      procedureObservation returns observed = some (body.eval store emitter .leftFirst state.external environment) := by
  have entered := invoke_procedure (backend store) registry (procedureProgram body) state state [] 0 environment returns
    (procedure 1 body).body (procedureProgram_root body)
  obtain ⟨effect, traced, represented⟩ := procedure_simulates store registry (procedureProgram body) emitter body 1
    (calleeState state environment returns) environment (calleeState_frame state environment returns)
    (calleeState_returns state environment returns) writable self (procedureProgram_contains body)
  simp only [calleeState] at represented
  cases effect with
  | returned after values events =>
      let finished := procedureState state after events state.locals state.mode
      refine ⟨.returned (environmentPacket values) finished, ?_, ?_⟩
      · have path := entered.trans (traced state.locals state.mode [] state)
        simp only [calleeState_finish] at path
        apply path.executes
        apply Executes.done (choice := 0)
        simp [transition, Machine.step, Machine.transition, environmentPacket_ofPacket, finished]
      · rw [← represented]
        simp [procedureObservation, ProcedureEffect.observe, finished, procedureState, logs, decode_environmentPacket]
  | failed failure =>
      refine ⟨fail state failure, entered.executes (traced.2 state.locals state.mode [] state), ?_⟩
      rw [← represented]
      cases failure <;> rfl

theorem procedure_run (store : Core.Store Ref Place State) (registry : Registry)
    (emitter : BitVec 160) (body : Core.Procedure Ref Place returns vars)
    (state : MachineState State) (environment : Core.Env vars)
    (writable : state.heap.execution.context.readOnly = false)
    (self : state.heap.execution.context.self = emitter.setWidth 256)
    (logs : state.heap.execution.world.logs = []) :
    ∃ fuel choices observed,
      Machine.execute (backend store) registry legacyLimits (procedureProgram body) fuel choices
        (procedureConfig body state environment) = .finished observed ∧
      procedureObservation returns observed = some (body.eval store emitter .leftFirst state.external environment) := by
  obtain ⟨observed, executed, represented⟩ := procedure_machine store registry emitter body state environment writable self logs
  obtain ⟨fuel, choices, finished⟩ := Solidity.Execution.run_complete _ executed
  exact ⟨fuel, choices, observed, finished, represented⟩

end Solidity.Execution.Compatibility
