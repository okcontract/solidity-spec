/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.ProcedureTraces

namespace Solidity.Execution.Compatibility
open Core Static
open Aggregates (Failure)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def environmentTypes (_ : Core.Env types) : List Core.Ty := types

theorem machineState_locals_only (state after : MachineState σ)
    (external : after.external = state.external) (heap : after.heap = state.heap)
    (mode : after.mode = state.mode) (budget : after.materializationRemaining = state.materializationRemaining) :
    after = {state with locals := after.locals} := by
  cases state; cases after; simp_all

@[simp] theorem ProcedureEffect.prepend_nil (effect : ProcedureEffect State returns) : effect.prepend [] = effect := by
  cases effect <;> rfl

theorem environmentPacket_ofPacket (environment : Core.Env types) :
    (Datum.ofPacket (environmentPacket environment)).asPacket = environmentPacket environment := by
  cases environment with
  | nil => rfl
  | cons head rest => cases rest <;> rfl

theorem calleeState_finish (state : MachineState σ) (environment : Core.Env types) (returns : List Core.Ty)
    (external : σ) (logs : List Contract.Interaction.Event) (caller : Locals) (mode : ArithmeticMode) :
    procedureState (calleeState state environment returns) external logs caller mode =
      procedureState state external logs caller mode := rfl

/-- Every finite legacy procedure executes in the shared continuation machine.
All local declarations, helper invocations and result writes are derived from
the concrete emitted syntax and checked table. The only store operations are
the original typed primitive reads and writes. -/
theorem procedure_simulates (store : Core.Store Ref Place State) (registry : Registry)
    (table : Program (Key Ref Place)) (emitter : BitVec 160)
    (body : Core.Procedure Ref Place returns vars) (start : Nat) (state : MachineState State)
    (environment : Core.Env vars) (frame : FrameEnv state.locals environment)
    (typed : ReturnTypes state.locals 0 returns)
    (writable : state.heap.execution.context.readOnly = false)
    (self : state.heap.execution.context.self = emitter.setWidth 256)
    (contains : ContainsTranslation table (procedure start body)) :
    ∃ effect, ProcedureTrace (backend store) registry table state (procedure start body).body effect ∧
      effect.observe = some (body.eval store emitter .leftFirst state.external environment) := by
  induction body generalizing start state with
  | ret values =>
      have reads := frame_reads store registry table environment
      cases calculated : values.eval (Core.FrameRef.read (store.read state.external) environment) .leftFirst with
      | error bytes =>
          refine ⟨.failed (Effects.failureOfBytes bytes), ⟨failureOfBytes_source bytes, ?_⟩, ?_⟩
          · intro caller mode stack entry
            exact expressions_return_failure _ _ _ reads values state frame.represented bytes calculated _ entry
          · simp [Core.Procedure.eval, calculated, procedure_failureOfBytes]
      | ok answers =>
          refine ⟨.returned state.external answers [], ?_, by simp [Core.Procedure.eval, calculated, ProcedureEffect.observe]⟩
          intro caller mode stack entry
          have path := expressions_return_prefix _ _ _ reads values state frame.represented answers calculated
            (.call caller mode (returnBinders 0 (environmentTypes answers)) :: stack) entry
          simpa only [procedure, procedureState_empty] using path.trans
            (explicitReturn_prefix (backend store) registry table state entry caller mode stack answers 0 typed)
  | revert bytes =>
      exact ⟨.failed (.revert bytes), ⟨rfl, fun _ _ _ _ => failed_executes (choice := 0) rfl rfl⟩, rfl⟩
  | let_ value next ih =>
      have interpreted := frameExpression_left store registry table state environment frame.represented value
      cases calculated : value.eval (Core.FrameRef.read (store.read state.external) environment) .leftFirst with
      | error bytes =>
          rw [calculated, coreResult_error] at interpreted
          refine ⟨.failed (Effects.failureOfBytes bytes), ?_, ?_⟩
          · exact procedureTrace_seq_failure _ _ _ (failureOfBytes_source bytes)
              (declare_failure state _ _ _ interpreted)
          · simp [Core.Procedure.eval, calculated, procedure_failureOfBytes]
      | ok answer =>
          rw [calculated, coreResult_ok] at interpreted
          obtain ⟨after, declared, framed, odd, external, heap, mode, budget⟩ :=
            declareValue_single (backend store) registry state environment frame answer
          have shape := machineState_locals_only state after external heap mode budget
          have returnTypes := ReturnTypes.frame typed (fun index _ _ => odd index)
          obtain ⟨effect, traced, observed⟩ := ih start after (.cons answer environment) framed returnTypes
            (by rw [heap]; exact writable) (by rw [heap]; exact self) contains
          refine ⟨effect, ?_, by simpa only [Core.Procedure.eval, calculated, external] using observed⟩
          have result := procedureTrace_seq (state := state) (tail := (procedure start next).body) []
            (.declare [some (expressionBinder value (environmentTypes environment).length)] (some (frameExpression value)))
            (declare_prefix state after _ _ (.atom (scalar _ answer)) interpreted declared)
            (by intro final rest caller arithmetic; rw [shape]; rfl) traced
          simpa only [procedure, ProcedureEffect.prepend_nil] using result
  | assign var value next ih =>
      have interpreted := frameExpression_left store registry table state environment frame.represented value
      cases calculated : value.eval (Core.FrameRef.read (store.read state.external) environment) .leftFirst with
      | error bytes =>
          rw [calculated, coreResult_error] at interpreted
          refine ⟨.failed (Effects.failureOfBytes bytes), ?_, ?_⟩
          · exact procedureTrace_seq_failure _ _ _ (failureOfBytes_source bytes)
              (local_assignment_failure state (localId var) (varType var) _ _ interpreted)
          · simp [Core.Procedure.eval, calculated, procedure_failureOfBytes]
      | ok answer =>
          rw [calculated, coreResult_ok] at interpreted
          have localType := typeOf_of_read state.locals (localId var) _ (frame.represented var)
          obtain ⟨locals, written⟩ := write_scalar_exists state.locals (localId var) _ answer localType
          let after : MachineState State := {state with locals}
          have framed := FrameEnv.write frame var answer written
          have odd := OddFrame.write_even (localIndex var) written
          have returnTypes := ReturnTypes.frame typed (fun index _ _ => odd index)
          obtain ⟨effect, traced, observed⟩ := ih start after (environment.set var answer) framed returnTypes writable self contains
          refine ⟨effect, ?_, by simpa only [Core.Procedure.eval, calculated] using observed⟩
          have result := procedureTrace_seq (tail := (procedure start next).body) []
            (.expr (.assign (.local (localId var) (varType var)) (frameExpression value)))
            (local_assignment_prefix (backend store) registry table state (localId var) _ _ answer locals interpreted localType written)
            (by intro final rest caller arithmetic; rfl) traced
          simpa only [procedure, ProcedureEffect.prepend_nil] using result
  | store place value next ih =>
      have interpreted := frameExpression_left store registry table state environment frame.represented value
      cases calculated : value.eval (Core.FrameRef.read (store.read state.external) environment) .leftFirst with
      | error bytes =>
          rw [calculated, coreResult_error] at interpreted
          refine ⟨.failed (Effects.failureOfBytes bytes), ?_, ?_⟩
          · exact procedureTrace_seq_failure _ _ _ (failureOfBytes_source bytes)
              (store_failure state (Key.place place) _ _ interpreted)
          · simp [Core.Procedure.eval, calculated, procedure_failureOfBytes]
      | ok answer =>
          rw [calculated, coreResult_ok] at interpreted
          cases written : store.write state.external place answer with
          | none =>
              refine ⟨.failed .exceptional, ?_, ?_⟩
              · exact procedureTrace_seq_failure _ _ _ rfl
                  (store_fault store registry table state place _ answer interpreted written)
              · simp [Core.Procedure.eval, calculated, written, ProcedureEffect.observe]
          | some middle =>
              obtain ⟨effect, traced, observed⟩ := ih start {state with external := middle} environment frame typed writable self contains
              refine ⟨effect, ?_, by simpa only [Core.Procedure.eval, calculated, written] using observed⟩
              have result := procedureTrace_seq (tail := (procedure start next).body) []
                (.storeExternal (Key.place place) (frameExpression value))
                (store_prefix store registry table state place _ answer middle interpreted written)
                (by intro final rest caller arithmetic; rfl) traced
              simpa only [procedure, ProcedureEffect.prepend_nil] using result
  | branch condition yes no yesIH noIH =>
      have interpreted := frameExpression_left store registry table state environment frame.represented condition
      cases calculated : condition.eval (Core.FrameRef.read (store.read state.external) environment) .leftFirst with
      | error bytes =>
          rw [calculated, coreResult_error] at interpreted
          refine ⟨.failed (Effects.failureOfBytes bytes), ⟨failureOfBytes_source bytes, ?_⟩, ?_⟩
          · intro caller mode stack entry
            exact branch_failure state _ _ _ _ interpreted _ entry
          · simp [Core.Procedure.eval, calculated, procedure_failureOfBytes]
      | ok answer =>
          rw [calculated, coreResult_ok] at interpreted
          have yesContains : ContainsTranslation table (procedure start yes) := contains.subset
            (by intro item member; exact List.mem_append_left _ member)
          have noContains : ContainsTranslation table (procedure (procedure start yes).nextHandle no) := contains.subset
            (by intro item member; exact List.mem_append_right _ member)
          cases answer with
          | false =>
              obtain ⟨effect, traced, observed⟩ := noIH _ state environment frame typed writable self noContains
              refine ⟨effect, ?_, by simpa only [Core.Procedure.eval, calculated, Bool.false_eq_true, ↓reduceIte] using observed⟩
              have result := procedureTrace_prefix []
                (branch_prefix state _ (procedure start yes).body (procedure (procedure start yes).nextHandle no).body false interpreted)
                (by intro final rest caller mode; rfl) traced
              simpa only [procedure, ProcedureEffect.prepend_nil] using result
          | true =>
              obtain ⟨effect, traced, observed⟩ := yesIH start state environment frame typed writable self yesContains
              refine ⟨effect, ?_, by simpa only [Core.Procedure.eval, calculated, ↓reduceIte] using observed⟩
              have result := procedureTrace_prefix []
                (branch_prefix state _ (procedure start yes).body (procedure (procedure start yes).nextHandle no).body true interpreted)
                (by intro final rest caller mode; rfl) traced
              simpa only [procedure, ProcedureEffect.prepend_nil] using result
  | @call results parameters vars returns helper arguments next helperIH nextIH =>
      have reads := frame_reads store registry table environment
      let compiled := procedure (start + 1) helper
      let continuation := procedure compiled.nextHandle next
      let definition : FunctionDefinition (Key Ref Place) :=
        ⟨.nonpayable, parameterBinders parameters, returnBinders 0 results, compiled.body⟩
      have resolved : table.lookup start = .ok definition := contains (start, definition) (by simp [procedure, definition, compiled])
      have helperContains : ContainsTranslation table compiled := contains.subset
        (by intro item member; exact List.mem_cons_of_mem _ (List.mem_append_left _ member))
      have nextContains : ContainsTranslation table continuation := contains.subset
        (by intro item member; exact List.mem_cons_of_mem _ (List.mem_append_right _ member))
      cases calculated : arguments.eval (Core.FrameRef.read (store.read state.external) environment) .leftFirst with
      | error bytes =>
          refine ⟨.failed (Effects.failureOfBytes bytes), ?_, ?_⟩
          · apply procedureTrace_seq_failure _ _ _ (failureOfBytes_source bytes)
            intro stack entry
            exact (next_reaches (choice := 0) (by rfl)).executes
              (expressions_call_failure _ _ _ reads arguments state frame.represented _ _ bytes calculated _ entry)
          · simp [Core.Procedure.eval, calculated, procedure_failureOfBytes]
      | ok answers =>
          have beginCall (stack : List (Frame (Key Ref Place))) (entry : MachineState State) :
              Reaches (transition (backend store) registry table)
                ⟨.exec (procedure start (.call helper arguments next)).body, stack, state, entry⟩
                ⟨.exec compiled.body,
                  .call state.locals state.mode (returnBinders 0 results) ::
                    .declare (resultBinders vars.length results) :: .next continuation.body :: stack,
                  calleeState state answers results, entry⟩ := by
            refine (sequence_enter state _ _ stack entry).trans ?_
            refine (next_reaches (choice := 0) (by rfl)).trans ?_
            exact (expressions_call_prefix _ _ _ reads arguments state frame.represented _ _ answers calculated _ entry).trans
              (invoke_procedure (backend store) registry table state entry _ start answers results compiled.body resolved)
          obtain ⟨helperEffect, helperTraced, helperObserved⟩ := helperIH (start+1) (calleeState state answers results) answers
            (calleeState_frame state answers results) (calleeState_returns state answers results)
            writable self helperContains
          cases helperEffect with
          | failed failure =>
              refine ⟨.failed failure, ⟨helperTraced.1, ?_⟩, ?_⟩
              · intro caller mode stack entry
                exact (beginCall (.call caller mode (returnBinders 0 _) :: stack) entry).executes
                  (helperTraced.2 state.locals state.mode _ entry)
              · simp only [calleeState] at helperObserved
                cases failure <;> simp [ProcedureEffect.observe] at helperObserved
                all_goals simp [ProcedureEffect.observe, Core.Procedure.eval, calculated, ← helperObserved]
          | returned middle values logs =>
              have helperEval : helper.eval store emitter .leftFirst state.external answers = .returned middle values logs :=
                (Option.some.inj helperObserved).symm
              let returned := procedureState state middle logs state.locals state.mode
              have returnedFrame : FrameEnv returned.locals environment := frame
              obtain ⟨after, declared, framed, odd, external, heap, mode, budget⟩ :=
                declareValues_results (backend store) registry returned values environment returnedFrame
              have shape := machineState_locals_only returned after external heap mode budget
              have returnTypes := ReturnTypes.frame typed (fun index _ _ => odd index)
              obtain ⟨effect, traced, observed⟩ := nextIH compiled.nextHandle after (values.append environment) framed returnTypes
                (by rw [heap]; exact writable) (by rw [heap]; exact self) nextContains
              refine ⟨effect.prepend logs, ?_, ?_⟩
              · apply procedureTrace_prefix logs (trace := traced)
                · intro stack entry
                  have helperRun := (beginCall stack entry).trans
                    (helperTraced state.locals state.mode
                      (.declare (resultBinders vars.length results) :: .next continuation.body :: stack) entry)
                  simp only [calleeState_finish] at helperRun
                  apply helperRun.trans
                  have bindResults : Reaches (transition (backend store) registry table)
                      ⟨.value (Datum.ofPacket (environmentPacket values)),
                        .declare (resultBinders vars.length results) :: .next continuation.body :: stack, returned, entry⟩
                      ⟨.resume .next, .next continuation.body :: stack, after, entry⟩ := by
                    apply next_reaches (choice := 0)
                    simp [Machine.transition, environmentPacket_ofPacket, declared, Machine.next]
                  exact bindResults.trans (sequence_next after continuation.body stack entry)
                · intro final rest caller arithmetic
                  rw [shape, procedureState_local]
                  exact procedureState_compose state middle final logs rest _ _ _ _
              · rw [ProcedureEffect.observe_prepend, observed]
                simp [Core.Procedure.eval, calculated, helperEval, external, returned, procedureState]
  | emit bounded topics data next ih =>
      have reads := frame_reads store registry table environment
      cases topicRead : topics.eval (Core.FrameRef.read (store.read state.external) environment) .leftFirst with
      | error bytes =>
          refine ⟨.failed (Effects.failureOfBytes bytes), ?_, ?_⟩
          · apply procedureTrace_seq_failure _ _ _ (failureOfBytes_source bytes)
            exact emit_failure _ _ _ reads topics data state frame.represented bytes
              (by simp [appendExpressions_eval, topicRead])
          · simp [Core.Procedure.eval, topicRead, procedure_failureOfBytes]
      | ok topicValues =>
          cases dataRead : data.eval (Core.FrameRef.read (store.read state.external) environment) .leftFirst with
          | error bytes =>
              refine ⟨.failed (Effects.failureOfBytes bytes), ?_, ?_⟩
              · apply procedureTrace_seq_failure _ _ _ (failureOfBytes_source bytes)
                exact emit_failure _ _ _ reads topics data state frame.represented bytes
                  (by simp [appendExpressions_eval, topicRead, dataRead])
              · simp [Core.Procedure.eval, topicRead, dataRead, procedure_failureOfBytes]
          | ok dataValues =>
              let after := eventState state topicValues dataValues
              let log : Contract.Interaction.Event :=
                ⟨emitter.setWidth 256, topicValues.abiWords, dataValues.abiWords.flatMap Contract.Interaction.wordBytes⟩
              obtain ⟨effect, traced, observed⟩ := ih start after environment frame typed writable self contains
              refine ⟨effect.prepend [log], ?_, ?_⟩
              · apply procedureTrace_seq [log] _
                  (emit_prefix _ _ _ reads topics data state frame.represented topicValues dataValues topicRead dataRead bounded writable)
                  (trace := traced)
                intro final rest caller mode
                simp [eventState, procedureState, log, self, List.append_assoc]
              · rw [ProcedureEffect.observe_prepend, observed]
                simp [Core.Procedure.eval, topicRead, dataRead, after, eventState, log]

end Solidity.Execution.Compatibility
