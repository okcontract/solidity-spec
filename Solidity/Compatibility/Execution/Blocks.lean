/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.State

/-! The previous finite block evaluator embeds through actual machine steps.
Successful prefixes retain every frame/heap field except the external store;
errors remain real invocation failures, never inconclusive observations. -/
namespace Solidity.Execution.Compatibility
open Core Static
open Aggregates (Failure)
open Contract.Interaction (Word wordBytes)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

inductive BlockEffect (State : Type) where
  | next : State → BlockEffect State
  | returned : Option Word → State → BlockEffect State
  | failed : Failure → BlockEffect State

def blockPacket : Option Word → Packet
  | none => []
  | some value => [.atom ⟨.uint 31, value⟩]

def BlockEffect.observe : BlockEffect State → Option (Core.Flow State)
  | .next after => some (.next after)
  | .returned value after => some (.halt (.returned (value.toList.flatMap wordBytes) after))
  | .failed failure => (failureOutcome failure).map Core.Flow.halt

def BlockTrace (backend : Backend State Keys) (registry : Registry) (program : Program Keys)
    (state : MachineState State) (body : Execution.Stmt Keys) : BlockEffect State → Prop
  | .next after => ∀ stack entry, Reaches (transition backend registry program)
      ⟨.exec body, stack, state, entry⟩ ⟨.resume .next, stack, {state with external := after}, entry⟩
  | .returned value after => ∀ stack entry, Reaches (transition backend registry program)
      ⟨.exec body, stack, state, entry⟩
      ⟨.resume (.return_ (some (Datum.ofPacket (blockPacket value)))), stack, {state with external := after}, entry⟩
  | .failed failure => isSourceFailure failure = true ∧ ∀ stack entry,
      Executes (transition backend registry program) ⟨.exec body, stack, state, entry⟩ (fail entry failure)

variable {State : Type} {Keys : SType → Type}
variable {failure : Failure} {effect : BlockEffect State}
variable {backend : Backend State Keys} {registry : Registry} {program : Program Keys}

theorem blockTrace_seq_next (state : MachineState State) (first rest : Execution.Stmt Keys)
    (before : BlockTrace backend registry program state first (.next middle))
    (tail : BlockTrace backend registry program {state with external := middle} rest effect) :
    BlockTrace backend registry program state (.seq first rest) effect := by
  have path (stack : List (Frame Keys)) (entry : MachineState State) :
      Reaches (transition backend registry program)
        ⟨.exec (.seq first rest), stack, state, entry⟩
        ⟨.exec rest, stack, {state with external := middle}, entry⟩ := by
    exact (next_reaches (choice := 0) (by rfl)).trans
      ((before (.next rest :: stack) entry).trans (next_reaches (choice := 0) (by rfl)))
  cases effect with
  | next after => intro stack entry; exact (path stack entry).trans (tail stack entry)
  | returned value after => intro stack entry; exact (path stack entry).trans (tail stack entry)
  | failed failure => exact ⟨tail.1, fun stack entry => (path stack entry).executes (tail.2 stack entry)⟩

theorem blockTrace_seq_return (state : MachineState State) (first rest : Execution.Stmt Keys)
    (before : BlockTrace backend registry program state first (.returned value after)) :
    BlockTrace backend registry program state (.seq first rest) (.returned value after) := by
  intro stack entry
  exact (next_reaches (choice := 0) (by rfl)).trans
    ((before (.next rest :: stack) entry).trans (next_reaches (choice := 0) (by rfl)))

theorem blockTrace_seq_failed (state : MachineState State) (first rest : Execution.Stmt Keys)
    (before : BlockTrace backend registry program state first (.failed failure)) :
    BlockTrace backend registry program state (.seq first rest) (.failed failure) :=
  ⟨before.1, fun stack entry => (next_reaches (choice := 0) (by rfl)).executes (before.2 (.next rest :: stack) entry)⟩

theorem blockTrace_branch (state : MachineState State) (test : Execution.Expr Keys)
    (yes no : Execution.Stmt Keys) (choice : Bool)
    (condition : PureResult backend registry program state test (.ok (.atom ⟨.bool, choice⟩)))
    (selected : BlockTrace backend registry program state (if choice then yes else no) effect) :
    BlockTrace backend registry program state (.if_ test yes no) effect := by
  have path (stack : List (Frame Keys)) (entry : MachineState State) :
      Reaches (transition backend registry program) ⟨.exec (.if_ test yes no), stack, state, entry⟩
        ⟨.exec (if choice then yes else no), stack, state, entry⟩ := by
    refine (next_reaches (choice := 0) (by rfl)).trans ((condition (.branch yes no :: stack) entry).trans ?_)
    apply next_reaches (choice := 0)
    cases choice <;> rfl
  cases effect with
  | next after => intro stack entry; exact (path stack entry).trans (selected stack entry)
  | returned value after => intro stack entry; exact (path stack entry).trans (selected stack entry)
  | failed failure => exact ⟨selected.1, fun stack entry => (path stack entry).executes (selected.2 stack entry)⟩

theorem blockTrace_branch_failure (state : MachineState State) (test : Execution.Expr Keys)
    (yes no : Execution.Stmt Keys) (failure : Failure) (source : isSourceFailure failure = true)
    (condition : PureResult backend registry program state test (.error failure)) :
    BlockTrace backend registry program state (.if_ test yes no) (.failed failure) :=
  ⟨source, fun stack entry => (next_reaches (choice := 0) (by rfl)).executes
    (condition (.branch yes no :: stack) entry)⟩

theorem emptyTuple_reaches (state : MachineState State) (stack : List (Frame Keys)) (entry : MachineState State) :
    Reaches (transition backend registry program) ⟨.eval (.tuple []), stack, state, entry⟩
      ⟨.value (.tuple []), stack, state, entry⟩ := by
  exact (next_reaches (choice := 0) (by rfl)).trans
    ((next_reaches (choice := 0) (by rfl)).trans (next_reaches (choice := 0) (by rfl)))

theorem blockTrace_stop (state : MachineState State) :
    BlockTrace backend registry program state (.return_ (some (.tuple []))) (.returned none state.external) := by
  intro stack entry
  exact (next_reaches (choice := 0) (by rfl)).trans
    ((emptyTuple_reaches state (.returnValue :: stack) entry).trans (next_reaches (choice := 0) (by rfl)))

theorem failureOfBytes_outcome (bytes : List UInt8) :
    failureOutcome (State := State) (Effects.failureOfBytes bytes) = some (.reverted bytes) := by
  cases same : bytes == Contract.panic ((bytes[35]?).getD 0) with
  | false => simp [Effects.failureOfBytes, same, failureOutcome]
  | true =>
      have equal : bytes = Contract.panic ((bytes[35]?).getD 0) := by simpa using same
      simp [Effects.failureOfBytes, failureOutcome, ← equal]

theorem blockTrace_return (state : MachineState State) (expression : Execution.Expr Keys) (value : Word)
    (evaluated : PureResult backend registry program state expression (.ok (.atom ⟨.uint 31, value⟩))) :
    BlockTrace backend registry program state (.return_ (some expression)) (.returned (some value) state.external) := by
  intro stack entry
  exact (next_reaches (choice := 0) (by rfl)).trans
    ((evaluated (.returnValue :: stack) entry).trans (next_reaches (choice := 0) (by rfl)))

theorem blockTrace_return_failure (state : MachineState State) (expression : Execution.Expr Keys)
    (source : isSourceFailure failure = true)
    (evaluated : PureResult backend registry program state expression (.error failure)) :
    BlockTrace backend registry program state (.return_ (some expression)) (.failed failure) :=
  ⟨source, fun stack entry => (next_reaches (choice := 0) (by rfl)).executes
    (evaluated (.returnValue :: stack) entry)⟩

theorem blockTrace_store_failure (state : MachineState State) (expression : Execution.Expr Keys)
    (key : Keys type) (source : isSourceFailure failure = true)
    (evaluated : PureResult backend registry program state expression (.error failure)) :
    BlockTrace backend registry program state (.storeExternal key expression) (.failed failure) :=
  ⟨source, fun stack entry => (next_reaches (choice := 0) (by rfl)).executes
    (evaluated (.storeExternal key :: stack) entry)⟩

theorem blockTrace_store (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (place : Place type)
    (expression : Execution.Expr (Key Ref Place)) (value : type.Value)
    (evaluated : PureResult (Compatibility.backend store) registry program state expression (.ok (.atom (scalar type value)))) :
    BlockTrace (Compatibility.backend store) registry program state (.storeExternal (.place place) expression)
      (match store.write state.external place value with | some after => .next after | none => .failed .exceptional) := by
  cases written : store.write state.external place value with
  | some after =>
      intro stack entry
      refine (next_reaches (choice := 0) (by rfl)).trans
        ((evaluated (.storeExternal (.place place) :: stack) entry).trans ?_)
      apply next_reaches (choice := 0)
      simp [Machine.transition, Datum.asAtom, write_external, written, Machine.next]
  | none =>
      refine ⟨rfl, fun stack entry => ?_⟩
      refine (next_reaches (choice := 0) (by rfl)).executes
        ((evaluated (.storeExternal (.place place) :: stack) entry).executes ?_)
      apply failed_executes (choice := 0) _ rfl
      simp [Machine.transition, Datum.asAtom, write_external, written]

/-- Every old finite block has a concrete transition-prefix interpretation.
No assumed old-evaluator callback or universal physical-slot injection occurs. -/
theorem block_simulates (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (body : Core.Block Ref Place) :
    ∃ effect, BlockTrace (Compatibility.backend store) registry program state (block body) effect ∧
      effect.observe = some (body.eval store .leftFirst state.external) := by
  induction body generalizing state with
  | skip => exact ⟨.next state.external, fun _ _ => next_reaches (choice := 0) (by rfl), rfl⟩
  | seq first rest firstIH restIH =>
      obtain ⟨effect, traced, observed⟩ := firstIH state
      cases effect with
      | next middle =>
          have evaluated : first.eval store .leftFirst state.external = .next middle := (Option.some.inj observed).symm
          obtain ⟨effect, tail, sameFlow⟩ := restIH {state with external := middle}
          exact ⟨effect, blockTrace_seq_next state _ _ traced tail, by simpa [Core.Block.eval, evaluated] using sameFlow⟩
      | returned value after =>
          have evaluated : first.eval store .leftFirst state.external = .halt (.returned (value.toList.flatMap wordBytes) after) :=
            (Option.some.inj observed).symm
          exact ⟨.returned value after, blockTrace_seq_return state _ _ traced, by simpa [Core.Block.eval, evaluated] using observed⟩
      | failed failure =>
          refine ⟨.failed failure, blockTrace_seq_failed state _ _ traced, ?_⟩
          cases failure <;> simp [BlockEffect.observe, failureOutcome] at observed
          all_goals simp [BlockEffect.observe, failureOutcome, Core.Block.eval, ← observed]
  | assign place value =>
      have interpreted := externalExpression_left (Place := Place) store registry program state value
      cases evaluated : value.eval (store.read state.external) .leftFirst with
      | error bytes =>
          rw [evaluated, coreResult_error] at interpreted
          exact ⟨.failed (Effects.failureOfBytes bytes), blockTrace_store_failure state _ _ (failureOfBytes_source bytes) interpreted,
            by simp [BlockEffect.observe, failureOfBytes_outcome, Core.Block.eval, evaluated]⟩
      | ok value =>
          rw [evaluated, coreResult_ok] at interpreted
          refine ⟨_, blockTrace_store store registry program state place _ value interpreted, ?_⟩
          cases written : store.write state.external place value <;>
            simp [Core.Block.eval, evaluated, written, BlockEffect.observe, failureOutcome]
  | ret value =>
      have interpreted := externalExpression_left (Place := Place) store registry program state value
      cases evaluated : value.eval (store.read state.external) .leftFirst with
      | error bytes =>
          rw [evaluated, coreResult_error] at interpreted
          exact ⟨.failed (Effects.failureOfBytes bytes), blockTrace_return_failure state _ (failureOfBytes_source bytes) interpreted,
            by simp [BlockEffect.observe, failureOfBytes_outcome, Core.Block.eval, evaluated]⟩
      | ok value =>
          rw [evaluated, coreResult_ok] at interpreted
          exact ⟨.returned (some value) state.external, blockTrace_return state _ value interpreted,
            by simp [BlockEffect.observe, Core.Block.eval, evaluated]⟩
  | stop => exact ⟨.returned none state.external, blockTrace_stop state, rfl⟩
  | revert bytes => exact ⟨.failed (.revert bytes), ⟨rfl, fun _ _ => failed_executes (choice := 0) (by rfl) rfl⟩, rfl⟩
  | branch test yes no yesIH noIH =>
      have interpreted := externalExpression_left (Place := Place) store registry program state test
      cases evaluated : test.eval (store.read state.external) .leftFirst with
      | error bytes =>
          rw [evaluated, coreResult_error] at interpreted
          exact ⟨.failed (Effects.failureOfBytes bytes), blockTrace_branch_failure state _ _ _ _ (failureOfBytes_source bytes) interpreted,
            by simp [BlockEffect.observe, failureOfBytes_outcome, Core.Block.eval, evaluated]⟩
      | ok value =>
          rw [evaluated, coreResult_ok] at interpreted
          cases value with
          | false =>
              obtain ⟨effect, tail, sameFlow⟩ := noIH state
              exact ⟨effect, blockTrace_branch state _ _ _ false interpreted tail, by simpa [Core.Block.eval, evaluated] using sameFlow⟩
          | true =>
              obtain ⟨effect, tail, sameFlow⟩ := yesIH state
              exact ⟨effect, blockTrace_branch state _ _ _ true interpreted tail, by simpa [Core.Block.eval, evaluated] using sameFlow⟩

theorem block_effect_observed (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (body : Core.Block Ref Place)
    (traced : BlockTrace (Compatibility.backend store) registry program state (block body) effect) :
    ∃ observed, Executes (transition (Compatibility.backend store) registry program)
      (Config.start state (blockBody body)) observed ∧ blockObservation observed = effect.observe := by
  cases effect with
  | next after =>
      refine ⟨.returned [.atom ⟨.bool, true⟩] {state with external := after}, ?_, rfl⟩
      let marker : Execution.Stmt (Key Ref Place) := .return_ (some fallthrough)
      have path := (next_reaches (choice := 0) (before := Config.start state (blockBody body)) (by rfl)).trans
        (traced [.next marker] state)
      refine path.executes ((next_reaches (choice := 0) (by rfl)).executes ?_)
      refine (next_reaches (choice := 0) (by rfl)).executes ?_
      refine (literal_reaches (Compatibility.backend store) registry program
        ⟨.eval fallthrough, [.returnValue], {state with external := after}, state⟩ ⟨.bool, true⟩).executes ?_
      refine (next_reaches (choice := 0) (by rfl)).executes ?_
      exact .done (choice := 0) (by rfl)
  | returned value after =>
      refine ⟨.returned (blockPacket value) {state with external := after}, ?_, ?_⟩
      · let marker : Execution.Stmt (Key Ref Place) := .return_ (some fallthrough)
        have path := (next_reaches (choice := 0) (before := Config.start state (blockBody body)) (by rfl)).trans
          (traced [.next marker] state)
        refine path.executes ((next_reaches (choice := 0) (by rfl)).executes ?_)
        apply Executes.done (choice := 0)
        cases value <;> rfl
      · cases value with
        | none => rfl
        | some value => simpa [blockPacket, BlockEffect.observe] using blockObservation_word {state with external := after} value
  | failed failure =>
      refine ⟨fail state failure, ?_, rfl⟩
      exact (next_reaches (choice := 0) (before := Config.start state (blockBody body)) (by rfl)).executes
        (traced.2 [.next (.return_ (some fallthrough))] state)

/-- The public old observation has an actual completed execution of the
shared machine. Interpreter fuel is existential and never a source premise. -/
theorem block_machine (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (body : Core.Block Ref Place) :
    ∃ observed, Executes (transition (Compatibility.backend store) registry program)
      (Config.start state (blockBody body)) observed ∧
      blockObservation observed = some (body.eval store .leftFirst state.external) := by
  obtain ⟨effect, traced, represented⟩ := block_simulates store registry program state body
  obtain ⟨observed, executed, same⟩ := block_effect_observed store registry program state body traced
  exact ⟨observed, executed, same.trans represented⟩

theorem block_run (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (body : Core.Block Ref Place) :
    ∃ fuel choices observed,
      Machine.execute (Compatibility.backend store) registry legacyLimits program fuel choices
        (Config.start state (blockBody body)) = .finished observed ∧
      blockObservation observed = some (body.eval store .leftFirst state.external) := by
  obtain ⟨observed, executed, represented⟩ := block_machine store registry program state body
  obtain ⟨fuel, choices, finished⟩ := Solidity.Execution.run_complete _ executed
  exact ⟨fuel, choices, observed, finished, represented⟩

end Solidity.Execution.Compatibility
