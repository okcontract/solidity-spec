/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Blocks

/-! Finite executions of the previous loop machine expand into actual shared
machine transitions. Body and post continuations are related separately; no
termination premise, equal fuel budget, or old-evaluator opcode is introduced. -/
namespace Solidity.Execution.Compatibility
open Core Static
open Aggregates (Failure)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

variable {Ref Place : Core.Ty → Type} {State : Type}

def controlObservation (observed : Observation State) : Option (Core.Control.Observation State) :=
  match observed with
  | .inconclusive .rejected _ => some .invalidControl
  | _ => (blockObservation observed).map Core.Control.Observation.completed

/-- The sentinel distinguishes fallthrough from an explicit empty return. -/
inductive ControlStack : List (Core.Control.Frame Ref Place) → List (Execution.Frame (Key Ref Place)) → Prop
  | root : ControlStack [] [.next (.return_ (some fallthrough))]
  | next (rest : Core.Control.Command Ref Place) : ControlStack before after →
      ControlStack (.next rest :: before) (.next (control rest) :: after)
  | loop (test : Core.Expr Ref .bool) (body : Core.Control.Command Ref Place) (post : Core.Block Ref Place) :
      ControlStack before after → ControlStack (.loop test body post :: before)
        (.loopBody (externalExpression test) (control body) (block post) :: after)
  | post (test : Core.Expr Ref .bool) (body : Core.Control.Command Ref Place) (post : Core.Block Ref Place) :
      ControlStack before after → ControlStack (.next (.loop test body post) :: before)
        (.loopPost (externalExpression test) (control body) (block post) :: after)

theorem ControlStack.return_reaches (backend : Backend State (Key Ref Place)) (registry : Registry)
    (program : Program (Key Ref Place)) (related : ControlStack before after)
    (value : Option Datum) (state entry : MachineState State) :
    Reaches (transition backend registry program) ⟨.resume (.return_ value), after, state, entry⟩
      ⟨.resume (.return_ value), [], state, entry⟩ := by
  induction related with
  | root => exact next_reaches (choice := 0) (by rfl)
  | next _ _ ih | loop _ _ _ _ ih | post _ _ _ _ ih =>
      exact (next_reaches (choice := 0) (by rfl)).trans ih

theorem ControlStack.return_executes (backend : Backend State (Key Ref Place)) (registry : Registry)
    (program : Program (Key Ref Place)) (related : ControlStack before after)
    (value : Option Contract.Interaction.Word) (state entry : MachineState State) :
    Executes (transition backend registry program)
      ⟨.resume (.return_ (some (Datum.ofPacket (blockPacket value)))), after, state, entry⟩
      (.returned (blockPacket value) state) := by
  refine (related.return_reaches backend registry program _ state entry).executes ?_
  apply Executes.done (choice := 0)
  cases value <;> rfl

theorem ControlStack.next_executes (backend : Backend State (Key Ref Place)) (registry : Registry)
    (program : Program (Key Ref Place)) (state entry : MachineState State) :
    Executes (transition backend registry program)
      ⟨.resume .next, [.next (.return_ (some fallthrough))], state, entry⟩
      (.returned [.atom ⟨.bool, true⟩] state) := by
  refine (next_reaches (choice := 0) (by rfl)).executes ?_
  refine (next_reaches (choice := 0) (by rfl)).executes ?_
  refine (literal_reaches backend registry program
    ⟨.eval fallthrough, [.returnValue], state, entry⟩ ⟨.bool, true⟩).executes ?_
  refine (next_reaches (choice := 0) (by rfl)).executes ?_
  exact .done (choice := 0) (by rfl)

inductive ControlMatch (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (base : MachineState State) :
    Core.Control.Config Ref Place State → Config State (Key Ref Place) → Prop
  | executing (body : Core.Control.Command Ref Place) (state : State)
      (related : ControlStack before after) :
      ControlMatch store registry program base (.exec body before state)
        ⟨.exec (control body), after, {base with external := state}, base⟩
  | testing (test : Core.Expr Ref .bool) (body : Core.Control.Command Ref Place)
      (post : Core.Block Ref Place) (state : State) (related : ControlStack before after) :
      ControlMatch store registry program base (.exec (.loop test body post) before state)
        ⟨.loopTest (externalExpression test) (control body) (block post), after,
          {base with external := state}, base⟩
  | sequence (first rest : Core.Control.Command Ref Place) (state : State)
      (related : ControlStack (.next rest :: before) after) :
      ControlMatch store registry program base (.exec (.seq first rest) before state)
        ⟨.exec (control first), after, {base with external := state}, base⟩
  | next (state : State) (related : ControlStack before after) :
      ControlMatch store registry program base (.resume .next before state)
        ⟨.resume .next, after, {base with external := state}, base⟩
  | break_ (state : State) (related : ControlStack before after) :
      ControlMatch store registry program base (.resume .break_ before state)
        ⟨.resume .break_, after, {base with external := state}, base⟩
  | continue_ (state : State) (related : ControlStack before after) :
      ControlMatch store registry program base (.resume .continue_ before state)
        ⟨.resume .continue_, after, {base with external := state}, base⟩
  | halted (result : Core.Outcome State) (state : State) (stack : List (Core.Control.Frame Ref Place))
      (executed : Executes (transition (Compatibility.backend store) registry program) config observed)
      (represented : controlObservation observed = some (.completed (.halt result))) :
      ControlMatch store registry program base (.resume (.halt result) stack state) config

@[simp] theorem controlObservation_returned (state : MachineState State)
    (value : Option Contract.Interaction.Word) :
    controlObservation (.returned (blockPacket value) state) =
      some (.completed (.halt (.returned (value.toList.flatMap Contract.Interaction.wordBytes) state.external))) := by
  cases value with
  | none => rfl
  | some value =>
      simp only [controlObservation]
      rw [show blockPacket (some value) = [.atom ⟨.uint 31, value⟩] from rfl, blockObservation_word]
      rfl

theorem controlObservation_failure (entry : MachineState State) (failure : Failure)
    (source : isSourceFailure failure = true) :
    controlObservation (fail entry failure) =
      (failureOutcome failure).map (fun result => Core.Control.Observation.completed (.halt result)) := by
  cases failure <;> simp_all [isSourceFailure, fail, controlObservation, failureOutcome, blockObservation]

theorem ControlMatch.block_advance (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (base : MachineState State)
    (body : Core.Block Ref Place) (state : State) (related : ControlStack before after)
    (moved : Core.Control.step store .leftFirst (.exec (.block body) before state) = .next middle) :
    ∃ next, Reaches (transition (Compatibility.backend store) registry program)
      ⟨.exec (block body), after, {base with external := state}, base⟩ next ∧
      ControlMatch store registry program base middle next := by
  obtain ⟨effect, traced, represented⟩ := block_simulates store registry program {base with external := state} body
  cases effect with
  | next updated =>
      have evaluated : body.eval store .leftFirst state = .next updated := (Option.some.inj represented).symm
      simp only [Core.Control.step, evaluated] at moved
      cases moved
      refine ⟨_, ?_, .next updated related⟩
      simpa using traced after base
  | returned value updated =>
      have evaluated : body.eval store .leftFirst state =
          .halt (.returned (value.toList.flatMap Contract.Interaction.wordBytes) updated) :=
        (Option.some.inj represented).symm
      simp only [Core.Control.step, evaluated] at moved
      cases moved
      refine ⟨_, traced after base, .halted _ state before
        (related.return_executes (Compatibility.backend store) registry program value _ base) ?_⟩
      simp
  | failed failure =>
      cases outcome : failureOutcome (State := State) failure with
      | none => simp [BlockEffect.observe, outcome] at represented
      | some result =>
          have evaluated : body.eval store .leftFirst state = .halt result := by
            simpa [BlockEffect.observe, outcome] using (Option.some.inj (by simpa [BlockEffect.observe, outcome] using represented)).symm
          simp only [Core.Control.step, evaluated] at moved
          cases moved
          refine ⟨_, .refl _, .halted result state before (traced.2 after base) ?_⟩
          simp [controlObservation_failure base failure traced.1, outcome]

theorem ControlMatch.loop_advance (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (base : MachineState State)
    (test : Core.Expr Ref .bool) (body : Core.Control.Command Ref Place) (post : Core.Block Ref Place)
    (state : State) (related : ControlStack before after)
    (moved : Core.Control.step store .leftFirst (.exec (.loop test body post) before state) = .next middle) :
    ∃ next, Reaches (transition (Compatibility.backend store) registry program)
      ⟨.loopTest (externalExpression test) (control body) (block post), after, {base with external := state}, base⟩ next ∧
      ControlMatch store registry program base middle next := by
  have interpreted := externalExpression_left store registry program {base with external := state} test
  cases evaluated : test.eval (store.read state) .leftFirst with
  | error bytes =>
      simp only [Core.Control.step, evaluated] at moved
      cases moved
      rw [evaluated] at interpreted
      refine ⟨_, .refl _, .halted (observed := fail base (Effects.failureOfBytes bytes))
        (.reverted bytes) state before ?_ ?_⟩
      · exact (next_reaches (choice := 0) (by rfl)).executes
          (interpreted (.loopCondition (externalExpression test) (control body) (block post) :: after) base)
      · rw [controlObservation_failure base _ (failureOfBytes_source bytes), failureOfBytes_outcome]
        rfl
  | ok choice =>
      rw [evaluated] at interpreted
      have path : Reaches (transition (Compatibility.backend store) registry program)
          ⟨.loopTest (externalExpression test) (control body) (block post), after, {base with external := state}, base⟩
          ⟨if choice then .exec (control body) else .resume .next,
            if choice then .loopBody (externalExpression test) (control body) (block post) :: after else after,
            {base with external := state}, base⟩ := by
        refine (next_reaches (choice := 0) (by rfl)).trans
          ((interpreted (.loopCondition (externalExpression test) (control body) (block post) :: after) base).trans ?_)
        apply next_reaches (choice := 0)
        cases choice <;> rfl
      cases choice with
      | false =>
          simp only [Core.Control.step, evaluated] at moved
          cases moved
          exact ⟨_, path, .next state related⟩
      | true =>
          simp only [Core.Control.step, evaluated] at moved
          cases moved
          exact ⟨_, path, .executing body state (.loop test body post related)⟩

theorem ControlMatch.branch_advance (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (base : MachineState State)
    (test : Core.Expr Ref .bool) (yes no : Core.Control.Command Ref Place)
    (state : State) (related : ControlStack before after)
    (moved : Core.Control.step store .leftFirst (.exec (.branch test yes no) before state) = .next middle) :
    ∃ next, Reaches (transition (Compatibility.backend store) registry program)
      ⟨.exec (.if_ (externalExpression test) (control yes) (control no)), after, {base with external := state}, base⟩ next ∧
      ControlMatch store registry program base middle next := by
  have interpreted := externalExpression_left store registry program {base with external := state} test
  cases evaluated : test.eval (store.read state) .leftFirst with
  | error bytes =>
      simp only [Core.Control.step, evaluated] at moved
      cases moved
      rw [evaluated] at interpreted
      refine ⟨_, .refl _, .halted (observed := fail base (Effects.failureOfBytes bytes))
        (.reverted bytes) state before ?_ ?_⟩
      · exact (next_reaches (choice := 0) (by rfl)).executes
          (interpreted (.branch (control yes) (control no) :: after) base)
      · rw [controlObservation_failure base _ (failureOfBytes_source bytes), failureOfBytes_outcome]
        rfl
  | ok choice =>
      rw [evaluated] at interpreted
      have path : Reaches (transition (Compatibility.backend store) registry program)
          ⟨.exec (.if_ (externalExpression test) (control yes) (control no)), after, {base with external := state}, base⟩
          ⟨.exec (control (if choice then yes else no)), after, {base with external := state}, base⟩ := by
        refine (next_reaches (choice := 0) (by rfl)).trans
          ((interpreted (.branch (control yes) (control no) :: after) base).trans ?_)
        apply next_reaches (choice := 0)
        cases choice <;> rfl
      simp only [Core.Control.step, evaluated] at moved
      cases moved
      exact ⟨_, path, .executing _ state related⟩

theorem ControlMatch.advance (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (base : MachineState State)
    (matched : ControlMatch store registry program base source target)
    (moved : Core.Control.step store .leftFirst source = .next middle) :
    ∃ next, Reaches (transition (Compatibility.backend store) registry program) target next ∧
      ControlMatch store registry program base middle next := by
  cases matched with
  | executing body state related =>
      cases body with
      | block body => exact ControlMatch.block_advance store registry program base body state related moved
      | seq first rest =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .executing first state (.next rest related)⟩
      | branch test yes no => exact ControlMatch.branch_advance store registry program base test yes no state related moved
      | loop test body post =>
          obtain ⟨next, path, matched⟩ := ControlMatch.loop_advance store registry program base test body post state related moved
          exact ⟨next, (next_reaches (choice := 0) (by rfl)).trans path, matched⟩
      | break_ =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .break_ state related⟩
      | continue_ =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .continue_ state related⟩
  | testing test body post state related =>
      exact ControlMatch.loop_advance store registry program base test body post state related moved
  | sequence first rest state related =>
      simp only [Core.Control.step] at moved
      cases moved
      exact ⟨_, .refl _, .executing first state related⟩
  | next state related =>
      cases related with
      | root => simp [Core.Control.step] at moved
      | next rest related =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .executing rest state related⟩
      | loop test body post related =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl),
            .sequence (.block post) (.loop test body post) state (.post test body post related)⟩
      | post test body post related =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .testing test body post state related⟩
  | break_ state related =>
      cases related with
      | root => simp [Core.Control.step] at moved
      | next rest related =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .break_ state related⟩
      | loop test body post related =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .next state related⟩
      | post test body post related =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .break_ state related⟩
  | continue_ state related =>
      cases related with
      | root => simp [Core.Control.step] at moved
      | next rest related =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .continue_ state related⟩
      | loop test body post related =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl),
            .sequence (.block post) (.loop test body post) state (.post test body post related)⟩
      | post test body post related =>
          simp only [Core.Control.step] at moved
          cases moved
          exact ⟨_, next_reaches (choice := 0) (by rfl), .continue_ state related⟩
  | halted result state stack executed represented => simp [Core.Control.step] at moved

theorem control_exec_not_done (store : Core.Store Ref Place State) (body : Core.Control.Command Ref Place)
    (stack : List (Core.Control.Frame Ref Place)) (state : State) (result : Core.Control.Observation State) :
    Core.Control.step store .leftFirst (.exec body stack state) ≠ .done result := by
  cases body with
  | block body => cases evaluated : body.eval store .leftFirst state <;> simp [Core.Control.step, evaluated]
  | seq first rest => simp [Core.Control.step]
  | branch test yes no => cases evaluated : test.eval (store.read state) .leftFirst <;> simp [Core.Control.step, evaluated]
  | loop test body post =>
      cases evaluated : test.eval (store.read state) .leftFirst with
      | error bytes => simp [Core.Control.step, evaluated]
      | ok choice => cases choice <;> simp [Core.Control.step, evaluated]
  | break_ => simp [Core.Control.step]
  | continue_ => simp [Core.Control.step]

theorem ControlMatch.terminal (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (base : MachineState State)
    (matched : ControlMatch store registry program base source target)
    (ended : Core.Control.step store .leftFirst source = .done result) :
    ∃ observed, Executes (transition (Compatibility.backend store) registry program) target observed ∧
      controlObservation observed = some result := by
  cases matched with
  | executing body state related => exact False.elim (control_exec_not_done store body _ state result ended)
  | testing test body post state related => exact False.elim (control_exec_not_done store (.loop test body post) _ state result ended)
  | sequence first rest state related => simp [Core.Control.step] at ended
  | next state related =>
      cases related with
      | root =>
          simp only [Core.Control.step, Core.Control.Progress.done.injEq] at ended
          cases ended
          exact ⟨_, ControlStack.next_executes (Compatibility.backend store) registry program _ base, rfl⟩
      | next rest related | loop test body post related | post test body post related =>
          simp [Core.Control.step] at ended
  | break_ state related =>
      cases related with
      | root =>
          simp only [Core.Control.step, Core.Control.Progress.done.injEq] at ended
          cases ended
          refine ⟨.inconclusive .rejected {base with external := state}, ?_, rfl⟩
          exact (next_reaches (choice := 0) (by rfl)).executes (.done (choice := 0) (by rfl))
      | next rest related | loop test body post related | post test body post related =>
          simp [Core.Control.step] at ended
  | continue_ state related =>
      cases related with
      | root =>
          simp only [Core.Control.step, Core.Control.Progress.done.injEq] at ended
          cases ended
          refine ⟨.inconclusive .rejected {base with external := state}, ?_, rfl⟩
          exact (next_reaches (choice := 0) (by rfl)).executes (.done (choice := 0) (by rfl))
      | next rest related | loop test body post related | post test body post related =>
          simp [Core.Control.step] at ended
  | halted outcome state stack executed represented =>
      simp only [Core.Control.step, Core.Control.Progress.done.injEq] at ended
      cases ended
      exact ⟨_, executed, represented⟩

/-- All finite old-control executions, including post/continue and nested break
paths, have actual finite executions of the shared machine. The source proof
is relational: divergent loops need not acquire an arbitrary fuel bound. -/
theorem control_simulates (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (base : MachineState State)
    (executed : Core.Control.Executes store .leftFirst source result)
    (matched : ControlMatch store registry program base source target) :
    ∃ observed, Executes (transition (Compatibility.backend store) registry program) target observed ∧
      controlObservation observed = some result := by
  induction executed generalizing target with
  | done ended => exact matched.terminal store registry program base ended
  | next moved _ ih =>
      obtain ⟨next, path, matched⟩ := matched.advance store registry program base moved
      obtain ⟨observed, tail, represented⟩ := ih matched
      exact ⟨observed, path.executes tail, represented⟩

theorem control_machine (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (body : Core.Control.Command Ref Place)
    (executed : Core.Control.Executes store .leftFirst (.exec body [] state.external) result) :
    ∃ observed, Executes (transition (Compatibility.backend store) registry program)
      (Config.start state (controlBody body)) observed ∧ controlObservation observed = some result := by
  have related : ControlMatch store registry program state (.exec body [] state.external)
      ⟨.exec (control body), [.next (.return_ (some fallthrough))], state, state⟩ :=
    .executing body state.external .root
  obtain ⟨observed, tail, represented⟩ := control_simulates store registry program state executed related
  exact ⟨observed, (next_reaches (choice := 0) (by rfl)).executes tail, represented⟩

theorem control_run (store : Core.Store Ref Place State) (registry : Registry)
    (program : Program (Key Ref Place)) (state : MachineState State) (body : Core.Control.Command Ref Place)
    (executed : Core.Control.Executes store .leftFirst (.exec body [] state.external) result) :
    ∃ fuel choices observed,
      Machine.execute (Compatibility.backend store) registry legacyLimits program fuel choices
        (Config.start state (controlBody body)) = .finished observed ∧ controlObservation observed = some result := by
  obtain ⟨observed, executed, represented⟩ := control_machine store registry program state body executed
  obtain ⟨fuel, choices, finished⟩ := Solidity.Execution.run_complete _ executed
  exact ⟨fuel, choices, observed, finished, represented⟩

end Solidity.Execution.Compatibility
