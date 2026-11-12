/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Machine
import Solidity.Core.Execution.TransitionRelations
import Solidity.Core.Execution.SyntaxLaws

namespace Solidity.Execution.Machine
open Static
open Core (ArithmeticMode)
open Aggregates (Failure)

variable {σ : Type} {Key : SType → Type}
variable {backend : Backend σ Key} {registry : Registry} {limits : Limits}
variable {program : Program Key} {choice : Nat} {config : Config σ Key} {failure : Failure}

theorem failure_restores (failed : transition backend registry limits program choice config = .error failure)
    (semantic : isSourceFailure failure = true) :
    step backend registry limits program choice config = .done (.failed failure config.entry) := by
  cases failure <;> simp_all [step, fail, isSourceFailure]

theorem inconclusive_preserves_partial_state
    (failed : transition backend registry limits program choice config = .error failure)
    (model : isSourceFailure failure = false) (notExhausted : failure ≠ .exhausted) :
    step backend registry limits program choice config = .done (.inconclusive failure config.state) := by
  cases failure <;> simp_all [step, isSourceFailure]

theorem primitive_exhaustion_suspends
    (failed : transition backend registry limits program choice config = .error .exhausted) :
    step backend registry limits program choice config = .suspended config := by
  simp [step, failed]

theorem host_limit_suspends
    (transitioned : transition backend registry limits program choice config = .ok (.next after))
    (bound : limits.hostContinuationLimit = some maximum) (exceeded : maximum < after.stack.length) :
    step backend registry limits program choice config = .suspended config := by
  simp [step, transitioned, bound, exceeded]

theorem target_limit_separate
    (transitioned : step backend registry limits program choice config = .next after)
    (observed : policy config after = some resource) :
    targetStep policy backend registry limits program choice config = .done (.resourceLimit resource config.entry) := by
  simp [targetStep, transitioned, observed]

theorem scope_enter (state : MachineState σ) (entry : MachineState σ) (body : Stmt Key)
    (stack : List (Frame Key)) :
    transition backend registry limits program choice ⟨.exec (.block body), stack, state, entry⟩ =
      .ok (.next ⟨.exec body, .scope :: stack, {state with locals := state.locals.enter}, entry⟩) := rfl

/-- Exit removes the inner cells from the updated environment, not from an
old snapshot. The law covers normal, break, continue and return unwinding. -/
theorem scope_exit (state : MachineState σ) (entry : MachineState σ) (signal : Signal)
    (stack : List (Frame Key)) (left : state.locals.leave = .ok locals) :
    transition backend registry limits program choice ⟨.resume signal, .scope :: stack, state, entry⟩ =
      .ok (.next ⟨.resume signal, stack, {state with locals}, entry⟩) := by
  simp [transition, left, next, Bind.bind, Except.bind]

theorem mode_exit (state : MachineState σ) (entry : MachineState σ) (signal : Signal)
    (stack : List (Frame Key)) (mode : ArithmeticMode) :
    transition backend registry limits program choice ⟨.resume signal, .mode mode :: stack, state, entry⟩ =
      .ok (.next ⟨.resume signal, stack, {state with mode}, entry⟩) := rfl

theorem continue_runs_post (state : MachineState σ) (entry : MachineState σ)
    (stack : List (Frame Key)) (test : Expr Key) (body post : Stmt Key) :
    transition backend registry limits program choice
      ⟨.resume .continue_, .loopBody test body post :: stack, state, entry⟩ =
      .ok (.next ⟨.exec post, .loopPost test body post :: stack, state, entry⟩) := rfl

theorem break_skips_post (state : MachineState σ) (entry : MachineState σ)
    (stack : List (Frame Key)) (test : Expr Key) (body post : Stmt Key) :
    transition backend registry limits program choice
      ⟨.resume .break_, .loopBody test body post :: stack, state, entry⟩ =
      .ok (.next ⟨.resume .next, stack, state, entry⟩) := rfl

theorem doWhile_body_first (state : MachineState σ) (entry : MachineState σ)
    (stack : List (Frame Key)) (test : Expr Key) (body : Stmt Key) :
    transition backend registry limits program choice ⟨.exec (.doWhile body test), stack, state, entry⟩ =
      .ok (.next ⟨.exec body, .doBody body test :: stack, state, entry⟩) := rfl

theorem doWhile_continue_tests (state : MachineState σ) (entry : MachineState σ)
    (stack : List (Frame Key)) (test : Expr Key) (body : Stmt Key) :
    transition backend registry limits program choice
      ⟨.resume .continue_, .doBody body test :: stack, state, entry⟩ =
      .ok (.next ⟨.eval test, .doCondition body test :: stack, state, entry⟩) := rfl

theorem return_preserves_heap_and_restores_frame
    (config : Config σ Key) (locals : Locals) (mode : ArithmeticMode) (returns : List Binder)
    (stack : List (Frame Key)) (collected : collectResults config.state.locals returns = .ok values) :
    finishCall config locals mode returns stack =
      .ok (.next {config with task := .value (Datum.ofPacket values), stack, state := {config.state with locals, mode}}) := by
  simp [finishCall, collected, next, Bind.bind, Except.bind]

/-- Permitted internal function conversions change only the mutability view;
the handle, including the null handle, is preserved. -/
theorem callee_conversion (actual expected : FunctionSignature) (handle : Option Nat)
    (permitted : actual.accepts expected = true) :
    Effects.scalarCast .implicit expected.type ⟨actual.type, handle⟩ = .ok ⟨expected.type, handle⟩ := by
  obtain ⟨parameters, returns, mutability⟩ := (FunctionSignature.accepts_iff actual expected).mp permitted
  cases actual with
  | mk actualMutability actualParameters actualReturns =>
      cases expected with
      | mk expectedMutability expectedParameters expectedReturns =>
          simp only at parameters returns mutability
          subst expectedParameters expectedReturns
          cases actualMutability <;> cases expectedMutability <;>
            simp_all [Mutability.Allows, Effects.scalarCast, FunctionSignature.type, Static.allows,
              Static.implicit, Static.convert, SType.scalarSupported, Static.coerce, Effects.liftConversion]
          all_goals rfl

/-- Calls always begin checked, while parameter/result allocation and reference
transfer share the caller's heap and materialization allowance. -/
theorem call_enters_checked
    (config : Config σ Key) (signature : FunctionSignature) (handle : Nat)
    (definition : FunctionDefinition Key)
    (resolved : program.lookup handle = .ok definition)
    (matching : definition.signature.accepts signature = true)
    (preparedArguments : prepareArguments registry limits config.state
      (typesList signature.parameters) arguments = .ok (converted, prepared))
    (argumentsBound : bindArguments backend registry limits
      {prepared with locals := Locals.empty, mode := .checked} definition.parameters converted = .ok bound)
    (resultsInitialized : definition.returns.foldlM (declareReturn registry limits) bound = .ok entered) :
    invoke backend registry limits program config signature ⟨signature.type, some handle⟩ arguments =
      .ok (.next {config with task := .exec definition.body, state := entered, stack := .call config.state.locals config.state.mode definition.returns :: config.stack}) := by
  cases signature with
  | mk mutability parameters returns =>
      have converted := callee_conversion ⟨mutability, parameters, returns⟩ ⟨mutability, parameters, returns⟩
        (some handle) (by simp [FunctionSignature.accepts, Mutability.allows_iff, Mutability.Allows])
      simp only [invoke, converted, Bind.bind, Except.bind]
      simp [FunctionSignature.type, preparedArguments, resolved, matching,
        argumentsBound, resultsInitialized, next, Pure.pure, Except.pure]

/-- Admission may expose a function under a permitted wider mutability type.
That conversion precedes parameter conversion; null dispatch still happens
after parameters have been converted by the ordinary invocation path. -/
theorem invoke_converted_callee (config : Config σ Key) (actual expected : FunctionSignature)
    (handle : Option Nat) (arguments : Packet) (permitted : actual.accepts expected = true) :
    invoke backend registry limits program config expected ⟨actual.type, handle⟩ arguments =
      invoke backend registry limits program config expected ⟨expected.type, handle⟩ arguments := by
  have converted := callee_conversion actual expected handle permitted
  have identity := callee_conversion expected expected handle
    (by simp [FunctionSignature.accepts, Mutability.allows_iff, Mutability.Allows])
  simp only [invoke, converted, identity]

/-- A simple source loop has an infinite transition witness. No theorem asks
that all source loops or recursive functions terminate. -/
def loopPhase (state : MachineState σ) (index : Nat) : Config σ Key :=
  let test : Expr Key := .literal ⟨.bool, true⟩
  match index % 7 with
  | 0 => ⟨.loopTest test .skip .skip, [], state, state⟩
  | 1 => ⟨.eval test, [.loopCondition test .skip .skip], state, state⟩
  | 2 => ⟨.value (.atom ⟨.bool, true⟩), [.loopCondition test .skip .skip], state, state⟩
  | 3 => ⟨.exec .skip, [.loopBody test .skip .skip], state, state⟩
  | 4 => ⟨.resume .next, [.loopBody test .skip .skip], state, state⟩
  | 5 => ⟨.exec .skip, [.loopPost test .skip .skip], state, state⟩
  | _ => ⟨.resume .next, [.loopPost test .skip .skip], state, state⟩

theorem loopPhase_step (state : MachineState σ) (index : Nat) :
    step backend registry {} program 0 (loopPhase (Key := Key) state index) =
      .next (loopPhase state (index + 1)) := by
  have bounded : index % 7 < 7 := Nat.mod_lt _ (by decide)
  have cases : index % 7 = 0 ∨ index % 7 = 1 ∨ index % 7 = 2 ∨ index % 7 = 3 ∨
      index % 7 = 4 ∨ index % 7 = 5 ∨ index % 7 = 6 := by omega
  rcases cases with h | h | h | h | h | h | h <;>
    simp [loopPhase, Nat.add_mod, h, step, transition, next, boolean, Datum.asAtom,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem whileTrue_diverges (state : MachineState σ) :
    Diverges (step backend registry {} program) (loopPhase (Key := Key) state 0) := by
  exact ⟨loopPhase state, fun _ => 0, rfl, loopPhase_step state⟩

end Solidity.Execution.Machine
