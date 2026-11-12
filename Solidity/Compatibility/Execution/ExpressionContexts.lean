/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Scalar
import Solidity.Core.Execution.TransitionRelations
import Solidity.Core.Execution.Machine

/-! Actual transition prefixes for compositional scalar-expression proofs.
Compatibility uses no target-stack cap; interpreter fuel remains explicit. -/
namespace Solidity.Execution.Compatibility
open Core Static
open Aggregates (Failure)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def legacyLimits : Limits := {aggregateFuel := 1}

abbrev transition (backend : Backend σ Keys) (registry : Registry) (program : Program Keys) :=
  Machine.step backend registry legacyLimits program

variable {σ : Type} {Keys : SType → Type}
variable {backend : Backend σ Keys} {registry : Registry} {program : Program Keys}

theorem next_reaches
    (moved : Machine.transition backend registry legacyLimits program choice before = .ok (.next after)) :
    Reaches (transition backend registry program) before after := by
  apply Reaches.single (choice := choice)
  change Machine.step backend registry legacyLimits program choice before = .next after
  rw [Machine.step, moved]
  rfl

theorem failed_executes {config : Config σ Keys} {failure : Failure}
    (failed : Machine.transition backend registry legacyLimits program choice config = .error failure)
    (sourceFailure : isSourceFailure failure = true) :
    Executes (transition backend registry program) config (fail config.entry failure) := by
  apply Executes.done (choice := choice)
  change Machine.step backend registry legacyLimits program choice config = .done (fail config.entry failure)
  rw [Machine.step, failed]
  cases failure <;> simp_all [isSourceFailure]

theorem literal_reaches (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (config : Config σ Keys) (value : Value) :
    Reaches (transition backend registry program)
      {config with task := .eval (.literal value)} {config with task := .value (.atom value)} := by
  apply next_reaches (choice := 0)
  rfl

theorem external_reaches (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (config : Config σ Keys) (key : Keys type) (value : type.Value)
    (read : backend.read config.state.external key = .ok value) :
    Reaches (transition backend registry program)
      {config with task := .eval (.externalRead key)} {config with task := .value (.atom ⟨type, value⟩)} := by
  apply next_reaches (choice := 0)
  simp [Machine.transition, read, Machine.next]

theorem mode_enter (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (config : Config σ Keys) (mode : ArithmeticMode) (value : Execution.Expr Keys) :
    Reaches (transition backend registry program)
      {config with task := .eval (.arithmetic mode value)}
      {config with task := .eval value, state := {config.state with mode}, stack := .mode config.state.mode :: config.stack} := by
  apply next_reaches (choice := 0)
  rfl

theorem mode_leave (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (config : Config σ Keys) (mode : ArithmeticMode) (value : Datum) :
    Reaches (transition backend registry program)
      {config with task := .value value, stack := .mode mode :: config.stack}
      {config with task := .value value, state := {config.state with mode}} := by
  apply next_reaches (choice := 0)
  rfl

theorem collect_cons (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (config : Config σ Keys) (index : Nat) (expression : Execution.Expr Keys)
    (rest : List (Nat × Execution.Expr Keys)) (values : List (Nat × Datum)) (finish : Completion) :
    Reaches (transition backend registry program)
      {config with task := .collect ((index, expression) :: rest) values finish}
      {config with task := .eval expression, stack := .collect index rest values finish :: config.stack} := by
  apply next_reaches (choice := 0)
  simp [Machine.transition, Machine.pick, Machine.next]

theorem collected_value (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (config : Config σ Keys) (index : Nat) (value : Datum)
    (rest : List (Nat × Execution.Expr Keys)) (values : List (Nat × Datum)) (finish : Completion) :
    Reaches (transition backend registry program)
      {config with task := .value value, stack := .collect index rest values finish :: config.stack}
      {config with task := .collect rest ((index, value) :: values) finish} := by
  apply next_reaches (choice := 0)
  rfl

theorem collect_empty (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (config : Config σ Keys) (values : List (Nat × Datum)) (finish : Completion) :
    Reaches (transition backend registry program)
      {config with task := .collect [] values finish}
      {config with task := .apply finish (Machine.ordered values)} := by
  apply next_reaches (choice := 0)
  rfl

def PureResult (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (state : MachineState σ) (expression : Execution.Expr Keys) : Aggregates.Result Datum → Prop
  | .ok value => ∀ stack entry, Reaches (transition backend registry program)
      ⟨.eval expression, stack, state, entry⟩ ⟨.value value, stack, state, entry⟩
  | .error failure => ∀ stack entry, Executes (transition backend registry program)
      ⟨.eval expression, stack, state, entry⟩ (fail entry failure)

theorem collect_success (state : MachineState σ) (expression : Execution.Expr Keys) (value : Datum)
    (evaluated : PureResult backend registry program state expression (.ok value))
    (index : Nat) (rest : List (Nat × Execution.Expr Keys)) (values : List (Nat × Datum))
    (finish : Completion) (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.collect ((index, expression) :: rest) values finish, stack, state, entry⟩
      ⟨.collect rest ((index, value) :: values) finish, stack, state, entry⟩ := by
  let config : Config σ Keys := ⟨.eval expression, stack, state, entry⟩
  exact (collect_cons backend registry program config index expression rest values finish).trans
    ((evaluated (.collect index rest values finish :: stack) entry).trans
      (collected_value backend registry program config index value rest values finish))

theorem collect_failure (state : MachineState σ) (expression : Execution.Expr Keys) (failure : Failure)
    (evaluated : PureResult backend registry program state expression (.error failure))
    (index : Nat) (rest : List (Nat × Execution.Expr Keys)) (values : List (Nat × Datum))
    (finish : Completion) (stack : List (Frame Keys)) (entry : MachineState σ) :
    Executes (transition backend registry program)
      ⟨.collect ((index, expression) :: rest) values finish, stack, state, entry⟩ (fail entry failure) := by
  let config : Config σ Keys := ⟨.eval expression, stack, state, entry⟩
  exact (collect_cons backend registry program config index expression rest values finish).executes
    (evaluated (.collect index rest values finish :: stack) entry)

/-- A successful one-child group reaches its actual primitive application.
The first premise is a single concrete syntax-dispatch equation. -/
theorem one_prefix (state : MachineState σ) (expression child : Execution.Expr Keys) (value : Datum)
    (evaluated : PureResult backend registry program state child (.ok value)) (finish : Completion)
    (started : ∀ stack entry, Machine.transition backend registry legacyLimits program 0
      ⟨.eval expression, stack, state, entry⟩ = .ok (.next ⟨.collect [(0, child)] [] finish, stack, state, entry⟩))
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.eval expression, stack, state, entry⟩ ⟨.apply finish [value], stack, state, entry⟩ := by
  let config : Config σ Keys := ⟨.eval expression, stack, state, entry⟩
  exact (next_reaches (started stack entry)).trans
    ((collect_success state child value evaluated 0 [] [] finish stack entry).trans
      (collect_empty backend registry program config [(0, value)] finish))

theorem one_failure (state : MachineState σ) (expression child : Execution.Expr Keys) (failure : Failure)
    (evaluated : PureResult backend registry program state child (.error failure)) (finish : Completion)
    (started : ∀ stack entry, Machine.transition backend registry legacyLimits program 0
      ⟨.eval expression, stack, state, entry⟩ = .ok (.next ⟨.collect [(0, child)] [] finish, stack, state, entry⟩)) :
    PureResult backend registry program state expression (.error failure) := by
  intro stack entry
  exact (next_reaches (started stack entry)).executes
    (collect_failure state child failure evaluated 0 [] [] finish stack entry)

theorem two_prefix (state : MachineState σ) (expression left right : Execution.Expr Keys)
    (a b : Datum) (first : PureResult backend registry program state left (.ok a))
    (second : PureResult backend registry program state right (.ok b)) (finish : Completion)
    (started : ∀ stack entry, Machine.transition backend registry legacyLimits program 0
      ⟨.eval expression, stack, state, entry⟩ =
        .ok (.next ⟨.collect [(0, left), (1, right)] [] finish, stack, state, entry⟩))
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.eval expression, stack, state, entry⟩ ⟨.apply finish [a, b], stack, state, entry⟩ := by
  let config : Config σ Keys := ⟨.eval expression, stack, state, entry⟩
  exact (next_reaches (started stack entry)).trans
    ((collect_success state left a first 0 [(1, right)] [] finish stack entry).trans
      ((collect_success state right b second 1 [] [(0, a)] finish stack entry).trans
        (collect_empty backend registry program config [(1, b), (0, a)] finish)))

theorem two_first_failure (state : MachineState σ) (expression left right : Execution.Expr Keys)
    (failure : Failure) (first : PureResult backend registry program state left (.error failure)) (finish : Completion)
    (started : ∀ stack entry, Machine.transition backend registry legacyLimits program 0
      ⟨.eval expression, stack, state, entry⟩ =
        .ok (.next ⟨.collect [(0, left), (1, right)] [] finish, stack, state, entry⟩)) :
    PureResult backend registry program state expression (.error failure) := by
  intro stack entry
  exact (next_reaches (started stack entry)).executes
    (collect_failure state left failure first 0 [(1, right)] [] finish stack entry)

theorem two_second_failure (state : MachineState σ) (expression left right : Execution.Expr Keys)
    (a : Datum) (failure : Failure) (first : PureResult backend registry program state left (.ok a))
    (second : PureResult backend registry program state right (.error failure)) (finish : Completion)
    (started : ∀ stack entry, Machine.transition backend registry legacyLimits program 0
      ⟨.eval expression, stack, state, entry⟩ =
        .ok (.next ⟨.collect [(0, left), (1, right)] [] finish, stack, state, entry⟩)) :
    PureResult backend registry program state expression (.error failure) := by
  intro stack entry
  exact (next_reaches (started stack entry)).executes
    ((collect_success state left a first 0 [(1, right)] [] finish stack entry).executes
      (collect_failure state right failure second 1 [] [(0, a)] finish stack entry))

end Solidity.Execution.Compatibility
