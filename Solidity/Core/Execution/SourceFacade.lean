/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Admission
import Solidity.Core.Execution.Machine

/-! Checked entry to resolved effectful execution. Admission checks every supplied
function and the whole entry tree before a strategy evaluates any operand.
This interface does not parse Solidity, resolve declarations/overloads, validate
an external ABI, or prove compiler preservation. Reference readiness requiring
an unavailable callee reachability summary stays explicitly unsupported.

Result-bearing functions enter through ordinary call expressions. The statement
entry is a void fragment; it never fabricates named return cells or bypasses
the machine's parameter/result transfer continuations. -/
namespace Solidity.Execution.SourceFacade
open Static
open Aggregates (Result)

def prepareExpression (registry : Registry) (limits : Limits) (program : Program Key)
    (state : MachineState σ) (expression : Expr Key) : Result (Config σ Key) := do
  Admission.checkProgram registry limits.aggregateFuel program
  Admission.admitExpression registry limits.aggregateFuel state.locals expression
  return Config.expression state expression

def prepareStatement (registry : Registry) (limits : Limits) (program : Program Key)
    (state : MachineState σ) (statement : Stmt Key) : Result (Config σ Key) := do
  Admission.checkProgram registry limits.aggregateFuel program
  Admission.admitStatement registry limits.aggregateFuel state.locals [] statement
  return Config.start state statement

def executeExpression (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (program : Program Key) (fuel : Nat) (choices : List Nat) (state : MachineState σ)
    (expression : Expr Key) : Result (Execution (Config σ Key) (Observation σ)) := do
  let config ← prepareExpression registry limits program state expression
  return Machine.execute backend registry limits program fuel choices config

def executeStatement (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (program : Program Key) (fuel : Nat) (choices : List Nat) (state : MachineState σ)
    (statement : Stmt Key) : Result (Execution (Config σ Key) (Observation σ)) := do
  let config ← prepareStatement registry limits program state statement
  return Machine.execute backend registry limits program fuel choices config

def executeFunction (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (program : Program Key) (fuel : Nat) (choices : List Nat) (state : MachineState σ)
    (signature : FunctionSignature) (handle : Nat) (arguments : List (Expr Key)) :
    Result (Execution (Config σ Key) (Observation σ)) :=
  executeExpression backend registry limits program fuel choices state
    (.call signature (.literal ⟨signature.type, some handle⟩) arguments)

theorem executeExpression_of_admitted
    (programChecked : Admission.checkProgram registry limits.aggregateFuel program = .ok ())
    (entryChecked : Admission.admitExpression registry limits.aggregateFuel state.locals expression = .ok ()) :
    executeExpression backend registry limits program fuel choices state expression =
      .ok (Machine.execute backend registry limits program fuel choices (Config.expression state expression)) := by
  simp [executeExpression, prepareExpression, programChecked, entryChecked, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

theorem executeStatement_of_admitted
    (programChecked : Admission.checkProgram registry limits.aggregateFuel program = .ok ())
    (entryChecked : Admission.admitStatement registry limits.aggregateFuel state.locals [] statement = .ok ()) :
    executeStatement backend registry limits program fuel choices state statement =
      .ok (Machine.execute backend registry limits program fuel choices (Config.start state statement)) := by
  simp [executeStatement, prepareStatement, programChecked, entryChecked, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- A successful checked execution carries the actual program/entry check
equations and an execution of the shared machine. No correspondence oracle or
source-preservation assumption is supplied to this theorem. -/
theorem executeExpression_sound
    (completed : executeExpression backend registry limits program fuel choices state expression =
      .ok (.finished observed)) :
    Admission.checkProgram registry limits.aggregateFuel program = .ok () ∧
      Admission.admitExpression registry limits.aggregateFuel state.locals expression = .ok () ∧
      Executes (Machine.step backend registry limits program) (Config.expression state expression) observed := by
  unfold executeExpression prepareExpression at completed
  cases programChecked : Admission.checkProgram registry limits.aggregateFuel program with
  | error failure => simp [programChecked, Bind.bind, Except.bind] at completed
  | ok checked =>
      cases checked
      cases entryChecked : Admission.admitExpression registry limits.aggregateFuel state.locals expression with
      | error failure => simp [programChecked, entryChecked, Bind.bind, Except.bind] at completed
      | ok checked =>
          cases checked
          simp only [programChecked, entryChecked, Bind.bind, Except.bind,
            Pure.pure, Except.pure, Except.ok.injEq] at completed
          exact ⟨rfl, rfl, Machine.execute_sound completed⟩

theorem executeStatement_sound
    (completed : executeStatement backend registry limits program fuel choices state statement =
      .ok (.finished observed)) :
    Admission.checkProgram registry limits.aggregateFuel program = .ok () ∧
      Admission.admitStatement registry limits.aggregateFuel state.locals [] statement = .ok () ∧
      Executes (Machine.step backend registry limits program) (Config.start state statement) observed := by
  unfold executeStatement prepareStatement at completed
  cases programChecked : Admission.checkProgram registry limits.aggregateFuel program with
  | error failure => simp [programChecked, Bind.bind, Except.bind] at completed
  | ok checked =>
      cases checked
      cases entryChecked : Admission.admitStatement registry limits.aggregateFuel state.locals [] statement with
      | error failure => simp [programChecked, entryChecked, Bind.bind, Except.bind] at completed
      | ok checked =>
          cases checked
          simp only [programChecked, entryChecked, Bind.bind, Except.bind,
            Pure.pure, Except.pure, Except.ok.injEq] at completed
          exact ⟨rfl, rfl, Machine.execute_sound completed⟩

/-- Every finite machine execution from an admitted expression has some host
fuel and independent choices accepted by this facade. This is finite-execution
completeness, not a claim that the source program terminates. -/
theorem executeExpression_complete
    (programChecked : Admission.checkProgram registry limits.aggregateFuel program = .ok ())
    (entryChecked : Admission.admitExpression registry limits.aggregateFuel state.locals expression = .ok ())
    (execution : Executes (Machine.step backend registry limits program)
      (Config.expression state expression) observed) :
    ∃ fuel choices, executeExpression backend registry limits program fuel choices state expression =
      .ok (.finished observed) := by
  obtain ⟨fuel, choices, completed⟩ := run_complete _ execution
  exact ⟨fuel, choices, by rw [executeExpression_of_admitted programChecked entryChecked]; exact congrArg Except.ok completed⟩

theorem executeStatement_complete
    (programChecked : Admission.checkProgram registry limits.aggregateFuel program = .ok ())
    (entryChecked : Admission.admitStatement registry limits.aggregateFuel state.locals [] statement = .ok ())
    (execution : Executes (Machine.step backend registry limits program)
      (Config.start state statement) observed) :
    ∃ fuel choices, executeStatement backend registry limits program fuel choices state statement =
      .ok (.finished observed) := by
  obtain ⟨fuel, choices, completed⟩ := run_complete _ execution
  exact ⟨fuel, choices, by rw [executeStatement_of_admitted programChecked entryChecked]; exact congrArg Except.ok completed⟩

end Solidity.Execution.SourceFacade
