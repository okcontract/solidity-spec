/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.SourceFacade

/-! The resolved-program boundary checks once and retains the equations.
Tokens are indexed by the exact registry, limits, program, state and tree; they
cannot be reused after changing an input. They certify resolved admission, not
source parsing, physical heap representation, termination or compiler adequacy.

Conversions remain at the operation that owns their effects: raw arguments
precede callee/parameter conversion, and tuple conversion follows raw component
evaluation. Preparation never hoists a conversion or chooses an operand order.
-/
namespace Solidity.Execution.Checked
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure
variable {Key : SType → Type} {σ : Type}

structure Program (registry : Registry) (limits : Limits)
    (program : Execution.Program Key) : Type where
  admitted : Admission.checkProgram registry limits.aggregateFuel program = .ok ()

structure Expression (registry : Registry) (limits : Limits)
    (program : Execution.Program Key) (state : MachineState σ) (expression : Expr Key) : Type where
  programChecked : Program registry limits program
  admitted : Admission.admitExpression registry limits.aggregateFuel state.locals expression = .ok ()

structure Statement (registry : Registry) (limits : Limits)
    (program : Execution.Program Key) (state : MachineState σ) (statement : Stmt Key) : Type where
  programChecked : Program registry limits program
  admitted : Admission.admitStatement registry limits.aggregateFuel state.locals [] statement = .ok ()

def checkProgram (registry : Registry) (limits : Limits) (program : Execution.Program Key) :
    Result (Program registry limits program) :=
  match equation : Admission.checkProgram registry limits.aggregateFuel program with
  | .error failure => .error failure
  | .ok () => .ok ⟨equation⟩

variable {registry : Registry} {limits : Limits} {program : Execution.Program Key}

def Program.expression (checked : Program registry limits program) (state : MachineState σ)
    (expression : Expr Key) : Result (Expression registry limits program state expression) :=
  match equation : Admission.admitExpression registry limits.aggregateFuel state.locals expression with
  | .error failure => .error failure
  | .ok () => .ok ⟨checked, equation⟩

def Program.statement (checked : Program registry limits program) (state : MachineState σ)
    (statement : Stmt Key) : Result (Statement registry limits program state statement) :=
  match equation : Admission.admitStatement registry limits.aggregateFuel state.locals [] statement with
  | .error failure => .error failure
  | .ok () => .ok ⟨checked, equation⟩

def prepareExpression (registry : Registry) (limits : Limits) (program : Execution.Program Key)
    (state : MachineState σ) (expression : Expr Key) :
    Result (Expression registry limits program state expression) := do
  let checked ← checkProgram registry limits program
  checked.expression state expression

def prepareStatement (registry : Registry) (limits : Limits) (program : Execution.Program Key)
    (state : MachineState σ) (statement : Stmt Key) :
    Result (Statement registry limits program state statement) := do
  let checked ← checkProgram registry limits program
  checked.statement state statement

variable {state : MachineState σ} {expression : Expr Key} {statement : Stmt Key}

def Expression.config (_ : Expression registry limits program state expression) : Config σ Key :=
  Config.expression state expression

def Statement.config (_ : Statement registry limits program state statement) : Config σ Key :=
  Config.start state statement

def Expression.execute (checked : Expression registry limits program state expression)
    (backend : Backend σ Key) (fuel : Nat) (choices : List Nat) :
    Execution (Config σ Key) (Observation σ) :=
  Machine.execute backend registry limits program fuel choices checked.config

def Statement.execute (checked : Statement registry limits program state statement)
    (backend : Backend σ Key) (fuel : Nat) (choices : List Nat) :
    Execution (Config σ Key) (Observation σ) :=
  Machine.execute backend registry limits program fuel choices checked.config

theorem expression_facade (checked : Expression registry limits program state expression) :
    SourceFacade.executeExpression backend registry limits program fuel choices state expression =
      .ok (checked.execute backend fuel choices) := by
  exact SourceFacade.executeExpression_of_admitted checked.programChecked.admitted checked.admitted

theorem statement_facade (checked : Statement registry limits program state statement) :
    SourceFacade.executeStatement backend registry limits program fuel choices state statement =
      .ok (checked.execute backend fuel choices) := by
  exact SourceFacade.executeStatement_of_admitted checked.programChecked.admitted checked.admitted

theorem prepareExpression_config :
    (prepareExpression registry limits program state expression).map Expression.config =
      SourceFacade.prepareExpression registry limits program state expression := by
  unfold prepareExpression checkProgram
  split
  · rename_i failure equation
    simp [SourceFacade.prepareExpression, equation, Except.map]
  · rename_i equation
    simp only [Bind.bind, Except.bind]
    unfold Program.expression
    split <;> simp_all [SourceFacade.prepareExpression, Expression.config, Except.map]

theorem prepareStatement_config :
    (prepareStatement registry limits program state statement).map Statement.config =
      SourceFacade.prepareStatement registry limits program state statement := by
  unfold prepareStatement checkProgram
  split
  · rename_i failure equation
    simp [SourceFacade.prepareStatement, equation, Except.map]
  · rename_i equation
    simp only [Bind.bind, Except.bind]
    unfold Program.statement
    split <;> simp_all [SourceFacade.prepareStatement, Statement.config, Except.map]

end Solidity.Execution.Checked
