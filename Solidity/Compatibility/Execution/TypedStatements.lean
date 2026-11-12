/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.ProcedureRoot
import Solidity.Proofs.TypedStatements

/-! The previous typed-statement compatibility endpoint is attached to actual
executions of the shared machine. The exact old store, result environment,
events and rollback outcomes are retained; no physical-slot injection or
well-formed raw-store premise is introduced. -/
namespace Solidity.Compatibility.Typed
open Core Execution Static
open Execution.Compatibility

theorem statement_machine (stmt : Contract.Stmt slots rs ts) (state : Contract.Storage slots)
    (ctx : Contract.Context) (env : Contract.Env ts) (registry : Registry) :
    ∃ observed,
      Executes (transition (backend (frameStore ctx)) registry (procedureProgram (procedure stmt)))
        (procedureConfig (procedure stmt) (initial state (environment env) ctx.self) (environment env)) observed ∧
      procedureObservation (types rs) observed = some (procedureOutcome (stmt.eval state ctx env)) := by
  obtain ⟨observed, executed, represented⟩ := procedure_machine (frameStore ctx) registry ctx.self (procedure stmt)
    (initial state (environment env) ctx.self) (environment env) rfl rfl rfl
  exact ⟨observed, executed, represented.trans (congrArg some (procedure_eval stmt state ctx env))⟩

theorem statement_run (stmt : Contract.Stmt slots rs ts) (state : Contract.Storage slots)
    (ctx : Contract.Context) (env : Contract.Env ts) (registry : Registry) :
    ∃ fuel choices observed,
      Machine.execute (backend (frameStore ctx)) registry legacyLimits (procedureProgram (procedure stmt)) fuel choices
        (procedureConfig (procedure stmt) (initial state (environment env) ctx.self) (environment env)) = .finished observed ∧
      procedureObservation (types rs) observed = some (procedureOutcome (stmt.eval state ctx env)) := by
  obtain ⟨observed, executed, represented⟩ := statement_machine stmt state ctx env registry
  obtain ⟨fuel, choices, finished⟩ := Solidity.Execution.run_complete _ executed
  exact ⟨fuel, choices, observed, finished, represented⟩

/-- Existing source postconditions retain their full original outcome. The
machine execution is an additional proved witness, not a narrower premise. -/
theorem statement_postcondition_machine (stmt : Contract.Stmt slots rs ts) (state : Contract.Storage slots)
    (ctx : Contract.Context) (env : Contract.Env ts) (registry : Registry)
    (postcondition : Contract.Outcome slots rs → Prop) (checked : postcondition (stmt.eval state ctx env)) :
    postcondition (stmt.eval state ctx env) ∧
      ∃ observed,
        Executes (transition (backend (frameStore ctx)) registry (procedureProgram (procedure stmt)))
          (procedureConfig (procedure stmt) (initial state (environment env) ctx.self) (environment env)) observed ∧
        procedureObservation (types rs) observed = some (procedureOutcome (stmt.eval state ctx env)) :=
  ⟨checked, statement_machine stmt state ctx env registry⟩

end Solidity.Compatibility.Typed
