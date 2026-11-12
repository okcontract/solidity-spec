/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.ProcedureCalls
import Solidity.Compatibility.Execution.Events
import Solidity.Compatibility.Execution.Blocks

namespace Solidity.Execution.Compatibility
open Core Static
open Aggregates (Failure)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

inductive ProcedureEffect (State : Type) (returns : List Core.Ty) where
  | returned : State → Core.Env returns → List Contract.Interaction.Event → ProcedureEffect State returns
  | failed : Failure → ProcedureEffect State returns

def ProcedureEffect.observe : ProcedureEffect State returns → Option (Core.ProcedureOutcome State returns)
  | .returned state values logs => some (.returned state values logs)
  | .failed (.revert bytes) => some (.reverted bytes)
  | .failed (.panic code) => some (.reverted (Contract.panic code))
  | .failed .exceptional => some .fault
  | .failed _ => none

def ProcedureEffect.prepend (logs : List Contract.Interaction.Event) : ProcedureEffect State returns → ProcedureEffect State returns
  | .returned state values rest => .returned state values (logs ++ rest)
  | .failed failure => .failed failure

theorem ProcedureEffect.observe_prepend (logs : List Contract.Interaction.Event) (effect : ProcedureEffect State returns) :
    (effect.prepend logs).observe = effect.observe.map (Core.ProcedureOutcome.prepend logs) := by
  cases effect with
  | returned => rfl
  | failed failure => cases failure <;> rfl

theorem procedure_failureOfBytes (bytes : List UInt8) :
    (ProcedureEffect.failed (State := State) (returns := returns) (Effects.failureOfBytes bytes)).observe =
      some (.reverted bytes) := by
  cases same : bytes == Contract.panic ((bytes[35]?).getD 0) with
  | false => simp [Effects.failureOfBytes, same, ProcedureEffect.observe]
  | true =>
      have equal : bytes = Contract.panic ((bytes[35]?).getD 0) := by simpa using same
      simp [Effects.failureOfBytes, ProcedureEffect.observe, ← equal]

/-- The exact successful heap/external observation. Scalar legacy execution
can append logs; caller locals and arithmetic mode come from the real saved
call frame. Every other heap component and the host allowance are retained. -/
def procedureState (state : MachineState σ) (external : σ) (logs : List Contract.Interaction.Event)
    (caller : Locals) (mode : ArithmeticMode) : MachineState σ :=
  {state with external, locals := caller, mode, heap := {state.heap with execution := {state.heap.execution with
    world := {state.heap.execution.world with logs := state.heap.execution.world.logs ++ logs}}}}

def ProcedureTrace (backend : Backend State Keys) (registry : Registry) (table : Program Keys)
    (state : MachineState State) (body : Execution.Stmt Keys) : ProcedureEffect State returns → Prop
  | .returned after values logs => ∀ caller mode stack entry,
      Reaches (transition backend registry table)
        ⟨.exec body, .call caller mode (returnBinders 0 returns) :: stack, state, entry⟩
        ⟨.value (Datum.ofPacket (environmentPacket values)), stack,
          procedureState state after logs caller mode, entry⟩
  | .failed failure => isSourceFailure failure = true ∧ ∀ caller mode stack entry,
      Executes (transition backend registry table)
        ⟨.exec body, .call caller mode (returnBinders 0 returns) :: stack, state, entry⟩ (fail entry failure)

variable {State : Type} {Keys : SType → Type} {returns : List Core.Ty}
variable {backend : Backend State Keys} {registry : Registry} {table : Program Keys}
variable {state after : MachineState State} {body tail : Execution.Stmt Keys} {effect : ProcedureEffect State returns}

theorem procedureTrace_prefix (logs : List Contract.Interaction.Event)
    (path : ∀ stack entry, Reaches (transition backend registry table)
      ⟨.exec body, stack, state, entry⟩ ⟨.exec tail, stack, after, entry⟩)
    (states : ∀ final rest caller mode,
      procedureState after final rest caller mode = procedureState state final (logs ++ rest) caller mode)
    (trace : ProcedureTrace backend registry table after tail effect) :
    ProcedureTrace backend registry table state body (effect.prepend logs) := by
  cases effect with
  | returned final values rest =>
      intro caller mode stack entry
      have result := (path (.call caller mode (returnBinders 0 returns) :: stack) entry).trans
        (trace caller mode stack entry)
      simpa only [ProcedureEffect.prepend, states] using result
  | failed failure => exact ⟨trace.1, fun caller mode stack entry =>
      (path (.call caller mode (returnBinders 0 returns) :: stack) entry).executes (trace.2 caller mode stack entry)⟩

theorem procedureTrace_seq (logs : List Contract.Interaction.Event)
    (first : Execution.Stmt Keys)
    (path : ∀ stack entry, Reaches (transition backend registry table)
      ⟨.exec first, stack, state, entry⟩ ⟨.resume .next, stack, after, entry⟩)
    (states : ∀ final rest caller mode,
      procedureState after final rest caller mode = procedureState state final (logs ++ rest) caller mode)
    (trace : ProcedureTrace backend registry table after tail effect) :
    ProcedureTrace backend registry table state (.seq first tail) (effect.prepend logs) := by
  apply procedureTrace_prefix logs (states := states) (trace := trace)
  intro stack entry
  exact (sequence_enter state first tail stack entry).trans
    ((path (.next tail :: stack) entry).trans (sequence_next after tail stack entry))

theorem procedureTrace_seq_failure (first tail : Execution.Stmt Keys) (failure : Failure)
    (source : isSourceFailure failure = true)
    (trace : ∀ stack entry, Executes (transition backend registry table)
      ⟨.exec first, stack, state, entry⟩ (fail entry failure)) :
    ProcedureTrace backend registry table state (.seq first tail) (ProcedureEffect.failed (returns := returns) failure) :=
  ⟨source, fun caller mode stack entry =>
    (sequence_enter state first tail _ entry).executes (trace (.next tail :: .call caller mode (returnBinders 0 returns) :: stack) entry)⟩

theorem procedureState_empty (state : MachineState σ) (external : σ) (caller : Locals) (mode : ArithmeticMode) :
    procedureState state external [] caller mode = {state with external, locals := caller, mode} := by
  simp [procedureState]

theorem procedureState_local (state : MachineState σ) (locals : Locals) (final : σ)
    (logs : List Contract.Interaction.Event) (caller : Locals) (mode : ArithmeticMode) :
    procedureState {state with locals} final logs caller mode = procedureState state final logs caller mode := rfl

theorem procedureState_external (state : MachineState σ) (external final : σ)
    (logs : List Contract.Interaction.Event) (caller : Locals) (mode : ArithmeticMode) :
    procedureState {state with external} final logs caller mode = procedureState state final logs caller mode := rfl

theorem procedureState_compose (state : MachineState σ) (middle final : σ)
    (first rest : List Contract.Interaction.Event) (saved caller : Locals) (oldMode mode : ArithmeticMode) :
    procedureState (procedureState state middle first saved oldMode) final rest caller mode =
      procedureState state final (first ++ rest) caller mode := by simp [procedureState, List.append_assoc]

end Solidity.Execution.Compatibility
