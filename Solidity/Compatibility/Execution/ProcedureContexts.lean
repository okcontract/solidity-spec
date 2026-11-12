/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.State
import Solidity.Compatibility.Execution.Vectors

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

variable {σ : Type} {Keys : SType → Type}
variable {backend : Backend σ Keys} {registry : Registry} {program : Program Keys}

theorem sequence_enter (state : MachineState σ) (first rest : Execution.Stmt Keys)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.exec (.seq first rest), stack, state, entry⟩
      ⟨.exec first, .next rest :: stack, state, entry⟩ := next_reaches (choice := 0) rfl

theorem sequence_next (state : MachineState σ) (rest : Execution.Stmt Keys)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.resume .next, .next rest :: stack, state, entry⟩
      ⟨.exec rest, stack, state, entry⟩ := next_reaches (choice := 0) rfl

theorem branch_prefix (state : MachineState σ) (test : Execution.Expr Keys) (yes no : Execution.Stmt Keys)
    (choice : Bool) (evaluated : PureResult backend registry program state test (.ok (.atom (scalar .bool choice))))
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.exec (.if_ test yes no), stack, state, entry⟩
      ⟨.exec (if choice then yes else no), stack, state, entry⟩ := by
  have start : Reaches (transition backend registry program)
      ⟨.exec (.if_ test yes no), stack, state, entry⟩
      ⟨.eval test, .branch yes no :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  apply start.trans ((evaluated (.branch yes no :: stack) entry).trans ?_)
  exact next_reaches (choice := 0) rfl

theorem branch_failure (state : MachineState σ) (test : Execution.Expr Keys) (yes no : Execution.Stmt Keys)
    (failure : Aggregates.Failure) (evaluated : PureResult backend registry program state test (.error failure))
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Executes (transition backend registry program)
      ⟨.exec (.if_ test yes no), stack, state, entry⟩ (fail entry failure) := by
  have start : Reaches (transition backend registry program)
      ⟨.exec (.if_ test yes no), stack, state, entry⟩
      ⟨.eval test, .branch yes no :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  exact start.executes (evaluated (.branch yes no :: stack) entry)

theorem store_prefix (store : Core.Store Ref Place State) (registry : Registry) (program : Program (Key Ref Place))
    (state : MachineState State) (place : Place type) (expression : Execution.Expr (Key Ref Place))
    (value : type.Value) (after : State)
    (evaluated : PureResult (Compatibility.backend store) registry program state expression (.ok (.atom (scalar type value))))
    (written : store.write state.external place value = some after)
    (stack : List (Frame (Key Ref Place))) (entry : MachineState State) :
    Reaches (transition (Compatibility.backend store) registry program)
      ⟨.exec (.storeExternal (Key.place place) expression), stack, state, entry⟩
      ⟨.resume .next, stack, {state with external := after}, entry⟩ := by
  have start : Reaches (transition (Compatibility.backend store) registry program)
      ⟨.exec (.storeExternal (Key.place place) expression), stack, state, entry⟩
      ⟨.eval expression, .storeExternal (Key.place place) :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  apply start.trans ((evaluated (.storeExternal (Key.place place) :: stack) entry).trans ?_)
  apply next_reaches (choice := 0)
  simp [Machine.transition, Datum.asAtom, write_external, written, Machine.next]

theorem store_fault (store : Core.Store Ref Place State) (registry : Registry) (program : Program (Key Ref Place))
    (state : MachineState State) (place : Place type) (expression : Execution.Expr (Key Ref Place)) (value : type.Value)
    (evaluated : PureResult (Compatibility.backend store) registry program state expression (.ok (.atom (scalar type value))))
    (written : store.write state.external place value = none)
    (stack : List (Frame (Key Ref Place))) (entry : MachineState State) :
    Executes (transition (Compatibility.backend store) registry program)
      ⟨.exec (.storeExternal (Key.place place) expression), stack, state, entry⟩ (fail entry .exceptional) := by
  have start : Reaches (transition (Compatibility.backend store) registry program)
      ⟨.exec (.storeExternal (Key.place place) expression), stack, state, entry⟩
      ⟨.eval expression, .storeExternal (Key.place place) :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  apply start.executes ((evaluated (.storeExternal (Key.place place) :: stack) entry).executes ?_)
  apply failed_executes (choice := 0) (sourceFailure := rfl)
  simp [Machine.transition, Datum.asAtom, write_external, written]

theorem store_failure (state : MachineState σ) (key : Keys type) (expression : Execution.Expr Keys)
    (failure : Aggregates.Failure) (evaluated : PureResult backend registry program state expression (.error failure))
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Executes (transition backend registry program)
      ⟨.exec (.storeExternal key expression), stack, state, entry⟩ (fail entry failure) := by
  have start : Reaches (transition backend registry program)
      ⟨.exec (.storeExternal key expression), stack, state, entry⟩
      ⟨.eval expression, .storeExternal key :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  exact start.executes (evaluated (.storeExternal key :: stack) entry)

theorem declare_prefix (state after : MachineState σ) (binders : List (Option Binder))
    (expression : Execution.Expr Keys) (value : Datum)
    (evaluated : PureResult backend registry program state expression (.ok value))
    (declared : Machine.declareValues backend registry legacyLimits state binders value.asPacket = .ok after)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.exec (.declare binders (some expression)), stack, state, entry⟩
      ⟨.resume .next, stack, after, entry⟩ := by
  have start : Reaches (transition backend registry program)
      ⟨.exec (.declare binders (some expression)), stack, state, entry⟩
      ⟨.eval expression, .declare binders :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  apply start.trans ((evaluated (.declare binders :: stack) entry).trans ?_)
  apply next_reaches (choice := 0)
  simp [Machine.transition, declared, Machine.next]

theorem declare_failure (state : MachineState σ) (binders : List (Option Binder))
    (expression : Execution.Expr Keys) (failure : Aggregates.Failure)
    (evaluated : PureResult backend registry program state expression (.error failure))
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Executes (transition backend registry program)
      ⟨.exec (.declare binders (some expression)), stack, state, entry⟩ (fail entry failure) := by
  have start : Reaches (transition backend registry program)
      ⟨.exec (.declare binders (some expression)), stack, state, entry⟩
      ⟨.eval expression, .declare binders :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  exact start.executes (evaluated (.declare binders :: stack) entry)

end Solidity.Execution.Compatibility
