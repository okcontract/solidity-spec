/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.ProcedureLocals
import Solidity.Compatibility.Execution.Tables
import Solidity.Core.Execution.MachineProofs

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure
variable {σ : Type} {Keys : SType → Type}
variable {table : Program Keys} {parent child : Translation Keys}

/-- A concrete closed table resolves all helpers emitted by this translation.
The root construction below discharges this relation from checked table lookup. -/
def ContainsTranslation (table : Program Keys) (compiled : Translation Keys) : Prop :=
  ∀ entry ∈ compiled.functions, table.lookup entry.1 = .ok entry.2

theorem ContainsTranslation.subset (contains : ContainsTranslation table parent)
    (included : ∀ entry ∈ child.functions, entry ∈ parent.functions) : ContainsTranslation table child :=
  fun entry member => contains entry (included entry member)

def calleeState (state : MachineState σ) (environment : Core.Env types) (returns : List Core.Ty) : MachineState σ :=
  {state with locals := [(returnScope 0 returns).reverse ++ (localScope environment).reverse], mode := .checked}

theorem calleeState_frame (state : MachineState σ) (environment : Core.Env types) (returns : List Core.Ty) :
    FrameEnv (calleeState state environment returns).locals environment :=
  returnScope_frame (reversedLocalEnv_frame environment) returns 0

theorem calleeState_returns (state : MachineState σ) (environment : Core.Env types) (returns : List Core.Ty) :
    ReturnTypes (calleeState state environment returns).locals 0 returns :=
  returnScope_types returns 0 _ []

theorem typesList_ofList (types : List SType) : typesList (Types.ofList types) = types := by
  induction types <;> simp [typesList, Types.ofList, *]

theorem signature_accepts_self (parameters returns : List Core.Ty) :
    (signature parameters returns).accepts (signature parameters returns) = true := by
  simp [FunctionSignature.accepts, signature, Mutability.allows]

theorem invoke_procedure (backend : Backend σ Keys) (registry : Registry) (table : Program Keys)
    (state entry : MachineState σ) (stack : List (Frame Keys)) (handle : Nat)
    (environment : Core.Env types) (returns : List Core.Ty) (body : Execution.Stmt Keys)
    (resolved : table.lookup handle = .ok ⟨.nonpayable, parameterBinders types, returnBinders 0 returns, body⟩) :
    Reaches (transition backend registry table)
      ⟨.apply (.call (signature types returns))
        (.atom ⟨(signature types returns).type, some handle⟩ :: environmentPacket environment), stack, state, entry⟩
      ⟨.exec body, .call state.locals state.mode (returnBinders 0 returns) :: stack,
        calleeState state environment returns, entry⟩ := by
  have prepared := prepareArguments_packet registry state environment
  have bound := bindArguments_packet backend registry environment {state with mode := .checked}
  have initialized := (initializeReturn_packet registry {state with mode := .checked} environment returns).1
  have enters := Machine.call_enters_checked (backend := backend) (registry := registry) (limits := legacyLimits)
    (program := table) (prepared := state) (converted := environmentPacket environment)
    (⟨.apply (.call (signature types returns))
      (.atom ⟨(signature types returns).type, some handle⟩ :: environmentPacket environment), stack, state, entry⟩)
    (signature types returns) handle
    (⟨.nonpayable, parameterBinders types, returnBinders 0 returns, body⟩)
    resolved (by rw [function_signature]; exact signature_accepts_self types returns)
    (by simpa only [signature, typesList_ofList] using prepared)
    bound initialized
  apply next_reaches (choice := 0)
  simpa only [Machine.transition, Machine.apply, Datum.asAtom, calleeState] using enters

end Solidity.Execution.Compatibility
