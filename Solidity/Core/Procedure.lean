/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Bindings
import Solidity.Core.Statement
import Solidity.Core.StaticABI
import Contract.Interaction.World

/-! Typed local frames and finite internal procedures over the shared expression
and Store interfaces. Helpers are closed finite syntax, not arbitrary execution
callbacks. General recursion is a separate control-machine extension. -/
namespace Solidity.Core

inductive FrameRef (Ref : Ty → Type) (vars : List Ty) : Ty → Type where
  | local : Var vars t → FrameRef Ref vars t
  | global : Ref t → FrameRef Ref vars t

def FrameRef.read (read : ∀ {t}, Ref t → t.Value) (env : Env vars) :
    ∀ {t}, FrameRef Ref vars t → t.Value
  | _, .local var => env.get var
  | _, .global ref => read ref

inductive Exprs (Ref : Ty → Type) : List Ty → Type where
  | nil : Exprs Ref []
  | cons : Expr Ref t → Exprs Ref ts → Exprs Ref (t :: ts)

def Exprs.eval (read : ∀ {t}, Ref t → t.Value) (order : OperandOrder) :
    Exprs Ref ts → Result (Env ts)
  | .nil => .ok .nil
  | .cons value rest => do
    let head ← value.eval read order
    let tail ← rest.eval read order
    pure (.cons head tail)

def Env.abiWords : Env ts → List (BitVec 256)
  | .nil => []
  | .cons (type := t) value rest => t.abiWord value :: rest.abiWords

inductive Procedure (Ref Place : Ty → Type) : List Ty → List Ty → Type where
  | ret : Exprs (FrameRef Ref vars) returns → Procedure Ref Place returns vars
  | revert : List UInt8 → Procedure Ref Place returns vars
  | let_ : Expr (FrameRef Ref vars) t → Procedure Ref Place returns (t :: vars) →
      Procedure Ref Place returns vars
  | assign : Var vars t → Expr (FrameRef Ref vars) t → Procedure Ref Place returns vars →
      Procedure Ref Place returns vars
  | store : Place t → Expr (FrameRef Ref vars) t → Procedure Ref Place returns vars →
      Procedure Ref Place returns vars
  | branch : Expr (FrameRef Ref vars) .bool → Procedure Ref Place returns vars →
      Procedure Ref Place returns vars → Procedure Ref Place returns vars
  | call : Procedure Ref Place results params → Exprs (FrameRef Ref vars) params →
      Procedure Ref Place returns (results ++ vars) → Procedure Ref Place returns vars
  | emit : topics.length ≤ 4 → Exprs (FrameRef Ref vars) topics → Exprs (FrameRef Ref vars) data →
      Procedure Ref Place returns vars → Procedure Ref Place returns vars

inductive ProcedureOutcome (State : Type) (returns : List Ty) where
  | returned : State → Env returns → List Contract.Interaction.Event → ProcedureOutcome State returns
  | reverted : List UInt8 → ProcedureOutcome State returns
  | fault : ProcedureOutcome State returns

def ProcedureOutcome.prepend (events : List Contract.Interaction.Event) :
    ProcedureOutcome State returns → ProcedureOutcome State returns
  | .returned state values rest => .returned state values (events ++ rest)
  | .reverted bytes => .reverted bytes
  | .fault => .fault

def ProcedureOutcome.observe : ProcedureOutcome State returns → Outcome State
  | .returned state values _ => .returned (values.abiWords.flatMap Contract.Interaction.wordBytes) state
  | .reverted bytes => .reverted bytes
  | .fault => .fault

def ProcedureOutcome.logs : ProcedureOutcome State returns → List Contract.Interaction.Event
  | .returned _ _ logs => logs
  | .reverted _ | .fault => []

def Procedure.eval (store : Store Ref Place State) (emitter : BitVec 160) (order : OperandOrder)
    (state : State) (env : Env vars) : Procedure Ref Place returns vars → ProcedureOutcome State returns
  | .ret values => match values.eval (FrameRef.read (store.read state) env) order with
    | .ok values => .returned state values []
    | .error bytes => .reverted bytes
  | .revert bytes => .reverted bytes
  | .let_ value next => match value.eval (FrameRef.read (store.read state) env) order with
    | .ok value => next.eval store emitter order state (.cons value env)
    | .error bytes => .reverted bytes
  | .assign var value next => match value.eval (FrameRef.read (store.read state) env) order with
    | .ok value => next.eval store emitter order state (env.set var value)
    | .error bytes => .reverted bytes
  | .store place value next => match value.eval (FrameRef.read (store.read state) env) order with
    | .error bytes => .reverted bytes
    | .ok value => match store.write state place value with
      | none => .fault
      | some after => next.eval store emitter order after env
  | .branch condition yes no => match condition.eval (FrameRef.read (store.read state) env) order with
    | .error bytes => .reverted bytes
    | .ok value => if value then yes.eval store emitter order state env else no.eval store emitter order state env
  | .call helper args next => match args.eval (FrameRef.read (store.read state) env) order with
    | .error bytes => .reverted bytes
    | .ok args => match helper.eval store emitter order state args with
      | .reverted bytes => .reverted bytes
      | .fault => .fault
      | .returned after values logs => (next.eval store emitter order after (values.append env)).prepend logs
  | .emit _ topics data next => match topics.eval (FrameRef.read (store.read state) env) order with
    | .error bytes => .reverted bytes
    | .ok topics => match data.eval (FrameRef.read (store.read state) env) order with
      | .error bytes => .reverted bytes
      | .ok data => (next.eval store emitter order state env).prepend
          [⟨emitter.setWidth 256, topics.abiWords, data.abiWords.flatMap Contract.Interaction.wordBytes⟩]

theorem Procedure.eval_cast (h : as = bs) (proc : Procedure Ref Place returns as)
    (store : Store Ref Place State) (emitter : BitVec 160) (order : OperandOrder)
    (state : State) (env : Env as) :
    (h ▸ proc).eval store emitter order state (h ▸ env) = proc.eval store emitter order state env := by
  cases h; rfl

theorem ProcedureOutcome.failure_discards_logs (events : List Contract.Interaction.Event) (bytes : List UInt8) :
    (ProcedureOutcome.prepend (State := State) (returns := returns) events (.reverted bytes)).logs = [] := rfl

theorem ProcedureOutcome.failure_restores (state : State) (events : List Contract.Interaction.Event)
    (bytes : List UInt8) :
    (ProcedureOutcome.prepend (returns := returns) events (.reverted bytes)).observe.committed state = state := rfl

end Solidity.Core
