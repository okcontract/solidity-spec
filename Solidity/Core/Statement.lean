/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Expression
import Contract.Interaction.Bytes

namespace Solidity.Core

variable {Ref Place : Ty → Type} {State : Type}

/-- Concrete resolved stores supply typed reads and writes. Write rejection is
an exceptional halt (e.g. a forbidden static write), never a source revert.
Instances must define storage representation; this interface is not an oracle. -/
structure Store (Ref Place : Ty → Type) (State : Type) where
  read : State → ∀ {type}, Ref type → type.Value
  write : State → ∀ {type}, Place type → type.Value → Option State

/-- Shared finite statement core. Expression types retain widths and arithmetic
modes; storage targets retain their types. General loop control is layered over
these finite blocks by the control machine. -/
inductive Block (Ref Place : Ty → Type) where
  | skip
  | seq : Block Ref Place → Block Ref Place → Block Ref Place
  | assign : Place type → Expr Ref type → Block Ref Place
  | ret : Expr Ref .word → Block Ref Place
  | stop
  | revert : List UInt8 → Block Ref Place
  | branch : Expr Ref .bool → Block Ref Place → Block Ref Place → Block Ref Place

inductive Outcome (State : Type) where
  | returned : List UInt8 → State → Outcome State
  | reverted : List UInt8 → Outcome State
  | fault : Outcome State

inductive Flow (State : Type) where
  | next : State → Flow State
  | halt : Outcome State → Flow State

/-- Only successful outcomes expose a committed store. -/
def Outcome.committed (before : State) : Outcome State → State
  | .returned _ after => after
  | .reverted _ | .fault => before

def Block.eval (store : Store Ref Place State) (order : OperandOrder)
    (state : State) : Block Ref Place → Flow State
  | .skip => .next state
  | .seq first rest => match first.eval store order state with
    | .next after => rest.eval store order after
    | .halt result => .halt result
  | .assign place value => match value.eval (store.read state) order with
    | .error bytes => .halt (.reverted bytes)
    | .ok value => match store.write state place value with
      | none => .halt .fault
      | some after => .next after
  | .ret value => match value.eval (store.read state) order with
    | .error bytes => .halt (.reverted bytes)
    | .ok value => .halt (.returned (Contract.Interaction.wordBytes value) state)
  | .stop => .halt (.returned [] state)
  | .revert bytes => .halt (.reverted bytes)
  | .branch test yes no => match test.eval (store.read state) order with
    | .error bytes => .halt (.reverted bytes)
    | .ok value => if value then yes.eval store order state else no.eval store order state

def Block.result (store : Store Ref Place State) (order : OperandOrder)
    (state : State) (fallthrough : List UInt8) (body : Block Ref Place) : Outcome State :=
  match body.eval store order state with
  | .next after => .returned fallthrough after
  | .halt result => result

theorem Block.seq_assoc (store : Store Ref Place State) (order : OperandOrder)
    (state : State) (a b c : Block Ref Place) :
    (Block.seq (.seq a b) c).eval store order state =
      (Block.seq a (.seq b c)).eval store order state := by
  simp only [eval]
  cases a.eval store order state <;> rfl

theorem Outcome.revert_rolls_back (state : State) (bytes : List UInt8) :
    (Outcome.reverted bytes).committed state = state := rfl

theorem Outcome.fault_rolls_back (state : State) :
    Outcome.fault.committed state = state := rfl

end Solidity.Core
