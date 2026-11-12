/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.State
import Solidity.Core.Execution.Syntax

namespace Solidity.Execution
open Static Core

inductive Target (Key : SType → Type) where
  | captured : Captured → Target Key
  | external {type : SType} : Key type → Target Key

def Target.type : Target Key → SType
  | .captured target => target.type
  | .external (type := type) _ => type

inductive CapturedPattern (Key : SType → Type) where
  | hole
  | target : Target Key → CapturedPattern Key
  | tuple : List (CapturedPattern Key) → CapturedPattern Key

inductive Signal where
  | next | break_ | continue_
  | return_ : Option Datum → Signal

/-- All eager child groups select a fresh pending child at each transition.
The recorded indices restore syntactic argument/result order after effects. -/
inductive Completion where
  | unary : UnaryCode → Completion
  | binary : BinaryCode → SType → Completion
  | tuple
  | cast : ConversionMode → SType → Completion
  | referenceCast : SType → Completion
  | call : FunctionSignature → Completion
  | newArray : SType → Completion
  | newBytes : Bool → Completion
  | length
  | slice : Bool → Bool → Completion
  | push | pop
  | field : SType → Nat → Completion
  | index : SType → Completion
  | readIndex : SType → Completion
  | mapping : SType → Completion
  | pushZero : SType → Completion
  | emit : Nat → Completion
  | assert_
  | require_ : ErrorEncoding → Completion
  | revertWith : ErrorEncoding → Completion
  | namedCall : FunctionSignature → List Nat → Completion
  | wrap : Nat → Elementary → Completion
  | unwrap : Nat → Elementary → Completion
  | functionAddress | functionSelector
  | structConstructor : Nat → List Nat → Completion

inductive Task (Key : SType → Type) where
  | eval : Expr Key → Task Key
  | capture : LValue Key → Task Key
  | pattern : Pattern Key → Task Key
  | patterns : List (Nat × Pattern Key) → List (Nat × CapturedPattern Key) → Task Key
  | patternValue : CapturedPattern Key → Task Key
  | value : Datum → Task Key
  | target : Target Key → Task Key
  | collect : List (Nat × Expr Key) → List (Nat × Datum) → Completion → Task Key
  | apply : Completion → Packet → Task Key
  | exec : Stmt Key → Task Key
  | resume : Signal → Task Key
  | loopTest : Expr Key → Stmt Key → Stmt Key → Task Key
  | writes : List (Target Key × Value) → Task Key
  | inlineElements : Aggregates.Place → SType → List (Nat × Expr Key) → Task Key
  | structFields : Aggregates.Place → Nat → List SType → Packet → Task Key

inductive Frame (Key : SType → Type) where
  | next : Stmt Key → Frame Key
  | scope
  | mode : ArithmeticMode → Frame Key
  | discard
  | returnValue
  | declare : List (Option Binder) → Frame Key
  | storeExternal {type : SType} : Key type → Frame Key
  | readTarget
  | update : UpdateCode → Frame Key
  | select : Expr Key → Expr Key → Frame Key
  | branch : Stmt Key → Stmt Key → Frame Key
  | lazy : Bool → Expr Key → Frame Key
  | collect : Nat → List (Nat × Expr Key) → List (Nat × Datum) → Completion → Frame Key
  | assignRight : LValue Key → Option BinaryCode → Frame Key
  | assignLeft : Expr Key → Option BinaryCode → Frame Key
  | commitValue : Datum → Option BinaryCode → Frame Key
  | commitTarget : Target Key → Option BinaryCode → Frame Key
  | compoundReadFirst : Expr Key → BinaryCode → Frame Key
  | commitOld : Target Key → BinaryCode → Value → Frame Key
  | tupleCapture : Pattern Key → Frame Key
  | tupleRight : Expr Key → Frame Key
  | tupleCommitValue : Datum → Frame Key
  | tupleCommitPattern : CapturedPattern Key → Frame Key
  | patternTarget
  | patternItem : Nat → List (Nat × Pattern Key) → List (Nat × CapturedPattern Key) → Frame Key
  | loopCondition : Expr Key → Stmt Key → Stmt Key → Frame Key
  | loopBody : Expr Key → Stmt Key → Stmt Key → Frame Key
  | loopPost : Expr Key → Stmt Key → Stmt Key → Frame Key
  | doBody : Stmt Key → Expr Key → Frame Key
  | doCondition : Stmt Key → Expr Key → Frame Key
  | forInit : Expr Key → Stmt Key → Stmt Key → Frame Key
  | call : Locals → ArithmeticMode → List Binder → Frame Key
  | resultTransfer : Locals → ArithmeticMode → List Binder → Frame Key
  | initializeElement : Aggregates.Place → SType → Nat → List (Nat × Expr Key) → Frame Key

structure Config (σ : Type) (Key : SType → Type) where
  task : Task Key
  stack : List (Frame Key) := []
  state : MachineState σ
  entry : MachineState σ

def Config.start (state : MachineState σ) (body : Stmt Key) : Config σ Key :=
  ⟨.exec body, [], state, state⟩

def Config.expression (state : MachineState σ) (body : Expr Key) : Config σ Key :=
  ⟨.eval body, [], state, state⟩

end Solidity.Execution
