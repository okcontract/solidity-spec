/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Unary

namespace Solidity.Static
open Core

abbrev Context := String → Option SType
abbrev Name (context : Context) (type : SType) := {name : String // context name = some type}
abbrev Environment (context : Context) := ∀ {type}, Name context type → type.Value

def Elementary.into (base : Elementary) : base.source.Value → base.core.Value := by
  cases base with
  | payableAddress => exact id
  | scalar type => cases type <;> exact id

def Elementary.out (base : Elementary) : base.core.Value → base.source.Value := by
  cases base with
  | payableAddress => exact id
  | scalar type => cases type <;> exact id

theorem Elementary.out_into (base : Elementary) (value : base.source.Value) :
    base.out (base.into value) = value := by
  cases base with
  | payableAddress => rfl
  | scalar type => cases type <;> rfl

/-- Typed source expressions retain nominal/payable/function distinctions and
share their arithmetic with Core.Scalar. Static cast evidence is required at the
constructor, so the mere existence of a machine coercion grants no source cast. -/
inductive SourceExpr (context : Context) : SType → Type where
  | literal : type.Value → SourceExpr context type
  | read : Name context type → SourceExpr context type
  | cast (mode : ConversionMode) (allowed : Allowed mode a b) :
      SourceExpr context a → SourceExpr context b
  | unary : ScalarUnary op type → SourceExpr context type → SourceExpr context type
  | binary : ScalarBinary op a b result → SourceExpr context a → SourceExpr context b → SourceExpr context result
  | ite : SourceExpr context .bool → SourceExpr context type → SourceExpr context type → SourceExpr context type
  | wrap (identity : Nat) (base : Elementary) : SourceExpr context base.source → SourceExpr context (.valueType identity base)
  | unwrap (identity : Nat) (base : Elementary) : SourceExpr context (.valueType identity base) → SourceExpr context base.source

variable {context : Context} {type : SType}

def SourceExpr.eval (env : Environment context) (mode : ArithmeticMode) (order : OperandOrder) {type : SType} :
    SourceExpr context type → Except ConversionFailure type.Value
  | .literal value => .ok value
  | .read name => .ok (env name)
  | .cast _ _ expression => do coerce _ _ (← expression.eval env mode order)
  | .unary operation arg => do (operation.eval mode (← arg.eval env mode order)).mapError .panic
  | .binary .and left right => do
      if ← left.eval env mode order then right.eval env mode order else .ok false
  | .binary .or left right => do
      if ← left.eval env mode order then .ok true else right.eval env mode order
  | .binary operation left right => do
      match order with
      | .leftFirst => (operation.eval mode (← left.eval env mode order) (← right.eval env mode order)).mapError .panic
      | .rightFirst =>
          let b ← right.eval env mode order
          let a ← left.eval env mode order
          (operation.eval mode a b).mapError .panic
  | .ite cond yes no => do
      if ← cond.eval env mode order then yes.eval env mode order else no.eval env mode order
  | .wrap _ base arg => do return base.into (← arg.eval env mode order)
  | .unwrap _ base arg => do return base.out (← arg.eval env mode order)

/-- Ordinary operands permit either order independently at each node. Lazy
operators have separate constructors; they never evaluate an unselected arm. -/
inductive SourceExpr.Evaluates (env : Environment context) (mode : ArithmeticMode) :
    {type : SType} → SourceExpr context type → Except ConversionFailure type.Value → Prop where
  | literal : Evaluates env mode (.literal value) (.ok value)
  | read : Evaluates env mode (.read name) (.ok (env name))
  | castOk : Evaluates env mode arg (.ok value) →
      Evaluates env mode (.cast conversion allowed arg) (coerce _ _ value)
  | castError : Evaluates env mode arg (.error error) →
      Evaluates env mode (.cast conversion allowed arg) (.error error)
  | unaryOk : Evaluates env mode arg (.ok value) →
      Evaluates env mode (.unary operation arg) ((operation.eval mode value).mapError .panic)
  | unaryError : Evaluates env mode arg (.error error) →
      Evaluates env mode (.unary operation arg) (.error error)
  | binaryOk (ordinary : op ≠ .and ∧ op ≠ .or) (operation : ScalarBinary op a b result) :
      Evaluates env mode left (.ok av) → Evaluates env mode right (.ok bv) →
      Evaluates env mode (.binary operation left right) ((operation.eval mode av bv).mapError .panic)
  | binaryLeftError (ordinary : op ≠ .and ∧ op ≠ .or) (operation : ScalarBinary op a b result) :
      Evaluates env mode left (.error error) →
      Evaluates env mode (.binary operation left right) (.error error)
  | binaryRightError (ordinary : op ≠ .and ∧ op ≠ .or) (operation : ScalarBinary op a b result) :
      Evaluates env mode right (.error error) →
      Evaluates env mode (.binary operation left right) (.error error)
  | andTrue : Evaluates env mode left (.ok true) → Evaluates env mode right result →
      Evaluates env mode (.binary .and left right) result
  | andFalse : Evaluates env mode left (.ok false) → Evaluates env mode (.binary .and left right) (.ok false)
  | andError : Evaluates env mode left (.error error) → Evaluates env mode (.binary .and left right) (.error error)
  | orTrue : Evaluates env mode left (.ok true) → Evaluates env mode (.binary .or left right) (.ok true)
  | orFalse : Evaluates env mode left (.ok false) → Evaluates env mode right result →
      Evaluates env mode (.binary .or left right) result
  | orError : Evaluates env mode left (.error error) → Evaluates env mode (.binary .or left right) (.error error)
  | iteTrue : Evaluates env mode testExpr (.ok true) → Evaluates env mode yes result →
      Evaluates env mode (.ite testExpr yes no) result
  | iteFalse : Evaluates env mode testExpr (.ok false) → Evaluates env mode no result →
      Evaluates env mode (.ite testExpr yes no) result
  | iteError : Evaluates env mode testExpr (.error error) → Evaluates env mode (.ite testExpr yes no) (.error error)
  | wrapOk {base : Elementary} {arg : SourceExpr context base.source} {value : base.source.Value} : Evaluates env mode arg (.ok value) →
      Evaluates env mode (.wrap identity base arg) (.ok (base.into value))
  | wrapError {base : Elementary} {arg : SourceExpr context base.source} : Evaluates env mode arg (.error error) →
      Evaluates env mode (.wrap identity base arg) (.error error)
  | unwrapOk {identity : Nat} {base : Elementary} {arg : SourceExpr context (.valueType identity base)} {value : base.core.Value} : Evaluates env mode arg (.ok value) →
      Evaluates env mode (.unwrap identity base arg) (.ok (base.out value))
  | unwrapError {identity : Nat} {base : Elementary} {arg : SourceExpr context (.valueType identity base)} : Evaluates env mode arg (.error error) →
      Evaluates env mode (.unwrap identity base arg) (.error error)

/-- Every completed strategy run is permitted, without assuming a globally
fixed operand order in the specification. -/
theorem SourceExpr.eval_permitted (env : Environment context) (mode : ArithmeticMode)
    (order : OperandOrder) (expression : SourceExpr context type) :
    expression.Evaluates env mode (expression.eval env mode order) := by
  induction expression with
  | literal => exact .literal
  | read => exact .read
  | cast conversion allowed arg ih =>
      simp only [eval]
      cases h : arg.eval env mode order with
      | error error => exact .castError (h ▸ ih)
      | ok value => exact .castOk (h ▸ ih)
  | unary operation arg ih =>
      simp only [eval]
      cases h : arg.eval env mode order with
      | error error => exact .unaryError (h ▸ ih)
      | ok value => exact .unaryOk (h ▸ ih)
  | binary operation left right il ir =>
      cases operation
      case and =>
        simp only [eval]
        cases h : left.eval env mode order with
        | error error => exact .andError (h ▸ il)
        | ok value => cases value with
          | false => exact .andFalse (h ▸ il)
          | true => exact .andTrue (h ▸ il) ir
      case or =>
        simp only [eval]
        cases h : left.eval env mode order with
        | error error => exact .orError (h ▸ il)
        | ok value => cases value with
          | false => exact .orFalse (h ▸ il) ir
          | true => exact .orTrue (h ▸ il)
      all_goals
        cases order <;> simp only [eval]
        all_goals
          cases hl : left.eval env mode _ <;> cases hr : right.eval env mode _
          all_goals first
            | (refine .binaryLeftError ?_ _ (hl ▸ il); simp)
            | (refine .binaryRightError ?_ _ (hr ▸ ir); simp)
            | (refine .binaryOk ?_ _ (hl ▸ il) (hr ▸ ir); simp)
  | ite test yes no it iy ino =>
      simp only [eval]
      cases h : test.eval env mode order with
      | error error => exact .iteError (h ▸ it)
      | ok value => cases value with
        | false => exact .iteFalse (h ▸ it) ino
        | true => exact .iteTrue (h ▸ it) iy
  | wrap identity base arg ih =>
      simp only [eval]
      cases h : arg.eval env mode order with
      | error error => exact .wrapError (h ▸ ih)
      | ok value => exact .wrapOk (h ▸ ih)
  | unwrap identity base arg ih =>
      simp only [eval]
      cases h : arg.eval env mode order with
      | error error => exact .unwrapError (h ▸ ih)
      | ok value => exact .unwrapOk (h ▸ ih)

end Solidity.Static
