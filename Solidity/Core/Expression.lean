/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Scalar

/-! One intrinsically typed scalar expression evaluator. The reference family
is supplied by the resolved program (typed locals, fields, or read-only inputs).
Expressions do not write state. Operand order is explicit because different
panics can already distinguish orders; Boolean and conditional branches remain
short-circuiting in both orders. -/
namespace Solidity.Core

variable {Ref Other : Ty → Type}

inductive Expr (Ref : Ty → Type) : Ty → Type where
  | literal : type.Value → Expr Ref type
  | read : Ref type → Expr Ref type
  | unary : Unary a b → Expr Ref a → Expr Ref b
  | binary : Binary a b c → Expr Ref a → Expr Ref b → Expr Ref c
  | ite : Expr Ref .bool → Expr Ref type → Expr Ref type → Expr Ref type
  | and : Expr Ref .bool → Expr Ref .bool → Expr Ref .bool
  | or : Expr Ref .bool → Expr Ref .bool → Expr Ref .bool

def Expr.eval (read : ∀ {type}, Ref type → type.Value) (order : OperandOrder) :
    Expr Ref type → Result type.Value
  | .literal value => .ok value
  | .read reference => .ok (read reference)
  | .unary op arg => do op.eval (← arg.eval read order)
  | .binary op left right => do
      match order with
      | .leftFirst => op.eval (← left.eval read order) (← right.eval read order)
      | .rightFirst =>
          let b ← right.eval read order
          let a ← left.eval read order
          op.eval a b
  | .ite cond yes no => do
      if ← cond.eval read order then yes.eval read order else no.eval read order
  | .and left right => do
      if ← left.eval read order then right.eval read order else .ok false
  | .or left right => do
      if ← left.eval read order then .ok true else right.eval read order

/-- Permitted evaluation chooses operand order independently at every binary
node. These rules are for pure reads: an operand that panics may be evaluated
first; successful binary evaluation requires both successful operands. Lazy
operators evaluate only their selected branch. -/
inductive Expr.Evaluates (read : ∀ {type}, Ref type → type.Value) :
    Expr Ref type → Result type.Value → Prop where
  | literal : Evaluates read (.literal value) (.ok value)
  | read : Evaluates read (.read reference) (.ok (read reference))
  | unaryOk : Evaluates read arg (.ok value) →
      Evaluates read (.unary op arg) (op.eval value)
  | unaryError : Evaluates read arg (.error bytes) →
      Evaluates read (.unary op arg) (.error bytes)
  | binaryOk : Evaluates read left (.ok a) → Evaluates read right (.ok b) →
      Evaluates read (.binary op left right) (op.eval a b)
  | binaryLeftError : Evaluates read left (.error bytes) →
      Evaluates read (.binary op left right) (.error bytes)
  | binaryRightError : Evaluates read right (.error bytes) →
      Evaluates read (.binary op left right) (.error bytes)
  | iteTrue {testExpr : Expr Ref .bool} : Evaluates read testExpr (.ok true) → Evaluates read yes result →
      Evaluates read (.ite testExpr yes no) result
  | iteFalse {testExpr : Expr Ref .bool} : Evaluates read testExpr (.ok false) → Evaluates read no result →
      Evaluates read (.ite testExpr yes no) result
  | iteError {testExpr : Expr Ref .bool} : Evaluates read testExpr (.error bytes) →
      Evaluates read (.ite testExpr yes no) (.error bytes)
  | andTrue {left right : Expr Ref .bool} : Evaluates read left (.ok true) → Evaluates read right result →
      Evaluates read (.and left right) result
  | andFalse {left right : Expr Ref .bool} : Evaluates read left (.ok false) → Evaluates read (.and left right) (.ok false)
  | andError {left right : Expr Ref .bool} : Evaluates read left (.error bytes) → Evaluates read (.and left right) (.error bytes)
  | orTrue {left right : Expr Ref .bool} : Evaluates read left (.ok true) → Evaluates read (.or left right) (.ok true)
  | orFalse {left right : Expr Ref .bool} : Evaluates read left (.ok false) → Evaluates read right result →
      Evaluates read (.or left right) result
  | orError {left right : Expr Ref .bool} : Evaluates read left (.error bytes) → Evaluates read (.or left right) (.error bytes)

/-- The executable uniform-order strategies are sound instances of the
permitted relation; the relation also includes mixed orders within a tree. -/
theorem Expr.eval_permitted (read : ∀ {type}, Ref type → type.Value)
    (expression : Expr Ref type) (order : OperandOrder) :
    expression.Evaluates read (expression.eval read order) := by
  induction expression with
  | literal => exact .literal
  | read => exact .read
  | unary op arg ih =>
      simp only [eval]
      cases h : arg.eval read order with
      | error bytes => exact .unaryError (h ▸ ih)
      | ok value => exact .unaryOk (h ▸ ih)
  | binary op left right il ir =>
      cases order <;> simp only [eval]
      case leftFirst =>
        cases hl : left.eval read .leftFirst <;> cases hr : right.eval read .leftFirst
        all_goals first
          | exact .binaryLeftError (hl ▸ il)
          | exact .binaryRightError (hr ▸ ir)
          | exact .binaryOk (hl ▸ il) (hr ▸ ir)
      case rightFirst =>
        cases hr : right.eval read .rightFirst <;> cases hl : left.eval read .rightFirst
        all_goals first
          | exact .binaryRightError (hr ▸ ir)
          | exact .binaryLeftError (hl ▸ il)
          | exact .binaryOk (hl ▸ il) (hr ▸ ir)
  | ite cond yes no ic iy ino =>
      simp only [eval]
      cases h : cond.eval read order with
      | error bytes => exact .iteError (h ▸ ic)
      | ok value => cases value with
        | false => exact .iteFalse (h ▸ ic) ino
        | true => exact .iteTrue (h ▸ ic) iy
  | and left right il ir =>
      simp only [eval]
      cases h : left.eval read order with
      | error bytes => exact .andError (h ▸ il)
      | ok value => cases value with
        | false => exact .andFalse (h ▸ il)
        | true => exact .andTrue (h ▸ il) ir
  | or left right il ir =>
      simp only [eval]
      cases h : left.eval read order with
      | error bytes => exact .orError (h ▸ il)
      | ok value => cases value with
        | false => exact .orFalse (h ▸ il) ir
        | true => exact .orTrue (h ▸ il)

/-- The enclosing resolver can rename references without changing semantics. -/
def Expr.rename (f : ∀ {type}, Ref type → Other type) : Expr Ref type → Expr Other type
  | .literal value => .literal value
  | .read ref => .read (f ref)
  | .unary op arg => .unary op (arg.rename f)
  | .binary op left right => .binary op (left.rename f) (right.rename f)
  | .ite cond yes no => .ite (cond.rename f) (yes.rename f) (no.rename f)
  | .and left right => .and (left.rename f) (right.rename f)
  | .or left right => .or (left.rename f) (right.rename f)

theorem Expr.eval_rename (f : ∀ {type}, Ref type → Other type)
    (read : ∀ {type}, Other type → type.Value) (order : OperandOrder) (e : Expr Ref type) :
    (e.rename f).eval read order = e.eval (fun ref => read (f ref)) order := by
  induction e with
  | literal => rfl
  | read => rfl
  | unary op arg ih => simp only [rename, eval, ih]
  | binary op a b ia ib => cases order <;> simp only [rename, eval, ia, ib]
  | ite c a b ic ia ib => simp only [rename, eval, ic, ia, ib]
  | and a b ia ib => simp only [rename, eval, ia, ib]
  | or a b ia ib => simp only [rename, eval, ia, ib]

end Solidity.Core
