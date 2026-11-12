/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Bindings

namespace Solidity.Core.Tests

-- Width boundaries, checked signed arithmetic, and unchecked zero division.
example : unsigned 0 .checked .add 255 1 = .error (Contract.panic 0x11) := by rfl
example : unsigned 0 .unchecked .add 255 1 = .ok 0 := by rfl
example : unsigned 31 .unchecked .div 7 0 = .error (Contract.panic 0x12) := by rfl
example : unsigned 31 .unchecked .mod 7 0 = .error (Contract.panic 0x12) := by rfl
example : signed 0 .checked .div 128 255 = .error (Contract.panic 0x11) := by rfl
example : signed 0 .unchecked .div 128 255 = .ok 128 := by rfl
example : signed 0 .checked .mod 128 255 = .ok 0 := by rfl
example : signed 0 .checked .div 251 2 = .ok 254 := by rfl
example : (Binary.sintShr 0 31).eval 253 1 = .ok 254 := by rfl
example : (Binary.sintShr 0 31).eval 253 256 = .ok 255 := by rfl
example : (Binary.uintShl 0 31).eval 1 8 = .ok 0 := by rfl
example : (Unary.uintCast 31 0).eval 257 = .ok 1 := by rfl
example : (Unary.sintCast 0 31).eval 255 = .ok (-1) := by rfl
example : (Unary.negate 0 .checked).eval 128 = .error (Contract.panic 0x11) := by rfl

abbrev Closed := Expr (fun _ => Empty)
def noReads {type : Ty} (ref : Empty) : type.Value := nomatch ref

def zeroDivide : Closed .word :=
  .binary (.uintArithmetic 31 .unchecked .div) (.literal 7) (.literal 0)
def overflow : Closed .word :=
  .binary (.uintArithmetic 31 .checked .sub) (.literal 0) (.literal 1)
def condition : Closed .bool := .binary (.uintCompare 31 .gt) zeroDivide (.literal 0)

-- Short-circuiting does not evaluate an unreachable panic.
example : (Expr.and (.literal false) condition).eval noReads .leftFirst = .ok false := by rfl
example : (Expr.or (.literal true) condition).eval noReads .rightFirst = .ok true := by rfl
example : (Expr.ite (.literal false) zeroDivide (.literal 3)).eval noReads .leftFirst = .ok 3 := by rfl

-- Arithmetic mode is per operation; it does not leak from an inner expression.
example : (Expr.binary (.uintArithmetic 31 .unchecked .add) overflow (.literal 1)).eval
    noReads .leftFirst = .error (Contract.panic 0x11) := by rfl

-- Different source panic codes make operand order observable already in pure code.
example : (Expr.binary (.uintArithmetic 31 .checked .add) zeroDivide overflow).eval
    noReads .leftFirst = .error (Contract.panic 0x12) := by rfl
example : (Expr.binary (.uintArithmetic 31 .checked .add) zeroDivide overflow).eval
    noReads .rightFirst = .error (Contract.panic 0x11) := by rfl

-- Mixed orders are needed: both uniform strategies panic with 0x11 here,
-- while the independently chosen inner-right operand can panic with 0x12.
def mixed : Closed .word := .binary (.uintArithmetic 31 .checked .add)
  (.binary (.uintArithmetic 31 .checked .add) overflow zeroDivide) overflow
example : mixed.eval noReads .leftFirst = .error (Contract.panic 0x11) := by rfl
example : mixed.eval noReads .rightFirst = .error (Contract.panic 0x11) := by rfl
example : mixed.Evaluates noReads (.error (Contract.panic 0x12)) :=
  .binaryLeftError (.binaryRightError (Expr.eval_permitted noReads zeroDivide .leftFirst))

end Solidity.Core.Tests
