/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Yul.Expression

/-! Resolved, pure Solidity uint256 expressions inside an unchecked block.
Every input is uint256; bitwise and shift operands remain word typed. Division,
remainder, checked arithmetic, casts, comparisons and effects are not admitted.
This is a typed source model, not a proof of the Solidity parser/type checker. -/
namespace Compiler.Validation.SolidityWord
open Contract.Yul

inductive Binary where
  | add | sub | mul | bitand | bitor | bitxor | shl | shr
  deriving DecidableEq, Repr

def Binary.eval : Binary → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .bitand, a, b => a &&& b
  | .bitor, a, b => a ||| b
  | .bitxor, a, b => a ^^^ b
  | .shl, a, b => if b.toNat < 256 then a <<< b.toNat else 0
  | .shr, a, b => if b.toNat < 256 then a >>> b.toNat else 0

inductive Expr where
  | literal (value : Nat)
  | input (name : String)
  | bitnot (arg : Expr)
  | binary (op : Binary) (left right : Expr)
  deriving DecidableEq, Repr

def Expr.eval (locals : String → Word) : Expr → Word
  | .literal n => BitVec.ofNat 256 n
  | .input name => locals name
  | .bitnot arg => ~~~arg.eval locals
  | .binary op a b => op.eval (a.eval locals) (b.eval locals)

def Binary.lower (op : Binary) (a b : Expression) : Expression :=
  match op with
  | .add => .binary .add a b
  | .sub => .binary .sub a b
  | .mul => .binary .mul a b
  | .bitand => .binary .and a b
  | .bitor => .binary .or a b
  | .bitxor => .binary .xor a b
  | .shl => .binary .shl b a
  | .shr => .binary .shr b a

def Expr.lower : Expr → Expression
  | .literal n => .literal n
  | .input name => .variable name
  | .bitnot arg => .unary .bitnot arg.lower
  | .binary op a b => op.lower a.lower b.lower


end Compiler.Validation.SolidityWord
