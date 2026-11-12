/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Checked
import Solidity.Core.Expression

/-! Universal correspondence with the existing word-expression evaluator.
The old interpreter is a specialization of the typed scalar core; the theorem
covers arbitrary environments and syntax, not an enumeration of examples. -/
namespace Solidity.Compatibility.Word
open Core
open Compiler.Validation

inductive Reference : Ty → Type where
  | name : String → Reference .word

def read (locals : String → BitVec 256) : {type : Ty} → Reference type → type.Value
  | _, .name name => locals name

def binary (mode : ArithmeticMode) : SolidityWord.Binary → Core.Binary .word .word .word
  | .add => .uintArithmetic 31 mode .add
  | .sub => .uintArithmetic 31 mode .sub
  | .mul => .uintArithmetic 31 mode .mul
  | .bitand => .uintBits 31 .bitand
  | .bitor => .uintBits 31 .bitor
  | .bitxor => .uintBits 31 .bitxor
  | .shl => .uintShl 31 31
  | .shr => .uintShr 31 31

def embed (mode : ArithmeticMode) : SolidityWord.Expr → Core.Expr Reference .word
  | .literal n => .literal (BitVec.ofNat 256 n)
  | .input name => .read (.name name)
  | .bitnot arg => .unary (.uintNot 31) (embed mode arg)
  | .binary op left right => .binary (binary mode op) (embed mode left) (embed mode right)

theorem binary_unchecked (op : SolidityWord.Binary) (a b : BitVec 256) :
    (binary .unchecked op).eval a b = .ok (op.eval a b) := by
  cases op <;> simp [binary, Core.Binary.eval, unsigned, bitwise, Width.bits, SolidityWord.Binary.eval] <;> rfl

theorem binary_checked (op : SolidityWord.Binary) (a b : BitVec 256) :
    (binary .checked op).eval a b = op.evalChecked a b := by
  cases op <;> simp [binary, Core.Binary.eval, unsigned, bitwise, Width.bits,
    SolidityWord.Binary.evalChecked, SolidityWord.Binary.eval, Contract.CheckedOp.eval] <;> rfl

theorem unchecked (e : SolidityWord.Expr) (locals : String → BitVec 256) (order : OperandOrder) :
    (embed .unchecked e).eval (read locals) order = .ok (e.eval locals) := by
  induction e with
  | literal => rfl
  | input => rfl
  | bitnot arg ih => simp [embed, Core.Expr.eval, ih, Unary.eval, SolidityWord.Expr.eval] <;> rfl
  | binary op left right il ir =>
      cases order <;> simp [embed, Core.Expr.eval, il, ir, binary_unchecked, SolidityWord.Expr.eval] <;> rfl

theorem checked (e : SolidityWord.Expr) (locals : String → BitVec 256) :
    (embed .checked e).eval (read locals) .leftFirst = e.evalChecked locals := by
  induction e with
  | literal => rfl
  | input => rfl
  | bitnot arg ih =>
      simp only [embed, Core.Expr.eval, ih, SolidityWord.Expr.evalChecked]
      cases arg.evalChecked locals <;> rfl
  | binary op left right il ir =>
      simp only [embed, Core.Expr.eval, il, ir, SolidityWord.Expr.evalChecked]
      cases left.evalChecked locals <;> cases right.evalChecked locals <;>
        simp [binary_checked] <;> rfl

/-- The compatibility checked result is a permitted execution of the core. -/
theorem checked_permitted (e : SolidityWord.Expr) (locals : String → BitVec 256) :
    (embed .checked e).Evaluates (read locals) (e.evalChecked locals) :=
  checked e locals ▸ Core.Expr.eval_permitted (read locals) (embed .checked e) .leftFirst

end Solidity.Compatibility.Word
