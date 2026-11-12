/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Proofs.Word
import Solidity.StorageSource

namespace Solidity.Compatibility.Conditions
open Core Compiler.Validation
open SolidityStorage

def mode (checked : Bool) : ArithmeticMode := if checked then .checked else .unchecked

def comparison : SolidityStorage.Comparison → Core.Comparison
  | .eq => .eq | .ne => .ne | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge

def embed (checked : Bool) : Condition → Core.Expr Word.Reference .bool
  | .literal value => .literal value
  | .boolean value => .binary (.uintCompare 31 .ne)
      (Word.embed (mode checked) value) (.literal 0)
  | .compare op left right => .binary (.uintCompare 31 (comparison op))
      (Word.embed (mode checked) left) (Word.embed (mode checked) right)
  | .not value => .unary .not (embed checked value)
  | .and left right => .and (embed checked left) (embed checked right)
  | .or left right => .or (embed checked left) (embed checked right)

theorem expression (variables : Layout) (source : SolidityFunction.Source)
    (input : Contract.Evm.Input) (cells : Contract.Evm.Stateful.Slots) (e : SolidityWord.Expr) :
    (Word.embed (mode source.checked) e).eval
      (Word.read (locals variables source input cells)) .leftFirst =
      SolidityStorage.expression variables source input cells e := by
  cases h : source.checked <;>
    simp [mode, h, SolidityStorage.expression, Word.checked, Word.unchecked] <;> rfl

theorem comparison_correct (op : SolidityStorage.Comparison) (a b : BitVec 256) :
    compareUnsigned (comparison op) a b = op.test a b := by
  cases op <;> simp [comparison, compareUnsigned, SolidityStorage.Comparison.test, BitVec.ult, BitVec.ule] <;> rfl

theorem eval_embed (e : Condition) (variables : Layout) (source : SolidityFunction.Source)
    (input : Contract.Evm.Input) (cells : Contract.Evm.Stateful.Slots) :
    (embed source.checked e).eval (Word.read (locals variables source input cells)) .leftFirst =
      e.eval variables source input cells := by
  induction e with
  | literal => rfl
  | boolean value =>
      simp only [embed, Core.Expr.eval, expression, Condition.eval]
      cases SolidityStorage.expression variables source input cells value with
      | error => rfl
      | ok word =>
          change Except.ok (word != (0#256)) = Except.ok (decide (word ≠ 0#256))
          congr 1
          simp [bne, Bool.beq_eq_decide_eq]
  | compare op a b =>
      simp only [embed, Core.Expr.eval, expression, Condition.eval]
      cases SolidityStorage.expression variables source input cells a with
      | error => rfl
      | ok av =>
          cases SolidityStorage.expression variables source input cells b with
          | error => rfl
          | ok bv =>
              exact congrArg (Except.ok (ε := List UInt8)) (comparison_correct op av bv)
  | not value ih =>
      simp only [embed, Core.Expr.eval, ih, Condition.eval]
      cases value.eval variables source input cells <;> rfl
  | and a b ia ib =>
      simp only [embed, Core.Expr.eval, ia, ib, Condition.eval]
      cases a.eval variables source input cells with
      | error => rfl
      | ok value => cases value <;> rfl
  | or a b ia ib =>
      simp only [embed, Core.Expr.eval, ia, ib, Condition.eval]
      cases a.eval variables source input cells with
      | error => rfl
      | ok value => cases value <;> rfl

end Solidity.Compatibility.Conditions
