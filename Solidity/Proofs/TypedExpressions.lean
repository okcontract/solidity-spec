/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Expression
import Contract.Semantics.Eval

namespace Solidity.Compatibility.Typed
open Core

abbrev type : Contract.Ty → Core.Ty
  | .word => .word | .bool => .bool | .address => .address

inductive Reference (slots : Nat) (vars : List Contract.Ty) : Core.Ty → Type where
  | var : Contract.Var vars t → Reference slots vars (type t)
  | load : Fin slots → Reference slots vars .word
  | caller : Reference slots vars .address
  | self : Reference slots vars .address

def read (state : Contract.Storage slots) (ctx : Contract.Context) (env : Contract.Env vars) :
    {t : Core.Ty} → Reference slots vars t → t.Value
  | _, .var (t := t) var => by cases t <;> exact env.get var
  | _, .load slot => state slot
  | _, .caller => ctx.caller
  | _, .self => ctx.self

/-- The old typed DSL deliberately exposes zero-totalized EVM div/mod. Translate
that behavior explicitly; it must not change Solidity source division. -/
def wordOp (op : Contract.WordOp) (a b : Core.Expr Ref .word) : Core.Expr Ref .word :=
  match op with
  | .mul => .binary (.uintArithmetic 31 .unchecked .mul) a b
  | .div => .ite (.binary (.equal .word) b (.literal 0)) (.literal 0)
      (.binary (.uintArithmetic 31 .unchecked .div) a b)
  | .mod => .ite (.binary (.equal .word) b (.literal 0)) (.literal 0)
      (.binary (.uintArithmetic 31 .unchecked .mod) a b)
  | .and => .binary (.uintBits 31 .bitand) a b
  | .or => .binary (.uintBits 31 .bitor) a b
  | .xor => .binary (.uintBits 31 .bitxor) a b
  | .shl => .binary (.uintShl 31 31) a b
  | .shr => .binary (.uintShr 31 31) a b

def embed : Contract.Expr slots vars t → Core.Expr (Reference slots vars) (type t)
  | .word value => .literal value
  | .bool value => .literal value
  | .address value => .literal value
  | .var var => .read (.var var)
  | .load slot => .read (.load slot)
  | .caller => .read .caller
  | .self => .read .self
  | .add a b => .binary (.uintArithmetic 31 .unchecked .add) (embed a) (embed b)
  | .sub a b => .binary (.uintArithmetic 31 .unchecked .sub) (embed a) (embed b)
  | .binary op a b => wordOp op (embed a) (embed b)
  | .bitnot a => .unary (.uintNot 31) (embed a)
  | .lt a b => .binary (.uintCompare 31 .lt) (embed a) (embed b)
  | .le a b => .binary (.uintCompare 31 .le) (embed a) (embed b)
  | .eq a b => .binary (.equal _) (embed a) (embed b)
  | .not a => .unary .not (embed a)

theorem wordOp_correct (op : Contract.WordOp) (a b : Core.Expr Ref .word)
    (read : ∀ {t}, Ref t → t.Value) (order : OperandOrder) (x y : BitVec 256)
    (ha : a.eval read order = .ok x) (hb : b.eval read order = .ok y) :
    (wordOp op a b).eval read order = .ok (op.eval x y) := by
  cases op <;> cases order <;>
    simp [wordOp, Core.Expr.eval, ha, hb, Core.Binary.eval, unsigned, bitwise,
      Core.Ty.equal, Contract.WordOp.eval]
  all_goals first
    | rfl
    | (change (if y == 0#256 then Except.ok (0#256) else
          if y = 0#256 then Except.error (Contract.panic 0x12) else Except.ok (x / y)) = Except.ok (x / y)
       by_cases h : y = 0#256 <;> simp [h])
    | (change (if y == 0#256 then Except.ok (0#256) else
          if y = 0#256 then Except.error (Contract.panic 0x12) else Except.ok (x % y)) =
          Except.ok (if y = 0 then 0 else x % y)
       by_cases h : y = 0#256 <;> simp [h])

/-- Reusing the same typed value, across the two syntax type universes. -/
def value (t : Contract.Ty) : t.Value → (type t).Value := by
  cases t <;> exact id

theorem equal_value (t : Contract.Ty) (a b : t.Value) :
    (type t).equal (value t a) (value t b) = t.equal a b := by
  cases t <;> rfl

theorem eval_embed (e : Contract.Expr slots vars t) (state : Contract.Storage slots)
    (ctx : Contract.Context) (env : Contract.Env vars) (order : OperandOrder) :
    (embed e).eval (read state ctx env) order = .ok (value t (e.eval state ctx env)) := by
  induction e with
  | word => rfl
  | bool => rfl
  | address => rfl
  | @var inner v => cases inner <;> rfl
  | load => rfl
  | caller => rfl
  | self => rfl
  | add a b ia ib =>
      cases order <;> simp [embed, Core.Expr.eval, ia, ib, Core.Binary.eval, unsigned, Contract.Expr.eval, value] <;> rfl
  | sub a b ia ib =>
      cases order <;> simp [embed, Core.Expr.eval, ia, ib, Core.Binary.eval, unsigned, Contract.Expr.eval, value] <;> rfl
  | binary op a b ia ib => exact wordOp_correct op _ _ _ _ _ _ ia ib
  | bitnot a ih => simp [embed, Core.Expr.eval, ih, Unary.eval, Contract.Expr.eval, value] <;> rfl
  | lt a b ia ib =>
      cases order <;> simp [embed, Core.Expr.eval, ia, ib, Core.Binary.eval, compareUnsigned, Contract.Expr.eval, value] <;> rfl
  | le a b ia ib =>
      cases order <;> simp [embed, Core.Expr.eval, ia, ib, Core.Binary.eval, compareUnsigned, Contract.Expr.eval, value] <;> rfl
  | @eq inner a b ia ib =>
      cases order <;> simp only [embed, Core.Expr.eval, ia, ib]
      all_goals
        change Except.ok ((type inner).equal (value inner (a.eval state ctx env))
          (value inner (b.eval state ctx env))) = Except.ok (inner.equal (a.eval state ctx env) (b.eval state ctx env))
        rw [equal_value]
  | not a ih => simp [embed, Core.Expr.eval, ih, Unary.eval, Contract.Expr.eval, value] <;> rfl

end Solidity.Compatibility.Typed
