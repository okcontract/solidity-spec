/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Registry

namespace Solidity.Static

/-- The declaration checker supplies candidate free functions. These rules check
the complete operator signature; a unique global using declaration and
body purity are input assumptions. No arbitrary function-result oracle is
introduced into scalar evaluation. -/
def OperatorResult (op : BinaryCode) (identity : Nat) (base : Elementary) : SType :=
  match op with | .compare _ => .bool | _ => .valueType identity base

def OperatorSignature (op : BinaryCode) (identity : Nat) (base : Elementary) (target : FunctionDescriptor) : Prop :=
  op.userDefinable = true ∧
  target.parameters = .cons (.valueType identity base) (.cons (.valueType identity base) .nil) ∧
  target.returns = .cons (OperatorResult op identity base) .nil ∧
  target.mutability = .pure ∧ target.freeFunction = true

def operatorSignature (op : BinaryCode) (identity : Nat) (base : Elementary) (target : FunctionDescriptor) : Bool :=
  op.userDefinable &&
  target.parameters == .cons (.valueType identity base) (.cons (.valueType identity base) .nil) &&
  target.returns == .cons (OperatorResult op identity base) .nil &&
  target.mutability == .pure && target.freeFunction

theorem operatorSignature_iff (op : BinaryCode) (identity : Nat) (base : Elementary) (target : FunctionDescriptor) :
    operatorSignature op identity base target = true ↔ OperatorSignature op identity base target := by
  simp [operatorSignature, OperatorSignature, and_assoc]

def bindOperator (op : BinaryCode) (identity : Nat) (base : Elementary) (target : FunctionDescriptor) :
    Option (OperatorBinding op identity base) :=
  if h : operatorSignature op identity base target then
    let valid := (operatorSignature_iff _ _ _ _).mp h
    some {
      target := target
      result := OperatorResult op identity base
      resultType := rfl
      operatorAllowed := valid.1
      parameters := valid.2.1
      returns := valid.2.2.1
      pureFunction := valid.2.2.2.1
      freeFunction := valid.2.2.2.2 }
  else none

theorem bindOperator_iff : (bindOperator op identity base target).isSome = true ↔
    OperatorSignature op identity base target := by
  simp only [bindOperator]
  split
  next valid => simp [(operatorSignature_iff _ _ _ _).mp valid]
  next invalid => simp [show ¬ OperatorSignature op identity base target from fun h =>
    invalid ((operatorSignature_iff _ _ _ _).mpr h)]

def UnaryOperatorSignature (op : UnaryCode) (identity : Nat) (base : Elementary) (target : FunctionDescriptor) : Prop :=
  (op = .neg ∨ op = .bitnot) ∧
  target.parameters = .cons (.valueType identity base) .nil ∧
  target.returns = .cons (.valueType identity base) .nil ∧
  target.mutability = .pure ∧ target.freeFunction = true

def unaryOperatorSignature (op : UnaryCode) (identity : Nat) (base : Elementary) (target : FunctionDescriptor) : Bool :=
  (op == .neg || op == .bitnot) &&
  target.parameters == .cons (.valueType identity base) .nil &&
  target.returns == .cons (.valueType identity base) .nil &&
  target.mutability == .pure && target.freeFunction

theorem unaryOperatorSignature_iff (op : UnaryCode) (identity : Nat) (base : Elementary) (target : FunctionDescriptor) :
    unaryOperatorSignature op identity base target = true ↔ UnaryOperatorSignature op identity base target := by
  simp [unaryOperatorSignature, UnaryOperatorSignature, and_assoc]

end Solidity.Static
