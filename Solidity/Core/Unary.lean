/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Operators

namespace Solidity.Static
open Core

inductive UnaryCode where
  | not | neg | bitnot
  deriving DecidableEq, Repr

inductive ScalarUnary : UnaryCode → SType → Type where
  | not : ScalarUnary .not .bool
  | neg : ScalarUnary .neg (.sint w)
  | uintNot : ScalarUnary .bitnot (.uint w)
  | sintNot : ScalarUnary .bitnot (.sint w)
  | bytesNot : ScalarUnary .bitnot (.fixedBytes w)

def checkUnary (op : UnaryCode) (type : SType) : Option (ScalarUnary op type) :=
  match op, type with
  | .not, .bool => some .not
  | .neg, .sint _ => some .neg
  | .bitnot, .uint _ => some .uintNot
  | .bitnot, .sint _ => some .sintNot
  | .bitnot, .fixedBytes _ => some .bytesNot
  | _, _ => none

theorem checkUnary_complete (operation : ScalarUnary op type) : checkUnary op type = some operation := by
  cases operation <;> rfl

theorem checkUnary_iff (op : UnaryCode) (type : SType) :
    (checkUnary op type).isSome = true ↔ Nonempty (ScalarUnary op type) := by
  constructor
  · intro h; cases hc : checkUnary op type with
    | none => simp [hc] at h
    | some operation => exact ⟨operation⟩
  · rintro ⟨operation⟩; simp [checkUnary_complete operation]

def ScalarUnary.eval (mode : ArithmeticMode) : ScalarUnary op type → type.Value → Core.Result type.Value
  | .not, value => .ok (!value)
  | .neg, value => signedResult _ mode (-value.toInt)
  | .uintNot, value | .sintNot, value | .bytesNot, value => .ok (~~~value)

inductive UpdateCode where
  | inc (post : Bool) | dec (post : Bool) | delete
  deriving DecidableEq, Repr

/-- Deletion of a user-defined value type is not a built-in unary operator in
0.8.36. Assignment of an explicitly wrapped zero is a separate expression. -/
def Deletable : SType → Prop
  | .uint _ | .sint _ | .fixedBytes _ | .bool | .address _ |
    .enumType _ _ | .contract _ _ _ | .function _ _ _ _ => True
  | _ => False

def deletable : SType → Bool
  | .uint _ | .sint _ | .fixedBytes _ | .bool | .address _ |
    .enumType _ _ | .contract _ _ _ | .function _ _ _ _ => true
  | _ => false

theorem deletable_iff (type : SType) : deletable type = true ↔ Deletable type := by
  cases type <;> simp [deletable, Deletable]

def UpdateAllowed (op : UpdateCode) (type : SType) (lvalue : Bool) : Prop :=
  lvalue = true ∧ match op with
  | .delete => Deletable type
  | .inc _ | .dec _ => match type with | .uint _ | .sint _ => True | _ => False

def updateAllowed (op : UpdateCode) (type : SType) (lvalue : Bool) : Bool :=
  lvalue && match op with
  | .delete => deletable type
  | .inc _ | .dec _ => match type with | .uint _ | .sint _ => true | _ => false

theorem updateAllowed_iff (op : UpdateCode) (type : SType) (lvalue : Bool) :
    updateAllowed op type lvalue = true ↔ UpdateAllowed op type lvalue := by
  cases op <;> cases type <;> simp [updateAllowed, UpdateAllowed, deletable, Deletable]

def defaultScalar : (type : SType) → Option type.Value
  | .uint _ | .sint _ | .fixedBytes _ => some 0
  | .bool => some false
  | .address _ | .contract _ _ _ => some 0
  | .enumType _ _ => some ⟨0, by omega⟩
  | .valueType _ base => match base with
    | .scalar (.uint w) | .scalar (.sint w) | .scalar (.fixedBytes w) => some (BitVec.ofNat w.bits 0)
    | .scalar .bool => some false
    | .scalar .address | .payableAddress => some (BitVec.ofNat 160 0)
  | .function .internal _ _ _ => some none
  | .function .external _ _ _ => some (0, 0)
  | _ => none

/-- A successful mutation supplies the new cell and expression result. `none`
is the empty tuple produced by delete. The enclosing effectful semantics writes
the cell only on success; this primitive does not pick an operand order. -/
structure Updated (type : SType) where
  next : type.Value
  result : Option type.Value

def updateScalar (mode : ArithmeticMode) (op : UpdateCode) (type : SType)
    (lvalue : Bool) (old : type.Value) : Except ConversionFailure (Updated type) := do
  if !type.scalarSupported then throw .unsupported
  if !updateAllowed op type lvalue then throw .rejected
  match op with
  | .delete =>
      let some zero := defaultScalar type | throw .unsupported
      return ⟨zero, none⟩
  | .inc post | .dec post =>
      let arithmetic := match op with | .inc _ => Arithmetic.add | _ => .sub
      let changed : Core.Result type.Value := match type, old with
        | .uint w, old => unsigned w mode arithmetic old 1
        | .sint w, old => signed w mode arithmetic old 1
        | _, value => .ok value -- unreachable after updateAllowed; no source permission
      match changed with
      | .error bytes => throw (.panic bytes)
      | .ok value => return ⟨value, some (if post then old else value)⟩

theorem update_requires_lvalue (mode : ArithmeticMode) (op : UpdateCode) (type : SType)
    (old : type.Value) (supported : type.scalarSupported = true) :
    updateScalar mode op type false old = .error .rejected := by
  simp [updateScalar, supported, updateAllowed]
  rfl

/-- User-defined operators are resolved pure free-function calls. This describes
the signature restriction; declaration lookup and uniqueness are input assumptions,
and resolved call execution uses the continuation machine. No value-producing callback is assumed here. -/
def BinaryCode.userDefinable : BinaryCode → Bool
  | .arithmetic _ | .bits _ | .compare _ => true
  | _ => false

structure FunctionDescriptor where
  identity : Nat
  parameters : Types
  returns : Types
  mutability : Mutability
  freeFunction : Bool
  deriving DecidableEq, Repr

structure OperatorBinding (op : BinaryCode) (identity : Nat) (base : Elementary) where
  target : FunctionDescriptor
  result : SType
  resultType : result = (match op with | .compare _ => .bool | _ => .valueType identity base)
  operatorAllowed : op.userDefinable = true
  parameters : target.parameters = .cons (.valueType identity base) (.cons (.valueType identity base) .nil)
  returns : target.returns = .cons result .nil
  pureFunction : target.mutability = .pure
  freeFunction : target.freeFunction = true

end Solidity.Static
