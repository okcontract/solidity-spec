/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Bindings
import Solidity.Core.Conversions
import Solidity.Core.Operators

/-! Closed resolved syntax for one effectful evaluator. Scalar operations keep
their source types; tuple groups carry Datum rather than SType.Value. Typed
external keys support the old generic stores through the same machine. -/
namespace Solidity.Execution
open Static Core
open Aggregates (Place Result)

def typesList : Types → List SType
  | .nil => []
  | .cons type rest => type :: typesList rest

structure FunctionSignature where
  mutability : Mutability
  parameters : Types
  returns : Types
  deriving DecidableEq, Repr

def FunctionSignature.type (signature : FunctionSignature) : SType :=
  .function .internal signature.mutability signature.parameters signature.returns

def FunctionSignature.resultType (signature : FunctionSignature) : SType :=
  match signature.returns with
  | .cons type .nil => type
  | returns => .tuple returns

/-- Function mutability can be widened by an implicit function conversion;
parameter and result shapes remain exact. This compares a table entry with
the signature under which its handle was used. -/
def FunctionSignature.accepts (actual expected : FunctionSignature) : Bool :=
  actual.parameters == expected.parameters && actual.returns == expected.returns &&
    actual.mutability.allows expected.mutability

inductive ErrorEncoding where
  | empty
  | string
  | custom : BitVec 32 → Types → ErrorEncoding
  deriving DecidableEq, Repr

namespace ArgumentOrder

def Valid (order : List Nat) (count : Nat) : Prop :=
  order.length = count ∧ order.Nodup ∧ ∀ index ∈ order, index < count

def valid (order : List Nat) (count : Nat) : Bool :=
  order.length == count && decide order.Nodup && order.all (· < count)

/-- Reorder already evaluated arguments. This operation cannot evaluate or
discard any source argument effects while binding named parameters. -/
def select (order : List Nat) (values : List α) : Aggregates.Result (List α) := do
  if !valid order values.length then throw .rejected
  order.mapM fun index => match values[index]? with
    | some value => pure value
    | none => throw (.invalidContext "named argument index outside captured packet")

theorem valid_iff (order : List Nat) (count : Nat) : valid order count = true ↔ Valid order count := by
  simp [valid, Valid, and_assoc]

end ArgumentOrder

mutual
inductive Expr (Key : SType → Type) where
  | literal : Value → Expr Key
  | bytesLiteral : Bool → List UInt8 → Expr Key
  | local : LocalId → SType → Expr Key
  | externalRead {type : SType} : Key type → Expr Key
  | read : LValue Key → Expr Key
  | cast : ConversionMode → SType → Expr Key → Expr Key
  | referenceCast : SType → Expr Key → Expr Key
  | wrap : Nat → Elementary → Expr Key → Expr Key
  | unwrap : Nat → Elementary → Expr Key → Expr Key
  | functionAddress : Expr Key → Expr Key
  | functionSelector : Expr Key → Expr Key
  | arithmetic : ArithmeticMode → Expr Key → Expr Key
  | unary : UnaryCode → Expr Key → Expr Key
  | binary : BinaryCode → SType → Expr Key → Expr Key → Expr Key
  | conditional : Expr Key → Expr Key → Expr Key → Expr Key
  | tuple : List (Expr Key) → Expr Key
  | assign : LValue Key → Expr Key → Expr Key
  | tupleAssign : Pattern Key → Expr Key → Expr Key
  | compound : BinaryCode → LValue Key → Expr Key → Expr Key
  | update : UpdateCode → LValue Key → Expr Key
  | call : FunctionSignature → Expr Key → List (Expr Key) → Expr Key
  | namedCall : FunctionSignature → Expr Key → List (Expr Key) → List Nat → Expr Key
  | assert_ : Expr Key → Expr Key
  | require_ : ErrorEncoding → Expr Key → List (Expr Key) → Expr Key
  | revertWith : ErrorEncoding → List (Expr Key) → Expr Key
  | newArray : SType → Expr Key → Expr Key
  | newBytes : Bool → Expr Key → Expr Key
  | inlineArray : SType → List (Expr Key) → Expr Key
  | structConstructor : Nat → List (Expr Key) → List Nat → Expr Key
  | length : Expr Key → Expr Key
  | index : SType → Expr Key → Expr Key → Expr Key
  | slice : Expr Key → Option (Expr Key) → Option (Expr Key) → Expr Key
  | push : Expr Key → Expr Key → Expr Key
  | pop : Expr Key → Expr Key

inductive LValue (Key : SType → Type) where
  | local : LocalId → SType → LValue Key
  | heap : Place → LValue Key
  | external {type : SType} : Key type → LValue Key
  | field : SType → Expr Key → Nat → LValue Key
  | index : SType → Expr Key → Expr Key → LValue Key
  | mapping : SType → Expr Key → Expr Key → LValue Key
  | pushZero : SType → Expr Key → LValue Key

inductive Pattern (Key : SType → Type) where
  | hole
  | target : LValue Key → Pattern Key
  | tuple : List (Pattern Key) → Pattern Key
end

abbrev Exprs (Key : SType → Type) := List (Expr Key)

mutual
def Expr.type : Expr Key → SType
  | .literal value => value.type
  | .bytesLiteral string _ => if string then .string .memory true else .bytes .memory true
  | .local _ type => type
  | .externalRead (type := type) _ => type
  | .read target => target.type
  | .cast _ target _ | .referenceCast target _ => target
  | .wrap identity base _ => .valueType identity base
  | .unwrap _ base _ => base.source
  | .functionAddress _ => .address false
  | .functionSelector _ => .fixedBytes 3
  | .arithmetic _ value => value.type
  | .unary _ value => value.type
  | .binary _ result _ _ => result
  | .conditional _ yes _ => yes.type
  | .tuple values => .tuple (expressionTypes values)
  | .assign target _ | .compound _ target _ => target.type
  | .tupleAssign _ _ => .tuple .nil
  | .update .delete _ => .tuple .nil
  | .update _ target => target.type
  | .call signature _ _ | .namedCall signature _ _ _ => signature.resultType
  | .assert_ _ | .require_ _ _ _ | .revertWith _ _ => .tuple .nil
  | .newArray element _ => .array (Aggregates.atLocation element .memory false) none .memory true
  | .newBytes string _ => if string then .string .memory true else .bytes .memory true
  | .inlineArray element values =>
      .array (Aggregates.atLocation element .memory false) (some values.length) .memory true
  | .structConstructor identity _ _ => .structType identity .memory true
  | .length value => match value.type with | .fixedBytes _ => .uint 0 | _ => .uint 31
  | .index type _ _ => type
  | .slice value _ _ => Aggregates.atLocation value.type .calldata true
  | .push _ _ | .pop _ => .tuple .nil

def LValue.type : LValue Key → SType
  | .local _ type => type
  | .heap place => place.type
  | .external (type := type) _ => type
  | .field type _ _ | .index type _ _ | .mapping type _ _ | .pushZero type _ => type

def expressionTypes : Exprs Key → Types
  | [] => .nil
  | value :: rest => .cons value.type (expressionTypes rest)
end

inductive Stmt (Key : SType → Type) where
  | skip
  | expr : Expr Key → Stmt Key
  | seq : Stmt Key → Stmt Key → Stmt Key
  | block : Stmt Key → Stmt Key
  | declare : List (Option Binder) → Option (Expr Key) → Stmt Key
  | if_ : Expr Key → Stmt Key → Stmt Key → Stmt Key
  | while_ : Expr Key → Stmt Key → Stmt Key
  /-- Normalized loop with an explicit post statement and no implicit scope. -/
  | loop : Expr Key → Stmt Key → Stmt Key → Stmt Key
  | doWhile : Stmt Key → Expr Key → Stmt Key
  | for_ : Stmt Key → Option (Expr Key) → Stmt Key → Stmt Key → Stmt Key
  | break_
  | continue_
  | return_ : Option (Expr Key) → Stmt Key
  | arithmetic : ArithmeticMode → Stmt Key → Stmt Key
  | emit : Exprs Key → Exprs Key → Stmt Key
  | revert : List UInt8 → Stmt Key
  /-- Legacy write-only keys do not gain an invented read operation. -/
  | storeExternal {type : SType} : Key type → Expr Key → Stmt Key

structure FunctionDefinition (Key : SType → Type) where
  mutability : Mutability := .nonpayable
  parameters : List Binder
  returns : List Binder
  body : Stmt Key

def FunctionDefinition.signature (function : FunctionDefinition Key) : FunctionSignature :=
  ⟨function.mutability, Types.ofList (function.parameters.map Binder.type),
    Types.ofList (function.returns.map Binder.type)⟩

def FunctionDefinition.distinctBindings (function : FunctionDefinition Key) : Bool :=
  ((function.parameters ++ function.returns).map Binder.id).eraseDups.length ==
    function.parameters.length + function.returns.length

/-- Handles select closed source bodies. Their equality is representation
dependent; no declaration-identity injectivity law is introduced here. -/
structure Program (Key : SType → Type) where
  functions : List (Nat × FunctionDefinition Key) := []

def Program.valid (program : Program Key) : Bool :=
  (program.functions.map Prod.fst).eraseDups.length == program.functions.length &&
    program.functions.all fun (_, function) => function.distinctBindings && function.mutability != .payable

def Program.lookup (program : Program Key) (handle : Nat) : Aggregates.Result (FunctionDefinition Key) := do
  if !program.valid then throw (.invalidContext "invalid internal function table")
  let some (_, function) := program.functions.find? (fun entry => entry.1 == handle) |
    throw (.invalidContext "unresolved internal function handle")
  return function

end Solidity.Execution
