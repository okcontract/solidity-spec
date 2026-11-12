/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Bindings
import Solidity.Core.Procedure
import Solidity.Core.Execution.Syntax

/-! Closed translations of the previous scalar specifications. Helpers become
ordinary entries in the shared function table; no old evaluator is embedded in
the new syntax. Semantic correspondence is proved against actual transitions in
the companion proof modules. -/
namespace Solidity.Execution.Compatibility
open Core Static

def unary (operation : Core.Unary a b) (value : Execution.Expr Keys) : Execution.Expr Keys :=
  match operation with
  | .not => .unary .not value
  | .uintNot _ | .sintNot _ | .bytesNot _ => .unary .bitnot value
  | .negate _ mode => .arithmetic mode (.unary .neg value)
  | .uintCast _ width => .cast (.explicit .ordinary) (.uint width) value
  | .sintCast _ width => .cast (.explicit .ordinary) (.sint width) value
  | .toSigned width => .cast (.explicit .ordinary) (.sint width) value
  | .toUnsigned width => .cast (.explicit .ordinary) (.uint width) value
  | .addressOfUint => .cast (.explicit .ordinary) (.address false) value
  | .uintOfAddress => .cast (.explicit .ordinary) (.uint 19) value
  | .boolWord => .conditional value (.literal ⟨.uint 31, 1⟩) (.literal ⟨.uint 31, 0⟩)

def binary (operation : Core.Binary a b result) (left right : Execution.Expr Keys) : Execution.Expr Keys :=
  match operation with
  | .uintArithmetic width mode code => .arithmetic mode (.binary (.arithmetic code) (.uint width) left right)
  | .sintArithmetic width mode code => .arithmetic mode (.binary (.arithmetic code) (.sint width) left right)
  | .uintBits width code => .binary (.bits code) (.uint width) left right
  | .sintBits width code => .binary (.bits code) (.sint width) left right
  | .bytesBits width code => .binary (.bits code) (.fixedBytes width) left right
  | .uintCompare _ code | .sintCompare _ code => .binary (.compare code) .bool left right
  | .equal _ => .binary (.compare .eq) .bool left right
  | .uintShl width _ => .binary .shl (.uint width) left right
  | .uintShr width _ => .binary .shr (.uint width) left right
  | .sintShl width _ => .binary .shl (.sint width) left right
  | .sintShr width _ => .binary .shr (.sint width) left right

def expression (resolve : ∀ {type}, Ref type → Execution.Expr Keys) :
    {type : Core.Ty} → Core.Expr Ref type → Execution.Expr Keys
  | type, .literal value => .literal ⟨SType.ofCore type, scalarValue type value⟩
  | _, .read reference => resolve reference
  | _, .unary operation value => unary operation (expression resolve value)
  | _, .binary operation left right => binary operation (expression resolve left) (expression resolve right)
  | _, .ite condition yes no =>
      .conditional (expression resolve condition) (expression resolve yes) (expression resolve no)
  | _, .and left right => .binary .and .bool (expression resolve left) (expression resolve right)
  | _, .or left right => .binary .or .bool (expression resolve left) (expression resolve right)

def externalExpression (value : Core.Expr Ref type) : Execution.Expr (Key Ref Place) :=
  expression (fun reference => .externalRead (.read reference)) value

def frameReference : Core.FrameRef Ref vars type → Execution.Expr (Key Ref Place)
  | .local var => .local (localId var) (SType.ofCore type)
  | .global reference => .externalRead (.read reference)

def frameExpression (value : Core.Expr (Core.FrameRef Ref vars) type) : Execution.Expr (Key Ref Place) :=
  expression frameReference value

def expressions (resolve : ∀ {type}, Ref type → Execution.Expr Keys) :
    Core.Exprs Ref types → List (Execution.Expr Keys)
  | .nil => []
  | .cons value rest => expression resolve value :: expressions resolve rest

def block : Core.Block Ref Place → Execution.Stmt (Key Ref Place)
  | .skip => .skip
  | .seq first rest => .seq (block first) (block rest)
  | .assign place value => .storeExternal (.place place) (externalExpression value)
  | .ret value => .return_ (some (externalExpression value))
  | .stop => .return_ (some (.tuple []))
  | .revert bytes => .revert bytes
  | .branch test yes no => .if_ (externalExpression test) (block yes) (block no)

def control : Core.Control.Command Ref Place → Execution.Stmt (Key Ref Place)
  | .block body => block body
  | .seq first rest => .seq (control first) (control rest)
  | .branch test yes no => .if_ (externalExpression test) (control yes) (control no)
  | .loop test body post => .loop (externalExpression test) (control body) (block post)
  | .break_ => .break_
  | .continue_ => .continue_

def parameterBinders : List Core.Ty → List Binder
  | [] => []
  | type :: rest => binder type rest.length :: parameterBinders rest

def resultBinders (base : Nat) : List Core.Ty → List (Option Binder)
  | [] => []
  | type :: rest => some (binder type (base + rest.length)) :: resultBinders base rest

def returnBinders (base : Nat := 0) : List Core.Ty → List Binder
  | [] => []
  | type :: rest => {id := 2 * base + 1, type := SType.ofCore type} :: returnBinders (base + 1) rest

def expressionBinder (_ : Core.Expr Ref type) (index : Nat) : Binder := binder type index

def varType (_ : Core.Var vars type) : SType := SType.ofCore type

structure Translation (Keys : SType → Type) where
  body : Execution.Stmt Keys
  functions : List (Nat × FunctionDefinition Keys)
  nextHandle : Nat

def signature (parameters returns : List Core.Ty) : FunctionSignature :=
  ⟨.nonpayable, Types.ofList (parameters.map SType.ofCore), Types.ofList (returns.map SType.ofCore)⟩

/-- Handles are allocated in deterministic traversal order. Each embedded
helper uses the same normal call continuation as a recursive source function. -/
def procedure (nextHandle : Nat) : Core.Procedure Ref Place returns vars → Translation (Key Ref Place)
  | .ret values => ⟨.return_ (some (.tuple (expressions frameReference values))), [], nextHandle⟩
  | .revert bytes => ⟨.revert bytes, [], nextHandle⟩
  | .let_ value next =>
      let compiled := procedure nextHandle next
      ⟨.seq (.declare [some (expressionBinder value vars.length)] (some (frameExpression value))) compiled.body,
        compiled.functions, compiled.nextHandle⟩
  | .assign var value next =>
      let compiled := procedure nextHandle next
      ⟨.seq (.expr (.assign (.local (localId var) (varType var)) (frameExpression value))) compiled.body,
        compiled.functions, compiled.nextHandle⟩
  | .store place value next =>
      let compiled := procedure nextHandle next
      ⟨.seq (.storeExternal (.place place) (frameExpression value)) compiled.body,
        compiled.functions, compiled.nextHandle⟩
  | .branch condition yes no =>
      let first := procedure nextHandle yes
      let second := procedure first.nextHandle no
      ⟨.if_ (frameExpression condition) first.body second.body,
        first.functions ++ second.functions, second.nextHandle⟩
  | .call (results := results) (params := parameters) helper arguments next =>
      let function := procedure (nextHandle + 1) helper
      let continuation := procedure function.nextHandle next
      let called := signature parameters results
      let handle : Aggregates.Value := ⟨called.type, some nextHandle⟩
      ⟨.seq (.declare (resultBinders vars.length results)
          (some (.call called (.literal handle) (expressions frameReference arguments)))) continuation.body,
        (nextHandle, ⟨.nonpayable, parameterBinders parameters, returnBinders 0 results, function.body⟩) ::
          (function.functions ++ continuation.functions), continuation.nextHandle⟩
  | .emit _ topics data next =>
      let compiled := procedure nextHandle next
      ⟨.seq (.emit (expressions frameReference topics) (expressions frameReference data)) compiled.body,
        compiled.functions, compiled.nextHandle⟩

def program (compiled : Translation Keys) : Program Keys := ⟨compiled.functions⟩

theorem binary_type (operation : Core.Binary a b result) (left right : Execution.Expr Keys) :
    (binary operation left right).type = SType.ofCore result := by
  cases operation <;> rfl

theorem unary_type (operation : Core.Unary a b) (value : Execution.Expr Keys)
    (typed : value.type = SType.ofCore a) : (unary operation value).type = SType.ofCore b := by
  cases operation <;> simp [unary, Execution.Expr.type, typed, SType.ofCore]

theorem expression_type (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (typed : ∀ {type} (reference : Ref type), (resolve reference).type = SType.ofCore type)
    (value : Core.Expr Ref type) : (expression resolve value).type = SType.ofCore type := by
  induction value with
  | literal => rfl
  | read reference => exact typed reference
  | unary operation value ih => exact unary_type operation _ ih
  | binary operation left right _ _ => exact binary_type operation _ _
  | ite condition yes no _ ih _ => exact ih
  | and | or => rfl

end Solidity.Execution.Compatibility
