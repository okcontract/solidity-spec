/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.BinaryTyping

namespace Solidity.Frontend.Inference
open Core Static Lexical

inductive AssignmentKind where
  | plain
  | compound : BinaryCode → AssignmentKind
  deriving DecidableEq, Repr

/-- Solidity has no **=, &&=, ||= or comparison-assignment tokens. -/
def compoundToken : BinaryCode → Bool
  | .arithmetic _ | .bits _ | .shl | .shr => true
  | _ => false

/-- A scalar assignment plan computes the next value. Resolving an lvalue once,
writing its location, and selecting effectful operand order use the place and continuation-machine interfaces.
The lvalue fact comes from declaration/reference checking, not from this value
expression. A compound result must convert back implicitly to the left type. -/
def assignment (kind : AssignmentKind) (lvalue : Bool) (old : SourceExpr context type)
    (right : Term context) : Except StaticError (SourceExpr context type) := do
  if !lvalue then throw .rejected
  match kind with
  | .plain => materialize .implicit right type
  | .compound code =>
      if !compoundToken code then throw .rejected
      materialize .implicit (← binary code (.runtime type old) right) type

inductive AssignmentTyping (old : SourceExpr context type) (right : Term context) :
    AssignmentKind → Bool → SourceExpr context type → Prop where
  | plain : Materializes .implicit right type next → AssignmentTyping old right .plain true next
  | compound : compoundToken code = true → BinaryTyping code (.runtime type old) right combined →
      Materializes .implicit combined type next → AssignmentTyping old right (.compound code) true next

private theorem bind_ok (arg : α) (next : α → Except ε β) :
    (Except.ok arg >>= next) = next arg := rfl
private theorem bind_error (error : ε) (next : α → Except ε β) :
    (Except.error error >>= next) = .error error := rfl
attribute [local simp] bind_ok bind_error

theorem assignment_complete (valid : AssignmentTyping old right kind lvalue next) :
    assignment kind lvalue old right = .ok next := by
  cases valid with
  | plain h => simp [assignment, materialize_complete h]
  | compound token combine h => simp [assignment, token, binary_iff.mpr combine, materialize_complete h]

theorem assignment_sound (checked : assignment kind lvalue old right = .ok next) :
    AssignmentTyping old right kind lvalue next := by
  cases lvalue with
  | false => cases checked
  | true =>
      cases kind with
      | plain => exact .plain (materialize_sound checked)
      | compound code =>
          cases allowed : compoundToken code with
          | false =>
              simp [assignment, allowed] at checked
              cases checked
          | true =>
              simp only [assignment, allowed, Bool.not_true, Bool.false_eq_true,
                ↓reduceIte] at checked
              cases hc : binary code (.runtime _ old) right with
              | error error => simp [hc] at checked
              | ok combined =>
                  simp only [hc, bind_ok] at checked
                  exact .compound allowed (binary_iff.mp hc) (materialize_sound checked)

theorem assignment_iff : assignment kind lvalue old right = .ok next ↔
    AssignmentTyping old right kind lvalue next := ⟨assignment_sound, assignment_complete⟩

theorem assignment_requires_lvalue (old : SourceExpr context type) (right : Term context) :
    assignment kind false old right = .error .rejected := rfl

end Solidity.Frontend.Inference
