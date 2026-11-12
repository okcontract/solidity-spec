/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Bindings

/-! Name resolution for type-annotated scalar expressions. This is a checked
stage after parsing/type inference, not a claim of a complete Solidity frontend.
A successful result contains typed de Bruijn references, never default-zero
free names. Shadowing selects the nearest declaration even on a type mismatch.
-/
namespace Solidity.Frontend
open Core

abbrev Scope := List (String × Ty)
abbrev Scope.types (scope : Scope) : List Ty := scope.map Prod.snd

inductive Error where
  | unbound : String → Error
  | typeMismatch : String → Ty → Ty → Error
  deriving DecidableEq, Repr

inductive Resolves : (scope : Scope) → String → {type : Ty} → Var scope.types type → Prop where
  | here : Resolves ((name, type) :: rest) name .here
  | there : name ≠ head → Resolves rest name var →
      Resolves ((head, other) :: rest) name (.there var)

def resolveName (scope : Scope) (name : String) (expected : Ty) :
    Except Error (Var scope.types expected) :=
  match scope with
  | [] => .error (.unbound name)
  | (head, actual) :: rest =>
    if name = head then
      if ht : actual = expected then .ok (ht ▸ Var.here)
      else .error (.typeMismatch name expected actual)
    else do return .there (← resolveName rest name expected)

theorem resolveName_sound (scope : Scope) (name : String) (expected : Ty)
    (var : Var scope.types expected) (h : resolveName scope name expected = .ok var) :
    Resolves scope name var := by
  induction scope with
  | nil => simp [resolveName] at h
  | cons head rest ih =>
      obtain ⟨head, actual⟩ := head
      by_cases hn : name = head
      · subst head
        by_cases ht : actual = expected
        · subst actual
          simp [resolveName] at h
          cases h
          exact .here
        · simp [resolveName, ht] at h
      · simp only [resolveName, if_neg hn] at h
        cases hr : resolveName rest name expected with
        | error error => simp [hr] at h <;> cases h
        | ok found =>
            simp [hr] at h
            cases h
            exact .there hn (ih found hr)

theorem resolveName_complete {scope : Scope} {type : Ty} {var : Var scope.types type}
    (h : Resolves scope name var) :
    resolveName scope name type = .ok var := by
  induction h with
  | here => simp [resolveName]
  | there different _ ih => simp [resolveName, different, ih] <;> rfl

/-- Source annotations are checked against the scope, not trusted as bindings. -/
inductive Named : Ty → Type where
  | name : String → Named type

def resolve (scope : Scope) : Expr Named type → Except Error (LocalExpr scope.types type)
  | .literal value => .ok (.literal value)
  | .read (.name name) => do return .read (← resolveName scope name type)
  | .unary op arg => do return .unary op (← resolve scope arg)
  | .binary op left right => do return .binary op (← resolve scope left) (← resolve scope right)
  | .ite test yes no => do return .ite (← resolve scope test) (← resolve scope yes) (← resolve scope no)
  | .and left right => do return .and (← resolve scope left) (← resolve scope right)
  | .or left right => do return .or (← resolve scope left) (← resolve scope right)

/-- Structural elaboration judgment, with an independently stated lexical
binding relation at leaves. It does not mention the resolver implementation. -/
inductive Elaborates (scope : Scope) : Expr Named type → LocalExpr scope.types type → Prop where
  | literal : Elaborates scope (.literal value) (.literal value)
  | read : Resolves scope name var → Elaborates scope (.read (.name name)) (.read var)
  | unary : Elaborates scope source target →
      Elaborates scope (.unary op source) (.unary op target)
  | binary : Elaborates scope a x → Elaborates scope b y →
      Elaborates scope (.binary op a b) (.binary op x y)
  | ite : Elaborates scope test check → Elaborates scope yes a → Elaborates scope no b →
      Elaborates scope (.ite test yes no) (.ite check a b)
  | and : Elaborates scope a x → Elaborates scope b y → Elaborates scope (.and a b) (.and x y)
  | or : Elaborates scope a x → Elaborates scope b y → Elaborates scope (.or a b) (.or x y)

theorem resolve_sound (scope : Scope) (source : Expr Named type) (target : LocalExpr scope.types type)
    (h : resolve scope source = .ok target) : Elaborates scope source target := by
  induction source with
  | literal value => cases h; exact .literal
  | @read ty ref =>
      cases ref with
      | name name =>
          simp only [resolve] at h
          cases hr : resolveName scope name ty with
          | error error => simp [hr] at h <;> cases h
          | ok var => simp [hr] at h; cases h; exact .read (resolveName_sound _ _ _ _ hr)
  | unary op arg ih =>
      simp only [resolve] at h
      cases hr : resolve scope arg with
      | error error => simp [hr] at h <;> cases h
      | ok next => simp [hr] at h; cases h; exact .unary (ih next hr)
  | binary op a b ia ib =>
      simp only [resolve] at h
      cases ha : resolve scope a with
      | error error => simp [ha] at h <;> cases h
      | ok x => cases hb : resolve scope b with
        | error error => simp [ha, hb] at h <;> cases h
        | ok y => simp [ha, hb] at h; cases h; exact .binary (ia x ha) (ib y hb)
  | ite test yes no it iy ino =>
      simp only [resolve] at h
      cases ht : resolve scope test with
      | error error => simp [ht] at h <;> cases h
      | ok check => cases hy : resolve scope yes with
        | error error => simp [ht, hy] at h <;> cases h
        | ok a => cases hn : resolve scope no with
          | error error => simp [ht, hy, hn] at h <;> cases h
          | ok b => simp [ht, hy, hn] at h; cases h; exact .ite (it check ht) (iy a hy) (ino b hn)
  | and a b ia ib =>
      simp only [resolve] at h
      cases ha : resolve scope a with
      | error error => simp [ha] at h <;> cases h
      | ok x => cases hb : resolve scope b with
        | error error => simp [ha, hb] at h <;> cases h
        | ok y => simp [ha, hb] at h; cases h; exact .and (ia x ha) (ib y hb)
  | or a b ia ib =>
      simp only [resolve] at h
      cases ha : resolve scope a with
      | error error => simp [ha] at h <;> cases h
      | ok x => cases hb : resolve scope b with
        | error error => simp [ha, hb] at h <;> cases h
        | ok y => simp [ha, hb] at h; cases h; exact .or (ia x ha) (ib y hb)

theorem resolve_complete (h : Elaborates scope source target) :
    resolve scope source = .ok target := by
  induction h with
  | literal => rfl
  | read h => simp [resolve, resolveName_complete h] <;> rfl
  | unary _ ih => simp [resolve, ih] <;> rfl
  | binary _ _ ia ib => simp [resolve, ia, ib] <;> rfl
  | ite _ _ _ it iy ino => simp [resolve, it, iy, ino] <;> rfl
  | and _ _ ia ib => simp [resolve, ia, ib] <;> rfl
  | or _ _ ia ib => simp [resolve, ia, ib] <;> rfl

/-- The resolved program reads exactly the values attached to the lexical
bindings used by elaboration. No condition is imposed on unbound names. -/
def Agrees (scope : Scope) (env : Env scope.types)
    (read : ∀ {type}, Named type → type.Value) : Prop :=
  ∀ {type} (name : String) (var : Var scope.types type), Resolves scope name var →
    read (.name name) = env.get var

theorem Elaborates.eval (h : Elaborates scope source target)
    (env : Env scope.types) (read : ∀ {type}, Named type → type.Value)
    (agrees : Agrees scope env read) (order : OperandOrder) :
    Expr.eval env.get order target = Expr.eval read order source := by
  induction h with
  | literal => rfl
  | read binding => exact congrArg Except.ok (agrees _ _ binding).symm
  | unary _ ih => simp only [Expr.eval, ih]
  | binary _ _ ia ib => cases order <;> simp only [Expr.eval, ia, ib]
  | ite _ _ _ it iy ino => simp only [Expr.eval, it, iy, ino]
  | and _ _ ia ib => simp only [Expr.eval, ia, ib]
  | or _ _ ia ib => simp only [Expr.eval, ia, ib]

theorem resolve_preserves (h : resolve scope source = .ok target)
    (env : Env scope.types) (read : ∀ {type}, Named type → type.Value)
    (agrees : Agrees scope env read) (order : OperandOrder) :
    Expr.eval env.get order target = Expr.eval read order source :=
  (resolve_sound scope source target h).eval env read agrees order

end Solidity.Frontend
