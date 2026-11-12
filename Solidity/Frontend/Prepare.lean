/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Traversal
import Solidity.Frontend.Resolve
import Solidity.Frontend.Literal

/-! Elaboration of typed expressions containing lexical names and exact constant
subexpressions. Operator/type annotations are still explicit input: this stage
checks bindings and constant representability, not parsing or type inference. -/
namespace Solidity.Frontend
open Core

inductive SourceLeaf : Ty → Type where
  | name : String → SourceLeaf type
  | uint : (width : Width) → Literal.Expr → SourceLeaf (.uint width)
  | sint : (width : Width) → Literal.Expr → SourceLeaf (.sint width)

inductive PrepareError where
  | binding : Error → PrepareError
  | constant : Literal.Error → PrepareError
  deriving DecidableEq, Repr

def prepareLeaf (scope : Scope) : SourceLeaf type → Except PrepareError (LocalExpr scope.types type)
  | .name name => ((resolveName scope name type).mapError .binding).map Expr.read
  | .uint width expr => ((expr.unsigned width).mapError .constant).map Expr.literal
  | .sint width expr => ((expr.signed width).mapError .constant).map Expr.literal

def prepare (scope : Scope) (source : Expr SourceLeaf type) :
    Except PrepareError (LocalExpr scope.types type) := source.traverse (prepareLeaf scope)

/-- Independent leaf specification: lexical binding, or an integral constant
whose exact mathematical value is represented by the target word. -/
inductive LeafPrepared (scope : Scope) : SourceLeaf type → LocalExpr scope.types type → Prop where
  | name : Resolves scope name var → LeafPrepared scope (.name name) (.read var)
  | uint : expr.eval = .ok value → value.den = 1 → (word.toNat : Int) = value.num →
      LeafPrepared scope (.uint width expr) (.literal word)
  | sint : expr.eval = .ok value → value.den = 1 → word.toInt = value.num →
      LeafPrepared scope (.sint width expr) (.literal word)

abbrev Prepared (scope : Scope) (source : Expr SourceLeaf type) (target : LocalExpr scope.types type) :=
  Expr.Traverses (LeafPrepared scope) source target

theorem prepareLeaf_sound (scope : Scope) (source : SourceLeaf type)
    (target : LocalExpr scope.types type) (h : prepareLeaf scope source = .ok target) :
    LeafPrepared scope source target := by
  cases source with
  | name name =>
      cases he : resolveName scope name type with
      | error error => simp [prepareLeaf, he] at h <;> cases h
      | ok var =>
          simp [prepareLeaf, he] at h; cases h
          exact .name (resolveName_sound _ _ _ _ he)
  | uint width expr =>
      cases he : expr.unsigned width with
      | error error => simp [prepareLeaf, he] at h <;> cases h
      | ok word =>
          simp [prepareLeaf, he] at h; cases h
          obtain ⟨value, hv, hd, hw⟩ := Literal.Expr.unsigned_exact _ _ _ he
          exact .uint hv hd hw
  | sint width expr =>
      cases he : expr.signed width with
      | error error => simp [prepareLeaf, he] at h <;> cases h
      | ok word =>
          simp [prepareLeaf, he] at h; cases h
          obtain ⟨value, hv, hd, hw⟩ := Literal.Expr.signed_exact _ _ _ he
          exact .sint hv hd hw

theorem prepareLeaf_complete (h : LeafPrepared scope source target) :
    prepareLeaf scope source = .ok target := by
  cases h with
  | name h => simp [prepareLeaf, resolveName_complete h] <;> rfl
  | uint hv hd hw =>
      have hc := (Literal.Expr.unsigned_iff _ _ _).mpr ⟨_, hv, hd, hw⟩
      simp [prepareLeaf, hc] <;> rfl
  | sint hv hd hw =>
      have hc := (Literal.Expr.signed_iff _ _ _).mpr ⟨_, hv, hd, hw⟩
      simp [prepareLeaf, hc] <;> rfl

theorem prepare_sound (h : prepare scope source = .ok target) : Prepared scope source target :=
  Expr.traverse_sound (prepareLeaf scope) (LeafPrepared scope) (prepareLeaf_sound scope) source target h

theorem prepare_complete (h : Prepared scope source target) : prepare scope source = .ok target :=
  Expr.traverse_complete (prepareLeaf scope) (LeafPrepared scope)
    (fun _ _ h => prepareLeaf_complete h) h

theorem prepare_iff : prepare scope source = .ok target ↔ Prepared scope source target :=
  ⟨prepare_sound, prepare_complete⟩

/-- A semantic reading assigns lexical names their environment values and
integral representable constants their mathematical values. It imposes no
meaning on names/constants that the frontend rejects. -/
structure SourceMeaning (scope : Scope) (env : Env scope.types)
    (read : ∀ {type}, SourceLeaf type → type.Value) : Prop where
  name : ∀ {type} (name : String) (var : Var scope.types type), Resolves scope name var →
    read (.name name) = env.get var
  uint : ∀ width expr value (word : BitVec width.bits), expr.eval = .ok value →
    value.den = 1 → (word.toNat : Int) = value.num → read (.uint width expr) = word
  sint : ∀ width expr value (word : BitVec width.bits), expr.eval = .ok value →
    value.den = 1 → word.toInt = value.num → read (.sint width expr) = word

theorem Prepared.eval (h : Prepared scope source target) (env : Env scope.types)
    (read : ∀ {type}, SourceLeaf type → type.Value) (meaning : SourceMeaning scope env read)
    (order : OperandOrder) : Expr.eval env.get order target = Expr.eval read order source := by
  apply Expr.Traverses.eval (LeafPrepared scope) read env.get order _ h
  intro type ref replacement leaf
  cases leaf with
  | name binding => exact congrArg Except.ok (meaning.name _ _ binding).symm
  | uint hv hd hw => exact congrArg Except.ok (meaning.uint _ _ _ _ hv hd hw).symm
  | sint hv hd hw => exact congrArg Except.ok (meaning.sint _ _ _ _ hv hd hw).symm

theorem prepare_preserves (h : prepare scope source = .ok target) (env : Env scope.types)
    (read : ∀ {type}, SourceLeaf type → type.Value) (meaning : SourceMeaning scope env read)
    (order : OperandOrder) : Expr.eval env.get order target = Expr.eval read order source :=
  (prepare_sound h).eval env read meaning order

end Solidity.Frontend
