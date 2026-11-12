/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.BinaryTyping

namespace Solidity.Frontend.Inference
open Core Static Lexical



/-- Structural expression elaboration, with node semantics factored out. Operator
nodes use the typed ScalarUnary/ScalarBinary rules and literal computation;
conversion nodes use the independent Materializes judgment above. Lexical
recognition is explicit here; exact source-byte correspondence is an
input assumption. -/
inductive Elaborates (context : Context) : Source → Term context → Prop where
  | name : named context name = .ok result → Elaborates context (.name name) result
  | number : numeric spelling unit = .ok result → Elaborates context (.number spelling unit) result
  | string : stringPieces pieces = .ok bytes → Elaborates context (.string pieces) (.string bytes)
  | bool : Elaborates context (.bool value) (.runtime .bool (.literal value))
  | unary : Elaborates context arg a → UnaryTyping context code a result → Elaborates context (.unary code arg) result
  | binary : Elaborates context left a → Elaborates context right b → BinaryTyping code a b result →
      Elaborates context (.binary code left right) result
  | cast : Elaborates context arg a → Materializes (.explicit kind) a type expression →
      Elaborates context (.cast kind type arg) (.runtime type expression)
  | ite : Elaborates context test t → Elaborates context yes a → Elaborates context no b →
      ConditionalTyping t a b result → Elaborates context (.ite test yes no) result
  | wrap {base : Elementary} {expression : SourceExpr context base.source} : Elaborates context arg a → Materializes .implicit a base.source expression →
      Elaborates context (.wrap identity base arg) (.runtime (.valueType identity base) (.wrap identity base expression))
  | unwrap {identity : Nat} {base : Elementary} {expression : SourceExpr context (.valueType identity base)} : Elaborates context arg a → Materializes .implicit a (.valueType identity base) expression →
      Elaborates context (.unwrap identity base arg) (.runtime base.source (.unwrap identity base expression))

variable {context : Context} {source : Source} {result : Term context}

private theorem bind_ok_iff (action : Except ε α) (next : α → Except ε β) (value : β) :
    (action >>= next) = .ok value ↔ ∃ arg, action = .ok arg ∧ next arg = .ok value := by
  cases action with
  | error error =>
      change (Except.error error : Except ε β) = .ok value ↔ _
      simp
  | ok arg =>
      change next arg = .ok value ↔ _
      simp

private theorem except_bind_ok (arg : α) (next : α → Except ε β) :
    (Except.ok arg >>= next) = next arg := rfl
private theorem except_bind_error (error : ε) (next : α → Except ε β) :
    (Except.error error >>= next) = .error error := rfl
private theorem except_map_ok (arg : α) (f : α → β) :
    (f <$> (Except.ok arg : Except ε α)) = .ok (f arg) := rfl
private theorem except_pure (value : α) : (pure value : Except ε α) = .ok value := rfl
attribute [local simp] except_bind_ok except_bind_error except_map_ok except_pure

theorem infer_complete (valid : Elaborates context source result) : infer context source = .ok result := by
  induction valid with
  | name h => exact h
  | number h => exact h
  | string h => simp [infer, h, Except.map, Except.mapError]
  | bool => rfl
  | unary _ h ih => simp [infer, ih, unary_complete h]
  | binary _ _ h il ir => simp [infer, il, ir, binary_iff.mpr h]
  | cast _ h ih => simp [infer, ih, materialize_complete h]
  | ite _ _ _ h it iy ino => simp [infer, it, iy, ino, conditional_complete h]
  | wrap _ h ih => simp [infer, ih, wrapTerm, materialize_complete h]
  | unwrap _ h ih => simp [infer, ih, unwrapTerm, materialize_complete h]

theorem infer_sound (checked : infer context source = .ok result) : Elaborates context source result := by
  induction source generalizing result with
  | name name => exact .name checked
  | number spelling unit => exact .number checked
  | string pieces =>
      cases h : stringPieces pieces with
      | error error => simp [infer, h, Except.map, Except.mapError] at checked
      | ok bytes => simp [infer, h, Except.map, Except.mapError] at checked; subst result; exact .string h
  | bool value => simp only [infer, Except.ok.injEq] at checked; subst result; exact .bool
  | unary code arg ih =>
      obtain ⟨a, ha, h⟩ := (bind_ok_iff _ _ _).mp checked
      exact .unary (ih ha) (unary_sound h)
  | binary code left right il ir =>
      obtain ⟨a, ha, h⟩ := (bind_ok_iff _ _ _).mp checked
      obtain ⟨b, hb, h⟩ := (bind_ok_iff _ _ _).mp h
      exact .binary (il ha) (ir hb) (binary_iff.mp h)
  | cast kind type arg ih =>
      obtain ⟨a, ha, h⟩ := (bind_ok_iff _ _ _).mp checked
      obtain ⟨value, hv, eq⟩ := (bind_ok_iff _ _ _).mp h
      cases eq
      exact .cast (ih ha) (materialize_sound hv)
  | ite test yes no it iy ino =>
      obtain ⟨t, ht, h⟩ := (bind_ok_iff _ _ _).mp checked
      obtain ⟨a, ha, h⟩ := (bind_ok_iff _ _ _).mp h
      obtain ⟨b, hb, h⟩ := (bind_ok_iff _ _ _).mp h
      exact .ite (it ht) (iy ha) (ino hb) (conditional_sound h)
  | wrap identity base arg ih =>
      obtain ⟨a, ha, h⟩ := (bind_ok_iff _ _ _).mp checked
      obtain ⟨value, hv, eq⟩ := (bind_ok_iff _ _ _).mp h
      cases eq
      exact .wrap (ih ha) (materialize_sound hv)
  | unwrap identity base arg ih =>
      obtain ⟨a, ha, h⟩ := (bind_ok_iff _ _ _).mp checked
      obtain ⟨value, hv, eq⟩ := (bind_ok_iff _ _ _).mp h
      cases eq
      exact .unwrap (ih ha) (materialize_sound hv)

theorem infer_iff : infer context source = .ok result ↔ Elaborates context source result :=
  ⟨infer_sound, infer_complete⟩

/-- In particular, constant conditions cannot excuse ill-typed branches. This
is a static theorem, independent of the lazy evaluation rules. -/
theorem conditional_checks_both (checked : infer context (.ite test yes no) = .ok result) :
    ∃ a b, Elaborates context yes a ∧ Elaborates context no b := by
  cases infer_sound checked with
  | ite _ yes no _ => exact ⟨_, _, yes, no⟩

theorem check_iff {type : SType} {expression : SourceExpr context type} : check context source type = .ok expression ↔
    ∃ result, Elaborates context source result ∧ Materializes .implicit result type expression := by
  simp only [check, bind_ok_iff, infer_iff, materialize_iff]

end Solidity.Frontend.Inference
