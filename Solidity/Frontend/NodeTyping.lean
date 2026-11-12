/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Materialization

namespace Solidity.Frontend.Inference
open Core Static Lexical

/-- Declarative term conversion and mobility preserve literal information until
an operator actually demands a runtime representation. -/
def ImplicitTerm (term : Term context) (type : SType) : Prop :=
  match term with
  | .number value => NumberConverts .implicit value type
  | .string bytes => StringConverts bytes type
  | .runtime source _ => Implicit source type

theorem implicitTerm_iff (term : Term context) (type : SType) :
    term.implicitTo type = true ↔ ImplicitTerm term type := by
  cases term <;> simp [Term.implicitTo, ImplicitTerm, numberConverts_iff, stringConverts_iff, implicit_iff]

inductive Mobile : Term context → SType → Prop where
  | number : IntegerMobile value.value width →
      Mobile (.number value) (if value.value.num < 0 then .sint width else .uint width)
  | string : Mobile (.string bytes) (.string .memory true)
  | runtime : Mobile (.runtime type expression) type

theorem mobile_complete (valid : Mobile term type) : term.mobile = .ok type := by
  cases valid with
  | @number width value proof =>
      have valid := proof
      obtain ⟨_, _, _, _, fits⟩ := proof
      have integral := fits.1
      simp [Term.mobile, Frontend.mobile, integral, (integerMobile_iff _ _).mpr valid]
  | string => rfl
  | runtime => rfl

theorem mobile_sound (checked : term.mobile = .ok type) : Mobile term type := by
  cases term with
  | number value =>
      simp only [Term.mobile, Frontend.mobile] at checked
      split at checked
      next => cases checked
      next =>
        cases hm : integerMobile value.value with
        | none => simp [hm] at checked
        | some width =>
            simp only [hm, Except.ok.injEq] at checked
            subst type
            exact .number ((integerMobile_iff _ _).mp hm)
  | string => cases checked; exact .string
  | runtime => cases checked; exact .runtime

theorem mobile_iff : term.mobile = .ok type ↔ Mobile term type := ⟨mobile_sound, mobile_complete⟩

inductive CommonChoice (a b : Term context) : SType → Prop where
  | left : Mobile a type → ImplicitTerm b type → CommonChoice a b type
  | right : Mobile a left → ¬ ImplicitTerm b left → Mobile b type → ImplicitTerm a type →
      CommonChoice a b type

private theorem node_bind_ok (arg : α) (next : α → Except ε β) :
    (Except.ok arg >>= next) = next arg := rfl
private theorem node_bind_error (error : ε) (next : α → Except ε β) :
    (Except.error error >>= next) = .error error := rfl
private theorem node_pure (value : α) : (pure value : Except ε α) = .ok value := rfl
attribute [local simp] node_bind_ok node_bind_error node_pure

theorem commonTerm_complete (valid : CommonChoice a b type) : commonTerm a b = .ok type := by
  cases valid with
  | left mobile compatible =>
      simp [commonTerm, mobile_complete mobile, (implicitTerm_iff _ _).mpr compatible]
  | right mobile incompatible other compatible =>
      rename_i left
      have no : b.implicitTo left = false := by
        cases h : b.implicitTo left with
        | false => rfl
        | true => exact False.elim (incompatible ((implicitTerm_iff _ _).mp h))
      simp [commonTerm, mobile_complete mobile, no, mobile_complete other, (implicitTerm_iff _ _).mpr compatible]

theorem commonTerm_sound (checked : commonTerm a b = .ok type) : CommonChoice a b type := by
  unfold commonTerm at checked
  cases hl : a.mobile with
  | error error => simp [hl] at checked
  | ok left =>
      simp only [hl] at checked
      change (if b.implicitTo left then (Except.ok left : Except StaticError SType) else _) = Except.ok type at checked
      split at checked
      next compatible => cases checked; exact .left (mobile_sound hl) ((implicitTerm_iff _ _).mp compatible)
      next incompatible =>
        have no : ¬ ImplicitTerm b left := fun yes => incompatible ((implicitTerm_iff _ _).mpr yes)
        cases hr : b.mobile with
        | error error => simp [hr] at checked
        | ok right =>
            simp only [hr] at checked
            change (if a.implicitTo right then (Except.ok right : Except StaticError SType) else _) = Except.ok type at checked
            split at checked
            next compatible => cases checked; exact .right (mobile_sound hl) no (mobile_sound hr) ((implicitTerm_iff _ _).mp compatible)
            next => cases checked

theorem commonTerm_iff : commonTerm a b = .ok type ↔ CommonChoice a b type :=
  ⟨commonTerm_sound, commonTerm_complete⟩

/-- Runtime operator construction requires both independently permitted
conversions and an indexed primitive typing rule. -/
inductive RuntimeBinary (code : BinaryCode) (a b : Term context) (left right : SType) : Term context → Prop where
  | mk (operation : ScalarBinary code left right result) :
      Materializes .implicit a left x → Materializes .implicit b right y →
      RuntimeBinary code a b left right (.runtime result (.binary operation x y))

theorem runtimeBinary_complete (valid : RuntimeBinary code a b left right result) :
    runtimeBinary code a b left right = .ok result := by
  cases valid with
  | mk operation x y =>
      simp [runtimeBinary, materialize_complete x, materialize_complete y, checkBinary_complete operation]

theorem runtimeBinary_sound (checked : runtimeBinary code a b left right = .ok result) :
    RuntimeBinary code a b left right result := by
  unfold runtimeBinary at checked
  cases hb : checkBinary code left right with
  | none => simp [hb] at checked
  | some operation =>
      rcases operation with ⟨type, operation⟩
      cases hx : materialize .implicit a left with
      | error error => simp [hb, hx] at checked
      | ok x =>
          cases hy : materialize .implicit b right with
          | error error => simp [hb, hx, hy] at checked
          | ok y =>
              simp [hb, hx, hy] at checked
              cases checked
              exact .mk operation (materialize_sound hx) (materialize_sound hy)

theorem runtimeBinary_iff : runtimeBinary code a b left right = .ok result ↔
    RuntimeBinary code a b left right result := ⟨runtimeBinary_sound, runtimeBinary_complete⟩

inductive UnaryTyping (context : Context) : UnaryCode → Term context → Term context → Prop where
  | neg : Literal.Unary.neg.eval value.value = .ok result →
      UnaryTyping context .neg (.number value) (.number ⟨result, none⟩)
  | bitnot : Literal.Unary.bitnot.eval value.value = .ok result →
      UnaryTyping context .bitnot (.number value) (.number ⟨result, none⟩)
  | runtime (operation : ScalarUnary code type) : type.scalarSupported = true →
      UnaryTyping context code (.runtime type arg) (.runtime type (.unary operation arg))

theorem unary_complete (valid : UnaryTyping context code arg result) : unary code arg = .ok result := by
  cases valid with
  | neg h => simp [unary, h, Except.mapError]
  | bitnot h => simp [unary, h, Except.mapError]
  | runtime operation supported => simp [unary, supported, checkUnary_complete operation]

theorem unary_sound {context : Context} {arg result : Term context} (checked : unary code arg = .ok result) : UnaryTyping context code arg result := by
  cases arg with
  | string bytes => cases checked
  | runtime type expression =>
      simp only [unary] at checked
      split at checked
      next => cases checked
      next supported =>
        have support : type.scalarSupported = true := by simpa using supported
        cases hc : checkUnary code type with
        | none => simp [hc] at checked
        | some operation => simp [hc] at checked; subst result; exact .runtime operation support
  | number value =>
      cases code with
      | not => cases checked
      | neg =>
          cases hc : Literal.Unary.neg.eval value.value with
          | error error => simp [unary, hc, Except.mapError] at checked
          | ok number => simp [unary, hc, Except.mapError] at checked; subst result; exact .neg hc
      | bitnot =>
          cases hc : Literal.Unary.bitnot.eval value.value with
          | error error => simp [unary, hc, Except.mapError] at checked
          | ok number => simp [unary, hc, Except.mapError] at checked; subst result; exact .bitnot hc

theorem unary_iff {context : Context} {arg result : Term context} : unary code arg = .ok result ↔ UnaryTyping context code arg result :=
  ⟨unary_sound, unary_complete⟩

inductive ConditionalTyping (condition yes no : Term context) : Term context → Prop where
  | mk : Materializes .implicit condition .bool test → Mobile yes left → Mobile no right →
      Common left right type → Materializes .implicit yes type a → Materializes .implicit no type b →
      ConditionalTyping condition yes no (.runtime type (.ite test a b))

theorem conditional_complete (valid : ConditionalTyping condition yes no result) :
    conditional condition yes no = .ok result := by
  cases valid with
  | mk test left right common a b =>
      simp [conditional, materialize_complete test, mobile_complete left, mobile_complete right,
        (common_iff _ _ _).mpr common, materialize_complete a, materialize_complete b]

theorem conditional_sound (checked : conditional condition yes no = .ok result) :
    ConditionalTyping condition yes no result := by
  unfold conditional at checked
  cases ht : materialize .implicit condition .bool with
  | error error => simp [ht] at checked
  | ok test =>
      cases hl : yes.mobile with
      | error error => simp [ht, hl] at checked
      | ok left =>
          cases hr : no.mobile with
          | error error => simp [ht, hl, hr] at checked
          | ok right =>
              cases hc : common left right with
              | none => simp [ht, hl, hr, hc] at checked
              | some type =>
                  cases ha : materialize .implicit yes type with
                  | error error => simp [ht, hl, hr, hc, ha] at checked
                  | ok a =>
                      cases hb : materialize .implicit no type with
                      | error error => simp [ht, hl, hr, hc, ha, hb] at checked
                      | ok b =>
                          simp [ht, hl, hr, hc, ha, hb] at checked; subst result
                          exact .mk (materialize_sound ht) (mobile_sound hl) (mobile_sound hr)
                            ((common_iff _ _ _).mp hc) (materialize_sound ha) (materialize_sound hb)

theorem conditional_iff : conditional condition yes no = .ok result ↔ ConditionalTyping condition yes no result :=
  ⟨conditional_sound, conditional_complete⟩

end Solidity.Frontend.Inference
