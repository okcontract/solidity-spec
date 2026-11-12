/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Unary

namespace Solidity.Static

/-- Resolved nominal metadata. Registry construction from declarations
and inheritance/visibility validation are caller responsibilities. Static clients may not assign two different
member counts, underlying types, or base lists to the same nominal identity. -/
structure Registry where
  enumerations : Nat → Option (Fin 256)
  valueTypes : Nat → Option Elementary
  contracts : Nat → Option (Bool × List Nat)
  structures : Nat → Bool
  /-- Resolved member order and types. These are supplied from declarations;
  aggregate access rejects an absent definition instead of guessing a layout. -/
  structFields : Nat → Option (List (String × SType)) := fun _ => none

mutual
inductive WellFormed (registry : Registry) : SType → Prop where
  | uint : WellFormed registry (.uint width)
  | sint : WellFormed registry (.sint width)
  | fixedBytes : WellFormed registry (.fixedBytes width)
  | bool : WellFormed registry .bool
  | address : WellFormed registry (.address payable)
  | enumType : registry.enumerations identity = some members → WellFormed registry (.enumType identity members)
  | valueType : registry.valueTypes identity = some base → WellFormed registry (.valueType identity base)
  | contract : registry.contracts identity = some (payable, bases) → WellFormed registry (.contract identity payable bases)
  | function : (visibility = .internal → mutability ≠ .payable) →
      WellFormedTypes registry parameters → WellFormedTypes registry returns →
      WellFormed registry (.function visibility mutability parameters returns)
  | fixedPoint : WellFormed registry (.fixedPoint signed width decimals)
  | array : WellFormed registry element → (∀ n, length = some n → 0 < n) →
      WellFormed registry (.array element length location pointer)
  | bytes : WellFormed registry (.bytes location pointer)
  | string : WellFormed registry (.string location pointer)
  | structType : registry.structures identity = true → WellFormed registry (.structType identity location pointer)
  | mapping : WellFormed registry key → WellFormed registry value → WellFormed registry (.mapping key value)
  | tuple : WellFormedTypes registry components → WellFormed registry (.tuple components)
  | metaType : WellFormed registry type → WellFormed registry (.metaType type)
  | superType : registry.contracts identity = some metadata → WellFormed registry (.superType identity)
  | omitted : WellFormed registry .omitted

inductive WellFormedTypes (registry : Registry) : Types → Prop where
  | nil : WellFormedTypes registry .nil
  | cons : WellFormed registry first → WellFormedTypes registry rest → WellFormedTypes registry (.cons first rest)
end

/- These checks establish nominal consistency and structural formation. Context
restrictions such as legal mapping keys, external ABI signatures, location and
storage eligibility are separate placement, declaration and ABI judgments, not implied by this one. -/
mutual
def wellFormed (registry : Registry) : SType → Bool
  | .enumType identity members => registry.enumerations identity == some members
  | .valueType identity base => registry.valueTypes identity == some base
  | .contract identity payable bases => registry.contracts identity == some (payable, bases)
  | .function visibility mutability parameters returns =>
      (visibility != .internal || mutability != .payable) &&
        wellFormedTypes registry parameters && wellFormedTypes registry returns
  | .array element length _ _ => wellFormed registry element &&
      (match length with | none => true | some n => n > 0)
  | .structType identity _ _ => registry.structures identity
  | .mapping key value => wellFormed registry key && wellFormed registry value
  | .tuple components => wellFormedTypes registry components
  | .metaType type => wellFormed registry type
  | .superType identity => (registry.contracts identity).isSome
  | _ => true

def wellFormedTypes (registry : Registry) : Types → Bool
  | .nil => true
  | .cons first rest => wellFormed registry first && wellFormedTypes registry rest
end

theorem enum_metadata_unique (a : WellFormed registry (.enumType identity membersA))
    (b : WellFormed registry (.enumType identity membersB)) : membersA = membersB := by
  cases a with | enumType ha => cases b with | enumType hb => exact Option.some.inj (ha.symm.trans hb)

theorem valueType_metadata_unique (a : WellFormed registry (.valueType identity baseA))
    (b : WellFormed registry (.valueType identity baseB)) : baseA = baseB := by
  cases a with | valueType ha => cases b with | valueType hb => exact Option.some.inj (ha.symm.trans hb)

theorem contract_metadata_unique (a : WellFormed registry (.contract identity payA basesA))
    (b : WellFormed registry (.contract identity payB basesB)) : payA = payB ∧ basesA = basesB := by
  cases a with | contract ha => cases b with | contract hb =>
    exact Prod.mk.inj (Option.some.inj (ha.symm.trans hb))

theorem wellFormed_complete (valid : WellFormed registry type) : wellFormed registry type = true := by
  induction valid using WellFormed.rec (motive_2 := fun types _ => wellFormedTypes registry types = true) with
  | uint | sint | fixedBytes | bool | address | fixedPoint | bytes | string | omitted => rfl
  | enumType h => simp [wellFormed, h]
  | valueType h => simp [wellFormed, h]
  | contract h => simp [wellFormed, h]
  | @function visibility mutability ps rs allowed _ _ hp hr =>
      simp only [wellFormed, hp, hr, Bool.and_true, Bool.or_eq_true, bne_iff_ne]
      cases visibility <;> cases mutability <;> simp_all
  | @array elem len loc ptr _ length ih =>
      simp only [wellFormed, ih, Bool.true_and]
      cases lengthValue : len with
      | none => rfl
      | some n => exact decide_eq_true (length n lengthValue)
  | structType h => exact h
  | mapping _ _ hk hv => simp [wellFormed, hk, hv]
  | tuple _ ih => exact ih
  | metaType _ ih => exact ih
  | superType h => simp [wellFormed, h]
  | nil => rfl
  | cons _ _ hf hr => simp [wellFormedTypes, hf, hr]

theorem wellFormedTypes_complete (valid : WellFormedTypes registry types) : wellFormedTypes registry types = true :=
  wellFormed_complete (.tuple valid)

theorem wellFormed_sound (checked : wellFormed registry type = true) : WellFormed registry type := by
  revert checked
  induction type using SType.rec
      (motive_2 := fun types => wellFormedTypes registry types = true → WellFormedTypes registry types) with
  | uint => intro _; exact .uint
  | sint => intro _; exact .sint
  | fixedBytes => intro _; exact .fixedBytes
  | bool => intro _; exact .bool
  | address => intro _; exact .address
  | enumType identity members => intro h; exact .enumType (by simpa [wellFormed] using h)
  | valueType identity base => intro h; exact .valueType (by simpa [wellFormed] using h)
  | contract identity payable bases => intro h; exact .contract (by simpa [wellFormed] using h)
  | function visibility mutability parameters returns hp hr =>
      intro h
      simp only [wellFormed, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at h
      have allowed : visibility = .internal → mutability ≠ .payable := by
        intro eq
        rcases h.1.1 with no | valid
        · exact False.elim (no eq)
        · exact valid
      exact .function allowed (hp h.1.2) (hr h.2)
  | fixedPoint => intro _; exact .fixedPoint
  | array element length location pointer ih =>
      intro h
      simp only [wellFormed, Bool.and_eq_true] at h
      refine .array (ih h.1) ?_
      intro n hn
      simpa [hn] using h.2
  | bytes => intro _; exact .bytes
  | string => intro _; exact .string
  | structType identity location pointer => intro h; exact .structType h
  | mapping key value hk hv =>
      intro h; have parts := (Bool.and_eq_true _ _).mp h
      exact .mapping (hk parts.1) (hv parts.2)
  | tuple components ih => intro h; exact .tuple (ih h)
  | metaType type ih => intro h; exact .metaType (ih h)
  | superType identity =>
      intro h
      cases hc : registry.contracts identity with
      | none => simp [wellFormed, hc] at h
      | some metadata => exact .superType hc
  | omitted => intro _; exact .omitted
  | nil _ => exact .nil
  | cons first rest hf hr h =>
      have parts := (Bool.and_eq_true _ _).mp h
      exact .cons (hf parts.1) (hr parts.2)

theorem wellFormedTypes_sound (checked : wellFormedTypes registry types = true) : WellFormedTypes registry types := by
  have h : WellFormed registry (.tuple types) := wellFormed_sound checked
  cases h with | tuple h => exact h

theorem wellFormed_iff : wellFormed registry type = true ↔ WellFormed registry type :=
  ⟨wellFormed_sound, wellFormed_complete⟩

theorem wellFormedTypes_iff : wellFormedTypes registry types = true ↔ WellFormedTypes registry types :=
  ⟨wellFormedTypes_sound, wellFormedTypes_complete⟩

end Solidity.Static
