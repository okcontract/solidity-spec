/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Transfers

/-! Checked placement and inventory for a supplied most-base-first declaration
bundle. Its C3 order and nonstorage declaration validity are supplied inputs.
The layout checker validates physical persistent/transient placements before
computing positions. -/
namespace Solidity.Aggregates
open Static

private theorem declaration_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem declaration_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] declaration_map_error declaration_map_ok Bind.bind Except.bind Pure.pure Except.pure

def StorageDeclaration.stored (declaration : StorageDeclaration) : Bool :=
  match declaration.kind with | .persistent | .transient => true | _ => false

def DeclarationLayout.Geometry (layout : DeclarationLayout) : Prop :=
  layout.persistentEnd.endSlot < storageLimit ∧ layout.transientEnd.endSlot < storageLimit ∧
  ∀ field ∈ layout.fields, field.position.byte.val + (storageBytes field.declaration.type).getD 32 ≤ 32

private theorem geometry_cons {layout : DeclarationLayout} {field : DeclarationPosition}
    (valid : layout.Geometry)
    (fits : field.position.byte.val + (storageBytes field.declaration.type).getD 32 ≤ 32) :
    ({layout with fields := field :: layout.fields} : DeclarationLayout).Geometry := by
  refine ⟨valid.1, valid.2.1, ?_⟩
  intro member inside
  rcases List.mem_cons.mp inside with same | rest
  · subst member; exact fits
  · exact valid.2.2 member rest

theorem declarationItems_valid
    (computed : declarationItems registry fuel items persistent transient = .ok layout) :
    layout.fields.map (fun field => (field.contract, field.declaration)) =
      items.filter (fun item => item.2.stored) ∧ layout.Geometry := by
  induction items generalizing fuel persistent transient layout with
  | nil =>
      simp only [declarationItems, finishDeclarations] at computed
      split at computed
      · rename_i bounded
        simp only [Bool.and_eq_true, decide_eq_true_eq] at bounded
        cases computed
        exact ⟨rfl, bounded.1, bounded.2, by intro field member; cases member⟩
      · cases computed
  | cons entry rest ih =>
      rcases entry with ⟨identity, declaration⟩
      cases fuel with
      | zero => cases computed
      | succ fuel =>
          simp only [declarationItems] at computed
          cases kind : declaration.kind <;> simp only [kind] at computed
          case constant => simpa [StorageDeclaration.stored, kind] using ih computed
          case immutable => simpa [StorageDeclaration.stored, kind] using ih computed
          case persistent =>
            cases sized : storageSize registry fuel declaration.type with
            | error failure => simp [sized] at computed
            | ok slots =>
                simp only [sized, Bind.bind, Except.bind] at computed
                cases allocated : allocateStorage persistent ((storageBytes declaration.type).getD 32) slots with
                | error failure => simp [allocated] at computed
                | ok positions =>
                    rcases positions with ⟨here, next⟩
                    have fits := (allocateStorage_valid allocated).2.2.2.1
                    simp only [allocated] at computed
                    cases continued : declarationItems registry fuel rest next transient with
                    | error failure => simp [continued] at computed
                    | ok after =>
                        have prior := ih continued
                        simp only [continued] at computed
                        cases computed
                        refine ⟨?_, geometry_cons prior.2 fits⟩
                        simp only [List.map_cons, prior.1]
                        simp [StorageDeclaration.stored, kind]
          case transient =>
            cases sized : storageBytes declaration.type with
            | none => simp [sized] at computed
            | some bytes =>
                simp only [sized] at computed
                cases allocated : allocateStorage transient bytes 1 with
                | error failure => simp [allocated] at computed
                | ok positions =>
                    rcases positions with ⟨here, next⟩
                    have fits := (allocateStorage_valid allocated).2.2.2.1
                    simp only [allocated, Bind.bind, Except.bind] at computed
                    cases continued : declarationItems registry fuel rest persistent next with
                    | error failure => simp [continued] at computed
                    | ok after =>
                        have prior := ih continued
                        simp only [continued] at computed
                        cases computed
                        refine ⟨?_, geometry_cons prior.2 (by simpa only [sized] using fits)⟩
                        simp only [List.map_cons, prior.1]
                        simp [StorageDeclaration.stored, kind]

def declarationBundle (contracts : List (Nat × List StorageDeclaration)) : List (Nat × StorageDeclaration) :=
  contracts.flatMap fun (identity, fields) => fields.map fun field => (identity, field)

theorem declarationLayout_valid
    (computed : declarationLayout registry fuel base contracts = .ok layout) :
    layout.fields.map (fun field => (field.contract, field.declaration)) =
      (declarationBundle contracts).filter (fun item => item.2.stored) ∧ layout.Geometry := by
  unfold declarationLayout at computed
  split at computed
  · exact declarationItems_valid computed
  · cases computed

def declarationPlacement (registry : Registry) (fuel : Nat) (declaration : StorageDeclaration) : Result Unit :=
  match declaration.kind with
  | .persistent => eligibleAt registry fuel (.storage 0) declaration.type
  | .transient => eligibleAt registry fuel (.transient 0) declaration.type
  | .constant | .immutable => .ok ()

def checkDeclarationPlacements (registry : Registry) (fuel : Nat) : List (Nat × StorageDeclaration) → Result Unit
  | [] => .ok ()
  | (_, declaration) :: rest => do
      declarationPlacement registry fuel declaration
      checkDeclarationPlacements registry fuel rest

theorem checkDeclarationPlacements_iff :
    checkDeclarationPlacements registry fuel items = .ok () ↔
      ∀ item ∈ items, declarationPlacement registry fuel item.2 = .ok () := by
  induction items with
  | nil => simp [checkDeclarationPlacements]
  | cons item rest ih =>
      rcases item with ⟨identity, declaration⟩
      cases checked : declarationPlacement registry fuel declaration with
      | error failure => simp [checkDeclarationPlacements, checked]
      | ok token => cases token; simpa [checkDeclarationPlacements, checked] using ih

def checkedDeclarationLayout (registry : Registry) (fuel base : Nat)
    (contracts : List (Nat × List StorageDeclaration)) : Result DeclarationLayout := do
  checkDeclarationPlacements registry fuel (declarationBundle contracts)
  declarationLayout registry fuel base contracts

theorem checkedDeclarationLayout_valid
    (computed : checkedDeclarationLayout registry fuel base contracts = .ok layout) :
    (∀ item ∈ declarationBundle contracts, declarationPlacement registry fuel item.2 = .ok ()) ∧
      layout.fields.map (fun field => (field.contract, field.declaration)) =
        (declarationBundle contracts).filter (fun item => item.2.stored) ∧ layout.Geometry := by
  unfold checkedDeclarationLayout at computed
  cases checked : checkDeclarationPlacements registry fuel (declarationBundle contracts) with
  | error failure => simp [checked] at computed
  | ok token =>
      cases token
      simp only [checked, Bind.bind, Except.bind] at computed
      exact ⟨checkDeclarationPlacements_iff.mp checked, declarationLayout_valid computed⟩

end Solidity.Aggregates
