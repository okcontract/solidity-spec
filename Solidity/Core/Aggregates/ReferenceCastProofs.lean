/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.ReferenceCasts

/-! Independent physical-prefix observations for explicit bytes conversion.
The relation names each resolved byte cell and its source read. It contains no
complete-cast equation or desired fixed-byte postcondition. -/
namespace Solidity.Aggregates.ReferenceCasts
open Core Static

private theorem prefix_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem prefix_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] prefix_map_error prefix_map_ok Bind.bind Except.bind Pure.pure Except.pure

inductive ReadPairs (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ReadPairs relation [] []
  | cons (head : relation item value) (tail : ReadPairs relation items values) :
      ReadPairs relation (item :: items) (value :: values)

theorem ReadPairs.length_eq (read : ReadPairs relation items values) : items.length = values.length := by
  induction read with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

private theorem mapM_forall₂ (operation : α → Result β) (relation : α → β → Prop)
    (law : ∀ item value, operation item = .ok value ↔ relation item value)
    (items : List α) (values : List β) : items.mapM operation = .ok values ↔ ReadPairs relation items values := by
  induction items generalizing values with
  | nil =>
      constructor
      · intro same; cases same; exact .nil
      · intro related; cases related; rfl
  | cons item items ih =>
      rw [List.mapM_cons]
      constructor
      · intro finished
        cases read : operation item with
        | error failure => simp [read] at finished
        | ok value =>
            simp only [read, Bind.bind, Except.bind] at finished
            cases rest : items.mapM operation with
            | error failure => simp [rest] at finished
            | ok tail =>
                simp only [rest, Pure.pure, Except.pure] at finished
                cases finished
                exact .cons ((law _ _).mp read) ((ih _).mp rest)
      · intro related
        cases related with
        | cons head tail =>
            simp only [(law _ _).mpr head, (ih _).mpr tail, Bind.bind, Except.bind, Pure.pure, Except.pure]

def PhysicalByteRead (registry : Registry) (fuel : Nat) (heap : Heap)
    (source : Place) (index : Nat) (byte : UInt8) : Prop :=
  ∃ child, Access.index registry fuel heap source index = .ok child ∧
    ∃ value : BitVec 8, Access.read heap child = .ok ⟨.fixedBytes 0, value⟩ ∧ byte = value.toNat.toUInt8

private def readPrefixByte (registry : Registry) (fuel : Nat) (heap : Heap)
    (source : Place) (index : Nat) : Result UInt8 := do
  let child ← Access.index registry fuel heap source index
  let value ← Access.read heap child
  match value with
  | ⟨.fixedBytes width, value⟩ => if width = 0 then pure value.toNat.toUInt8 else throw .rejected
  | _ => throw .rejected

private theorem readPrefixByte_iff : readPrefixByte registry fuel heap source index = .ok byte ↔
    PhysicalByteRead registry fuel heap source index byte := by
  unfold readPrefixByte
  constructor
  · intro finished
    cases selected : Access.index registry fuel heap source index with
    | error failure => simp [selected] at finished
    | ok child =>
        simp only [selected, Bind.bind, Except.bind] at finished
        cases read : Access.read heap child with
        | error failure => simp [read] at finished
        | ok box =>
            rcases box with ⟨type, value⟩
            simp only [read] at finished
            cases type <;> simp only at finished
            all_goals try cases finished
            case fixedBytes width =>
              by_cases zero : width = 0
              · subst width
                simp only [↓reduceIte, Pure.pure, Except.pure] at finished
                cases finished
                exact ⟨child, selected, value, read, rfl⟩
              · simp [zero] at finished
  · rintro ⟨child, selected, value, read, rfl⟩
    simp only [selected, Bind.bind, Except.bind, read, ↓reduceIte, Pure.pure, Except.pure]
    rfl

/-- The bytes packet is exactly the sequence of physical used-cell reads in
increasing index order. This covers storage, memory and admitted calldata views. -/
theorem sourceBytes_physical_iff :
    Copy.sourceBytes registry fuel heap ⟨.bytes location pointer, reference⟩ 0 count = .ok bytes ↔
    ReadPairs (PhysicalByteRead registry fuel heap ⟨.bytes location pointer, reference⟩)
      (List.range count) bytes := by
  simp only [Copy.sourceBytes, Bind.bind, Except.bind, Pure.pure, Except.pure, Nat.zero_add]
  change (List.range count).mapM (readPrefixByte registry fuel heap
    ⟨.bytes location pointer, reference⟩) = .ok bytes ↔ _
  exact mapM_forall₂ _ _ (fun _ _ => readPrefixByte_iff) _ _

/-- Physical cast representation, bidirectional: successful bounded reads
produce exactly the zero-padded scalar and every such read derivation executes. -/
theorem toFixedBytes_physical_iff :
    toFixedBytes registry fuel budget heap ⟨.bytes location pointer, reference⟩ width = .ok (value, remaining) ↔
    ∃ length bytes,
      Access.sourceLength registry fuel heap ⟨.bytes location pointer, reference⟩ = .ok length ∧
      reserve budget (min (width.val+1) length+1) = .ok remaining ∧
      ReadPairs (PhysicalByteRead registry fuel heap ⟨.bytes location pointer, reference⟩)
        (List.range (min (width.val+1) length)) bytes ∧
      value = ⟨.fixedBytes width, prefixValue width bytes⟩ := by
  rw [toFixedBytes_iff]
  constructor
  · rintro ⟨length, bytes, readLength, reserved, read, result⟩
    exact ⟨length, bytes, readLength, reserved, sourceBytes_physical_iff.mp read, result⟩
  · rintro ⟨length, bytes, readLength, reserved, read, result⟩
    exact ⟨length, bytes, readLength, reserved, sourceBytes_physical_iff.mpr read, result⟩

theorem physical_prefix_length
    (read : ReadPairs (PhysicalByteRead registry fuel heap source) (List.range count) bytes) :
    bytes.length = count := by simpa using read.length_eq.symm

theorem cast_prefix_observation_bounded {width : Width} {length : Nat}
    (read : ReadPairs (PhysicalByteRead registry fuel heap source)
      (List.range (min (width.val+1) length)) bytes) : bytes.length ≤ 32 := by
  rw [physical_prefix_length read]
  exact prefix_work_bounded width length

end Solidity.Aggregates.ReferenceCasts
