/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Types

/-! Storage layout is intrinsic to resolved types. Location eligibility and
declaration resolution are separate judgments. Supplied contract declarations
are already in most-base-first C3 order; this module does not assume a hash is
injective or that different logical access paths occupy distinct slots. -/
namespace Solidity.Aggregates
open Static Core

def storageLimit : Nat := 2^256

structure StoragePosition where
  slot : Nat := 0
  byte : Fin 32 := 0
  deriving DecidableEq, Repr

def StoragePosition.linear (position : StoragePosition) : Nat :=
  position.slot * 32 + position.byte.val

/-- First whole slot after the occupied prefix. The strict bound follows the
pinned StorageOffsets::computeOffsets final extent check. -/
def StoragePosition.endSlot (position : StoragePosition) : Nat :=
  position.slot + if position.byte.val = 0 then 0 else 1

structure StorageField where
  name : String
  type : SType
  position : StoragePosition
  deriving DecidableEq, Repr

structure StorageLayout where
  fields : List StorageField
  next : StoragePosition
  deriving DecidableEq, Repr

def checkedStorageCount (count : Nat) : Result Nat :=
  if 0 < count && count < storageLimit then .ok count else .error .rejected

private def checkedStorageResult (result : Result Nat) : Result Nat := do
  checkedStorageCount (← result)

theorem checkedStorageCount_bounds (checked : checkedStorageCount count = .ok size) :
    size = count ∧ 0 < size ∧ size < storageLimit := by
  unfold checkedStorageCount at checked
  split at checked
  next valid => cases checked; simpa using valid
  next => cases checked

private theorem checkedStorageResult_bounds
    (checked : checkedStorageResult result = .ok size) : 0 < size ∧ size < storageLimit := by
  cases result with
  | error error => cases checked
  | ok count => exact (checkedStorageCount_bounds checked).2

def StoragePosition.align (cursor : StoragePosition) (bytes : Nat) : StoragePosition :=
  if cursor.byte.val + bytes ≤ 32 then cursor else ⟨cursor.slot + 1, 0⟩

def StoragePosition.advance (here : StoragePosition) (bytes slots : Nat) : StoragePosition :=
  if packed : slots = 1 ∧ here.byte.val + bytes < 32 then
    ⟨here.slot, ⟨here.byte.val + bytes, packed.2⟩⟩
  else ⟨here.slot + slots, 0⟩

theorem StoragePosition.align_fits (cursor : StoragePosition) (bytes : Nat)
    (bounded : bytes ≤ 32) : (cursor.align bytes).byte.val + bytes ≤ 32 := by
  unfold align
  split <;> simp_all

theorem StoragePosition.align_monotone (cursor : StoragePosition) (bytes : Nat) :
    cursor.linear ≤ (cursor.align bytes).linear := by
  unfold align linear
  split
  next => exact Nat.le_refl _
  next => have := cursor.byte.isLt; dsimp; omega

theorem StoragePosition.advance_extent (here : StoragePosition) (bytes slots : Nat)
    (positive : 0 < bytes) : (here.advance bytes slots).endSlot = here.slot + slots := by
  unfold advance
  split
  next packed =>
    have nonzero : here.byte.val + bytes ≠ 0 := by omega
    change here.slot + (if here.byte.val + bytes = 0 then 0 else 1) = here.slot + slots
    rw [if_neg nonzero, packed.1]
  next => simp [endSlot]

theorem StoragePosition.advance_progress (here : StoragePosition) (bytes slots : Nat)
    (positive : 0 < slots) (fits : here.byte.val + bytes ≤ 32) :
    here.linear + bytes ≤ (here.advance bytes slots).linear := by
  unfold advance linear
  split
  next => dsimp; omega
  next => dsimp; omega

/-- Allocate a scalar byte extent or a whole-slot aggregate extent. Non-scalars
use bytes=32; no aggregate shares its first or last slot with another field. -/
def allocateStorage (cursor : StoragePosition) (bytes slots : Nat) :
    Result (StoragePosition × StoragePosition) :=
  if 0 < bytes ∧ bytes ≤ 32 ∧ 0 < slots ∧ (slots = 1 ∨ bytes = 32) then
    let here := cursor.align bytes
    let next := here.advance bytes slots
    if next.endSlot < storageLimit then .ok (here, next) else .error .rejected
  else .error .rejected

/-- The allocation publishes fitting fields and a bounded, monotone cursor.
Consequently subsequent declarations cannot overlap this field's byte range.
This concerns static linear layout only, not hash-derived dynamic locations. -/
theorem allocateStorage_valid
    (allocated : allocateStorage cursor bytes slots = .ok (here, next)) :
    0 < bytes ∧ bytes ≤ 32 ∧ 0 < slots ∧
    here.byte.val + bytes ≤ 32 ∧ cursor.linear ≤ here.linear ∧
    here.linear + bytes ≤ next.linear ∧ next.endSlot = here.slot + slots ∧
    next.endSlot < storageLimit := by
  unfold allocateStorage at allocated
  split at allocated
  next dimensions =>
    dsimp only at allocated
    split at allocated
    next bounded =>
      cases allocated
      exact ⟨dimensions.1, dimensions.2.1, dimensions.2.2.1,
        StoragePosition.align_fits cursor bytes dimensions.2.1,
        StoragePosition.align_monotone cursor bytes,
        StoragePosition.advance_progress _ bytes slots dimensions.2.2.1
          (StoragePosition.align_fits cursor bytes dimensions.2.1),
        StoragePosition.advance_extent _ bytes slots dimensions.1, bounded⟩
    next => cases allocated
  next => cases allocated

private def finishLayout (cursor : StoragePosition) : Result StorageLayout :=
  if cursor.endSlot < storageLimit then .ok ⟨[], cursor⟩ else .error .rejected

mutual
/-- Exact intrinsic storage extent, with a host recursion/work allowance.
Dynamic headers cut recursion, allowing structs containing arrays of themselves.
An exhausted allowance is never interpreted as source rejection or overflow. -/
def storageSize (registry : Registry) : Nat → SType → Result Nat
  | 0, _ => .error .exhausted
  | fuel + 1, type => checkedStorageResult (do
      if (storageBytes type).isSome then return 1
      match type with
      | .array _ none _ _ | .bytes _ _ | .string _ _ | .mapping _ _ => return 1
      | .array element (some length) _ _ =>
          if length = 0 ∨ storageLimit ≤ length then throw .rejected
          match storageBytes element with
          | some bytes =>
              let perSlot := 32 / bytes
              return length / perSlot + if length % perSlot = 0 then 0 else 1
          | none => return length * (← storageSize registry fuel element)
      | .structType identity _ _ =>
          let some fields := registry.structFields identity |
            throw (.invalidContext "missing resolved struct fields")
          let layout ← fieldLayout registry fuel fields {}
          return max 1 layout.next.endSlot
      | .fixedPoint _ _ _ => throw (.unsupported "fixed-point storage representation")
      | _ => throw .rejected)

/-- Members are laid out in source order. Each member consumes work allowance,
and nested fixed arrays/structs also consume it through storageSize. -/
def fieldLayout (registry : Registry) : Nat → List (String × SType) →
    StoragePosition → Result StorageLayout
  | _, [], cursor => finishLayout cursor
  | 0, _ :: _, _ => .error .exhausted
  | fuel + 1, (name, type) :: rest, cursor => do
      let slots ← storageSize registry fuel type
      let bytes := (storageBytes type).getD 32
      let (here, next) ← allocateStorage cursor bytes slots
      let after ← fieldLayout registry fuel rest next
      return ⟨⟨name, type, here⟩ :: after.fields, after.next⟩
end

theorem storageSize_exhausted (registry : Registry) (type : SType) :
    storageSize registry 0 type = .error .exhausted := rfl

theorem storageSize_bounds (sized : storageSize registry fuel type = .ok size) :
    0 < size ∧ size < storageLimit := by
  cases fuel with
  | zero => cases sized
  | succ fuel => exact checkedStorageResult_bounds sized

theorem storageSize_scalar (registry : Registry) (fuel : Nat) (type : SType)
    (sized : storageBytes type = some bytes) :
    storageSize registry (fuel + 1) type = .ok 1 := by
  simp [storageSize, sized, checkedStorageResult, checkedStorageCount, storageLimit]

theorem fieldLayout_empty (registry : Registry) (fuel : Nat) (cursor : StoragePosition)
    (bounded : cursor.endSlot < storageLimit) :
    fieldLayout registry fuel [] cursor = .ok ⟨[], cursor⟩ := by
  simp [fieldLayout, finishLayout, bounded]

private theorem resultBind_ok (value : α) (next : α → Except ε β) :
    (Except.ok value >>= next) = next value := rfl

private theorem resultBind_error (error : ε) (next : α → Except ε β) :
    (Except.error error >>= next) = .error error := rfl

/-- Successful layouts retain every supplied member in order and publish a
checked total extent. Failed or exhausted prefixes cannot omit later fields. -/
theorem fieldLayout_complete_inventory
    (computed : fieldLayout registry fuel fields cursor = .ok layout) :
    layout.fields.map (fun field => (field.name, field.type)) = fields ∧
      layout.next.endSlot < storageLimit := by
  induction fields generalizing fuel cursor layout with
  | nil =>
      simp only [fieldLayout, finishLayout] at computed
      split at computed
      next bounded => cases computed; exact ⟨rfl, bounded⟩
      next => cases computed
  | cons field rest ih =>
      rcases field with ⟨name, type⟩
      cases fuel with
      | zero => cases computed
      | succ fuel =>
          simp only [fieldLayout] at computed
          cases sized : storageSize registry fuel type with
          | error error =>
              rw [sized, resultBind_error] at computed
              cases computed
          | ok slots =>
              rw [sized, resultBind_ok] at computed
              cases allocated : allocateStorage cursor ((storageBytes type).getD 32) slots with
              | error error =>
                  rw [allocated, resultBind_error] at computed
                  cases computed
              | ok positions =>
                  rcases positions with ⟨here, next⟩
                  rw [allocated, resultBind_ok] at computed
                  cases continued : fieldLayout registry fuel rest next with
                  | error error =>
                      rw [continued, resultBind_error] at computed
                      cases computed
                  | ok after =>
                      rw [continued, resultBind_ok] at computed
                      cases computed
                      have retained := ih continued
                      exact ⟨congrArg (List.cons (name, type)) retained.1, retained.2⟩

/-- Concrete member offsets. Absent declarations are invalid input; a member
index outside the supplied declaration is rejected, never read as zero. -/
def fieldOffset (registry : Registry) (fuel identity index : Nat) :
    Result (SType × Nat × Fin 32) := do
  let some fields := registry.structFields identity |
    throw (.invalidContext "missing resolved struct fields")
  let layout ← fieldLayout registry fuel fields {}
  let some field := layout.fields[index]? | throw .rejected
  return (field.type, field.position.slot, field.position.byte)

theorem packedElementFits (bytes index : Nat) (positive : 0 < bytes) (bounded : bytes ≤ 32) :
    0 < 32 / bytes ∧ (index % (32 / bytes)) * bytes + bytes ≤ 32 := by
  have perSlot : 0 < 32 / bytes := Nat.div_pos bounded positive
  have remainder := Nat.mod_lt index perSlot
  have position := Nat.mul_le_mul_right bytes (Nat.succ_le_of_lt remainder)
  have extent := Nat.div_mul_le_self 32 bytes
  constructor
  · exact perSlot
  · simpa [Nat.succ_mul] using Nat.le_trans position extent

/-- Distinct indices of one packed array occupy different relative slots or
disjoint byte ranges. This does not assert separation from another array or
from any hash-derived location in the surrounding storage world. -/
theorem packedElements_separate (bytes a b : Nat) (distinct : a ≠ b) :
    a / (32 / bytes) ≠ b / (32 / bytes) ∨
      (a % (32 / bytes)) * bytes + bytes ≤ (b % (32 / bytes)) * bytes ∨
      (b % (32 / bytes)) * bytes + bytes ≤ (a % (32 / bytes)) * bytes := by
  by_cases slots : a / (32 / bytes) = b / (32 / bytes)
  · right
    have different : a % (32 / bytes) ≠ b % (32 / bytes) := by
      intro equal
      have first := Nat.mod_add_div a (32 / bytes)
      have second := Nat.mod_add_div b (32 / bytes)
      rw [slots, equal] at first
      exact distinct (first.symm.trans second)
    rcases Nat.lt_or_gt_of_ne different with before | after
    · left
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right bytes (Nat.succ_le_of_lt before)
    · right
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right bytes (Nat.succ_le_of_lt after)
  · exact Or.inl slots

/-- Intrinsic element offset relative to the fixed-array start, or the hashed
dynamic-array data start. The caller owns the length check and concrete hash.
The result is a slot offset and byte within that slot. Runtime aggregate
strides multiply as Words, retaining wraparound even when a raw length admits
an enormous index. Static declaration extents are checked separately. Packed
uint24 therefore uses ten elements per word. -/
def elementOffset (registry : Registry) (fuel : Nat) (element : SType) (index : Nat) :
    Result (Nat × Fin 32) := do
  match sized : storageBytes element with
  | some bytes =>
      let bounds := storageBytes_bound element bytes sized
      let fits := (packedElementFits bytes index bounds.1 bounds.2).2
      let slot := index / (32 / bytes)
      if slot < storageLimit then
        return (slot, ⟨index % (32 / bytes) * bytes, by omega⟩)
      else throw .rejected
  | none =>
      let size ← storageSize registry fuel element
      return (((BitVec.ofNat 256 index) * BitVec.ofNat 256 size).toNat, 0)

theorem elementOffset_packed_fits (sized : storageBytes element = some bytes)
    (located : elementOffset registry fuel element index = .ok (slot, byte)) :
    byte.val + bytes ≤ 32 := by
  simp only [elementOffset] at located
  split at located
  next packedBytes matched =>
    have same : packedBytes = bytes := Option.some.inj (matched.symm.trans sized)
    subst packedBytes
    split at located
    next =>
      cases located
      exact (packedElementFits bytes index (storageBytes_bound element bytes sized).1
        (storageBytes_bound element bytes sized).2).2
    next => cases located
  next matched => simp_all

/-- Classify finite resolved metadata, cutting only a previously checked
struct reached after a dynamic-array edge. Such a guarded cycle is dynamic;
an inline cycle rejects. Every unvisited definition and sibling is inspected,
including children of dynamic arrays, so a back edge cannot hide a mapping or
unsupported member. Recursive external ABI admission is a separate judgment. -/
def calldataDynamicFrom (registry : Registry) : Nat → List Nat → List Nat → SType → Result Bool
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, seen, inline, type => do
      if let .function .internal _ _ _ := type then throw .rejected
      if let .fixedPoint _ _ _ := type then
        throw (.unsupported "fixed-point calldata representation")
      if (storageBytes type).isSome then return false
      match type with
      | .bytes _ _ | .string _ _ => return true
      | .array element length _ _ =>
          if length = some 0 ∨ (length.any fun size => storageLimit ≤ size) then throw .rejected
          let nextInline := if length.isNone then [] else inline
          let dynamic ← calldataDynamicFrom registry fuel seen nextInline element
          return length.isNone || dynamic
      | .structType identity _ _ =>
          if inline.contains identity then throw .rejected
          if seen.contains identity then return true
          let some fields := registry.structFields identity |
            throw (.invalidContext "missing resolved struct fields")
          let flags ← fields.mapM fun (_, type) =>
            calldataDynamicFrom registry fuel (identity :: seen) (identity :: inline) type
          return flags.any id
      | .fixedPoint _ _ _ => throw (.unsupported "fixed-point calldata representation")
      | _ => throw .rejected

/-- ABI dynamism is a representation property, not external decoder admission.
Guarded recursive types can be accessed by internal calldata paths even though
external function signatures cannot expose them. -/
def calldataDynamic (registry : Registry) (fuel : Nat) (type : SType) : Result Bool :=
  calldataDynamicFrom registry fuel [] [] type

/-- Size of a component's calldata head: one relative-offset word for a dynamic
component, its full inline extent for a recursively static array or struct.
Offsets/length validation and source ABI admission remain separate consumers. -/
def calldataHeadSize (registry : Registry) : Nat → SType → Result Nat
  | 0, _ => .error .exhausted
  | fuel + 1, type => checkedStorageResult (do
      if ← calldataDynamic registry (fuel + 1) type then return 32
      if (storageBytes type).isSome then return 32
      match type with
      | .array element (some length) _ _ =>
          return length * (← calldataHeadSize registry fuel element)
      | .structType identity _ _ =>
          let some fields := registry.structFields identity |
            throw (.invalidContext "missing resolved struct fields")
          let sizes ← fields.mapM fun (_, type) => calldataHeadSize registry fuel type
          return sizes.foldl Nat.add 0
      | _ => throw .rejected)

theorem calldataDynamicFrom_inline_cycle (seen inline : List Nat)
    (cycle : inline.contains identity = true) :
    calldataDynamicFrom registry (fuel+1) seen inline (.structType identity location pointer) =
      .error .rejected := by
  simp only [calldataDynamicFrom, storageBytes, Option.isSome_none, Bool.false_eq_true,
    ↓reduceIte, cycle]
  rfl

theorem calldataDynamicFrom_guarded_cycle (seen inline : List Nat)
    (visited : seen.contains identity = true) (guarded : inline.contains identity = false) :
    calldataDynamicFrom registry (fuel+1) seen inline (.structType identity location pointer) =
      .ok true := by
  simp only [calldataDynamicFrom, storageBytes, Option.isSome_none, Bool.false_eq_true,
    ↓reduceIte, guarded, visited]
  rfl

theorem calldataHeadSize_dynamic
    (dynamic : calldataDynamic registry (fuel+1) type = .ok true) :
    calldataHeadSize registry (fuel+1) type = .ok 32 := by
  simp [calldataHeadSize, dynamic, checkedStorageResult, checkedStorageCount, storageLimit,
    bind, Except.bind]
  rfl

theorem calldataDynamic_exhausted (registry : Registry) (type : SType) :
    calldataDynamic registry 0 type = .error .exhausted := rfl

theorem calldataHeadSize_exhausted (registry : Registry) (type : SType) :
    calldataHeadSize registry 0 type = .error .exhausted := rfl

theorem calldataHeadSize_bounds (sized : calldataHeadSize registry fuel type = .ok size) :
    0 < size ∧ size < storageLimit := by
  cases fuel with
  | zero => cases sized
  | succ fuel => exact checkedStorageResult_bounds sized

inductive StorageClass where
  | persistent | transient | constant | immutable
  deriving DecidableEq, Repr

structure StorageDeclaration where
  name : String
  type : SType
  kind : StorageClass := .persistent
  deriving DecidableEq, Repr

structure DeclarationPosition where
  contract : Nat
  declaration : StorageDeclaration
  position : StoragePosition
  deriving DecidableEq, Repr

structure DeclarationLayout where
  fields : List DeclarationPosition
  persistentEnd : StoragePosition
  transientEnd : StoragePosition
  deriving DecidableEq, Repr

def finishDeclarations (persistent transient : StoragePosition) : Result DeclarationLayout :=
  if persistent.endSlot < storageLimit && transient.endSlot < storageLimit then
    .ok ⟨[], persistent, transient⟩ else .error .rejected

def declarationItems (registry : Registry) : Nat → List (Nat × StorageDeclaration) →
    StoragePosition → StoragePosition → Result DeclarationLayout
  | _, [], persistent, transient => finishDeclarations persistent transient
  | 0, _ :: _, _, _ => .error .exhausted
  | fuel + 1, (contract, declaration) :: rest, persistent, transient => do
      match declaration.kind with
      | .constant | .immutable => declarationItems registry fuel rest persistent transient
      | .persistent =>
          let slots ← storageSize registry fuel declaration.type
          let (here, next) ← allocateStorage persistent ((storageBytes declaration.type).getD 32) slots
          let after ← declarationItems registry fuel rest next transient
          return {after with fields := ⟨contract, declaration, here⟩ :: after.fields}
      | .transient =>
          let some bytes := storageBytes declaration.type | throw .rejected
          let (here, next) ← allocateStorage transient bytes 1
          let after ← declarationItems registry fuel rest persistent next
          return {after with fields := ⟨contract, declaration, here⟩ :: after.fields}

/-- The declaration bundle is already most-base-first C3 linearized. Consecutive
base and derived declarations share packing. Only persistent layout receives
the supplied custom base; transient storage starts independently at zero.
Constants and immutables never consume either layout. -/
def declarationLayout (registry : Registry) (fuel base : Nat)
    (contracts : List (Nat × List StorageDeclaration)) : Result DeclarationLayout :=
  if base < storageLimit then
    declarationItems registry fuel (contracts.flatMap fun (identity, fields) =>
      fields.map fun field => (identity, field)) ⟨base, 0⟩ {}
  else .error .rejected

theorem declarationLayout_invalid_base (outside : storageLimit ≤ base) :
    declarationLayout registry fuel base contracts = .error .rejected := by
  simp [declarationLayout, Nat.not_lt.mpr outside]

end Solidity.Aggregates
