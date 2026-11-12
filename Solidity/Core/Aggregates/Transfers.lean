/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Layout
import Solidity.Core.Aggregates.Scalars

/-! Resolved aggregate location and assignment rules. These decide whether a
source operation is permitted and select aliasing versus copying; they do not
execute a copy or confer source-byte admission. Struct metadata is the same
registry consumed by layout and place access. -/
namespace Solidity.Aggregates
open Static Core

def mappingKeyAllowed : SType → Bool
  | .uint _ | .sint _ | .fixedBytes _ | .bool | .address _ | .enumType _ _ |
    .valueType _ _ | .contract _ _ _ | .fixedPoint _ _ _ | .bytes _ _ | .string _ _ => true
  | _ => false

/-- A repeated struct cuts a finite graph search, not an unknown subtree.
Every unvisited definition is inspected, including siblings after a back edge.
An unresolved definition or an insufficient traversal budget remains explicit. -/
def containsMappingFrom (registry : Registry) : Nat → List Nat → SType → Result Bool
  | 0, _, _ => .error .exhausted
  | fuel + 1, seen, type => do
      match type with
      | .mapping _ _ => return true
      | .array element _ _ _ => containsMappingFrom registry fuel seen element
      | .structType identity _ _ =>
          if seen.contains identity then return false
          let some fields := registry.structFields identity |
            throw (.invalidContext "missing resolved struct fields")
          let flags ← fields.mapM fun (_, member) =>
            containsMappingFrom registry fuel (identity :: seen) member
          return flags.any id
      | _ => return false

def containsMapping (registry : Registry) (fuel : Nat) (type : SType) : Result Bool :=
  containsMappingFrom registry fuel [] type

/-- Match the native static memory-array size check: consecutive fixed array
dimensions multiply; the final struct has one head word per member and the
final dynamic reference has one pointer word. This is type admission, not a
host-materialization or runtime-memory limit. -/
def memoryTypeExtent (registry : Registry) : Nat → SType → Result Nat
  | 0, _ => .error .exhausted
  | fuel + 1, .array element (some length) _ _ => do
      return length * (← memoryTypeExtent registry fuel element)
  | _ + 1, .structType identity _ _ => do
      let some fields := registry.structFields identity |
        throw (.invalidContext "missing resolved struct fields")
      return fields.length * 32
  | _ + 1, _ => .ok 32

private def admitsReferences : Region → Bool
  | .transient _ => false
  | _ => true

private def isStorage : Region → Bool
  | .storage _ => true
  | _ => false

private def isCalldata : Region → Bool
  | .calldata _ => true
  | _ => false

/-- `inline` tracks the current unguarded expansion. Dynamic arrays break it
at every admitted location; mappings do so in storage. Guarded recursion is
legal for internal references, including memory/calldata. External recursive
ABI signatures remain the declaration/interface checker's responsibility.
The separate `seen` set still checks every finite metadata definition. -/
def eligibleFrom (registry : Registry) : Nat → Region → List Nat → List Nat → SType → Result Unit
  | 0, _, _, _, _ => .error .exhausted
  | fuel + 1, region, seen, inline, type => do
      if !Static.wellFormed registry type then throw .rejected
      if (storageBytes type).isSome then
        if isCalldata region then
          if let .function .internal _ _ _ := type then throw .rejected
        return ()
      if !admitsReferences region then throw .rejected
      if referenceLocation type != some (regionLocation region) then throw .rejected
      match type with
      | .bytes _ _ | .string _ _ => return ()
      | .mapping key value =>
          if !isStorage region || !mappingKeyAllowed key then throw .rejected
          eligibleFrom registry fuel region seen [] (atLocation value .storage false)
      | .array element length _ _ =>
          if length = some 0 ∨ (length.any fun n => storageLimit ≤ n) then throw .rejected
          let nextInline := if length.isNone then [] else inline
          eligibleFrom registry fuel region seen nextInline
            (atLocation element (regionLocation region) false)
          if let some count := length then
            match region with
            | .memory _ =>
                if (← memoryTypeExtent registry (fuel+1) type) ≥ 2^32-1 then throw .rejected
            | .calldata _ =>
                let head ← calldataHeadSize registry fuel element
                if (count * head + 31) / 32 * 32 ≥ 2^32-1 then throw .rejected
            | _ => pure ()
      | .structType identity _ _ =>
          if seen.contains identity then
            if !inline.contains identity then return () else throw .rejected
          let some fields := registry.structFields identity |
            throw (.invalidContext "missing resolved struct fields")
          if fields.isEmpty then throw .rejected
          for (_, member) in fields do
            eligibleFrom registry fuel region (identity :: seen) (identity :: inline)
              (atLocation member (regionLocation region) false)
      | _ => throw .rejected

/-- Complete placement check for a resolved type. Storage extent is checked
after location/recursion eligibility; transient state admits scalar values only.
Fixed-point execution is outside the supported scalar value domain. -/
def eligibleAt (registry : Registry) (fuel : Nat) (region : Region) (type : SType) : Result Unit := do
  eligibleFrom registry fuel region [] [] type
  if isStorage region then
    let _ ← storageSize registry fuel type
    pure ()

private def typeRegion (type : SType) : Region :=
  match referenceLocation type with
  | some .memory => .memory 0
  | some .calldata => .calldata 0
  | _ => .storage 0

def eligibleType (registry : Registry) (fuel : Nat) (type : SType) : Result Unit :=
  eligibleAt registry fuel (typeRegion type) type

/-- Alias bindings preserve the full element shape and fixed lengths. Location
and storage-pointer markers do not change a reference's nominal content type. -/
def sameShape : SType → SType → Bool
  | .array a n _ _, .array b m _ _ => n == m && sameShape a b
  | .bytes _ _, .bytes _ _ | .string _ _, .string _ _ => true
  | .structType a _ _, .structType b _ _ => a == b
  | .mapping ka va, .mapping kb vb => sameShape ka kb && sameShape va vb
  | a, b => a == b

def SameShape : SType → SType → Prop
  | .array a n _ _, .array b m _ _ => n = m ∧ SameShape a b
  | .bytes _ _, .bytes _ _ | .string _ _, .string _ _ => True
  | .structType a _ _, .structType b _ _ => a = b
  | .mapping ka va, .mapping kb vb => SameShape ka kb ∧ SameShape va vb
  | a, b => a = b

theorem sameShape_iff (source target : SType) : sameShape source target = true ↔ SameShape source target := by
  cases source <;> cases target <;> simp [sameShape, SameShape]
  case array.array a n _ _ b m _ _ => intro _; exact sameShape_iff a b
  case mapping.mapping ka va kb vb => simp [sameShape_iff ka kb, sameShape_iff va vb]
termination_by source

def lengthFits (source target : Option Nat) : Bool :=
  match target with | none => true | some bound => source.any (· ≤ bound)

def LengthFits (source target : Option Nat) : Prop :=
  match target with | none => True | some bound => ∃ length, source = some length ∧ length ≤ bound

theorem lengthFits_iff (source target : Option Nat) : lengthFits source target = true ↔ LengthFits source target := by
  cases source <;> cases target <;> simp [lengthFits, LengthFits]

/-- Assignment into storage contents may widen scalar elements and copy a
fixed array into a dynamic or sufficiently long fixed array. Memory aliases and
memory copies use exact shape instead. Nested mappings are rejected separately
before any copy is selected for execution. -/
def contentCompatible : SType → SType → Bool
  | .array a n _ _, .array b m _ _ => lengthFits n m && contentCompatible a b
  | .bytes _ _, .bytes _ _ | .string _ _, .string _ _ => true
  | .structType a _ _, .structType b _ _ => a == b
  | .mapping _ _, .mapping _ _ => false
  | a, b => Static.implicit a b

def ContentCompatible : SType → SType → Prop
  | .array a n _ _, .array b m _ _ => LengthFits n m ∧ ContentCompatible a b
  | .bytes _ _, .bytes _ _ | .string _ _, .string _ _ => True
  | .structType a _ _, .structType b _ _ => a = b
  | .mapping _ _, .mapping _ _ => False
  | a, b => Static.Implicit a b

theorem contentCompatible_iff (source target : SType) :
    contentCompatible source target = true ↔ ContentCompatible source target := by
  cases source <;> cases target <;> simp [contentCompatible, ContentCompatible, Static.implicit_iff]
  case array.array a n _ _ b m _ _ => simp [lengthFits_iff, contentCompatible_iff a b]
termination_by source

def storagePointer : SType → Bool
  | .array _ _ .storage pointer | .bytes .storage pointer | .string .storage pointer |
    .structType _ .storage pointer => pointer
  | .mapping _ _ => true
  | _ => false

inductive TransferKind where
  | scalarConversion
  | storageAlias
  | memoryAlias
  | calldataAlias
  | storageCopy
  | memoryCopy
  deriving DecidableEq, Repr

def TransferKind.copies : TransferKind → Bool
  | .storageCopy | .memoryCopy => true
  | _ => false

/-- Local storage-reference binding is different from assigning to a storage
aggregate lvalue. Memory aggregate assignment updates a pointer binding; source
storage/calldata inputs require a fresh memory copy instead. -/
def selectTransfer (localBinding : Bool) (source destination : SType) : Option TransferKind :=
  match referenceLocation source, referenceLocation destination with
  | none, none => if Static.implicit source destination then some .scalarConversion else none
  | some origin, some .storage =>
      if localBinding then
        if origin == .storage && storagePointer destination && sameShape source destination then
          some .storageAlias else none
      else if contentCompatible source destination then some .storageCopy else none
  | some origin, some .memory =>
      if sameShape source destination then
        some (if origin == .memory then .memoryAlias else .memoryCopy)
      else none
  | some origin, some .calldata =>
      if localBinding && origin == .calldata && sameShape source destination then some .calldataAlias else none
  | _, _ => none

/-- Independent operation-selection judgment. Placement validity and absence
of nested mappings for copies are additional checks in `planTransfer`. -/
def TransferRule (localBinding : Bool) (source destination : SType) : TransferKind → Prop
  | .scalarConversion => referenceLocation source = none ∧ referenceLocation destination = none ∧
      Static.Implicit source destination
  | .storageAlias => localBinding = true ∧ referenceLocation source = some .storage ∧
      referenceLocation destination = some .storage ∧ storagePointer destination = true ∧ SameShape source destination
  | .memoryAlias => referenceLocation source = some .memory ∧ referenceLocation destination = some .memory ∧
      SameShape source destination
  | .calldataAlias => localBinding = true ∧ referenceLocation source = some .calldata ∧
      referenceLocation destination = some .calldata ∧ SameShape source destination
  | .storageCopy => localBinding = false ∧ referenceLocation source ≠ none ∧
      referenceLocation destination = some .storage ∧ ContentCompatible source destination
  | .memoryCopy => (referenceLocation source = some .storage ∨ referenceLocation source = some .calldata) ∧
      referenceLocation destination = some .memory ∧ SameShape source destination

theorem selectTransfer_iff (localBinding : Bool) (source destination : SType) (kind : TransferKind) :
    selectTransfer localBinding source destination = some kind ↔ TransferRule localBinding source destination kind := by
  cases origin : referenceLocation source with
  | none =>
      cases to : referenceLocation destination with
      | none => cases kind <;> simp [selectTransfer, TransferRule, origin, to, Static.implicit_iff]
      | some location => cases kind <;> cases location <;> simp [selectTransfer, TransferRule, origin, to]
  | some fromLocation =>
      cases to : referenceLocation destination with
      | none => cases kind <;> simp [selectTransfer, TransferRule, origin, to]
      | some toLocation =>
          cases fromLocation <;> cases toLocation <;> cases localBinding <;> cases kind <;>
            simp [selectTransfer, TransferRule, origin, to, sameShape_iff, contentCompatible_iff]

private def finishTransfer (registry : Registry) (fuel : Nat) (source destination : SType)
    (kind : TransferKind) : Result TransferKind :=
  if kind.copies then do
    let sourceMapping ← containsMapping registry fuel source
    let destinationMapping ← containsMapping registry fuel destination
    if sourceMapping || destinationMapping then .error .rejected else .ok kind
  else .ok kind

def planTransfer (registry : Registry) (fuel : Nat) (localBinding : Bool)
    (source destination : SType) : Result TransferKind := do
  eligibleType registry fuel source
  eligibleType registry fuel destination
  let some kind := selectTransfer localBinding source destination | throw .rejected
  finishTransfer registry fuel source destination kind

private theorem finishTransfer_selected
    (finished : finishTransfer registry fuel source destination selected = .ok kind) : kind = selected := by
  unfold finishTransfer at finished
  split at finished
  · cases sourceMapping : containsMapping registry fuel source with
    | error failure => simp [sourceMapping, bind, Except.bind] at finished
    | ok sourceFlag =>
        cases destinationMapping : containsMapping registry fuel destination with
        | error failure => simp [sourceMapping, destinationMapping, bind, Except.bind] at finished
        | ok destinationFlag =>
            simp only [sourceMapping, destinationMapping, bind, Except.bind] at finished
            split at finished
            · cases finished
            · exact (Except.ok.inj finished).symm
  · exact (Except.ok.inj finished).symm

theorem planTransfer_rule
    (planned : planTransfer registry fuel localBinding source destination = .ok kind) :
    TransferRule localBinding source destination kind := by
  apply (selectTransfer_iff localBinding source destination kind).mp
  unfold planTransfer at planned
  cases sourceAdmitted : eligibleType registry fuel source with
  | error failure => simp [sourceAdmitted, bind, Except.bind] at planned
  | ok sourceToken =>
      cases destinationAdmitted : eligibleType registry fuel destination with
      | error failure => simp [sourceAdmitted, destinationAdmitted, bind, Except.bind] at planned
      | ok destinationToken =>
          simp only [sourceAdmitted, destinationAdmitted, bind, Except.bind] at planned
          cases selected : selectTransfer localBinding source destination with
          | none => simp [selected] at planned
          | some operation =>
              simp only [selected] at planned
              have same := finishTransfer_selected planned
              simp only [same]

theorem eligibleAt_exhausted (registry : Registry) (region : Region) (type : SType) :
    eligibleAt registry 0 region type = .error .exhausted := rfl

theorem containsMapping_exhausted (registry : Registry) (type : SType) :
    containsMapping registry 0 type = .error .exhausted := rfl

theorem transient_scalar_only (registry : Registry) (fuel : Nat) (account : BitVec 160) (type : SType)
    (admitted : eligibleAt registry fuel (.transient account) type = .ok ()) :
    (storageBytes type).isSome = true := by
  cases sized : storageBytes type with
  | some bytes => simp
  | none =>
      cases fuel with
      | zero => cases admitted
      | succ remaining =>
          simp [eligibleAt, eligibleFrom, sized, admitsReferences,
            bind, Except.bind, pure, Except.pure] at admitted

theorem storageAlias_requires_local (valid : TransferRule localBinding source destination .storageAlias) :
    localBinding = true := valid.1

theorem storageCopy_is_contents (valid : TransferRule localBinding source destination .storageCopy) :
    localBinding = false ∧ referenceLocation destination = some .storage := ⟨valid.1, valid.2.2.1⟩

theorem memoryAlias_requires_memory (valid : TransferRule localBinding source destination .memoryAlias) :
    referenceLocation source = some .memory ∧ referenceLocation destination = some .memory := ⟨valid.1, valid.2.1⟩

theorem calldataAlias_requires_local (valid : TransferRule localBinding source destination .calldataAlias) :
    localBinding = true := valid.1

theorem calldata_contents_reject (source destination : SType)
    (readonly : referenceLocation destination = some .calldata) :
    selectTransfer false source destination = none := by
  cases origin : referenceLocation source <;> simp [selectTransfer, readonly, origin]

end Solidity.Aggregates
