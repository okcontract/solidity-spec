/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.StorageBytes
import Solidity.Core.Aggregates.Access

/-! Storage aggregate erasure and dynamic-array resizing. Mapping cells are
never enumerated or erased. Internal traversal captures positions before
shrinking a length; a previously exported reference still retains its guards
and is classified as dangling when subsequently used. -/
namespace Solidity.Aggregates.StorageArrays
open Core Static
open Contract.Interaction (Word)

def captured (place : Place) : Place :=
  {place with reference := {place.reference with guards := []}}

def scalarZero (heap : Heap) (place : Place) : Result Heap := do
  let some zero := defaultScalar place.type |
    throw (.unsupported "type has no scalar zero representation")
  writeScalar heap place zero

def slotCount (bytes slots count : Nat) : Result Nat :=
  if 1 < slots then
    if count * slots < 2^256 then .ok (count * slots) else .error (.panic 0x11)
  else
    let perSlot := 32 / bytes
    .ok ((BitVec.ofNat 256 count + BitVec.ofNat 256 (perSlot-1)) /
      BitVec.ofNat 256 perSlot).toNat

/-- Shared native partial-word cleanup; full obsolete words are handled by the
range traversal. Reads occur after any earlier header publication. -/
def clearPartial (heap : Heap) (region : Region) (data : Word)
    (start bytes newSlots : Nat) : Result Heap :=
  if bytes ≤ 16 then do
    let offset := (start % (32/bytes)) * bytes
    if offset = 0 then pure heap else do
      let slot := data + BitVec.ofNat 256 newSlots - 1
      let word ← Slot.read heap region slot
      Slot.write heap region slot ((word.extractLsb' 0 (8*offset)).setWidth 256)
  else pure heap

/-- The callback is always the decreasing eraser below. Packed struct members
share one whole-slot erase, including unused suffix bytes. -/
def eraseMember (clear : Nat → Heap → Place → Result (Heap × Nat))
    (reference : Reference) (state : Heap × Nat × List Word) (member : StorageField) :
    Result (Heap × Nat × List Word) := do
  let (state, budget, cleared) := state
  let slot := reference.address + BitVec.ofNat 256 member.position.slot
  let child : Place := ⟨atLocation member.type .storage false, rebase reference slot member.position.byte⟩
  match member.type with
  | .mapping _ _ => return (state, budget, cleared)
  | _ =>
      if (storageBytes member.type).getD 32 < 32 then
        if cleared.contains slot then return (state, budget, cleared)
        else return (← Slot.write state reference.region slot 0, budget, slot :: cleared)
      else
        let (state, budget) ← clear budget state (captured child)
        return (state, budget, cleared)

def eraseRangeElement (clear : Nat → Heap → Place → Result (Heap × Nat))
    (reference : Reference) (data : Word) (element : SType) (bytes newSlots step : Nat)
    (state : Heap × Nat) (index : Nat) : Result (Heap × Nat) := do
  let (state, budget) := state
  let slot := data + BitVec.ofNat 256 (newSlots + index*step)
  if bytes < 32 then return (← Slot.write state reference.region slot 0, budget)
  else clear budget state ⟨atLocation element .storage false, { (rebase reference slot) with guards := [] }⟩

def cleanupData (place : Place) : Reference :=
  match place.type with
  | .array _ none _ _ => Access.dataArea place.reference
  | _ => place.reference

/-- The recursive callbacks are the decreasing eraser and captured range
cleanup below. This body shares the exact native per-type deletion primitives. -/
def eraseContents (registry : Registry) (fuel : Nat)
    (clear : Nat → Heap → Place → Result (Heap × Nat))
    (clearArray : Nat → Heap → Place → SType → Nat → Nat → Result (Heap × Nat))
    (budget : Nat) (heap : Heap) (place : Place) : Result (Heap × Nat) := do
  match place.type with
  | .mapping _ _ => return (heap, budget)
  | .bytes _ _ | .string _ _ => StorageBytes.writeChecked heap budget place.reference []
  | .array element size _ _ =>
      let count ← Access.length heap place
      let after ← if size.isNone then Slot.write heap place.reference.region place.reference.address 0
        else pure heap
      let after := if size.isNone then
        after.journalResize place.reference.region place.reference.address count 0 else after
      clearArray budget after place element count 0
  | .structType identity _ _ =>
      let some members := registry.structFields identity |
        throw (.invalidContext "missing struct definition during deletion")
      let layout ← fieldLayout registry fuel members {}
      let budget ← reserve budget layout.fields.length
      let (after, remaining, _) ← layout.fields.foldlM
        (eraseMember clear place.reference) (heap, budget, ([] : List Word))
      return (after, remaining)
  | _ => return (← scalarZero heap place, budget)

mutual
/-- Native aggregate erasure clears whole occupied packed words, while a
standalone scalar delete clears only its own field. Dynamic headers are set
before the captured old range is cleared. -/
def erase (registry : Registry) : Nat → Nat → Heap → Place → Result (Heap × Nat)
  | 0, _, _, _ => .error .exhausted
  | fuel+1, budget, heap, place => do
      Access.validate heap place
      let budget ← reserve budget 1
      match place.reference.region with
      | .storage _ | .transient _ => pure ()
      | _ => throw .rejected
      eraseContents registry fuel (erase registry fuel) (clearTail registry fuel) budget heap place

/-- Captured array cleanup uses the original length and data address, and reads
current words after any earlier header write. Packed suffix cleanup preserves
only the retained low bytes and zeros all obsolete whole slots. -/
def clearTail (registry : Registry) : Nat → Nat → Heap → Place → SType → Nat → Nat → Result (Heap × Nat)
  | 0, _, _, _, _, _, _ => .error .exhausted
  | fuel+1, budget, heap, place, element, oldLength, start => do
      if oldLength ≤ start then return (heap, budget)
      if let .mapping _ _ := element then return (heap, budget)
      let bytes := (storageBytes element).getD 32
      let slots ← storageSize registry fuel element
      let oldSlots ← slotCount bytes slots oldLength
      let newSlots ← slotCount bytes slots start
      let data := cleanupData place
      let count := ((BitVec.ofNat 256 oldSlots) - BitVec.ofNat 256 newSlots).toNat
      let step := if bytes < 32 then 1 else slots
      let iterations := (count + step-1) / step
      let budget ← reserve budget (iterations+1)
      let after ← clearPartial heap place.reference.region data.address start bytes newSlots
      (List.range iterations).foldlM
        (eraseRangeElement (erase registry fuel) place.reference data.address element bytes newSlots step)
        (after, budget)
end

/-- A standalone delete of a mapping is a source error. Recursive erasure of
an enclosing struct/array deliberately skips its mapping members instead. -/
def delete (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place) :
    Result (Heap × Nat) :=
  match place.type with
  | .mapping _ _ => .error .rejected
  | _ => erase registry fuel budget heap place

/-- Compiler-internal resize, not a source permission to assign `.length`.
The source surface uses push/pop or a checked aggregate-copy plan. -/
def resize (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place)
    (newLength : Nat) : Result (Heap × Nat) := do
  Access.validate heap place
  let .array element size .storage _ := place.type | throw .rejected
  let .storage _ := place.reference.region | throw .rejected
  if 2^64 < newLength then throw (.panic 0x41)
  let oldLength ← Access.length heap place
  if size.isSome && oldLength < newLength then throw .rejected
  let after ← if size.isNone then Slot.write heap place.reference.region place.reference.address (BitVec.ofNat 256 newLength) else pure heap
  let after := if size.isNone then
    after.journalResize place.reference.region place.reference.address oldLength newLength else after
  clearTail registry fuel budget after place element oldLength newLength

/-- Native push-without-argument first advances the length and returns the
new physical element reference. Its zero/default law requires the ordinary
unused-cell invariant; arbitrary prior raw assembly writes are not erased here.
Mapping payloads retained by a prior pop intentionally become visible again. -/
def pushZero (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place) :
    Result (Place × Heap × Nat) := do
  Access.validate heap place
  let .array _ none .storage _ := place.type | throw .rejected
  let .storage _ := place.reference.region | throw .rejected
  let count ← Access.length heap place
  if 2^64 ≤ count then throw (.panic 0x41)
  let budget ← reserve budget 1
  let after ← Slot.write heap place.reference.region place.reference.address
    (BitVec.ofNat 256 (count+1))
  let element ← Access.index registry fuel after place count
  return (element, after, budget)

def pop (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place) :
    Result (Heap × Nat) := do
  Access.validate heap place
  let .array _ none .storage _ := place.type | throw .rejected
  let .storage _ := place.reference.region | throw .rejected
  let count ← Access.length heap place
  if count = 0 then throw (.panic 0x31)
  let element ← Access.index registry fuel heap place (count-1)
  let (after, remaining) ← erase registry fuel budget heap (captured element)
  let after ← Slot.write after place.reference.region place.reference.address (BitVec.ofNat 256 (count-1))
  return (after.journalResize place.reference.region place.reference.address count (count-1), remaining)

theorem erase_exhausted (registry : Registry) (budget : Nat) (heap : Heap) (place : Place) :
    erase registry 0 budget heap place = .error .exhausted := rfl

theorem delete_mapping_rejected (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (key value : SType) (reference : Reference) :
    delete registry fuel budget heap ⟨.mapping key value, reference⟩ = .error .rejected := rfl

theorem captured_address (place : Place) :
    (captured place).reference.address = place.reference.address := rfl

theorem captured_retains_binding (place : Place) :
    (captured place).reference.bindingCell = place.reference.bindingCell := rfl

end Solidity.Aggregates.StorageArrays
