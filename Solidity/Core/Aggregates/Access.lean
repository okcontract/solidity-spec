/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Layout
import Solidity.Core.Aggregates.Scalars
import Solidity.Core.Aggregates.Transfers
import Solidity.Core.Aggregates.Memory

/-! Fallible physical place resolution. Typed paths do not imply distinct
slots: storage addition and concrete Keccak retain all collisions. Calldata
references here describe the ABI representation. Entry decoding and the
relationship to exact source bundles are caller-supplied assumptions. -/
namespace Solidity.Aggregates.Access
open Core Static
open Contract.Interaction (Word bytesWord wordBytes)

def hash (bytes : List UInt8) : Word :=
  bytesWord (Contract.Export.Keccak.hash ⟨bytes.toArray⟩).data.toList

def dataArea (reference : Reference) : Reference :=
  rebase reference (hash (wordBytes reference.address))

/-- Short bytes are left aligned and have an even length marker; long bytes
have an odd marker and at least 32 bytes. Invalid raw headers panic with 0x22. -/
def byteLength (word : Word) : Result Nat :=
  if word.toNat % 2 = 0 then
    let length := word.toNat % 256 / 2
    if length < 32 then .ok length else .error (.panic 0x22)
  else
    let length := word.toNat / 2
    if 32 ≤ length then .ok length else .error (.panic 0x22)

def readWord (heap : Heap) (reference : Reference) : Result Word := do
  match reference.region with
  | .storage _ | .transient _ => Slot.read heap reference.region reference.address
  | .memory _ =>
      checkExtent heap reference 32
      return bytesWord (heap.execution.memory.read reference.address.toNat 32)
  | .calldata _ =>
      checkExtent heap reference 32
      return bytesWord ((heap.execution.context.calldata.drop reference.address.toNat).take 32)

def checkGuard (heap : Heap) (region : Region) (guard : ReferenceGuard) : Result Unit := do
  if heap.historyEpoch region != guard.historyEpoch then
    throw (.invalidContext "storage reference lifetime history invalidated by raw transition")
  if heap.generations region guard.slot guard.index != guard.generation then
    throw (.undefinedBehavior "dangling storage reference after element removal")
  if let some generation := guard.layoutGeneration then
    if heap.layouts region guard.slot != generation then
      throw (.undefinedBehavior "dangling bytes reference after layout transition")
  let word ← Slot.read heap region guard.slot
  let length ← if guard.bytes then byteLength word else .ok word.toNat
  if length ≤ guard.index then
    throw (.undefinedBehavior "dangling storage reference after array removal")

def checkGuards (heap : Heap) (reference : Reference) : Result Unit := do
  for guard in reference.guards do
    checkGuard heap reference.region guard

theorem checkGuard_history_rejected {heap : Heap} {region : Region} {guard : ReferenceGuard}
    (different : heap.historyEpoch region ≠ guard.historyEpoch) :
    checkGuard heap region guard =
      .error (.invalidContext "storage reference lifetime history invalidated by raw transition") := by
  simp [checkGuard, different, Bind.bind, Except.bind]

theorem checkGuards_head_error {heap : Heap} {reference : Reference} {guard : ReferenceGuard}
    {rest : List ReferenceGuard} {failure : Failure}
    (failed : checkGuard heap reference.region guard = .error failure) :
    checkGuards heap {reference with guards := guard :: rest} = .error failure := by
  simp [checkGuards, ForIn.forIn, failed, Bind.bind, Except.bind]

def regionMatches (type : SType) (region : Region) : Bool :=
  match referenceLocation type, region with
  | some .storage, .storage _ | some .memory, .memory _ |
    some .calldata, .calldata _ => true
  | none, _ => (storageBytes type).isSome
  | _, _ => false

def validate (heap : Heap) (place : Place) : Result Unit := do
  if !regionMatches place.type place.reference.region then throw .rejected
  if place.reference.byteCell && place.type != .fixedBytes 0 then throw .rejected
  if isReference place.type && place.reference.byte != 0 then throw .rejected
  match place.reference.region with
  | .storage _ | .transient _ =>
      if let some bytes := storageBytes place.type then
        if 32 < place.reference.byte.val + bytes then throw .rejected
  | .memory invocation | .calldata invocation =>
      if invocation != heap.invocation then throw (.invalidContext "foreign invocation reference")
  checkGuards heap place.reference

def read (heap : Heap) (place : Place) : Result Value := do
  validate heap place
  if isReference place.type then place.asValue else
    return ⟨place.type, ← readScalar heap place⟩

def write (heap : Heap) (place : Place) (value : Value) : Result Heap := do
  validate heap place
  if equal : value.type = place.type then
    writeScalar heap place (equal ▸ value.value)
  else throw .rejected

def length (heap : Heap) (place : Place) : Result Nat := do
  validate heap place
  match place.type with
  | .array _ (some length) _ _ => return length
  | .array _ none _ _ | .bytes _ _ | .string _ _ =>
      match place.reference.region, place.reference.viewLength with
      | .calldata _, some length => return length
      | _, some _ => throw (.invalidContext "a slice length requires calldata")
      | _, none =>
          let word ← readWord heap place.reference
          match place.type, place.reference.region with
          | .bytes _ _, .storage _ | .string _ _, .storage _ => byteLength word
          | _, _ => return word.toNat
  | _ => throw .rejected

/-- Source references promise physical head packets. A raw violation of that
domain is inconclusive; it is not evidence of a native source revert. ABI
decoders use their own ordered checks and retain their semantic reverts. -/
def sourceExtent (heap : Heap) (reference : Reference) (needed : Nat) : Result Unit := do
  if heap.execution.context.calldata.length < reference.address.toNat + needed ||
      2^256 < reference.address.toNat + needed then
    throw (.invalidContext "source calldata head outside typed physical extent")

def sourceLength (registry : Registry) (fuel : Nat) (heap : Heap) (place : Place) : Result Nat := do
  if let .calldata _ := place.reference.region then
    match place.type with
    | .array _ none _ _ | .bytes _ _ | .string _ _ =>
        if place.reference.viewLength.isNone then sourceExtent heap place.reference 32
    | _ => pure ()
  let count ← length heap place
  if let .calldata _ := place.reference.region then
    let description : Result (Nat × Nat) := match place.type with
      | .array element size _ _ => do
          let stride ← calldataHeadSize registry fuel element
          return (stride,
            if size.isNone && place.reference.viewLength.isNone then 32 else 0)
      | .bytes _ _ | .string _ _ =>
          pure (1, if place.reference.viewLength.isNone then 32 else 0)
      | _ => throw .rejected
    let (stride, header) ← description
    sourceExtent heap place.reference (header + count*stride)
  return count

def advance (reference : Reference) (bytes : Nat) : Result Reference :=
  match reference.region with
  | .storage _ | .transient _ =>
      .ok (rebase reference (reference.address + BitVec.ofNat 256 bytes))
  | .memory _ =>
      if reference.address.toNat + bytes < 2^256 then
        .ok (rebase reference (BitVec.ofNat 256 (reference.address.toNat + bytes)))
      else .error (.panic 0x41)
  | .calldata _ =>
      if reference.address.toNat + bytes < 2^256 then
        .ok (rebase reference (BitVec.ofNat 256 (reference.address.toNat + bytes)))
      else .error (.revert [])

/-- Minimum ABI tail head consumed by the source calldata-tail accessor. This
is distinct from the single offset word occupied in an enclosing head. -/
def calldataTailMinimum (registry : Registry) (fuel : Nat) (type : SType) : Result Nat := do
  let count ← do
    match type with
    | .array _ none _ _ | .bytes _ _ | .string _ _ => return 32
    | .array element (some count) _ _ =>
        return count * (← calldataHeadSize registry fuel element)
    | .structType identity _ _ =>
        let some fields := registry.structFields identity |
          throw (.invalidContext "missing calldata tail struct definition")
        fields.foldlM (fun count (_, type) => do
          return count + (← calldataHeadSize registry fuel type)) 0
    | _ => throw .rejected
  checkedStorageCount count

/-- Native source-tail predicates use signed comparisons and wrapping Word
arithmetic. Valid backward aliases must survive these checks. A native-passing
view outside the physical typed domain is explicitly inconclusive, rather than
being turned into a fabricated natural-arithmetic source revert. -/
def calldataTail (registry : Registry) (fuel : Nat) (heap : Heap) (type : SType)
    (cell : Reference) (base : Word) : Result Reference := do
  sourceExtent heap cell 32
  let offset ← readWord heap cell
  let needed ← calldataTailMinimum registry fuel type
  let size := BitVec.ofNat 256 heap.execution.context.calldata.length
  let limit := size - base - (BitVec.ofNat 256 needed - 1)
  if !offset.slt limit then throw (.revert [])
  let tail := rebase cell (base + offset)
  let dynamic : Option SType := match type with
    | .array element none _ _ => some element
    | .bytes _ _ | .string _ _ => some (.fixedBytes 0)
    | _ => none
  match dynamic with
  | none =>
      if heap.execution.context.calldata.length < tail.address.toNat + needed then
        throw (.invalidContext "native calldata tail outside typed physical extent")
      return tail
  | some element =>
      -- The native metadata load is padded. Ordinary typed scalar packet
      -- reads still require their full extent and never invent payload bytes.
      let count := bytesWord (Contract.Interaction.readBytesPadded
        heap.execution.context.calldata tail.address.toNat 32)
      if MemoryOps.maximumMemory < count.toNat then throw (.revert [])
      let data := rebase tail (tail.address + 32)
      let stride ← match type with
        | .bytes _ _ | .string _ _ => pure 1
        | _ => calldataHeadSize registry fuel element
      if (size - count * BitVec.ofNat 256 stride).slt data.address then throw (.revert [])
      if heap.execution.context.calldata.length < data.address.toNat + count.toNat * stride then
        throw (.invalidContext "native calldata view outside typed physical extent")
      return {data with viewLength := some count.toNat, relativeBase := some data.address}

/-- A memory aggregate cell stores a pointer. A dynamic calldata cell stores an
offset relative to its enclosing sequence. Static calldata aggregates are inline. -/
def child (registry : Registry) (fuel : Nat) (heap : Heap) (type : SType)
    (cell : Reference) (calldataBase : Word) : Result Place := do
  let type := atLocation type (regionLocation cell.region) false
  if isReference type then
    match cell.region with
    | .memory _ =>
        let pointer ← readWord heap cell
        return ⟨type, { (rebase cell pointer) with bindingCell := some cell.address }⟩
    | .calldata _ =>
        if ← calldataDynamic registry fuel type then
          return ⟨type, ← calldataTail registry fuel heap type cell calldataBase⟩
        else return ⟨type, cell⟩
    | _ => return ⟨type, cell⟩
  else return ⟨type, cell⟩

def field (registry : Registry) (fuel : Nat) (heap : Heap) (place : Place)
    (index : Nat) : Result Place := do
  validate heap place
  let .structType identity _ _ := place.type | throw .rejected
  let some members := registry.structFields identity |
    throw (.invalidContext "missing resolved struct members")
  let some (_, type) := members[index]? | throw .rejected
  match place.reference.region with
  | .storage _ =>
      let (_, slot, byte) ← fieldOffset registry fuel identity index
      let reference := rebase place.reference
        (place.reference.address + BitVec.ofNat 256 slot) byte
      return ⟨atLocation type .storage false, reference⟩
  | .transient _ => throw .rejected
  | .memory _ =>
      child registry fuel heap type (← advance place.reference (32 * index)) place.reference.address
  | .calldata _ =>
      let head ← members.foldlM (fun size (_, type) => do
        return size + (← calldataHeadSize registry fuel type)) 0
      sourceExtent heap place.reference head
      let offset ← (members.take index).foldlM (fun offset (_, type) => do
        return offset + (← calldataHeadSize registry fuel type)) 0
      child registry fuel heap type (← advance place.reference offset) place.reference.address

def arrayData (place : Place) : Result Reference :=
  match place.type, place.reference.region, place.reference.viewLength with
  | .array _ none _ _, .storage _, _ => .ok (dataArea place.reference)
  | .array _ none _ _, .memory _, _ => advance place.reference 32
  | .array _ none _ _, .calldata _, none => advance place.reference 32
  | .array _ _ _ _, _, _ => .ok place.reference
  | _, _, _ => .error .rejected

def captureGuard (heap : Heap) (reference : Reference) (index : Nat) (bytes : Bool) : ReferenceGuard where
  slot := reference.address
  index := index
  bytes := bytes
  generation := heap.generations reference.region reference.address index
  layoutGeneration := if bytes then some (heap.layouts reference.region reference.address) else none
  historyEpoch := heap.historyEpoch reference.region

/-- The common physical byte lvalue operation, also used by no-argument
storage bytes push after its native header/data writes. -/
def byteIndex (heap : Heap) (reference : Reference) (index : Nat) : Result Place := do
  let place : Place := ⟨.bytes (regionLocation reference.region) false, reference⟩
  let count ← length heap place
  if count ≤ index then throw (.panic 0x32)
  match reference.region with
  | .storage _ =>
      let header ← readWord heap reference
      let result := if header.toNat % 2 = 0 then
          { reference with byte := ⟨31-index, by omega⟩ }
        else
          let data := dataArea reference
          { data with address := data.address + BitVec.ofNat 256 (index/32)
                      byte := ⟨31-index%32, by omega⟩ }
      return ⟨.fixedBytes 0, { result with
        guards := reference.guards ++ [captureGuard heap reference index true] }⟩
  | .memory _ | .calldata _ =>
      let header := match reference.region, reference.viewLength with
        | .calldata _, some _ => 0 | _, _ => 32
      let result ← advance reference (header + index)
      return ⟨.fixedBytes 0, { result with byteCell := true }⟩
  | .transient _ => throw .rejected

def index (registry : Registry) (fuel : Nat) (heap : Heap) (place : Place)
    (index : Nat) : Result Place := do
  let count ← sourceLength registry fuel heap place
  if count ≤ index then throw (.panic 0x32)
  match place.type with
  | .array element size _ _ =>
      let data ← arrayData place
      match place.reference.region with
      | .storage _ =>
          let (slot, byte) ← elementOffset registry fuel element index
          let reference := rebase data (data.address + BitVec.ofNat 256 slot) byte
          let reference := if size.isNone then
            { reference with guards := place.reference.guards ++ [captureGuard heap place.reference index false] }
            else reference
          return ⟨atLocation element .storage false, reference⟩
      | .transient _ => throw .rejected
      | .memory _ => child registry fuel heap element (← advance data (index * 32)) data.address
      | .calldata _ =>
          let stride ← calldataHeadSize registry fuel element
          child registry fuel heap element (← advance data (index * stride))
            (data.relativeBase.getD data.address)
  | .bytes _ _ => byteIndex heap place.reference index
  | _ => throw .rejected

inductive MappingKey where
  | scalar : Value → MappingKey
  | bytes (string : Bool) (value : List UInt8)

def keyBytes (expected : SType) (key : MappingKey) : Result (List UInt8) := do
  match expected, key with
  | .bytes _ _, .bytes false bytes | .string _ _, .bytes true bytes => return bytes
  | _, .scalar value =>
      if equal : value.type = expected then
        return wordBytes (← encodeMemory expected (equal ▸ value.value))
      else throw .rejected
  | _, _ => throw .rejected

def mapping (heap : Heap) (place : Place) (key : MappingKey) : Result Place := do
  validate heap place
  let .mapping keyType valueType := place.type | throw .rejected
  let .storage _ := place.reference.region | throw .rejected
  let key ← keyBytes keyType key
  return ⟨atLocation valueType .storage false,
    rebase place.reference (hash (key ++ wordBytes place.reference.address))⟩

def slice (registry : Registry) (fuel : Nat) (heap : Heap) (place : Place)
    (start stop : Nat) : Result Place := do
  validate heap place
  let .calldata _ := place.reference.region | throw .rejected
  let count ← sourceLength registry fuel heap place
  if stop < start || count < stop then throw (.revert [])
  let description : Result (SType × Nat × Reference) := match place.type with
    | .array element none .calldata _ => do
        if ← calldataDynamic registry fuel element then throw .rejected
        return (.array element none .calldata true,
          ← calldataHeadSize registry fuel element, ← arrayData place)
    | .bytes .calldata _ => do
        let data ← if place.reference.viewLength.isSome then pure place.reference
          else advance place.reference 32
        return (.bytes .calldata true, 1, data)
    | _ => throw .rejected
  let (type, stride, data) ← description
  let reference ← advance data (start * stride)
  return ⟨type, { reference with viewLength := some (stop-start), relativeBase := some (data.relativeBase.getD data.address) }⟩

inductive Step where
  | field (index : Nat)
  | index (index : Nat)
  | mapping (key : MappingKey)
  | slice (start stop : Nat)

def step (registry : Registry) (fuel : Nat) (heap : Heap) (place : Place) : Step → Result Place
  | .field index => field registry fuel heap place index
  | .index index => Access.index registry fuel heap place index
  | .mapping key => mapping heap place key
  | .slice start stop => slice registry fuel heap place start stop

def resolve (registry : Registry) (fuel : Nat) (heap : Heap) (root : Place) :
    List Step → Result Place
  | [] => do validate heap root; return root
  | first :: rest => do resolve registry fuel heap (← step registry fuel heap root first) rest

/-- Source-facing endpoints validate resolved type/location metadata as well
as the physical operation. The lower-level operations remain usable by proved
copy/initialization traversals after their placement check has been discharged. -/
def resolveChecked (registry : Registry) (fuel : Nat) (heap : Heap) (root : Place)
    (path : List Step) : Result Place := do
  eligibleAt registry fuel root.reference.region root.type
  let target ← resolve registry fuel heap root path
  eligibleAt registry fuel target.reference.region target.type
  return target

def readChecked (registry : Registry) (fuel : Nat) (heap : Heap) (place : Place) : Result Value := do
  eligibleAt registry fuel place.reference.region place.type
  read heap place

def writeChecked (registry : Registry) (fuel : Nat) (heap : Heap) (place : Place)
    (value : Value) : Result Heap := do
  eligibleAt registry fuel place.reference.region place.type
  write heap place value

/-- Finite path execution is independent of the recursive path runner. The
single-step rules are the concrete layout/hash/bounds operations above. -/
inductive Resolves (registry : Registry) (fuel : Nat) (heap : Heap) :
    Place → List Step → Place → Prop where
  | nil : validate heap root = .ok () → Resolves registry fuel heap root [] root
  | cons : step registry fuel heap root first = .ok next →
      Resolves registry fuel heap next rest target →
      Resolves registry fuel heap root (first :: rest) target

theorem resolve_sound
    (finished : resolve registry fuel heap root path = .ok target) :
    Resolves registry fuel heap root path target := by
  induction path generalizing root with
  | nil =>
      unfold resolve at finished
      cases checked : validate heap root with
      | error failure => simp [checked, bind, Except.bind] at finished
      | ok resultUnit =>
          cases resultUnit
          change (do validate heap root; pure root) = .ok target at finished
          simp [checked, bind, Except.bind] at finished
          cases finished
          exact .nil checked
  | cons first rest ih =>
      unfold resolve at finished
      cases advanced : step registry fuel heap root first with
      | error failure => simp [advanced, bind, Except.bind] at finished
      | ok next =>
          simp [advanced, bind, Except.bind] at finished
          exact .cons advanced (ih finished)

theorem resolve_complete (valid : Resolves registry fuel heap root path target) :
    resolve registry fuel heap root path = .ok target := by
  induction valid with
  | nil checked => simp [resolve, checked, bind, Except.bind]; rfl
  | cons advanced _ ih => simp [resolve, advanced, bind, Except.bind, ih]

theorem resolve_iff : resolve registry fuel heap root path = .ok target ↔
    Resolves registry fuel heap root path target := ⟨resolve_sound, resolve_complete⟩

theorem Resolves.valid (derivation : Resolves registry fuel heap root path target) :
    validate heap target = .ok () := by
  induction derivation with
  | nil checked => exact checked
  | cons _ _ ih => exact ih

theorem resolve_valid (finished : resolve registry fuel heap root path = .ok target) :
    validate heap target = .ok () := (resolve_sound finished).valid

theorem length_fixed (heap : Heap) (element : SType) (n : Nat) (location : Location)
    (pointer : Bool) (reference : Reference)
    (valid : validate heap ⟨.array element (some n) location pointer, reference⟩ = .ok ()) :
    length heap ⟨.array element (some n) location pointer, reference⟩ = .ok n := by
  simp [length, valid]; rfl

theorem index_out_of_bounds (registry : Registry) (fuel : Nat) (heap : Heap)
    (place : Place) (index count : Nat)
    (sized : sourceLength registry fuel heap place = .ok count)
    (outside : count ≤ index) :
    Access.index registry fuel heap place index = .error (.panic 0x32) := by
  simp [Access.index, sized, bind, Except.bind, outside]

theorem transient_aggregate_rejected (heap : Heap) (type : SType) (account : BitVec 160)
    (reference : Reference) (aggregate : referenceLocation type = some location)
    (transient : reference.region = .transient account) :
    validate heap ⟨type, reference⟩ = .error .rejected := by
  simp [validate, regionMatches, aggregate, transient]
  rfl

end Solidity.Aggregates.Access
