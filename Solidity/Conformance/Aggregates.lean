/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy
import Solidity.Core.Aggregates.ReferenceCasts
import Solidity.Target
import Lean.Data.Json.FromToJson

/-! Executable aggregate witnesses. Solidity source is paired manually with
resolved model operations; calldata helper arguments are paired with
already admitted byte views, not an ABI-decoder proof. All runtime
expectations come from the physical heap APIs. Unsupported execution and host
exhaustion remain separate from Solidity reverts and source rejections. -/
namespace Solidity.Conformance.Aggregates
open Solidity.Aggregates Static Lean
open Contract.Interaction (Word wordBytes)

private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun identity => identity == 1 || identity == 2 || identity == 3
  structFields := fun identity =>
    if identity == 1 then some [("value", .uint 1), ("saved", .mapping (.uint 31) (.uint 31))]
    else if identity == 2 then some [("a", .uint 1), ("b", .uint 1)]
    else if identity == 3 then some [("n", .uint 31),
      ("children", .array (.structType 3 .storage false) none .storage false)] else none }

private def declarations : List StorageDeclaration := [
  ⟨"left", .uint 1, .persistent⟩, ⟨"right", .uint 1, .persistent⟩,
  ⟨"numbers", .array (.uint 2) none .storage false, .persistent⟩,
  ⟨"buckets", .mapping (.uint 31) (.array (.uint 2) none .storage false), .persistent⟩,
  ⟨"box", .structType 1 .storage false, .persistent⟩,
  ⟨"boxes", .array (.structType 1 .storage false) none .storage false, .persistent⟩,
  ⟨"payload", .bytes .storage false, .persistent⟩, ⟨"pair", .structType 2 .storage false, .persistent⟩,
  ⟨"text", .string .storage false, .persistent⟩,
  ⟨"fixedNumbers", .array (.uint 2) (some 11) .storage false, .persistent⟩]

private def root (index : Nat) : Result Place := do
  let layout ← declarationLayout registry 64 0 [(0, declarations)]
  let some field := layout.fields[index]? | throw (.invalidContext "missing corpus declaration")
  return ⟨field.declaration.type,
    {region := .storage 0, address := BitVec.ofNat 256 field.position.slot,
     byte := field.position.byte}⟩

private def initial : Heap := MemoryOps.initialHeap
private def allowance : Nat := 100000
private def fuel : Nat := 64

private def unsigned (value : Value) : Result Nat :=
  match value with
  | ⟨.uint _, value⟩ | ⟨.fixedBytes _, value⟩ => .ok value.toNat
  | _ => .error .rejected

private def get (heap : Heap) (place : Place) : Result Nat := do
  unsigned (← Access.read heap place)

private def put (heap : Heap) (place : Place) (value : Nat) : Result Heap :=
  match place.type with
  | .uint width => Access.write heap place ⟨.uint width, BitVec.ofNat width.bits value⟩
  | .fixedBytes width => Access.write heap place ⟨.fixedBytes width, BitVec.ofNat width.bits value⟩
  | _ => .error .rejected

private def field (heap : Heap) (place : Place) (index : Nat) : Result Place :=
  Access.field registry fuel heap place index
private def index (heap : Heap) (place : Place) (offset : Nat) : Result Place :=
  Access.index registry fuel heap place offset
private def key (heap : Heap) (place : Place) (value : Nat) : Result Place :=
  Access.mapping heap place (.scalar ⟨.uint 31, BitVec.ofNat 256 value⟩)

private def append (heap : Heap) (place : Place) (value : Nat) : Result Heap := do
  let (cell, heap, _) ← StorageArrays.pushZero registry fuel allowance heap place
  put heap cell value

private def observed (value : Nat) : Result Word := .ok (BitVec.ofNat 256 value)

private def packedFields : Result Word := do
  let left ← root 0
  let right ← root 1
  let heap ← put initial left 0x1234
  let heap ← put heap right 0xabcd
  let heap ← put heap left 1
  observed ((← get heap right) * 65536 + (← get heap left))

private def packedArray : Result Word := do
  let numbers ← root 2
  let heap ← (List.range 11).foldlM (fun heap n => append heap numbers (n+1)) initial
  let heap ← put heap (← index heap numbers 9) 0xaabbcc
  let heap ← put heap (← index heap numbers 10) 0x123456
  observed ((← get heap (← index heap numbers 8)) * 2^48 +
    (← get heap (← index heap numbers 9)) * 2^24 + (← get heap (← index heap numbers 10)))

private def packedStruct : Result Word := do
  let pair ← root 7
  let a ← field initial pair 0
  let b ← field initial pair 1
  let heap ← put initial a 0x1234
  let heap ← put heap b 0xabcd
  let heap ← put heap a 1
  observed ((← get heap b) * 65536 + (← get heap a))

private def fixedStorageArray : Result Word := do
  let array ← root 9
  let heap ← put initial (← index initial array 9) 0xaabbcc
  let heap ← put heap (← index heap array 10) 0x123456
  observed ((← get heap (← index heap array 9)) * 2^24 + (← get heap (← index heap array 10)))

private def nestedMappingArray : Result Word := do
  let buckets ← root 3
  let seven ← key initial buckets 7
  let eight ← key initial buckets 8
  let heap ← append initial seven 9
  let heap ← append heap seven 11
  let heap ← append heap eight 13
  observed ((← get heap (← index heap seven 1)) * 256 + (← get heap (← index heap eight 0)))

private def storageAlias : Result Word := do
  let numbers ← root 2
  let source ← numbers.asValue
  let (bound, heap, _) ← Copy.bind registry fuel allowance initial
    (.array (.uint 2) none .storage true) source
  let alias ← Defaults.asPlace bound
  let heap ← append heap alias 7
  observed (← get heap (← index heap numbers 0))

private def memoryAlias : Result Word := do
  let (source, heap, budget) ← Defaults.newArray registry fuel allowance initial (.uint 0) 2
  let original ← Defaults.asPlace source
  let (bound, heap, _) ← Copy.bind registry fuel budget heap (.array (.uint 0) none .memory true) source
  let alias ← Defaults.asPlace bound
  let heap ← put heap (← index heap alias 1) 17
  observed (← get heap (← index heap original 1))

private def memoryReferenceAssignment : Result Word := do
  let (source, heap, budget) ← Defaults.newArray registry fuel allowance initial
    (.structType 2 .memory false) 2
  let array ← Defaults.asPlace source
  let first ← index heap array 0
  let second ← index heap array 1
  let (bound, heap, budget) ← Copy.bind registry fuel budget heap
    (.structType 2 .memory true) (← first.asValue)
  let alias ← Defaults.asPlace bound
  let (heap, _) ← Copy.assign registry fuel budget heap first (← second.asValue)
  let heap ← put heap (← field heap alias 0) 7
  let current ← index heap array 0
  observed ((← get heap (← field heap current 0)) * 256 + (← get heap (← field heap alias 0)))

private def nestedMemoryDefaults : Result Word := do
  let (value, heap, _) ← Defaults.newArray registry fuel allowance initial
    (.array (.uint 0) (some 2) .memory false) 2
  let array ← Defaults.asPlace value
  let first ← index heap array 0
  let second ← index heap array 1
  let heap ← put heap (← index heap first 0) 7
  observed ((← get heap (← index heap first 0)) * 256 + (← get heap (← index heap second 0)))

private def recursiveMemoryDefault : Result Word := do
  let (zero, heap, budget) ← Defaults.defaultValue registry fuel allowance initial
    (.structType 3 .memory true)
  let zero ← Defaults.asPlace zero
  let (values, heap, budget) ← Defaults.newArray registry fuel budget heap
    (.structType 3 .memory false) 2
  let array ← Defaults.asPlace values
  let first ← index heap array 0
  let second ← index heap array 1
  let (bound, heap, _) ← Copy.bind registry fuel budget heap
    (.structType 3 .memory true) (← first.asValue)
  let alias ← Defaults.asPlace bound
  let heap ← put heap (← field heap alias 0) 7
  observed ((← Access.length heap (← field heap zero 1)) +
    (← get heap (← field heap first 0)) * 65536 + (← get heap (← field heap second 0)))

private def fixedMemoryDefault : Result Word := do
  let (value, heap, _) ← Defaults.defaultValue registry fuel allowance initial
    (.array (.uint 1) (some 2) .memory true)
  let array ← Defaults.asPlace value
  observed ((← get heap (← index heap array 0)) + (← get heap (← index heap array 1)))

private def memoryToStorage : Result Word := do
  let numbers ← root 2
  let (source, heap, budget) ← Defaults.newArray registry fuel allowance initial (.uint 2) 2
  let memory ← Defaults.asPlace source
  let heap ← put heap (← index heap memory 0) 7
  let heap ← put heap (← index heap memory 1) 9
  let (heap, _) ← Copy.assign registry fuel budget heap numbers source
  let heap ← put heap (← index heap memory 0) 1
  observed ((← get heap (← index heap numbers 0)) * 256 + (← get heap (← index heap numbers 1)))

private def storageToMemory : Result Word := do
  let numbers ← root 2
  let heap ← append initial numbers 7
  let (value, heap, _) ← Copy.bind registry fuel allowance heap
    (.array (.uint 2) none .memory true) (← numbers.asValue)
  let memory ← Defaults.asPlace value
  let heap ← put heap (← index heap memory 0) 99
  observed ((← get heap (← index heap numbers 0)) * 256 + (← get heap (← index heap memory 0)))

private def storageToStorage : Result Word := do
  let numbers ← root 2
  let buckets ← root 3
  let destination ← key initial buckets 7
  let heap ← append initial numbers 7
  let heap ← append heap numbers 9
  let (heap, _) ← Copy.assign registry fuel allowance heap destination (← numbers.asValue)
  let heap ← put heap (← index heap numbers 0) 1
  observed ((← get heap (← index heap destination 0)) * 256 + (← get heap (← index heap destination 1)))

private def calldataWords : Heap := MemoryOps.initialHeap {
  context := {calldata := wordBytes 2 ++ wordBytes 7 ++ wordBytes 9}}
private def calldataArray : Place := ⟨.array (.uint 2) none .calldata true,
  {region := .calldata 0, address := 0}⟩

private def calldataToMemory : Result Word := do
  let (value, heap, _) ← Copy.bind registry fuel allowance calldataWords
    (.array (.uint 2) none .memory true) (← calldataArray.asValue)
  let memory ← Defaults.asPlace value
  let heap ← put heap (← index heap memory 0) 99
  observed ((← get heap (← index heap calldataArray 0)) * 256 + (← get heap (← index heap memory 0)))

private def calldataToStorage : Result Word := do
  let numbers ← root 2
  let (heap, _) ← Copy.assign registry fuel allowance calldataWords numbers (← calldataArray.asValue)
  observed ((← get heap (← index heap numbers 0)) * 256 + (← get heap (← index heap numbers 1)))

private def bytes (count : Nat) : List UInt8 :=
  (List.range count).map (fun n => UInt8.ofNat (n+1))

private def byteTransition (count : Nat) (push : Bool) : Result Word := do
  let payload ← root 6
  let (heap, budget) ← StorageBytes.writeChecked initial allowance payload.reference (bytes count)
  let (heap, _) ← if push then StorageBytes.pushChecked heap budget payload.reference 0xab
    else StorageBytes.popChecked heap budget payload.reference
  let count ← Access.length heap payload
  observed (count * 256 + (← get heap (← index heap payload (count-1))))

private def byteNoArg (count : Nat) : Result Word := do
  let payload ← root 6
  let (heap, budget) ← StorageBytes.writeChecked initial allowance payload.reference (bytes count)
  let (cell, heap, _) ← StorageBytes.pushZeroChecked heap budget payload.reference
  observed ((← Access.length heap payload) * 256 + (← get heap cell))

private def byteNoArgDirty (long : Bool) : Result Word := do
  let payload ← root 6
  let heap ← if long then do
      let (heap, _) ← StorageBytes.writeChecked initial allowance payload.reference (bytes 32)
      Slot.write heap payload.reference.region (StorageBytes.dataSlot payload.reference 1)
        (BitVec.ofNat 256 (0xff * 2^248))
    else
      Slot.write initial payload.reference.region payload.reference.address
        (BitVec.ofNat 256 (0xaa * 2^248))
  let (cell, heap, _) ← StorageBytes.pushZeroChecked heap allowance payload.reference
  observed ((← Access.length heap payload) * 256 + (← get heap cell))

private def bytesShrink : Result Word := do
  let payload ← root 6
  let (heap, budget) ← StorageBytes.writeChecked initial allowance payload.reference (bytes 65)
  let (heap, _) ← StorageBytes.writeChecked heap budget payload.reference [0xaa]
  let tail ← Slot.read heap payload.reference.region (StorageBytes.dataSlot payload.reference 2)
  observed (tail.toNat + (← Access.length heap payload) * 256 + (← get heap (← index heap payload 0)))

private def bytesDelete : Result Word := do
  let payload ← root 6
  let (heap, budget) ← StorageBytes.writeChecked initial allowance payload.reference (bytes 33)
  let (heap, _) ← StorageArrays.delete registry fuel budget heap payload
  let data ← Slot.read heap payload.reference.region (StorageBytes.dataSlot payload.reference 0)
  observed (data.toNat + (← Access.length heap payload))

private def stringDelete : Result Word := do
  let text ← root 8
  let (heap, budget) ← StorageBytes.writeChecked initial allowance text.reference [0x61, 0x62, 0x63]
  let before ← Access.length heap text
  let (heap, _) ← StorageArrays.delete registry fuel budget heap text
  observed (before * 256 + (← Access.length heap text))

private def mappingRetained : Result Word := do
  let box ← root 4
  let saved ← field initial box 1
  let heap ← put initial (← key initial saved 7) 11
  let heap ← put heap (← field heap box 0) 9
  let (heap, _) ← StorageArrays.delete registry fuel allowance heap box
  observed ((← get heap (← key heap saved 7)) + (← get heap (← field heap box 0)))

private def poppedMappingRetained : Result Word := do
  let boxes ← root 5
  let (box, heap, budget) ← StorageArrays.pushZero registry fuel allowance initial boxes
  let saved ← field heap box 1
  let heap ← put heap (← key heap saved 7) 11
  let heap ← put heap (← field heap box 0) 9
  let (heap, budget) ← StorageArrays.pop registry fuel budget heap boxes
  let (box, heap, _) ← StorageArrays.pushZero registry fuel budget heap boxes
  let saved ← field heap box 1
  observed ((← get heap (← key heap saved 7)) + (← get heap (← field heap box 0)))

private def arrayDelete : Result Word := do
  let numbers ← root 2
  let heap ← append initial numbers 7
  let heap ← append heap numbers 9
  let (heap, budget) ← StorageArrays.delete registry fuel allowance heap numbers
  let (cell, heap, _) ← StorageArrays.pushZero registry fuel budget heap numbers
  observed (← get heap cell)

private def calldataBytes : Heap := MemoryOps.initialHeap {context := {calldata := [1,2,3,4]}}
private def calldataByteView : Result Place := do
  return ⟨.bytes .calldata true, ← MemoryOps.calldataView calldataBytes 0 4⟩

private def calldataSlice : Result Word := do
  let selected ← Access.slice registry fuel calldataBytes (← calldataByteView) 1 3
  observed ((← Access.length calldataBytes selected) * 65536 +
    (← get calldataBytes (← index calldataBytes selected 0)) * 256 +
    (← get calldataBytes (← index calldataBytes selected 1)))

private def calldataSliceBounds : Result Word := do
  let selected ← Access.slice registry fuel calldataBytes (← calldataByteView) 1 5
  observed (← Access.length calldataBytes selected)

private def calldataIndexBounds : Result Word := do
  observed (← get calldataBytes (← index calldataBytes (← calldataByteView) 4))

private def arrayBounds : Result Word := do
  let numbers ← root 2
  let heap ← append initial numbers 7
  observed (← get heap (← index heap numbers 1))

private def arrayEmptyPop : Result Word := do
  let (heap, _) ← StorageArrays.pop registry fuel allowance initial (← root 2)
  observed (← Access.length heap (← root 2))

private def byteEmptyPop : Result Word := do
  let payload ← root 6
  let (heap, _) ← StorageBytes.popChecked initial allowance payload.reference
  observed (← Access.length heap payload)

private def byteInvalid : Result Word := do
  let payload ← root 6
  let heap ← Slot.write initial payload.reference.region payload.reference.address 64
  observed (← Access.length heap payload)

private def allocationPanic : Result Word := do
  let (_, _, _) ← Defaults.newBytes allowance initial (2^256-1)
  observed 0

private def memoryCastAlias : Result Word := do
  let (value, heap, budget) ← Copy.materializeMemory registry fuel allowance initial
    (.bytes .memory true) (.bytes false [1,2,3])
  let original ← Defaults.asPlace value
  let (text, budget) ← ReferenceCasts.cast registry fuel budget heap (.string .memory true) value
  let (bytes, _) ← ReferenceCasts.cast registry fuel budget heap (.bytes .memory true) text
  let alias ← Defaults.asPlace bytes
  let heap ← put heap (← index heap alias 0) 0x7a
  observed (← get heap (← index heap original 0))

private def storageCastAlias : Result Word := do
  let payload ← root 6
  let (heap, budget) ← StorageBytes.writeChecked initial allowance payload.reference [1]
  let (text, budget) ← ReferenceCasts.cast registry fuel budget heap (.string .storage true) (← payload.asValue)
  let (bytes, _) ← ReferenceCasts.cast registry fuel budget heap (.bytes .storage true) text
  let alias ← Defaults.asPlace bytes
  let heap ← put heap (← index heap alias 0) 0x7a
  observed (← get heap (← index heap payload 0))

private def calldataCastSlice : Result Word := do
  let selected ← Access.slice registry fuel calldataBytes (← calldataByteView) 1 3
  let (text, budget) ← ReferenceCasts.cast registry fuel allowance calldataBytes
    (.string .calldata true) (← selected.asValue)
  let (bytes, _) ← ReferenceCasts.cast registry fuel budget calldataBytes (.bytes .calldata true) text
  let roundtrip ← Defaults.asPlace bytes
  observed ((← Access.length calldataBytes roundtrip) * 65536 +
    (← get calldataBytes (← index calldataBytes roundtrip 0)) * 256 +
    (← get calldataBytes (← index calldataBytes roundtrip 1)))

private def memoryFixedPrefix (values : List UInt8) (dirty : Bool := false) : Result Word := do
  let (value, heap, budget) ← Copy.materializeMemory registry fuel allowance initial
    (.bytes .memory true) (.bytes false values)
  let source ← Defaults.asPlace value
  let heap := if dirty then
    {heap with execution := {heap.execution with memory := (heap.execution.memory.write
      (source.reference.address.toNat+32) (wordBytes (BitVec.ofNat 256 (0x11*2^248+0xff*2^240))))}}
    else heap
  let (fixed, _) ← ReferenceCasts.cast registry fuel budget heap (.fixedBytes 3) value
  observed (← unsigned fixed)

private def storageFixedPrefix (values : List UInt8) : Result Word := do
  let payload ← root 6
  let (heap, budget) ← StorageBytes.writeChecked initial allowance payload.reference values
  let (fixed, _) ← ReferenceCasts.cast registry fuel budget heap (.fixedBytes 3) (← payload.asValue)
  observed (← unsigned fixed)

private def calldataSliceFixedPrefix : Result Word := do
  let selected ← Access.slice registry fuel calldataBytes (← calldataByteView) 1 3
  let (fixed, _) ← ReferenceCasts.cast registry fuel allowance calldataBytes (.fixedBytes 3) (← selected.asValue)
  observed (← unsigned fixed)

private def hexDigit (value : Nat) : Char :=
  Char.ofNat (if value < 10 then 48+value else 87+value)
private def hexLiteral (values : List UInt8) : String :=
  "hex\"" ++ String.ofList (values.flatMap (fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)])) ++ "\""

structure Case where
  name : String
  body : String
  model : Result Word
  mutability : String := "nonpayable"

def cases : List Case := [
  ⟨"packed_fields", "left = 0x1234; right = 0xabcd; left = 1; return uint256(right) * 65536 + left;", packedFields, "nonpayable"⟩,
  ⟨"packed_struct_fields", "pair.a = 0x1234; pair.b = 0xabcd; pair.a = 1; return uint256(pair.b) * 65536 + pair.a;", packedStruct, "nonpayable"⟩,
  ⟨"uint24_array_packing", "for (uint256 i; i < 11; ++i) numbers.push(uint24(i+1)); numbers[9] = 0xaabbcc; numbers[10] = 0x123456; return uint256(numbers[8]) * 2**48 + uint256(numbers[9]) * 2**24 + numbers[10];", packedArray, "nonpayable"⟩,
  ⟨"uint24_fixed_array_packing", "fixedNumbers[9] = 0xaabbcc; fixedNumbers[10] = 0x123456; return uint256(fixedNumbers[9]) * 2**24 + fixedNumbers[10];", fixedStorageArray, "nonpayable"⟩,
  ⟨"mapping_array_paths", "buckets[7].push(9); buckets[7].push(11); buckets[8].push(13); return uint256(buckets[7][1]) * 256 + buckets[8][0];", nestedMappingArray, "nonpayable"⟩,
  ⟨"storage_alias", "uint24[] storage alias_ = numbers; alias_.push(7); return numbers[0];", storageAlias, "nonpayable"⟩,
  ⟨"memory_alias", "uint8[] memory original = new uint8[](2); uint8[] memory alias_ = original; alias_[1] = 17; return original[1];", memoryAlias, "pure"⟩,
  ⟨"memory_reference_cast_alias", "bytes memory value = hex\"010203\"; string memory alias_ = string(value); bytes(alias_)[0] = 0x7a; return uint8(value[0]);", memoryCastAlias, "pure"⟩,
  ⟨"storage_reference_cast_alias", "payload = hex\"01\"; string storage alias_ = string(payload); bytes(alias_)[0] = 0x7a; return uint8(payload[0]);", storageCastAlias, "nonpayable"⟩,
  ⟨"calldata_slice_reference_cast", "return this.castSliceHelper(hex\"01020304\");", calldataCastSlice, "view"⟩,
  ⟨"memory_bytes_fixed_short", "bytes memory value = hex\"0102\"; return uint32(bytes4(value));", memoryFixedPrefix [1,2], "pure"⟩,
  ⟨"memory_bytes_fixed_long", "bytes memory value = " ++ hexLiteral (bytes 33) ++ "; return uint32(bytes4(value));", memoryFixedPrefix (bytes 33), "pure"⟩,
  ⟨"memory_bytes_fixed_empty", "bytes memory value = new bytes(0); return uint32(bytes4(value));", memoryFixedPrefix [], "pure"⟩,
  ⟨"memory_bytes_fixed_dirty_padding", "bytes memory value = hex\"11\"; assembly { mstore(add(value, 32), or(shl(248, 0x11), shl(240, 0xff))) } return uint32(bytes4(value));", memoryFixedPrefix [0x11] true, "pure"⟩,
  ⟨"storage_bytes_fixed_short", "payload = hex\"0102\"; return uint32(bytes4(payload));", storageFixedPrefix [1,2], "nonpayable"⟩,
  ⟨"storage_bytes_fixed_long", "payload = " ++ hexLiteral (bytes 33) ++ "; return uint32(bytes4(payload));", storageFixedPrefix (bytes 33), "nonpayable"⟩,
  ⟨"calldata_slice_bytes_fixed", "return this.castSlicePrefixHelper(hex\"01020304\");", calldataSliceFixedPrefix, "view"⟩,
  ⟨"memory_reference_assignment", "Pair[] memory values = new Pair[](2); Pair memory alias_ = values[0]; values[0] = values[1]; alias_.a = 7; return uint256(values[0].a) * 256 + alias_.a;", memoryReferenceAssignment, "pure"⟩,
  ⟨"nested_memory_defaults", "uint8[2][] memory values = new uint8[2][](2); values[0][0] = 7; return uint256(values[0][0]) * 256 + values[1][0];", nestedMemoryDefaults, "pure"⟩,
  ⟨"recursive_memory_defaults", "Node memory zero; Node[] memory values = new Node[](2); Node memory alias_ = values[0]; alias_.n = 7; return zero.children.length + values[0].n * 65536 + values[1].n;", recursiveMemoryDefault, "pure"⟩,
  ⟨"fixed_memory_default", "uint16[2] memory values; return uint256(values[0]) + values[1];", fixedMemoryDefault, "pure"⟩,
  ⟨"memory_to_storage_copy", "uint24[] memory values = new uint24[](2); values[0] = 7; values[1] = 9; numbers = values; values[0] = 1; return uint256(numbers[0]) * 256 + numbers[1];", memoryToStorage, "nonpayable"⟩,
  ⟨"storage_to_memory_copy", "numbers.push(7); uint24[] memory values = numbers; values[0] = 99; return uint256(numbers[0]) * 256 + values[0];", storageToMemory, "nonpayable"⟩,
  ⟨"storage_to_storage_copy", "numbers.push(7); numbers.push(9); buckets[7] = numbers; numbers[0] = 1; return uint256(buckets[7][0]) * 256 + buckets[7][1];", storageToStorage, "nonpayable"⟩,
  ⟨"calldata_to_memory_copy", "uint24[] memory values = new uint24[](2); values[0] = 7; values[1] = 9; return this.copyMemoryHelper(values);", calldataToMemory, "view"⟩,
  ⟨"calldata_to_storage_copy", "uint24[] memory values = new uint24[](2); values[0] = 7; values[1] = 9; return this.copyStorageHelper(values);", calldataToStorage, "nonpayable"⟩,
  ⟨"bytes_31_to_32", "payload = " ++ hexLiteral (bytes 31) ++ "; payload.push(0xab); return payload.length * 256 + uint8(payload[payload.length-1]);", byteTransition 31 true, "nonpayable"⟩,
  ⟨"bytes_32_to_31", "payload = " ++ hexLiteral (bytes 32) ++ "; payload.pop(); return payload.length * 256 + uint8(payload[payload.length-1]);", byteTransition 32 false, "nonpayable"⟩,
  ⟨"bytes_noarg_short", "payload = hex\"01\"; payload.push(); return payload.length * 256 + uint8(payload[1]);", byteNoArg 1, "nonpayable"⟩,
  ⟨"bytes_noarg_31_to_32", "payload = " ++ hexLiteral (bytes 31) ++ "; payload.push(); return payload.length * 256 + uint8(payload[31]);", byteNoArg 31, "nonpayable"⟩,
  ⟨"bytes_noarg_dirty_short", "assembly { sstore(payload.slot, shl(248, 0xaa)) } payload.push(); return payload.length * 256 + uint8(payload[0]);", byteNoArgDirty false, "nonpayable"⟩,
  ⟨"bytes_noarg_dirty_long", "payload = " ++ hexLiteral (bytes 32) ++ "; assembly { mstore(0, payload.slot) sstore(add(keccak256(0, 32), 1), shl(248, 0xff)) } payload.push(); return payload.length * 256 + uint8(payload[32]);", byteNoArgDirty true, "nonpayable"⟩,
  ⟨"bytes_shrink_clears_tail", "payload = " ++ hexLiteral (bytes 65) ++ "; payload = hex\"aa\"; uint256 tail; assembly { mstore(0, payload.slot) tail := sload(add(keccak256(0, 32), 2)) } return tail + payload.length * 256 + uint8(payload[0]);", bytesShrink, "nonpayable"⟩,
  ⟨"bytes_delete", "payload = " ++ hexLiteral (bytes 33) ++ "; delete payload; uint256 data; assembly { mstore(0, payload.slot) data := sload(keccak256(0, 32)) } return data + payload.length;", bytesDelete, "nonpayable"⟩,
  ⟨"string_delete", "text = \"abc\"; uint256 before_ = bytes(text).length; delete text; return before_ * 256 + bytes(text).length;", stringDelete, "nonpayable"⟩,
  ⟨"delete_retains_mapping", "box.saved[7] = 11; box.value = 9; delete box; return box.saved[7] + box.value;", mappingRetained, "nonpayable"⟩,
  ⟨"pop_retains_mapping", "boxes.push(); boxes[0].saved[7] = 11; boxes[0].value = 9; boxes.pop(); boxes.push(); return boxes[0].saved[7] + boxes[0].value;", poppedMappingRetained, "nonpayable"⟩,
  ⟨"delete_array_clears_values", "numbers.push(7); numbers.push(9); delete numbers; numbers.push(); return numbers[0];", arrayDelete, "nonpayable"⟩,
  ⟨"calldata_slice", "return this.sliceHelper(hex\"01020304\");", calldataSlice, "view"⟩,
  ⟨"calldata_slice_bounds", "return this.sliceBoundsHelper(hex\"01020304\");", calldataSliceBounds, "view"⟩,
  ⟨"calldata_index_bounds", "return this.indexBoundsHelper(hex\"01020304\");", calldataIndexBounds, "view"⟩,
  ⟨"storage_array_bounds", "numbers.push(7); return numbers[1];", arrayBounds, "nonpayable"⟩,
  ⟨"empty_array_pop", "numbers.pop(); return numbers.length;", arrayEmptyPop, "nonpayable"⟩,
  ⟨"empty_bytes_pop", "payload.pop(); return payload.length;", byteEmptyPop, "nonpayable"⟩,
  ⟨"invalid_bytes_header", "assembly { sstore(payload.slot, 64) } return payload.length;", byteInvalid, "nonpayable"⟩,
  ⟨"allocation_resource_panic", "bytes memory values = new bytes(type(uint256).max); return values.length;", allocationPanic, "pure"⟩]

private def failureName : Failure → String
  | .rejected => "rejected" | .revert _ => "revert" | .panic code => "panic:" ++ toString code.toNat
  | .exceptional => "exceptional" | .invalidContext reason => "invalidContext:" ++ reason
  | .unsupported reason => "unsupported:" ++ reason
  | .undefinedBehavior reason => "undefinedBehavior:" ++ reason | .exhausted => "exhausted"

private def resultJson : Result Word → Json
  | .ok value => Json.mkObj [("status", toJson "returned"), ("word", toJson (toString value.toNat))]
  | .error (.revert bytes) => Json.mkObj [("status", toJson "reverted"), ("bytes", toJson (bytes.map UInt8.toNat))]
  | .error (.panic code) => Json.mkObj [("status", toJson "reverted"),
      ("bytes", toJson ((Contract.panic code).map UInt8.toNat))]
  | .error failure => Json.mkObj [("status", toJson "modelFailure"), ("reason", toJson (failureName failure))]

-- Probe actual root and hash-derived physical slots. These observations check
-- eth_call rollback at the selected slots; return values check in-call effects.
private def storageProbes : List String :=
  ((List.range 11) ++ [
    (Access.hash (wordBytes 1)).toNat,
    (Access.hash (wordBytes 1) + 1).toNat,
    (Contract.Interaction.mappingKey 7 2).toNat,
    (Access.hash (wordBytes (Contract.Interaction.mappingKey 7 2))).toNat,
    (Contract.Interaction.mappingKey 8 2).toNat,
    (Access.hash (wordBytes (Contract.Interaction.mappingKey 8 2))).toNat,
    (Contract.Interaction.mappingKey 7 4).toNat,
    (Access.hash (wordBytes 5)).toNat,
    (Contract.Interaction.mappingKey 7 (Access.hash (wordBytes 5) + 1)).toNat,
    (Access.hash (wordBytes 6)).toNat,
    (Access.hash (wordBytes 6) + 1).toNat,
    (Access.hash (wordBytes 6) + 2).toNat]).map toString

private def caseJson (case : Case) : Json := Json.mkObj [
  ("name", toJson case.name), ("body", toJson case.body), ("mutability", toJson case.mutability),
  ("outcomes", toJson [resultJson case.model]), ("storageProbes", toJson storageProbes)]

private def calldataWrite : Result Unit := do
  let source : Place := ⟨.array (.uint 0) none .calldata true, calldataArray.reference⟩
  let cell ← index calldataWords source 0
  let _ ← put calldataWords cell 1
  return ()

private def dynamicSlice : Result Unit := do
  let source : Place := ⟨.array (.array (.uint 31) none .calldata false) none .calldata true,
    calldataArray.reference⟩
  let _ ← Access.slice registry fuel calldataWords source 1 2
  return ()

private def arrayStringCast : Result Unit := do
  let (value, heap, budget) ← Defaults.newArray registry fuel allowance initial (.uint 0) 2
  let _ ← ReferenceCasts.cast registry fuel budget heap (.string .memory true) value
  return ()

private def stringFixedCast : Result Unit := do
  let (value, heap, budget) ← Copy.materializeMemory registry fuel allowance initial
    (.string .memory true) (.bytes true [97,98,99])
  let _ ← ReferenceCasts.cast registry fuel budget heap (.fixedBytes 3) value
  return ()

private def modelCheck (name expected : String) (result : Result α) : Json :=
  let actual := match result with | .ok _ => "success" | .error failure => failureName failure
  Json.mkObj [("name", toJson name), ("expectedFailure", toJson expected),
    ("actualFailure", toJson actual), ("passed", toJson (actual == expected))]

private def danglingAfterRegrowth : Result Unit := do
  let numbers ← root 2
  let heap ← append initial numbers 7
  let old ← index heap numbers 0
  let (heap, budget) ← StorageArrays.pop registry fuel allowance heap numbers
  let (_, heap, _) ← StorageArrays.pushZero registry fuel budget heap numbers
  Access.validate heap old

private def danglingAfterByteLayout : Result Unit := do
  let payload ← root 6
  let (heap, budget) ← StorageBytes.writeChecked initial allowance payload.reference (bytes 31)
  let old ← index heap payload 0
  let (_, heap, _) ← StorageBytes.pushZeroChecked heap budget payload.reference
  Access.validate heap old

def modelChecks : List Json := [
  modelCheck "allocation_host_exhaustion" "exhausted" (Defaults.newBytes 0 initial 32),
  modelCheck "storage_byte_read_host_exhaustion" "exhausted"
    (do StorageBytes.read initial 0 (← root 6).reference),
  modelCheck "layout_fuel_exhaustion" "exhausted"
    (storageSize registry 0 (.structType 2 .storage false)),
  modelCheck "calldata_write_rejected" "rejected" calldataWrite,
  modelCheck "dynamic_element_slice_rejected" "rejected" dynamicSlice,
  modelCheck "memory_mapping_rejected" "rejected"
    (eligibleAt registry fuel (.memory 0) (.mapping (.uint 31) (.uint 31))),
  modelCheck "reference_dangling_after_regrowth"
    "undefinedBehavior:dangling storage reference after element removal" danglingAfterRegrowth,
  modelCheck "byte_reference_dangling_after_layout"
    "undefinedBehavior:dangling bytes reference after layout transition" danglingAfterByteLayout,
  modelCheck "recursive_internal_calldata_location_admitted" "success"
    (eligibleAt registry fuel (.calldata 0) (.structType 3 .calldata true))]

private def diagnostic (code message : String) : Json := Json.mkObj [
  ("type", toJson "TypeError"), ("errorCode", toJson code), ("message", toJson message)]

-- Complete ordered native diagnostics, retained by the cheap Standard JSON
-- preflight. They do not supply model permission or runtime expectations.
private def rejection (name parameters body : String) (model : Result Unit)
    (diagnostics : List Json) : Json :=
  let rejected := match model with | .error .rejected => toJson "staticRejected" | _ => Json.null
  Json.mkObj [("name", toJson name), ("parameters", toJson parameters),
    ("body", toJson body), ("modelError", rejected), ("diagnostics", toJson diagnostics)]

def rejections : List Json := [
  rejection "calldata_write" "uint8[] calldata values" "values[0] = 1; return 0;" calldataWrite
    [diagnostic "6182" "Calldata arrays are read-only."],
  rejection "slice_dynamic_element" "uint256[][] calldata values"
    "uint256[][] calldata selected = values[1:]; return selected.length;" dynamicSlice
    [diagnostic "2148" "Index range access is not supported for arrays with dynamically encoded base types."],
  rejection "mapping_memory" "" "mapping(uint256 => uint256) memory value; return 0;"
    (eligibleAt registry fuel (.memory 0) (.mapping (.uint 31) (.uint 31)))
    [diagnostic "4182" "Uninitialized mapping. Mappings cannot be created dynamically, you have to assign them from a state variable.",
     diagnostic "4061" "Type mapping(uint256 => uint256) is only valid in storage because it contains a (nested) mapping."],
  rejection "array_to_string_cast" ""
    "uint8[] memory values = new uint8[](2); string memory value = string(values); return bytes(value).length;"
    arrayStringCast [diagnostic "9640" "Explicit type conversion not allowed from \"uint8[] memory\" to \"string memory\"."],
  rejection "string_to_fixed_bytes_cast" ""
    "string memory value = \"abc\"; return uint32(bytes4(value));"
    stringFixedCast [diagnostic "9640" "Explicit type conversion not allowed from \"string memory\" to \"bytes4\"."]]

private def sourceDeclarations : String :=
  "uint16 left; uint16 right; uint24[] numbers; mapping(uint256 => uint24[]) buckets;\n" ++
  "struct Box { uint16 value; mapping(uint256 => uint256) saved; } Box box; Box[] boxes;\n" ++
  "bytes payload; struct Pair { uint16 a; uint16 b; } Pair pair; string text; uint24[11] fixedNumbers;\n" ++
  "struct Node { uint256 n; Node[] children; }\n" ++
  "function recursiveCalldataHelper(Node calldata value) internal pure returns(uint256) { return value.children.length; }\n" ++
  "function copyMemoryHelper(uint24[] calldata values) external pure returns(uint256) { uint24[] memory copied = values; copied[0] = 99; return uint256(values[0]) * 256 + copied[0]; }\n" ++
  "function copyStorageHelper(uint24[] calldata values) external returns(uint256) { numbers = values; return uint256(numbers[0]) * 256 + numbers[1]; }\n" ++
  "function sliceHelper(bytes calldata values) external pure returns(uint256) { bytes calldata selected = values[1:3]; return selected.length * 65536 + uint256(uint8(selected[0])) * 256 + uint8(selected[1]); }\n" ++
  "function castSliceHelper(bytes calldata values) external pure returns(uint256) { bytes calldata selected = values[1:3]; string calldata alias_ = string(selected); bytes calldata roundtrip = bytes(alias_); return roundtrip.length * 65536 + uint256(uint8(roundtrip[0])) * 256 + uint8(roundtrip[1]); }\n" ++
  "function castSlicePrefixHelper(bytes calldata values) external pure returns(uint256) { return uint32(bytes4(values[1:3])); }\n" ++
  "function sliceBoundsHelper(bytes calldata values) external pure returns(uint256) { bytes calldata selected = values[1:5]; return selected.length; }\n" ++
  "function indexBoundsHelper(bytes calldata values) external pure returns(uint256) { return uint8(values[4]); }\n"

def json : Json := Json.mkObj [
  ("solidityVersion", toJson Target.solidityVersion),
  ("referenceCompilerVersion", toJson Target.referenceCompilerVersion),
  ("evmVersion", toJson Target.evmVersion),
  ("sourceModelPairing", toJson "manualSourcePairing"),
  ("calldataAdmission", toJson "manuallyPairedAdmittedViews;decoderCorrespondenceNotProved"),
  ("declarations", toJson sourceDeclarations),
  ("cases", toJson (cases.map caseJson)), ("rejections", toJson rejections),
  ("modelChecks", toJson modelChecks)]

end Solidity.Conformance.Aggregates

def main : IO Unit := IO.println Solidity.Conformance.Aggregates.json.compress
