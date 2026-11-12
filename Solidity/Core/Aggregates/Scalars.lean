/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Types
import Solidity.Core.StaticABI

namespace Solidity.Aggregates
open Static Core
open Contract.Interaction (Word Memory bytesWord wordBytes)

namespace Packed

def mask (bits offset : Nat) : Word := (BitVec.allOnes bits).setWidth 256 <<< offset

def extract (bits offset : Nat) (word : Word) : BitVec bits :=
  (word >>> offset).setWidth bits

def insert (bits offset : Nat) (word : Word) (value : BitVec bits) : Word :=
  (word &&& ~~~mask bits offset) ||| (value.setWidth 256 <<< offset)

/-- Insertion preserves every bit outside the physical field, even in dirty
words. This premise is physical separation, not distinct source field names. -/
theorem insert_frame (bits offset : Nat) (word : Word) (value : BitVec bits) :
    insert bits offset word value &&& ~~~mask bits offset = word &&& ~~~mask bits offset := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [insert, mask, BitVec.getElem_and, BitVec.getElem_or,
    BitVec.getElem_not, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_allOnes]
  by_cases before : i < offset
  · simp [before]
  · by_cases inside : i - offset < bits
    · simp [before, inside]
    · have outside : value.getLsbD (i-offset) = false := by
        apply BitVec.getLsbD_of_ge
        omega
      simp [before, inside, outside]

/-- Every field value survives a write/read pair when the field fits the word. -/
theorem extract_insert (bits offset : Nat) (word : Word) (value : BitVec bits)
    (fits : offset + bits ≤ 256) : extract bits offset (insert bits offset word value) = value := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have position : offset + i < 256 := by omega
  have shifted : offset + i - offset = i := by omega
  simp [extract, insert, mask, position, shifted, hi, show ¬offset+i < offset by omega]

theorem extract_insert_disjoint (readBits readOffset writeBits writeOffset : Nat)
    (word : Word) (value : BitVec writeBits) (fits : readOffset + readBits ≤ 256)
    (separate : readOffset + readBits ≤ writeOffset ∨ writeOffset + writeBits ≤ readOffset) :
    extract readBits readOffset (insert writeBits writeOffset word value) =
      extract readBits readOffset word := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have position : readOffset+i < 256 := by omega
  by_cases before : readOffset+i < writeOffset
  · simp [extract, insert, mask, position, before]
  · have outside : writeBits ≤ readOffset+i-writeOffset := by omega
    have clear : value.getLsbD (readOffset+i-writeOffset) = false :=
      BitVec.getLsbD_of_ge value _ outside
    simp [extract, insert, mask, position, before, clear, show ¬readOffset+i-writeOffset < writeBits by omega]

end Packed

def encodeCoreStorage : (type : Core.Ty) → type.Value → Word
  | .uint _, value | .sint _, value | .fixedBytes _, value => value.setWidth 256
  | .bool, value => if value then 1 else 0
  | .address, value => value.setWidth 256

def decodeCoreStorage : (type : Core.Ty) → Word → Result type.Value
  | .uint width, word | .sint width, word | .fixedBytes width, word => .ok (word.setWidth width.bits)
  | .bool, word =>
      if word = 0 then .ok false else if word = 1 then .ok true
      else .error (.invalidContext "noncanonical storage boolean")
  | .address, word => .ok (word.setWidth 160)

/-- Internal handles are abstract identities, with zero reserved for the
uninitialized value. Binding this concrete n+1 representation to an artifact
is a client-supplied representation premise; no declaration-identity injection is
assumed. A handle outside its physical width rejects instead of truncating. -/
def encodeInternal (bits : Nat) (value : Option Nat) : Result Word :=
  match value with
  | none => .ok 0
  | some handle => if handle + 1 < 2^bits && bits ≤ 256 then .ok (BitVec.ofNat 256 (handle+1))
      else .error (.invalidContext "internal function handle does not fit representation")

def decodeInternal (word : Word) : Option Nat :=
  if word = 0 then none else some (word.toNat - 1)

def encodeExternal (value : BitVec 160 × BitVec 32) : Word :=
  (value.1.setWidth 256 <<< 32) ||| value.2.setWidth 256

def decodeExternal (word : Word) : BitVec 160 × BitVec 32 :=
  ((word >>> 32).setWidth 160, word.setWidth 32)

def encodeStorage : (type : SType) → type.Value → Result Word
  | .uint _, value | .sint _, value | .fixedBytes _, value => .ok (value.setWidth 256)
  | .bool, value => .ok (if value then 1 else 0)
  | .address _, value | .contract _ _ _, value => .ok (value.setWidth 256)
  | .enumType _ _, value => .ok (BitVec.ofNat 256 value.val)
  | .valueType _ base, value => .ok (encodeCoreStorage base.core value)
  | .function .internal _ _ _, value => encodeInternal 64 value
  | .function .external _ _ _, value => .ok (encodeExternal value)
  | .fixedPoint _ _ _, _ => .error (.unsupported "fixed-point storage encoding")
  | _, _ => .error .rejected

/-- The storage read helper masks enum/bool bytes without validating them.
Such dirty words have no value in the current Fin/Bool source families. Keep
them inconclusive rather than inventing a panic or a normalized source value.
Memory cleanup and calldata validation below have their distinct behavior. -/
def decodeStorage : (type : SType) → Word → Result type.Value
  | .uint width, word | .sint width, word | .fixedBytes width, word => .ok (word.setWidth width.bits)
  | .bool, word => decodeCoreStorage .bool word
  | .address _, word | .contract _ _ _, word => .ok (word.setWidth 160)
  | .enumType _ members, word =>
      if bound : word.toNat < members.val+1 then .ok ⟨word.toNat, bound⟩
      else .error (.invalidContext "out-of-range storage enum")
  | .valueType _ base, word => decodeCoreStorage base.core word
  | .function .internal _ _ _, word => .ok (decodeInternal word)
  | .function .external _ _ _, word => .ok (decodeExternal word)
  | .fixedPoint _ _ _, _ => .error (.unsupported "fixed-point storage decoding")
  | _, _ => .error .rejected

def encodeCoreMemory (type : Core.Ty) : type.Value → Word := type.abiWord

def decodeCoreMemory : (type : Core.Ty) → Word → Result type.Value
  | .uint width, word | .sint width, word => .ok (word.setWidth width.bits)
  | .fixedBytes width, word => .ok ((word >>> (256-width.bits)).setWidth width.bits)
  | .bool, word => .ok (decide (word ≠ 0))
  | .address, word => .ok (word.setWidth 160)

def encodeMemory : (type : SType) → type.Value → Result Word
  | .uint _, value => .ok (value.setWidth 256)
  | .sint _, value => .ok (BitVec.ofInt 256 value.toInt)
  | .fixedBytes width, value => .ok (value.setWidth 256 <<< (256-width.bits))
  | .bool, value => .ok (if value then 1 else 0)
  | .address _, value | .contract _ _ _, value => .ok (value.setWidth 256)
  | .enumType _ _, value => .ok (BitVec.ofNat 256 value.val)
  | .valueType _ base, value => .ok (encodeCoreMemory base.core value)
  | .function .internal _ _ _, value => encodeInternal 256 value
  | .function .external _ _ _, value => .ok (encodeExternal value <<< 64)
  | .fixedPoint _ _ _, _ => .error (.unsupported "fixed-point memory encoding")
  | _, _ => .error .rejected

def decodeMemory : (type : SType) → Word → Result type.Value
  | .uint width, word | .sint width, word => .ok (word.setWidth width.bits)
  | .fixedBytes width, word => .ok ((word >>> (256-width.bits)).setWidth width.bits)
  | .bool, word => .ok (decide (word ≠ 0))
  | .address _, word | .contract _ _ _, word => .ok (word.setWidth 160)
  | .enumType _ members, word =>
      if bound : word.toNat < members.val+1 then .ok ⟨word.toNat, bound⟩
      else .error (.panic 0x21)
  | .valueType _ base, word => decodeCoreMemory base.core word
  | .function .internal _ _ _, word => .ok (decodeInternal word)
  | .function .external _ _ _, word => .ok (decodeExternal (word >>> 64))
  | .fixedPoint _ _ _, _ => .error (.unsupported "fixed-point memory decoding")
  | _, _ => .error .rejected

/-- Calldata words must have their canonical full-word encoding. Internal
function values have no external ABI representation. Enum validation is an
empty revert at this boundary, not memory cleanup's enum panic. -/
def decodeCalldata (type : SType) (word : Word) : Result type.Value :=
  if (match type with | .function .internal _ _ _ => true | _ => false) then .error .rejected
  else match decodeMemory type word with
    | .error (.panic _) => .error (.revert [])
    | .error failure => .error failure
    | .ok value => match encodeMemory type value with
      | .error failure => .error failure
      | .ok canonical => if canonical = word then .ok value else .error (.revert [])

def scalarCellBytes (reference : Reference) : Nat := if reference.byteCell then 1 else 32

private def byteType (type : SType) : Bool := type == .fixedBytes 0

/-- Low-level scalar access. The public place resolver checks source location
eligibility, guard liveness and paths before calling this operation. This
function still checks physical field fit and memory/calldata extents itself. -/
def readScalar (heap : Heap) (place : Place) : Result place.type.Value := do
  let some bytes := storageBytes place.type | throw .rejected
  match place.reference.region with
  | .storage _ | .transient _ =>
      if place.reference.byte.val + bytes > 32 then throw .rejected
      let word ← Slot.read heap place.reference.region place.reference.address
      decodeStorage place.type ((Packed.extract (8*bytes) (8*place.reference.byte.val) word).setWidth 256)
  | .memory _ | .calldata _ =>
      if place.reference.byte != 0 then throw .rejected
      if place.reference.byteCell && !byteType place.type then throw .rejected
      let _ ← checkExtent heap place.reference (scalarCellBytes place.reference)
      let packet := match place.reference.region with
        | .memory _ => heap.execution.memory.read place.reference.address.toNat (scalarCellBytes place.reference)
        | _ => (heap.execution.context.calldata.drop place.reference.address.toNat).take (scalarCellBytes place.reference)
      let word := bytesWord packet
      if place.reference.byteCell then decodeStorage place.type word
      else match place.reference.region with
        | .memory _ => decodeMemory place.type word
        | _ => decodeCalldata place.type word

def writeScalar (heap : Heap) (place : Place) (value : place.type.Value) : Result Heap := do
  let some bytes := storageBytes place.type | throw .rejected
  match place.reference.region with
  | .storage _ | .transient _ =>
      if place.reference.byte.val + bytes > 32 then throw .rejected
      let word ← Slot.read heap place.reference.region place.reference.address
      let encoded ← encodeStorage place.type value
      Slot.write heap place.reference.region place.reference.address
        (Packed.insert (8*bytes) (8*place.reference.byte.val) word (encoded.setWidth (8*bytes)))
  | .calldata _ => throw .rejected
  | .memory _ =>
      if place.reference.byte != 0 then throw .rejected
      if place.reference.byteCell && !byteType place.type then throw .rejected
      let _ ← checkExtent heap place.reference (scalarCellBytes place.reference)
      let encoded ← if place.reference.byteCell then encodeStorage place.type value else encodeMemory place.type value
      let packet := if place.reference.byteCell then [encoded.toNat.toUInt8] else wordBytes encoded
      return { heap with execution := { heap.execution with
        memory := heap.execution.memory.write place.reference.address.toNat packet } }

theorem calldata_immutable (heap : Heap) (type : SType) (invocation : Nat)
    (address : Word) (value : type.Value) :
    writeScalar heap ⟨type, {region := .calldata invocation, address}⟩ value = .error .rejected := by
  unfold writeScalar
  cases storageBytes type <;> rfl

/-- Writing a captured memory cell changes only memory. Allocation ownership,
the frontier and the shared world survive scalar initialization/assignment. -/
theorem writeScalar_memory_frame (heap after : Heap) (place : Place)
    (value : place.type.Value) (invocation : Nat)
    (memory : place.reference.region = .memory invocation)
    (written : writeScalar heap place value = .ok after) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation ∧
    after.nextMemory = heap.nextMemory ∧ after.allocations = heap.allocations := by
  unfold writeScalar at written
  cases sized : storageBytes place.type with
  | none => simp [sized] at written
  | some bytes =>
      simp only [sized, memory, bind, Except.bind, pure, Except.pure] at written
      split at written
      · cases written
      · split at written
        · cases written
        · cases extent : checkExtent heap place.reference (scalarCellBytes place.reference) with
          | error failure => simp [extent] at written
          | ok token =>
              simp only [extent] at written
              cases byteFlag : place.reference.byteCell <;>
                simp only [byteFlag, Bool.false_eq_true, ↓reduceIte] at written
              all_goals
                split at written
                · cases written
                · cases written; exact ⟨rfl, rfl, rfl, rfl⟩

theorem storage_boolean_dirty (word : Word) (nonzero : word ≠ 0) (nonone : word ≠ 1) :
    decodeStorage .bool word = .error (.invalidContext "noncanonical storage boolean") := by
  change (if word = 0 then _ else if word = 1 then _ else _) = _
  rw [if_neg nonzero, if_neg nonone]

theorem memory_enum_invalid (identity : Nat) (members : Fin 256) (word : Word)
    (invalid : members.val+1 ≤ word.toNat) :
    decodeMemory (.enumType identity members) word = .error (.panic 0x21) := by
  simp [decodeMemory, Nat.not_lt.mpr invalid]

theorem uint_storage_roundtrip (width : Width) (value : BitVec width.bits) :
    (encodeStorage (.uint width) value >>= decodeStorage (.uint width)) = .ok value := by
  simp [encodeStorage, bind, Except.bind, decodeStorage, BitVec.setWidth_setWidth_of_le value width.bits_le]

theorem sint_storage_roundtrip (width : Width) (value : BitVec width.bits) :
    (encodeStorage (.sint width) value >>= decodeStorage (.sint width)) = .ok value := by
  simp [encodeStorage, bind, Except.bind, decodeStorage, BitVec.setWidth_setWidth_of_le value width.bits_le]

theorem bytes_storage_roundtrip (width : Width) (value : BitVec width.bits) :
    (encodeStorage (.fixedBytes width) value >>= decodeStorage (.fixedBytes width)) = .ok value := by
  simp [encodeStorage, bind, Except.bind, decodeStorage, BitVec.setWidth_setWidth_of_le value width.bits_le]

theorem bool_storage_roundtrip (value : Bool) :
    (encodeStorage .bool value >>= decodeStorage .bool) = .ok value := by
  cases value <;> rfl

theorem address_storage_roundtrip (payable : Bool) (value : BitVec 160) :
    (encodeStorage (.address payable) value >>= decodeStorage (.address payable)) = .ok value := by
  simp [encodeStorage, bind, Except.bind, decodeStorage,
    BitVec.setWidth_setWidth_of_le value (by decide : 160 ≤ 256)]

theorem enum_storage_roundtrip (identity : Nat) (members : Fin 256)
    (value : Fin (members.val+1)) :
    (encodeStorage (.enumType identity members) value >>= decodeStorage (.enumType identity members)) = .ok value := by
  have fits : value.val < 2^256 := by have := value.isLt; have := members.isLt; omega
  simp [encodeStorage, bind, Except.bind, decodeStorage, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt fits, value.isLt]

theorem core_storage_roundtrip (type : Core.Ty) (value : type.Value) :
    decodeCoreStorage type (encodeCoreStorage type value) = .ok value := by
  cases type with
  | uint width | sint width | fixedBytes width =>
      simp [encodeCoreStorage, decodeCoreStorage,
        BitVec.setWidth_setWidth_of_le value width.bits_le]
  | bool => cases value <;> rfl
  | address => simp [encodeCoreStorage, decodeCoreStorage,
      BitVec.setWidth_setWidth_of_le value (by decide : 160 ≤ 256)]

theorem valueType_storage_roundtrip (identity : Nat) (base : Elementary)
    (value : base.core.Value) :
    (encodeStorage (.valueType identity base) value >>= decodeStorage (.valueType identity base)) = .ok value := by
  simp only [encodeStorage, bind, Except.bind, decodeStorage]
  exact core_storage_roundtrip base.core value

theorem uint_memory_roundtrip (width : Width) (value : BitVec width.bits) :
    (encodeMemory (.uint width) value >>= decodeMemory (.uint width)) = .ok value := by
  simp [encodeMemory, bind, Except.bind, decodeMemory,
    BitVec.setWidth_setWidth_of_le value width.bits_le]

theorem sint_memory_roundtrip (width : Width) (value : BitVec width.bits) :
    (encodeMemory (.sint width) value >>= decodeMemory (.sint width)) = .ok value := by
  simp only [encodeMemory, bind, Except.bind, decodeMemory]
  congr 1
  change (value.signExtend 256).setWidth width.bits = value
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have fits : i < 256 := Nat.lt_of_lt_of_le hi width.bits_le
  simp [BitVec.getElem_signExtend, hi, fits]

theorem bytes_memory_roundtrip (width : Width) (value : BitVec width.bits) :
    (encodeMemory (.fixedBytes width) value >>= decodeMemory (.fixedBytes width)) = .ok value := by
  simp only [encodeMemory, bind, Except.bind, decodeMemory]
  congr 1
  have fits : 256-width.bits + width.bits ≤ 256 := by have := width.bits_le; omega
  simpa [Packed.extract, Packed.insert] using
    Packed.extract_insert width.bits (256-width.bits) 0 value fits

theorem bool_memory_roundtrip (value : Bool) :
    (encodeMemory .bool value >>= decodeMemory .bool) = .ok value := by
  cases value <;> rfl

theorem core_memory_roundtrip (type : Core.Ty) (value : type.Value) :
    decodeCoreMemory type (encodeCoreMemory type value) = .ok value := by
  cases type with
  | uint width => exact uint_memory_roundtrip width value
  | sint width => exact sint_memory_roundtrip width value
  | fixedBytes width => exact bytes_memory_roundtrip width value
  | bool => cases value <;> rfl
  | address =>
      simp [encodeCoreMemory, Core.Ty.abiWord, decodeCoreMemory,
        BitVec.setWidth_setWidth_of_le value (by decide : 160 ≤ 256)]

theorem valueType_memory_roundtrip (identity : Nat) (base : Elementary)
    (value : base.core.Value) :
    (encodeMemory (.valueType identity base) value >>= decodeMemory (.valueType identity base)) = .ok value := by
  simp only [encodeMemory, bind, Except.bind, decodeMemory]
  exact core_memory_roundtrip base.core value

theorem address_memory_roundtrip (payable : Bool) (value : BitVec 160) :
    (encodeMemory (.address payable) value >>= decodeMemory (.address payable)) = .ok value := by
  simp [encodeMemory, bind, Except.bind, decodeMemory,
    BitVec.setWidth_setWidth_of_le value (by decide : 160 ≤ 256)]

theorem enum_memory_roundtrip (identity : Nat) (members : Fin 256)
    (value : Fin (members.val+1)) :
    (encodeMemory (.enumType identity members) value >>= decodeMemory (.enumType identity members)) = .ok value := by
  have fits : value.val < 2^256 := by have := value.isLt; have := members.isLt; omega
  simp [encodeMemory, bind, Except.bind, decodeMemory, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt fits, value.isLt]

theorem decodeExternal_encode (value : BitVec 160 × BitVec 32) :
    decodeExternal (encodeExternal value) = value := by
  rcases value with ⟨address, selector⟩
  apply Prod.ext
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    simp [decodeExternal, encodeExternal, hi,
      show 32+i < 256 by omega, show ¬32+i < 32 by omega]
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    simp [decodeExternal, encodeExternal]

theorem external_storage_roundtrip (mutability : Mutability) (parameters returns : Types)
    (value : BitVec 160 × BitVec 32) :
    (encodeStorage (.function .external mutability parameters returns) value >>=
      decodeStorage (.function .external mutability parameters returns)) = .ok value := by
  simp [encodeStorage, bind, Except.bind, decodeStorage, decodeExternal_encode]

theorem external_memory_roundtrip (mutability : Mutability) (parameters returns : Types)
    (value : BitVec 160 × BitVec 32) :
    (encodeMemory (.function .external mutability parameters returns) value >>=
      decodeMemory (.function .external mutability parameters returns)) = .ok value := by
  simp only [encodeMemory, bind, Except.bind, decodeMemory]
  congr 1
  rcases value with ⟨address, selector⟩
  apply Prod.ext
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    simp [decodeExternal, encodeExternal,
      show 96+i < 256 by omega, show ¬96+i < 64 by omega,
      show 96+i-64 = 32+i by omega, show ¬32+i < 32 by omega]
    exact BitVec.getLsbD_eq_getElem hi
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    simp [decodeExternal, encodeExternal, hi,
      show 64+i < 256 by omega, show ¬64+i < 64 by omega]

theorem internal_roundtrip (bits : Nat) (handle : Nat)
    (fits : handle + 1 < 2^bits) (width : bits ≤ 256) :
    (encodeInternal bits (some handle)).map decodeInternal = .ok (some handle) := by
  have machineFits : handle+1 < 2^256 :=
    Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) width)
  have decoded : (BitVec.ofNat 256 (handle+1)).toNat = handle+1 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt machineFits]
  have nonzero : BitVec.ofNat 256 (handle+1) ≠ 0 := by
    intro zero
    have h := congrArg BitVec.toNat zero
    simp [decoded] at h
  simp [encodeInternal, fits, width, Except.map, decodeInternal, decoded]
  exact nonzero

/-- Successful calldata admission entails the exact padded representation;
no ignored upper bits can enter a typed scalar value from the byte boundary. -/
theorem calldata_canonical (type : SType) (word : Word) (value : type.Value)
    (admitted : decodeCalldata type word = .ok value) : encodeMemory type value = .ok word := by
  unfold decodeCalldata at admitted
  split at admitted
  · cases admitted
  · cases decoded : decodeMemory type word with
    | error failure =>
        cases failure <;> simp [decoded] at admitted
    | ok found =>
        simp only [decoded] at admitted
        cases encoded : encodeMemory type found with
        | error failure => simp [encoded] at admitted
        | ok packet =>
            simp only [encoded] at admitted
            by_cases same : packet = word
            · have equality : found = value := by simpa [same] using admitted
              subst value
              simpa [same] using encoded
            · simp [same] at admitted

end Solidity.Aggregates
