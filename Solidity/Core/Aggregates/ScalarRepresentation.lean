/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Scalars

/-! Physical scalar representation laws for the existing byte, memory and
packed-slot operations. Raw surrounding words and bytes remain arbitrary. -/
namespace Contract.Interaction

private theorem byte_toNat (number : Nat) :
    ((number % 256).toUInt8).toNat = number % 256 := by
  change (number % 256) % 2^8 = number % 256
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))

private theorem fold_wordDigits (count number : Nat) :
    ((List.range count).map (fun index =>
      (number / 256^(count-1-index) % 256).toUInt8)).foldl
        (fun accumulator byte => accumulator * 256 + byte.toNat) 0 = number % 256^count := by
  induction count generalizing number with
  | zero => simp [Nat.mod_one]
  | succ count ih =>
      have initialDigits : (List.range count).map (fun index =>
          (number / 256^(count-index) % 256).toUInt8) =
          (List.range count).map (fun index =>
            ((number/256) / 256^(count-1-index) % 256).toUInt8) := by
        apply List.map_congr_left
        intro index inside
        have bound : index < count := List.mem_range.mp inside
        have exponent : count-index = count-1-index+1 := by omega
        simp only [exponent, Nat.pow_succ', Nat.div_div_eq_div_mul]
      simp only [List.range_succ, List.map_append, List.map_singleton,
        List.foldl_append, Nat.add_sub_cancel]
      rw [initialDigits, ih]
      simp only [List.foldl_cons, List.foldl_nil, Nat.sub_self, Nat.pow_zero,
        Nat.div_one, byte_toNat]
      rw [Nat.pow_succ', Nat.mod_mul]
      omega

/-- The existing big-endian byte packet retains all 256 bits of its word. -/
theorem bytesWord_wordBytes (word : Word) : bytesWord (wordBytes word) = word := by
  unfold bytesWord wordBytes
  rw [fold_wordDigits 32 word.toNat]
  have power : 256^32 = 2^256 := by decide
  rw [power, Nat.mod_eq_of_lt word.isLt]
  exact BitVec.ofNat_toNat 256 word

theorem Memory.bytesWord_read_word_write (memory : Memory) (offset : Nat) (word : Word) :
    bytesWord ((memory.write offset (wordBytes word)).read offset 32) = word := by
  rw [← wordBytes_length word, Memory.read_write, bytesWord_wordBytes]

end Contract.Interaction

namespace Solidity.Aggregates
open Static Core
open Contract.Interaction (Word Memory bytesWord wordBytes)

private theorem truncate_extend (word : Word) (bits : Nat)
    (fits : word.toNat < 2^bits) : (word.setWidth bits).setWidth 256 = word := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt word.isLt]

/-- Every successful encoder fits its actual storage cell. In particular the
abstract internal-function handle encoder must succeed before this law applies. -/
theorem encodeStorage_width (type : SType) (value : type.Value) (word : Word) (bytes : Nat)
    (sized : storageBytes type = some bytes) (encoded : encodeStorage type value = .ok word) :
    (word.setWidth (8*bytes)).setWidth 256 = word := by
  cases type with
  | uint width | sint width | fixedBytes width =>
      simp only [storageBytes, Option.some.injEq] at sized
      cases encoded
      subst bytes
      have bits : 8 * (width.val+1) = width.bits := rfl
      rw [bits, BitVec.setWidth_setWidth_of_le value width.bits_le]
      simp
  | bool =>
      cases encoded
      simp only [storageBytes, Option.some.injEq] at sized
      subst bytes
      cases value <;> rfl
  | address payable | contract identity payable bases =>
      cases encoded
      simp only [storageBytes, Option.some.injEq] at sized
      subst bytes
      rw [BitVec.setWidth_setWidth_of_le value (by decide : 160 ≤ 256)]
      simp
  | enumType identity members =>
      cases encoded
      simp only [storageBytes, Option.some.injEq] at sized
      subst bytes
      apply truncate_extend
      have bound := value.isLt
      have count := members.isLt
      simp only [BitVec.toNat_ofNat]
      omega
  | valueType identity base =>
      cases base with
      | payableAddress =>
          cases encoded
          simp only [storageBytes, Option.some.injEq] at sized
          subst bytes
          simp [encodeCoreStorage, Elementary.core,
            BitVec.setWidth_setWidth_of_le value (by decide : 160 ≤ 256)]
      | scalar type =>
          cases type with
          | uint width | sint width | fixedBytes width =>
              cases encoded
              simp only [storageBytes, Option.some.injEq] at sized
              subst bytes
              change ((value.setWidth 256).setWidth width.bits).setWidth 256 = value.setWidth 256
              simp [BitVec.setWidth_setWidth_of_le value width.bits_le]
          | bool => cases encoded; cases sized; cases value <;> rfl
          | address =>
              cases encoded
              cases sized
              simp [encodeCoreStorage, Elementary.core,
                BitVec.setWidth_setWidth_of_le value (by decide : 160 ≤ 256)]
  | function visibility mutability parameters returns =>
      cases visibility with
      | external =>
          cases encoded
          cases sized
          rcases value with ⟨address, selector⟩
          apply BitVec.eq_of_getElem_eq
          intro index inside
          by_cases compact : index < 192
          · simp [encodeExternal, compact]
          · have addressOutside : address.getLsbD (index-32) = false :=
                BitVec.getLsbD_of_ge address _ (by omega)
            have selectorOutside : selector.getLsbD index = false :=
                BitVec.getLsbD_of_ge selector _ (by omega)
            simp [encodeExternal, compact, addressOutside, selectorOutside,
              show ¬index < 32 by omega]
      | internal =>
          cases sized
          change encodeInternal 64 value = .ok word at encoded
          cases value with
          | none => cases encoded; rfl
          | some handle =>
              by_cases bounded : handle+1 < 2^64
              · simp [encodeInternal, bounded] at encoded
                subst word
                apply truncate_extend
                simp only [BitVec.toNat_ofNat]
                exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) bounded
              · simp [encodeInternal, bounded] at encoded
  | _ => simp [encodeStorage] at encoded

private theorem decodeInternal_encode_success (bits : Nat) (value : Option Nat) (word : Word)
    (encoded : encodeInternal bits value = .ok word) : decodeInternal word = value := by
  cases value with
  | none => cases encoded; rfl
  | some handle =>
      by_cases fits : handle+1 < 2^bits
      · by_cases width : bits ≤ 256
        · have known := internal_roundtrip bits handle fits width
          simpa [encoded, Except.map] using known
        · simp [encodeInternal, width] at encoded
      · simp [encodeInternal, fits] at encoded

theorem decodeStorage_encode_success (type : SType) (value : type.Value) (word : Word)
    (encoded : encodeStorage type value = .ok word) : decodeStorage type word = .ok value := by
  cases type with
  | uint width => simpa [encoded, bind, Except.bind] using uint_storage_roundtrip width value
  | sint width => simpa [encoded, bind, Except.bind] using sint_storage_roundtrip width value
  | fixedBytes width => simpa [encoded, bind, Except.bind] using bytes_storage_roundtrip width value
  | bool => simpa [encoded, bind, Except.bind] using bool_storage_roundtrip value
  | address payable => simpa [encoded, bind, Except.bind] using address_storage_roundtrip payable value
  | contract identity payable bases =>
      cases encoded
      simp [decodeStorage, BitVec.setWidth_setWidth_of_le value (by decide : 160 ≤ 256)]
  | enumType identity members =>
      simpa [encoded, bind, Except.bind] using enum_storage_roundtrip identity members value
  | valueType identity base =>
      simpa [encoded, bind, Except.bind] using valueType_storage_roundtrip identity base value
  | function visibility mutability parameters returns =>
      cases visibility with
      | external =>
          simpa [encoded, bind, Except.bind] using external_storage_roundtrip mutability parameters returns value
      | internal =>
          exact congrArg Except.ok (decodeInternal_encode_success 64 value word encoded)
  | _ => simp [encodeStorage] at encoded

theorem decodeMemory_encode_success (type : SType) (value : type.Value) (word : Word)
    (encoded : encodeMemory type value = .ok word) : decodeMemory type word = .ok value := by
  cases type with
  | uint width => simpa [encoded, bind, Except.bind] using uint_memory_roundtrip width value
  | sint width => simpa [encoded, bind, Except.bind] using sint_memory_roundtrip width value
  | fixedBytes width => simpa [encoded, bind, Except.bind] using bytes_memory_roundtrip width value
  | bool => simpa [encoded, bind, Except.bind] using bool_memory_roundtrip value
  | address payable => simpa [encoded, bind, Except.bind] using address_memory_roundtrip payable value
  | contract identity payable bases =>
      cases encoded
      simp [decodeMemory, BitVec.setWidth_setWidth_of_le value (by decide : 160 ≤ 256)]
  | enumType identity members =>
      simpa [encoded, bind, Except.bind] using enum_memory_roundtrip identity members value
  | valueType identity base =>
      simpa [encoded, bind, Except.bind] using valueType_memory_roundtrip identity base value
  | function visibility mutability parameters returns =>
      cases visibility with
      | external =>
          simpa [encoded, bind, Except.bind] using external_memory_roundtrip mutability parameters returns value
      | internal =>
          exact congrArg Except.ok (decodeInternal_encode_success 256 value word encoded)
  | _ => simp [encodeMemory] at encoded

theorem encodeMemory_storageBytes (type : SType) (value : type.Value) (word : Word)
    (encoded : encodeMemory type value = .ok word) : ∃ bytes, storageBytes type = some bytes := by
  cases type <;> first
    | (solve | simp [storageBytes])
    | (simp [encodeMemory] at encoded)
  case valueType identity base =>
    cases base with
    | payableAddress => exact ⟨20, rfl⟩
    | scalar type => cases type <;> exact ⟨_, rfl⟩
  case function visibility mutability parameters returns => cases visibility <;> exact ⟨_, rfl⟩

/-- Padded scalar cells implement a physical write/read round trip in any
previous memory. Successful write supplies the extent and representability
checks, including the explicit bound on internal-function handles. -/
theorem readScalar_writeScalar_memory (heap after : Heap) (place : Place)
    (value : place.type.Value) (invocation : Nat)
    (memory : place.reference.region = .memory invocation)
    (padded : place.reference.byteCell = false)
    (written : writeScalar heap place value = .ok after) :
    readScalar after place = .ok value := by
  unfold writeScalar at written
  cases sized : storageBytes place.type with
  | none => simp [sized] at written
  | some bytes =>
      simp only [sized, memory, padded, scalarCellBytes, Bool.false_eq_true,
        Bool.false_and, ↓reduceIte, bind, Except.bind, pure, Except.pure] at written
      split at written
      · cases written
      · rename_i byteZero
        have aligned : place.reference.byte = 0 := by simpa using byteZero
        cases extent : checkExtent heap place.reference 32 with
        | error failure => simp [extent] at written
        | ok token =>
            cases token
            simp only [extent] at written
            cases encoded : encodeMemory place.type value with
            | error failure => simp [encoded] at written
            | ok word =>
                simp only [encoded] at written
                cases written
                have extentAfter : checkExtent
                    {heap with execution := {heap.execution with memory :=
                      (heap.execution.memory.write place.reference.address.toNat (wordBytes word))}}
                    place.reference 32 = .ok () := extent
                simp only [readScalar, sized, memory, aligned, padded, scalarCellBytes,
                  Bool.false_eq_true, Bool.false_and, bne_self_eq_false,
                  ↓reduceIte, extentAfter, bind, Except.bind, pure, Except.pure]
                rw [Memory.bytesWord_read_word_write]
                exact decodeMemory_encode_success place.type value word encoded

/-- A successful scalar read remains valid when its physical packet is
unchanged and its extent remains admitted. This includes dirty-word failures
only through the separate equality theorem below, not a cleanup assumption. -/
theorem readScalar_memory_preserved (heap after : Heap) (place : Place)
    (value : place.type.Value) (invocation : Nat)
    (memory : place.reference.region = .memory invocation)
    (extent : checkExtent after place.reference (scalarCellBytes place.reference) = .ok ())
    (packet : after.execution.memory.read place.reference.address.toNat (scalarCellBytes place.reference) =
      heap.execution.memory.read place.reference.address.toNat (scalarCellBytes place.reference))
    (read : readScalar heap place = .ok value) : readScalar after place = .ok value := by
  cases originalExtent : checkExtent heap place.reference (scalarCellBytes place.reference) with
  | error failure =>
      cases sized : storageBytes place.type <;>
        simp [readScalar, sized, memory, originalExtent, bind, Except.bind, pure, Except.pure] at read
      split at read
      · split at read <;> cases read
      · cases read
  | ok token =>
      cases token
      simpa [readScalar, memory, originalExtent, extent, packet] using read

theorem readScalar_memory_congr (heap after : Heap) (place : Place) (invocation : Nat)
    (memory : place.reference.region = .memory invocation)
    (extent : checkExtent after place.reference (scalarCellBytes place.reference) =
      checkExtent heap place.reference (scalarCellBytes place.reference))
    (packet : after.execution.memory.read place.reference.address.toNat (scalarCellBytes place.reference) =
      heap.execution.memory.read place.reference.address.toNat (scalarCellBytes place.reference)) :
    readScalar after place = readScalar heap place := by
  simp [readScalar, memory, extent, packet]

private theorem memory_byte_decode (value : BitVec 8) :
    decodeStorage (.fixedBytes 0) (bytesWord [((value.setWidth 256).toNat).toUInt8]) = .ok value := by
  simp only [bytesWord, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add, decodeStorage]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt value.isLt, Width.bits]

theorem readScalar_writeScalar_byte (heap after : Heap) (reference : Reference)
    (value : BitVec 8) (invocation : Nat)
    (memory : reference.region = .memory invocation) (byteCell : reference.byteCell = true)
    (written : writeScalar heap ⟨.fixedBytes 0, reference⟩ value = .ok after) :
    readScalar after ⟨.fixedBytes 0, reference⟩ = .ok value := by
  let packet : List UInt8 := [((value.setWidth 256).toNat).toUInt8]
  let updated : Heap := {heap with execution := {heap.execution with memory :=
    (heap.execution.memory.write reference.address.toNat packet)}}
  unfold writeScalar at written
  simp only [storageBytes, memory, byteCell, scalarCellBytes, ↓reduceIte,
    bind, Except.bind, pure, Except.pure] at written
  split at written
  · cases written
  · rename_i byteZero
    have aligned : reference.byte = 0 := by simpa using byteZero
    split at written
    · cases written
    · rename_i byteAllowed
      cases extent : checkExtent heap reference 1 with
      | error failure => simp [extent] at written
      | ok token =>
          cases token
          simp only [extent, encodeStorage] at written
          cases written
          simp only [readScalar, storageBytes, memory, aligned, byteCell, scalarCellBytes,
            bne_self_eq_false, Bool.false_eq_true, byteAllowed, ↓reduceIte,
            bind, Except.bind, pure, Except.pure]
          simp only [checkExtent, memory, Heap.allocated] at extent ⊢
          split at extent
          · cases extent
          · rename_i owned
            split at extent
            · rename_i allocated
              simp only [owned, allocated, Bool.false_eq_true, ↓reduceIte]
              simpa [Memory.read, Memory.write] using memory_byte_decode value
            · cases extent

end Solidity.Aggregates
