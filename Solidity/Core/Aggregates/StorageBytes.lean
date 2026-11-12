/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Access

/-! The physical bytes/string representation. Bulk assignment, push and pop
retain their distinct store orders, including when a concrete hashed data slot
aliases its header. No hash-injectivity or fresh-storage premise is imposed.
Source push/pop permission is the caller's bytes-only typing obligation. -/
namespace Solidity.Aggregates.StorageBytes
open Core Static
open Contract.Interaction (Word World wordBytes bytesWord readBytesPadded)

def maximumCopyLength : Nat := 2^64 - 1
def pushLimit : Nat := 2^64

def slotCount (length : Nat) : Nat :=
  if length < 32 then 0 else (length + 31) / 32

def dataSlot (reference : Reference) (index : Nat) : Word :=
  (Access.dataArea reference).address + BitVec.ofNat 256 index

/-- The payload contains the 31 high-order header bytes. The final byte is
reserved for the even length marker. Padding policy is supplied by the encoder. -/
def shortHeader (payload : BitVec 248) (length : Fin 32) : Word :=
  BitVec.ofNat 256 (payload.toNat * 256 + 2 * length.val)

def longHeader (length : Nat) : Word := BitVec.ofNat 256 (2 * length + 1)

def leadingWord (word : Word) (length : Nat) : Word :=
  (word >>> (8 * (32 - length))) <<< (8 * (32 - length))

def shortFromWord (word : Word) (length : Fin 32) : Word :=
  shortHeader (((leadingWord word length.val) >>> 8).setWidth 248) length

def packet (bytes : List UInt8) (index : Nat) : Word :=
  bytesWord (readBytesPadded bytes (index * 32) 32)

def encodeHeader (bytes : List UInt8) : Word :=
  if short : bytes.length < 32 then
    shortHeader (((packet bytes 0) >>> 8).setWidth 248) ⟨bytes.length, short⟩
  else longHeader bytes.length

theorem shortHeader_toNat (payload : BitVec 248) (length : Fin 32) :
    (shortHeader payload length).toNat = payload.toNat * 256 + 2 * length.val := by
  have payloadBound := payload.isLt
  have lengthBound := length.isLt
  simp only [shortHeader, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  omega

theorem shortHeader_length (payload : BitVec 248) (length : Fin 32) :
    Access.byteLength (shortHeader payload length) = .ok length.val := by
  have lengthBound := length.isLt
  simp only [Access.byteLength, shortHeader_toNat]
  have even : (payload.toNat * 256 + 2 * length.val) % 2 = 0 := by omega
  have low : (payload.toNat * 256 + 2 * length.val) % 256 = 2 * length.val := by omega
  rw [if_pos even, low]
  have div : 2 * length.val / 2 = length.val := by omega
  rw [div, if_pos lengthBound]

theorem longHeader_toNat (length : Nat) (bounded : length < 2^255) :
    (longHeader length).toNat = 2 * length + 1 := by
  simp only [longHeader, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  omega

theorem longHeader_length (length : Nat) (long : 32 ≤ length) (bounded : length < 2^255) :
    Access.byteLength (longHeader length) = .ok length := by
  simp only [Access.byteLength, longHeader_toNat length bounded]
  have odd : (2 * length + 1) % 2 ≠ 0 := by omega
  rw [if_neg odd]
  have div : (2 * length + 1) / 2 = length := by omega
  rw [div, if_pos long]

theorem encodeHeader_length (bytes : List UInt8) (bounded : bytes.length < 2^255) :
    Access.byteLength (encodeHeader bytes) = .ok bytes.length := by
  unfold encodeHeader
  split
  next => exact shortHeader_length _ _
  next long => exact longHeader_length _ (by omega) bounded

def loadHeader (heap : Heap) (reference : Reference) : Result (Word × Nat) := do
  Access.validate heap ⟨.bytes .storage false, reference⟩
  if reference.viewLength.isSome then throw (.invalidContext "storage bytes cannot have a slice length")
  let header ← Slot.read heap reference.region reference.address
  let length ← Access.byteLength header
  return (header, length)

/-- Reserve before constructing the result list. Byte indexing shares the
header decoder, concrete data-area hash and high-order byte representation with
Access.index; bulk reading does not recheck an unchanged header for each byte. -/
def read (heap : Heap) (budget : Nat) (reference : Reference) : Result (List UInt8 × Nat) := do
  let (header, length) ← loadHeader heap reference
  let remaining ← reserve budget (length + 1)
  if length < 32 then return ((wordBytes header).take length, remaining)
  let bytes ← (List.range length).mapM fun index => do
    let word ← Slot.read heap reference.region (dataSlot reference (index / 32))
    return (wordBytes word)[index % 32]!
  return (bytes, remaining)

abbrev Writes := List (Word × Word)

/-- Ordered writes, including all concrete collisions. Every component is
published only through the successful Result; errors expose no partial heap. -/
def applyWrites (heap : Heap) (region : Region) : Writes → Result Heap
  | [] => .ok heap
  | (slot, value) :: rest => do
      applyWrites (← Slot.write heap region slot value) region rest

structure WritePlan where
  writes : Writes
  remaining : Nat
  deriving DecidableEq, Repr

/-- The copy helper's bound is 2^64−1. Native push has a different bound and
therefore is modeled separately below. Clearing obsolete long slots precedes
new payload writes; the header is written last. Partial final packets are zero
padded, so shrinking also clears the removed suffix within the retained word. -/
def planWrite (heap : Heap) (budget : Nat) (reference : Reference) (bytes : List UInt8) :
    Result WritePlan :=
  if maximumCopyLength < bytes.length then .error (.panic 0x41) else do
    let (_, oldLength) ← loadHeader heap reference
    let oldSlots := slotCount oldLength
    let newSlots := slotCount bytes.length
    let clearCount := oldSlots - newSlots
    let remaining ← reserve budget (bytes.length + newSlots + clearCount + 1)
    let clear := (List.range clearCount).map fun index =>
      (dataSlot reference (newSlots + index), (0 : Word))
    let payload := (List.range newSlots).map fun index => (dataSlot reference index, packet bytes index)
    return ⟨clear ++ payload ++ [(reference.address, encodeHeader bytes)], remaining⟩

def write (heap : Heap) (budget : Nat) (reference : Reference) (bytes : List UInt8) :
    Result (Heap × Nat) := do
  let plan ← planWrite heap budget reference bytes
  return (← applyWrites heap reference.region plan.writes, plan.remaining)

def setByte (heap : Heap) (reference : Reference) (slot : Word) (offset : Nat)
    (value : UInt8) : Result Heap := do
  let before ← Slot.read heap reference.region slot
  Slot.write heap reference.region slot
    (Packed.insert 8 offset before (BitVec.ofNat 8 value.toNat))

/-- Constant-work push, preserving dirty unused bits just as the pinned helper
does. In the long case, the header update happens before the data-word read. -/
def push (heap : Heap) (budget : Nat) (reference : Reference) (value : UInt8) :
    Result (Heap × Nat) := do
  let (header, length) ← loadHeader heap reference
  if pushLimit ≤ length then throw (.panic 0x41)
  let remaining ← reserve budget 4
  if length < 32 then
    if length = 31 then
      let data := Packed.insert 8 0 header (BitVec.ofNat 8 value.toNat)
      let after ← Slot.write heap reference.region (dataSlot reference 0) data
      return (← Slot.write after reference.region reference.address (longHeader 32), remaining)
    else
      let data := Packed.insert 8 (8 * (31-length)) (header + 2) (BitVec.ofNat 8 value.toNat)
      return (← Slot.write heap reference.region reference.address data, remaining)
  else
    let after ← Slot.write heap reference.region reference.address (header + 2)
    return (← setByte after reference (dataSlot reference (length / 32))
      (8 * (31-length%32)) value, remaining)

/-- Native no-argument extension does not write a zero byte. A short header
retains the newly exposed byte and masks the still-unused suffix. At 31→32,
the old marker is cleared before copying the packet, followed by the long
header. Long arrays only change their length header. -/
def extensionWrites (reference : Reference) (header : Word) (length : Nat) : Writes :=
  if short : length < 31 then
    [(reference.address, shortFromWord header ⟨length+1, by omega⟩)]
  else if length = 31 then
    [(dataSlot reference 0, header &&& ~~~(BitVec.ofNat 256 255)),
     (reference.address, longHeader 32)]
  else [(reference.address, longHeader (length+1))]

def extend (heap : Heap) (budget : Nat) (reference : Reference) : Result (Heap × Nat) := do
  let (header, length) ← loadHeader heap reference
  if pushLimit ≤ length then throw (.panic 0x41)
  let remaining ← reserve budget 4
  return (← applyWrites heap reference.region (extensionWrites reference header length), remaining)

/-- Empty pop is Panic(0x31). A 32-to-31 transition reads the old long packet,
writes the short header, then clears its former data word, in that order. -/
def pop (heap : Heap) (budget : Nat) (reference : Reference) : Result (Heap × Nat) := do
  let (header, length) ← loadHeader heap reference
  if length = 0 then throw (.panic 0x31)
  let remaining ← reserve budget 4
  if length = 32 then
    let data ← Slot.read heap reference.region (dataSlot reference 0)
    let after ← Slot.write heap reference.region reference.address (shortFromWord data 31)
    return (← Slot.write after reference.region (dataSlot reference 0) 0, remaining)
  else if short : length < 32 then
    let newLength : Fin 32 := ⟨length - 1, by omega⟩
    return (← Slot.write heap reference.region reference.address (shortFromWord header newLength), remaining)
  else
    let newLength := length - 1
    let after ← setByte heap reference (dataSlot reference (newLength / 32))
      (8 * (31-newLength%32)) 0
    return (← Slot.write after reference.region reference.address (header - 2), remaining)

def erase (heap : Heap) (budget : Nat) (reference : Reference) : Result (Heap × Nat) :=
  write heap budget reference []

/-- Source-reference bookkeeping wraps the physical primitives without
changing their concrete storage order or packet/frame theorems. -/
def writeChecked (heap : Heap) (budget : Nat) (reference : Reference) (bytes : List UInt8) :
    Result (Heap × Nat) := do
  let (_, oldLength) ← loadHeader heap reference
  let (after, remaining) ← write heap budget reference bytes
  return (after.journalResize reference.region reference.address oldLength bytes.length true, remaining)

def pushChecked (heap : Heap) (budget : Nat) (reference : Reference) (value : UInt8) :
    Result (Heap × Nat) := do
  let (_, oldLength) ← loadHeader heap reference
  let (after, remaining) ← push heap budget reference value
  return (after.journalResize reference.region reference.address oldLength (oldLength+1) true, remaining)

/-- No-argument push returns the newly indexed physical byte after applying
the native writes and updating reference lifetimes. Its read is not assumed to
be zero: the ordinary unused-cell invariant is a separate source invariant. -/
def pushZeroChecked (heap : Heap) (budget : Nat) (reference : Reference) :
    Result (Place × Heap × Nat) := do
  let (_, oldLength) ← loadHeader heap reference
  let (after, remaining) ← extend heap budget reference
  let after := after.journalResize reference.region reference.address oldLength (oldLength+1) true
  let place ← Access.byteIndex after reference oldLength
  return (place, after, remaining)

def popChecked (heap : Heap) (budget : Nat) (reference : Reference) : Result (Heap × Nat) := do
  let (_, oldLength) ← loadHeader heap reference
  let (after, remaining) ← pop heap budget reference
  return (after.journalResize reference.region reference.address oldLength (oldLength-1) true, remaining)

private theorem bind_ok (value : α) (next : α → Except ε β) :
    (Except.ok value >>= next) = next value := rfl

private theorem bind_error (error : ε) (next : α → Except ε β) :
    (Except.error error >>= next) = .error error := rfl

theorem read_short (loaded : loadHeader heap reference = .ok (header, length))
    (short : length < 32) (enough : length + 1 ≤ budget) :
    read heap budget reference =
      .ok ((wordBytes header).take length, budget - (length + 1)) := by
  simp only [read, loaded, bind_ok, reserve_sufficient _ _ enough, short, ↓reduceIte]
  rfl

theorem read_exhausted (loaded : loadHeader heap reference = .ok (header, length))
    (small : budget < length + 1) : read heap budget reference = .error .exhausted := by
  simp only [read, loaded, bind_ok, reserve_exhausted _ _ small, bind_error]

variable {owner : BitVec 160}

/-- A byte read is the exact physical packet byte. This fixes the read meaning
without any logical separation or zero-initialization premise on storage. -/
theorem read_long (loaded : loadHeader heap reference = .ok (header, length))
    (region : reference.region = .storage owner) (long : 32 ≤ length)
    (enough : length + 1 ≤ budget) :
    read heap budget reference = .ok
      ((List.range length).map fun index =>
        (wordBytes (heap.execution.world.storage (owner.setWidth 256)
          (dataSlot reference (index / 32))))[index % 32]!, budget - (length + 1)) := by
  simp only [read, loaded, bind_ok, reserve_sufficient _ _ enough,
    if_neg (Nat.not_lt.mpr long), Slot.read, region]
  simp [List.mapM_pure]
  rfl

/-- Last matching physical write wins. This specification retains collisions
among payloads, obsolete tails and headers rather than assuming them away. -/
def finalValue (writes : Writes) (slot value : Word) : Word :=
  writes.foldl (fun previous change => if change.1 = slot then change.2 else previous) value

theorem applyWrites_value
    (finished : applyWrites heap (.storage owner) writes = .ok after) :
    after.execution.world.storage (owner.setWidth 256) slot =
      finalValue writes slot (heap.execution.world.storage (owner.setWidth 256) slot) := by
  induction writes generalizing heap with
  | nil => cases finished; rfl
  | cons change rest ih =>
      rcases change with ⟨key, value⟩
      unfold applyWrites at finished
      cases written : Slot.write heap (.storage owner) key value with
      | error failure => rw [written, bind_error] at finished; cases finished
      | ok next =>
          rw [written, bind_ok] at finished
          unfold Slot.write at written
          split at written
          next => cases written
          next =>
            cases written
            have observed := ih finished
            have firstStore : (heap.execution.world.store (owner.setWidth 256) key value).storage
                (owner.setWidth 256) slot =
                if key = slot then value else heap.execution.world.storage (owner.setWidth 256) slot := by
              by_cases equal : key = slot
              · subst key; simp [World.store]
              · simp [World.store, equal, Ne.symm equal]
            change after.execution.world.storage (owner.setWidth 256) slot =
              finalValue rest slot ((heap.execution.world.store (owner.setWidth 256) key value).storage
                (owner.setWidth 256) slot) at observed
            rw [firstStore] at observed
            exact observed

theorem finalValue_untouched (separate : ∀ change ∈ writes, change.1 ≠ slot) :
    finalValue writes slot before = before := by
  induction writes generalizing before with
  | nil => rfl
  | cons change rest ih =>
      have head := separate change (by simp)
      have tail : ∀ pair ∈ rest, pair.1 ≠ slot := by
        intro pair member; exact separate pair (by simp [member])
      simpa [finalValue, head] using ih tail (before := before)

/-- An actual physical address not touched by the write plan is framed. -/
theorem applyWrites_frame
    (finished : applyWrites heap (.storage owner) writes = .ok after)
    (separate : ∀ change ∈ writes, change.1 ≠ slot) :
    after.execution.world.storage (owner.setWidth 256) slot =
      heap.execution.world.storage (owner.setWidth 256) slot := by
  rw [applyWrites_value finished, finalValue_untouched separate]

/-- Every account outside the physical storage owner is framed for all keys. -/
theorem applyWrites_other_account
    (finished : applyWrites heap (.storage owner) writes = .ok after)
    (separate : account ≠ owner.setWidth 256) :
    after.execution.world.storage account slot = heap.execution.world.storage account slot := by
  induction writes generalizing heap with
  | nil => cases finished; rfl
  | cons change rest ih =>
      rcases change with ⟨key, value⟩
      unfold applyWrites at finished
      cases written : Slot.write heap (.storage owner) key value with
      | error failure => rw [written, bind_error] at finished; cases finished
      | ok next =>
          rw [written, bind_ok] at finished
          unfold Slot.write at written
          split at written
          next => cases written
          next =>
            cases written
            have observed := ih finished
            change after.execution.world.storage account slot =
              (heap.execution.world.store (owner.setWidth 256) key value).storage account slot at observed
            simpa only [World.store, separate, decide_false, Bool.false_and, Bool.false_eq_true,
              ↓reduceIte] using observed

/-- Payload and clearing packets have their exact intended values when no
later physical write aliases that slot. The premise includes any final header
write and refers to concrete Word keys, never source names or assumed hashes. -/
theorem applyWrites_packet
    (finished : applyWrites heap (.storage owner) (before ++ (slot, value) :: later) = .ok after)
    (separate : ∀ change ∈ later, change.1 ≠ slot) :
    after.execution.world.storage (owner.setWidth 256) slot = value := by
  rw [applyWrites_value finished]
  simp only [finalValue, List.foldl_append, List.foldl_cons, ↓reduceIte]
  exact finalValue_untouched separate

/-- A nonempty plan in a static invocation fails at its first attempted SSTORE. -/
theorem applyWrites_static (readOnly : heap.execution.context.readOnly = true) :
    applyWrites heap region ((slot, value) :: rest) = .error .exceptional := by
  simp [applyWrites, Slot.write, readOnly]
  rfl

theorem extensionWrites_nonempty (reference : Reference) (header : Word) (length : Nat) :
    extensionWrites reference header length ≠ [] := by
  unfold extensionWrites
  split <;> (try split) <;> simp

theorem extend_resource (loaded : loadHeader heap reference = .ok (header, length))
    (large : pushLimit ≤ length) : extend heap budget reference = .error (.panic 0x41) := by
  simp only [extend, loaded, bind_ok, large, ↓reduceIte]
  rfl

theorem extend_exhausted (loaded : loadHeader heap reference = .ok (header, length))
    (smallLength : length < pushLimit) (smallBudget : budget < 4) :
    extend heap budget reference = .error .exhausted := by
  simp only [extend, loaded, bind_ok, Nat.not_le.mpr smallLength, ↓reduceIte,
    reserve_exhausted _ _ smallBudget]
  rfl

theorem extend_value (loaded : loadHeader heap reference = .ok (header, length))
    (smallLength : length < pushLimit) (enough : 4 ≤ budget)
    (extended : extend heap budget reference = .ok (after, remaining))
    (region : reference.region = .storage owner) :
    after.execution.world.storage (owner.setWidth 256) slot =
      finalValue (extensionWrites reference header length) slot
        (heap.execution.world.storage (owner.setWidth 256) slot) := by
  simp only [extend, loaded, bind_ok, Nat.not_le.mpr smallLength, ↓reduceIte,
    reserve_sufficient _ _ enough] at extended
  cases written : applyWrites heap reference.region (extensionWrites reference header length) with
  | error failure =>
      simp only [written] at extended
      change Except.error failure = Except.ok (after, remaining) at extended
      cases extended
  | ok result =>
      simp only [written] at extended
      change Except.ok (result, budget-4) = Except.ok (after, remaining) at extended
      cases extended
      apply applyWrites_value
      simpa [region] using written

theorem extend_frame (loaded : loadHeader heap reference = .ok (header, length))
    (smallLength : length < pushLimit) (enough : 4 ≤ budget)
    (extended : extend heap budget reference = .ok (after, remaining))
    (region : reference.region = .storage owner)
    (separate : ∀ change ∈ extensionWrites reference header length, change.1 ≠ slot) :
    after.execution.world.storage (owner.setWidth 256) slot =
      heap.execution.world.storage (owner.setWidth 256) slot := by
  rw [extend_value loaded smallLength enough extended region]
  exact finalValue_untouched separate

/-- The length header is the final write, including the short-to-long case.
Its length law therefore needs no separation hypothesis for the data hash. -/
theorem extend_length (loaded : loadHeader heap reference = .ok (header, length))
    (smallLength : length < pushLimit) (enough : 4 ≤ budget)
    (extended : extend heap budget reference = .ok (after, remaining))
    (region : reference.region = .storage owner) :
    Access.byteLength (after.execution.world.storage (owner.setWidth 256) reference.address) =
      .ok (length+1) := by
  rw [extend_value loaded smallLength enough extended region]
  unfold extensionWrites
  split
  next short =>
    simp only [finalValue, List.foldl_cons, List.foldl_nil, ↓reduceIte, shortFromWord]
    exact shortHeader_length _ _
  next notShort =>
    split
    next boundary =>
      subst length
      simp only [finalValue, List.foldl_cons, List.foldl_nil, ↓reduceIte]
      exact longHeader_length 32 (by decide) (by decide)
    next notBoundary =>
      simp only [finalValue, List.foldl_cons, List.foldl_nil, ↓reduceIte]
      apply longHeader_length
      · omega
      · simp only [pushLimit] at smallLength
        omega

theorem planWrite_complete (planned : planWrite heap budget reference bytes = .ok plan) :
    bytes.length ≤ maximumCopyLength ∧
      ∃ initial, plan.writes = initial ++ [(reference.address, encodeHeader bytes)] := by
  unfold planWrite at planned
  split at planned
  next => cases planned
  next bounded =>
    cases loaded : loadHeader heap reference with
    | error failure => rw [loaded, bind_error] at planned; cases planned
    | ok old =>
        rcases old with ⟨header, oldLength⟩
        rw [loaded, bind_ok] at planned
        dsimp only at planned
        cases reserved : reserve budget
            (bytes.length + slotCount bytes.length + (slotCount oldLength - slotCount bytes.length) + 1) with
        | error failure => rw [reserved, bind_error] at planned; cases planned
        | ok remaining =>
            rw [reserved, bind_ok] at planned
            cases planned
            exact ⟨by omega, ⟨_, rfl⟩⟩

/-- Public bulk assignment consumes the exact ordered physical plan. -/
theorem write_value (planned : planWrite heap budget reference bytes = .ok plan)
    (region : reference.region = .storage owner)
    (finished : write heap budget reference bytes = .ok (after, remaining)) :
    after.execution.world.storage (owner.setWidth 256) slot =
      finalValue plan.writes slot (heap.execution.world.storage (owner.setWidth 256) slot) := by
  unfold write at finished
  rw [planned, bind_ok] at finished
  cases run : applyWrites heap reference.region plan.writes with
  | error failure => rw [run, bind_error] at finished; cases finished
  | ok next =>
      rw [run, bind_ok] at finished
      cases finished
      rw [region] at run
      exact applyWrites_value run

theorem write_frame (planned : planWrite heap budget reference bytes = .ok plan)
    (region : reference.region = .storage owner)
    (finished : write heap budget reference bytes = .ok (after, remaining))
    (separate : ∀ change ∈ plan.writes, change.1 ≠ slot) :
    after.execution.world.storage (owner.setWidth 256) slot =
      heap.execution.world.storage (owner.setWidth 256) slot := by
  rw [write_value planned region finished, finalValue_untouched separate]

theorem write_static (planned : planWrite heap budget reference bytes = .ok plan)
    (readOnly : heap.execution.context.readOnly = true) :
    write heap budget reference bytes = .error .exceptional := by
  obtain ⟨initial, shape⟩ := (planWrite_complete planned).2
  unfold write
  rw [planned, bind_ok, shape]
  cases initial with
  | nil => simp only [List.nil_append, applyWrites_static readOnly, bind_error]
  | cons first rest =>
      rcases first with ⟨slot, value⟩
      simp only [List.cons_append, applyWrites_static readOnly, bind_error]

/-- The header is the final physical write even if a hashed payload aliases
it. Payload round trips need the explicit separation premise in packet laws. -/
theorem write_header (planned : planWrite heap budget reference bytes = .ok plan)
    (region : reference.region = .storage owner)
    (finished : write heap budget reference bytes = .ok (after, remaining)) :
    Access.byteLength (after.execution.world.storage (owner.setWidth 256) reference.address) =
      .ok bytes.length := by
  have complete := planWrite_complete planned
  obtain ⟨initial, shape⟩ := complete.2
  rw [write_value planned region finished, shape]
  simp only [finalValue, List.foldl_append, List.foldl_cons, ↓reduceIte, List.foldl_nil]
  exact encodeHeader_length bytes (by
    have bound : maximumCopyLength < 2^255 := by decide
    omega)

theorem write_oversized (large : maximumCopyLength < bytes.length) :
    write heap budget reference bytes = .error (.panic 0x41) := by
  simp [write, planWrite, large]
  rfl

theorem push_resource (loaded : loadHeader heap reference = .ok (header, length))
    (large : pushLimit ≤ length) : push heap budget reference value = .error (.panic 0x41) := by
  simp only [push, loaded, bind_ok, large, ↓reduceIte]
  rfl

theorem pop_empty (loaded : loadHeader heap reference = .ok (header, 0)) :
    pop heap budget reference = .error (.panic 0x31) := by
  simp only [pop, loaded, bind_ok, ↓reduceIte]
  rfl

end Solidity.Aggregates.StorageBytes
