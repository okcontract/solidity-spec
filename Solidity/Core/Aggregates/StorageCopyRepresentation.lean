/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy.Laws
import Solidity.Core.Aggregates.ScalarRepresentation
import Solidity.Core.Aggregates.StorageTrace

/-! Ordered physical storage effects and aggregate-copy representation.
Every separation condition concerns actual owner/slot/bit addresses. -/
namespace Solidity.Aggregates
open Static Core
open Contract.Interaction (Word World)

theorem Slot.read_write_same (heap after : Heap) (region : Region) (slot word : Word)
    (written : Slot.write heap region slot word = .ok after) :
    Slot.read after region slot = .ok word := by
  unfold Slot.write at written
  split at written
  · cases written
  · cases region <;> simp only at written
    case storage owner => cases written; simp [Slot.read, World.store]
    case transient owner => cases written; simp [Slot.read, World.tstore]
    case memory invocation => cases written
    case calldata invocation => cases written

/-- A successful packed storage write is a physical read-after-write law for
every supported scalar family, including bounded abstract function handles. -/
theorem readScalar_writeScalar_storage (heap after : Heap) (place : Place)
    (value : place.type.Value) (owner : BitVec 160)
    (storage : place.reference.region = .storage owner)
    (written : writeScalar heap place value = .ok after) :
    readScalar after place = .ok value := by
  unfold writeScalar at written
  cases sized : storageBytes place.type with
  | none => simp [sized] at written
  | some bytes =>
      simp only [sized, storage, bind, Except.bind, Slot.read, pure, Except.pure] at written
      split at written
      · cases written
      · rename_i fieldFits
        have fits : place.reference.byte.val + bytes ≤ 32 := by omega
        cases encoded : encodeStorage place.type value with
        | error failure => simp [encoded] at written
        | ok word =>
            simp only [encoded] at written
            have stored := Slot.read_write_same heap after (.storage owner)
              place.reference.address _ written
            simp only [readScalar, sized, storage, Nat.not_lt.mpr fits, ↓reduceIte,
              stored, bind, Except.bind, pure, Except.pure]
            rw [Packed.extract_insert (8*bytes) (8*place.reference.byte.val) _ _ (by omega),
              encodeStorage_width place.type value word bytes sized encoded]
            exact decodeStorage_encode_success place.type value word encoded

namespace Copy

variable {sourceBytes targetBytes : Nat}

/-- An ordered finite traversal records each step's own transcript. This is a
proof combinator; its relation is instantiated below by closed copy operations. -/
inductive CopyFold (relation : σ → α → List StorageEvent → σ → Prop) :
    σ → List α → List StorageEvent → σ → Prop where
  | nil (state : σ) : CopyFold relation state [] [] state
  | cons (head : relation before item first middle)
      (tail : CopyFold relation middle items rest after) :
      CopyFold relation before (item :: items) (first ++ rest) after

theorem CopyFold.iff_foldlM (function : σ → α → Result σ)
    (law : ∀ before item after, function before item = .ok after ↔ ∃ events, relation before item events after)
    (items : List α) (before after : σ) :
    items.foldlM function before = .ok after ↔ ∃ events, CopyFold relation before items events after := by
  induction items generalizing before with
  | nil =>
      constructor
      · intro same; cases same; exact ⟨[], .nil _⟩
      · rintro ⟨_, derivation⟩; cases derivation; rfl
  | cons item rest ih =>
      constructor
      · intro finished
        simp only [List.foldlM_cons] at finished
        cases first : function before item with
        | error failure => simp [first, Bind.bind, Except.bind] at finished
        | ok middle =>
            simp only [first, Bind.bind, Except.bind] at finished
            obtain ⟨initial, advanced⟩ := (law before item middle).mp first
            obtain ⟨tail, followed⟩ := (ih middle).mp finished
            exact ⟨initial ++ tail, .cons advanced followed⟩
      · rintro ⟨_, derivation⟩
        cases derivation with
        | cons advanced followed =>
            rw [List.foldlM_cons, (law _ _ _).mpr ⟨_, advanced⟩]
            exact (ih _).mpr ⟨_, followed⟩

theorem CopyFold.trace (project : σ → Heap)
    (law : ∀ before item events after, relation before item events after →
      StorageTrace (project before) events (project after))
    (derivation : CopyFold relation before items events after) :
    StorageTrace (project before) events (project after) := by
  induction derivation with
  | nil => exact .nil _
  | cons head _ ih => exact (law _ _ _ _ head).append ih

/-- The cursor may reuse a cached packet or fetch the next physical source
word. The latter load occurs before the pending destination store. -/
inductive CursorAdvance (region : Region) (bytes : Nat) :
    Cursor → List StorageEvent → Cursor → Prop where
  | load (cursor : Cursor) (word : Word)
      (advance : 16 < bytes ∨ cursor.item+1 = 32/bytes)
      (read : Slot.read cursor.heap region (cursor.slot+1) = .ok word) :
      CursorAdvance region bytes cursor [.load region (cursor.slot+1) word]
        {cursor with slot := cursor.slot+1, word, item := 0}
  | cached (cursor : Cursor) (reuse : ¬(16 < bytes ∨ cursor.item+1 = 32/bytes)) :
      CursorAdvance region bytes cursor [] {cursor with item := cursor.item+1}

theorem CursorAdvance.trace (derivation : CursorAdvance region bytes before events after) :
    StorageTrace before.heap events after.heap := by
  cases derivation with
  | load _ _ read => exact StorageTrace.read read
  | cached => exact .nil _

theorem advanceCursor_iff : advanceCursor region bytes before = .ok after ↔
    ∃ events, CursorAdvance region bytes before events after := by
  unfold advanceCursor
  by_cases advance : 16 < bytes ∨ before.item+1 = 32/bytes
  · have chosen : (decide (16 < bytes) || (before.item+1 == 32/bytes)) = true := by simpa using advance
    simp only [chosen, ↓reduceIte, Bind.bind, Except.bind, pure, Except.pure]
    change (Except.map (fun word => {before with slot := before.slot+1, word, item := 0})
      (Slot.read before.heap region (before.slot+1)) = .ok after) ↔
      ∃ events, CursorAdvance region bytes before events after
    constructor
    · intro finished
      cases read : Slot.read before.heap region (before.slot+1) with
      | error failure =>
          change Slot.read before.heap region (before.slot+1#256) = .error failure at read
          simp [read, Except.map] at finished
      | ok word =>
          simp only [read, Except.map] at finished
          cases finished
          exact ⟨_, .load before word advance read⟩
    · rintro ⟨_, derivation⟩
      cases derivation with
      | load word _ read => rw [read]; rfl
      | cached reuse => exact False.elim (reuse advance)
  · have chosen : (decide (16 < bytes) || (before.item+1 == 32/bytes)) = false := by simpa using advance
    simp only [chosen, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro same; cases same; exact ⟨[], .cached before advance⟩
    · rintro ⟨_, derivation⟩
      cases derivation with
      | load word moved _ => exact False.elim (advance moved)
      | cached => rfl

theorem scalarWord_value (encoded : scalarWord type source = .ok word) :
    ∃ value : type.Value, convertScalar type source = .ok ⟨type, value⟩ ∧
      encodeStorage type value = .ok word := by
  unfold scalarWord at encoded
  cases converted : convertScalar type source with
  | error failure => simp [converted, Bind.bind, Except.bind] at encoded
  | ok box =>
      have correct := convertScalar_type converted
      rcases box with ⟨actual, value⟩
      cases correct
      simp only [converted, Bind.bind, Except.bind, ↓reduceDIte] at encoded
      exact ⟨value, rfl, encoded⟩

/-- A converted item reads the cached source packet, prepares the target
encoding, inserts it into the pending word, then advances/prefetches the cursor.
The destination word is not stored until its enclosing word transcript commits. -/
inductive ScalarConsume (source target : SType) (region : Region) (sourceBytes targetBytes : Nat) :
    Cursor × Word → Nat → List StorageEvent → Cursor × Word → Prop where
  | step (cursor : Cursor) (previous : Word) (index : Nat) (value : source.Value) (encoded : Word)
      (next : Cursor) (events : List StorageEvent)
      (decoded : decodeStorage source
        ((Packed.extract (8*sourceBytes) (8*sourceBytes*cursor.item) cursor.word).setWidth 256) = .ok value)
      (prepared : scalarWord target ⟨source, value⟩ = .ok encoded)
      (advanced : CursorAdvance region sourceBytes cursor events next) :
      ScalarConsume source target region sourceBytes targetBytes (cursor, previous) index events
        (next, Packed.insert (8*targetBytes) (8*targetBytes*index) previous
          (encoded.setWidth (8*targetBytes)))

theorem ScalarConsume.trace
    (derivation : ScalarConsume source target region sourceBytes targetBytes before index events after) :
    StorageTrace before.1.heap events after.1.heap := by
  cases derivation with
  | step _ _ _ _ _ _ _ _ _ advanced => exact advanced.trace

theorem consumeScalar_iff : consumeScalar source target region sourceBytes targetBytes before index = .ok after ↔
    ∃ events, ScalarConsume source target region sourceBytes targetBytes before index events after := by
  rcases before with ⟨cursor, previous⟩
  unfold consumeScalar
  simp only [Bind.bind, Except.bind]
  constructor
  · intro finished
    cases decoded : decodeStorage source
      ((Packed.extract (8*sourceBytes) (8*sourceBytes*cursor.item) cursor.word).setWidth 256) with
    | error failure => simp [decoded] at finished
    | ok value =>
        simp only [decoded] at finished
        cases prepared : scalarWord target ⟨source, value⟩ with
        | error failure => simp [prepared] at finished
        | ok encoded =>
            simp only [prepared] at finished
            cases advanced : advanceCursor region sourceBytes cursor with
            | error failure => simp [advanced] at finished
            | ok next =>
                simp only [advanced, pure, Except.pure] at finished
                cases finished
                obtain ⟨events, moved⟩ := advanceCursor_iff.mp advanced
                exact ⟨events, .step cursor previous index value encoded next events decoded prepared moved⟩
  · rintro ⟨_, derivation⟩
    cases derivation with
    | step _ _ _ value encoded next events decoded prepared advanced =>
        have moved : advanceCursor region sourceBytes cursor = .ok next :=
          advanceCursor_iff.mpr ⟨_, advanced⟩
        simp only [decoded, prepared, pure, Except.pure]
        rw [moved]

/-- The item transcript establishes its represented target value from the
actual codec and physical insertion, rather than assuming a read-back result. -/
theorem ScalarConsume.representation
    (derivation : ScalarConsume source target region sourceBytes targetBytes before index events after)
    (sized : storageBytes target = some targetBytes)
    (fits : 8*targetBytes*index + 8*targetBytes ≤ 256) :
    ∃ value : source.Value, ∃ converted : target.Value,
      decodeStorage source ((Packed.extract (8*sourceBytes)
        (8*sourceBytes*before.1.item) before.1.word).setWidth 256) = .ok value ∧
      convertScalar target ⟨source, value⟩ = .ok ⟨target, converted⟩ ∧
      decodeStorage target ((Packed.extract (8*targetBytes) (8*targetBytes*index) after.2).setWidth 256) =
        .ok converted := by
  cases derivation with
  | step cursor previous index value encoded next events decoded prepared advanced =>
      obtain ⟨converted, conversion, encoding⟩ := scalarWord_value prepared
      refine ⟨value, converted, decoded, conversion, ?_⟩
      rw [Packed.extract_insert _ _ _ _ fits, encodeStorage_width target converted encoded targetBytes sized encoding]
      exact decodeStorage_encode_success target converted encoded encoding

inductive WordTransfer (source target : SType) (region : Region) (sourceBytes targetBytes items : Nat) :
    Cursor → List StorageEvent → Cursor × Word → Prop where
  | cached (before next : Cursor) (events : List StorageEvent)
      (same : sameScalarLayout source target = true)
      (advanced : CursorAdvance region 32 before events next) :
      WordTransfer source target region sourceBytes targetBytes items before events
        (next, (Packed.extract (8*items*targetBytes) 0 before.word).setWidth 256)
  | converted (before : Cursor) (events : List StorageEvent) (after : Cursor × Word)
      (different : sameScalarLayout source target = false)
      (copied : CopyFold (ScalarConsume source target region sourceBytes targetBytes)
        (before, 0) (List.range items) events after) :
      WordTransfer source target region sourceBytes targetBytes items before events after

theorem WordTransfer.trace
    (derivation : WordTransfer source target region sourceBytes targetBytes items before events after) :
    StorageTrace before.heap events after.1.heap := by
  cases derivation with
  | cached _ _ _ advanced => exact advanced.trace
  | converted _ _ _ copied =>
      exact copied.trace (fun state => state.1.heap) (fun _ _ _ _ item => item.trace)

theorem transferWord_iff : transferWord source target region sourceBytes targetBytes items before = .ok after ↔
    ∃ events, WordTransfer source target region sourceBytes targetBytes items before events after := by
  unfold transferWord
  cases same : sameScalarLayout source target with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro finished
        obtain ⟨events, copied⟩ := (CopyFold.iff_foldlM _ (fun _ _ _ => consumeScalar_iff) _ _ _).mp finished
        exact ⟨events, .converted before events after same copied⟩
      · rintro ⟨_, derivation⟩
        cases derivation with
        | cached _ _ other _ => simp [same] at other
        | converted _ _ _ copied =>
            exact (CopyFold.iff_foldlM _ (fun _ _ _ => consumeScalar_iff) _ _ _).mpr ⟨_, copied⟩
  | true =>
      simp only [↓reduceIte, Bind.bind, Except.bind, pure, Except.pure]
      constructor
      · intro finished
        cases advanced : advanceCursor region 32 before with
        | error failure => simp [advanced] at finished
        | ok next =>
            simp only [advanced] at finished
            cases finished
            obtain ⟨events, moved⟩ := advanceCursor_iff.mp advanced
            exact ⟨events, .cached before next events same moved⟩
      · rintro ⟨_, derivation⟩
        cases derivation with
        | cached _ _ _ advanced =>
            rw [advanceCursor_iff.mpr ⟨_, advanced⟩]
        | converted _ _ other _ => simp [same] at other

inductive WordStore (source target : SType) (sourceData targetData : Reference)
    (sourceBytes targetBytes count : Nat) : Cursor → Nat → List StorageEvent → Cursor → Prop where
  | step (before next : Cursor) (index : Nat) (word : Word) (events : List StorageEvent) (heap : Heap)
      (transferred : WordTransfer source target sourceData.region sourceBytes targetBytes
        (min (32/targetBytes) (count-index*(32/targetBytes))) before events (next, word))
      (written : Slot.write next.heap targetData.region
        (targetData.address+BitVec.ofNat 256 index) word = .ok heap) :
      WordStore source target sourceData targetData sourceBytes targetBytes count before index
        (events ++ [.store targetData.region (targetData.address+BitVec.ofNat 256 index) word])
        {next with heap}

theorem WordStore.trace
    (derivation : WordStore source target sourceData targetData sourceBytes targetBytes count before index events after) :
    StorageTrace before.heap events after.heap := by
  cases derivation with
  | step _ _ _ _ _ copied written => exact copied.trace.append (StorageTrace.write written)

theorem storeWord_iff : storeWord source target sourceData targetData sourceBytes targetBytes count before index = .ok after ↔
    ∃ events, WordStore source target sourceData targetData sourceBytes targetBytes count before index events after := by
  unfold storeWord
  simp only [Bind.bind, Except.bind]
  constructor
  · intro finished
    cases transferred : transferWord source target sourceData.region sourceBytes targetBytes
        (min (32/targetBytes) (count-index*(32/targetBytes))) before with
    | error failure => simp [transferred] at finished
    | ok result =>
        rcases result with ⟨next, word⟩
        simp only [transferred] at finished
        cases written : Slot.write next.heap targetData.region
            (targetData.address+BitVec.ofNat 256 index) word with
        | error failure => simp [written] at finished
        | ok heap =>
            simp only [written, pure, Except.pure] at finished
            cases finished
            obtain ⟨events, copied⟩ := transferWord_iff.mp transferred
            exact ⟨_, .step before next index word events heap copied written⟩
  · rintro ⟨_, derivation⟩
    cases derivation with
    | step _ _ _ _ _ copied written =>
        simp only [transferWord_iff.mpr ⟨_, copied⟩, written, pure, Except.pure]

/-- A complete scalar-array transcript begins with the source cache load and
then commits each destination word in increasing word index. Child transcripts
retain every prefetch before the corresponding commit. -/
inductive ScalarStream (source target : SType) (sourceData targetData : Reference)
    (sourceBytes targetBytes count budget : Nat) : Heap → List StorageEvent → Heap × Nat → Prop where
  | complete (before : Heap) (first : Word) (next : Cursor) (available : Nat) (events : List StorageEvent)
      (widths : 0 < sourceBytes ∧ sourceBytes ≤ 32 ∧ 0 < targetBytes ∧ targetBytes ≤ 32)
      (reserved : reserve budget (count+(count+32/targetBytes-1)/(32/targetBytes)+1) = .ok available)
      (read : Slot.read before sourceData.region sourceData.address = .ok first)
      (copied : CopyFold
        (WordStore source target sourceData targetData sourceBytes targetBytes count)
        ⟨before, sourceData.address, first, 0⟩
        (List.range ((count+32/targetBytes-1)/(32/targetBytes))) events next) :
      ScalarStream source target sourceData targetData sourceBytes targetBytes count budget before
        (.load sourceData.region sourceData.address first :: events) (next.heap, available)

theorem ScalarStream.trace
    (derivation : ScalarStream source target sourceData targetData sourceBytes targetBytes count budget before events after) :
    StorageTrace before events after.1 := by
  cases derivation with
  | complete _ _ _ _ _ _ read copied =>
      exact .load read (copied.trace Cursor.heap (fun _ _ _ _ word => word.trace))

theorem streamScalars_iff :
    streamScalars before budget sourceData targetData source target sourceBytes targetBytes count = .ok after ↔
    ∃ events, ScalarStream source target sourceData targetData sourceBytes targetBytes count budget before events after := by
  unfold streamScalars
  constructor
  · intro finished
    split at finished
    · cases finished
    · rename_i admitted
      have widths : 0 < sourceBytes ∧ sourceBytes ≤ 32 ∧ 0 < targetBytes ∧ targetBytes ≤ 32 := by omega
      simp only [Bind.bind, Except.bind, pure, Except.pure] at finished
      cases reserved : reserve budget (count+(count+32/targetBytes-1)/(32/targetBytes)+1) with
      | error failure => simp [reserved] at finished
      | ok available =>
          simp only [reserved] at finished
          cases read : Slot.read before sourceData.region sourceData.address with
          | error failure => simp [read] at finished
          | ok first =>
              simp only [read] at finished
              cases copied : (List.range ((count+32/targetBytes-1)/(32/targetBytes))).foldlM
                  (storeWord source target sourceData targetData sourceBytes targetBytes count)
                  ⟨before, sourceData.address, first, 0⟩ with
              | error failure => simp [copied] at finished
              | ok next =>
                  simp only [copied] at finished
                  cases finished
                  obtain ⟨events, traversal⟩ := (CopyFold.iff_foldlM _ (fun _ _ _ => storeWord_iff) _ _ _).mp copied
                  exact ⟨_, .complete before first next available events widths reserved read traversal⟩
  · rintro ⟨_, derivation⟩
    cases derivation with
    | complete _ _ _ _ widths reserved read copied =>
        have admitted : ¬(sourceBytes = 0 ∨ targetBytes = 0 ∨ 32 < sourceBytes ∨ 32 < targetBytes) := by omega
        simp only [if_neg admitted, Bind.bind, Except.bind, reserved, read,
          (CopyFold.iff_foldlM _ (fun _ _ _ => storeWord_iff) _ _ _).mpr ⟨_, copied⟩, pure, Except.pure]

inductive ByteSource where
  | storage (reference : Reference) (length : Nat)
  | immutable (registry : Registry) (fuel : Nat) (place : Place)

def ByteSource.reader : ByteSource → ByteReader
  | .storage reference length => storedByteWord reference length
  | .immutable registry fuel place => immutableByteWord registry fuel place

/-- Only the two concrete source readers used by the copy implementation occur
here. An immutable source's decoded bytes are recorded before packet formation. -/
inductive ChunkRead : ByteSource → Heap → Nat → Nat → List StorageEvent → Word → Prop where
  | storage (reference : Reference) (length : Nat) (heap : Heap) (start size : Nat) (word : Word)
      (read : Slot.read heap reference.region
        (if length < 32 then reference.address else StorageBytes.dataSlot reference (start/32)) = .ok word) :
      ChunkRead (.storage reference length) heap start size
        [.load reference.region (if length < 32 then reference.address else StorageBytes.dataSlot reference (start/32)) word]
        (StorageBytes.leadingWord word size)
  | immutable (registry : Registry) (fuel : Nat) (place : Place) (heap : Heap)
      (start size : Nat) (bytes : List UInt8)
      (read : Copy.sourceBytes registry fuel heap place start size = .ok bytes) :
      ChunkRead (.immutable registry fuel place) heap start size [] (StorageBytes.packet bytes 0)

theorem ChunkRead.trace (read : ChunkRead source heap start size events word) : StorageTrace heap events heap := by
  cases read with
  | storage _ _ _ _ _ _ read => exact StorageTrace.read read
  | immutable => exact .nil _

theorem chunkRead_iff : source.reader heap start size = .ok word ↔
    ∃ events, ChunkRead source heap start size events word := by
  cases source with
  | storage reference length =>
      simp only [ByteSource.reader, storedByteWord, Bind.bind, Except.bind, pure, Except.pure]
      constructor
      · intro finished
        cases read : Slot.read heap reference.region
            (if length < 32 then reference.address else StorageBytes.dataSlot reference (start/32)) with
        | error failure => simp [read] at finished
        | ok packet =>
            simp only [read] at finished
            cases finished
            exact ⟨_, .storage reference length heap start size packet read⟩
      · rintro ⟨_, read⟩
        cases read with
        | storage _ _ _ _ _ _ read => rw [read]
  | immutable registry fuel place =>
      simp only [ByteSource.reader, immutableByteWord, Bind.bind, Except.bind, pure, Except.pure]
      constructor
      · intro finished
        cases read : Copy.sourceBytes registry fuel heap place start size with
        | error failure => simp [read] at finished
        | ok bytes =>
            simp only [read] at finished
            cases finished
            exact ⟨[], .immutable registry fuel place heap start size bytes read⟩
      · rintro ⟨_, read⟩
        cases read with
        | immutable _ _ _ _ _ _ _ read => rw [read]

inductive ByteWordStore (source : ByteSource) (target : Reference) (length : Nat) :
    Heap → Nat → List StorageEvent → Heap → Prop where
  | step (before after : Heap) (index : Nat) (word : Word) (events : List StorageEvent)
      (read : ChunkRead source before (index*32) (min 32 (length-index*32)) events word)
      (written : Slot.write before target.region (StorageBytes.dataSlot target index) word = .ok after) :
      ByteWordStore source target length before index
        (events ++ [.store target.region (StorageBytes.dataSlot target index) word]) after

theorem ByteWordStore.trace (written : ByteWordStore source target length before index events after) :
    StorageTrace before events after := by
  cases written with
  | step _ _ _ _ read stored => exact read.trace.append (StorageTrace.write stored)

def writeByteWord (source : ByteSource) (target : Reference) (length : Nat) (heap : Heap) (index : Nat) : Result Heap := do
  let word ← source.reader heap (index*32) (min 32 (length-index*32))
  Slot.write heap target.region (StorageBytes.dataSlot target index) word

theorem writeByteWord_iff : writeByteWord source target length before index = .ok after ↔
    ∃ events, ByteWordStore source target length before index events after := by
  unfold writeByteWord
  simp only [Bind.bind, Except.bind]
  constructor
  · intro finished
    cases read : source.reader before (index*32) (min 32 (length-index*32)) with
    | error failure => simp [read] at finished
    | ok word =>
        simp only [read] at finished
        obtain ⟨events, decoded⟩ := chunkRead_iff.mp read
        exact ⟨_, .step before after index word events decoded finished⟩
  · rintro ⟨_, derivation⟩
    cases derivation with
    | step _ _ _ _ read stored => simp only [chunkRead_iff.mpr ⟨_, read⟩]; exact stored

structure HeaderRead (heap : Heap) (reference : Reference) (header : Word) (length : Nat) : Prop where
  valid : Access.validate heap ⟨.bytes .storage false, reference⟩ = .ok ()
  whole : reference.viewLength.isSome = false
  read : Slot.read heap reference.region reference.address = .ok header
  decoded : Access.byteLength header = .ok length

theorem loadHeader_iff : StorageBytes.loadHeader heap reference = .ok (header, length) ↔
    HeaderRead heap reference header length := by
  unfold StorageBytes.loadHeader
  constructor
  · intro finished
    cases valid : Access.validate heap ⟨.bytes .storage false, reference⟩ with
    | error failure => simp [valid, Bind.bind, Except.bind] at finished
    | ok token =>
        cases token
        simp only [valid, Bind.bind, Except.bind] at finished
        split at finished
        · cases finished
        · rename_i whole
          have wholeView : reference.viewLength.isSome = false := by simpa using whole
          simp only [pure, Except.pure] at finished
          cases read : Slot.read heap reference.region reference.address with
          | error failure => simp [read] at finished
          | ok packet =>
              simp only [read] at finished
              cases decoded : Access.byteLength packet with
              | error failure => simp [decoded] at finished
              | ok count =>
                  simp only [decoded] at finished
                  cases finished
                  exact ⟨valid, wholeView, read, decoded⟩
  · intro checked
    simp only [checked.valid, checked.whole, Bool.false_eq_true, ↓reduceIte,
      checked.read, checked.decoded, Bind.bind, Except.bind, pure, Except.pure]

def StoredWord (region : Region) (slot word : Word) (before : Heap)
    (events : List StorageEvent) (after : Heap) : Prop :=
  events = [.store region slot word] ∧ Slot.write before region slot word = .ok after

theorem StoredWord.trace (stored : StoredWord region slot word before events after) :
    StorageTrace before events after := by
  rcases stored with ⟨rfl, written⟩
  exact StorageTrace.write written

theorem storedWord_iff : Slot.write before region slot word = .ok after ↔
    ∃ events, StoredWord region slot word before events after :=
  ⟨fun written => ⟨_, rfl, written⟩, fun ⟨_, _, written⟩ => written⟩

inductive SmallRead (source : ByteSource) (length : Nat) : Heap → List StorageEvent → Word → Prop where
  | empty (heap : Heap) (empty : length = 0) : SmallRead source length heap [] 0
  | read (heap : Heap) (events : List StorageEvent) (word : Word) (nonempty : length ≠ 0)
      (decoded : ChunkRead source heap 0 length events word) : SmallRead source length heap events word

theorem SmallRead.trace (read : SmallRead source length heap events word) : StorageTrace heap events heap := by
  cases read with
  | empty => exact .nil _
  | read _ _ _ decoded => exact decoded.trace

theorem smallRead_iff :
    (if length = 0 then Except.ok 0 else source.reader heap 0 length) = .ok word ↔
    ∃ events, SmallRead source length heap events word := by
  by_cases empty : length = 0
  · simp only [if_pos empty]
    constructor
    · intro same; cases same; exact ⟨[], .empty heap empty⟩
    · rintro ⟨_, read⟩
      cases read with
      | empty => rfl
      | read _ _ nonempty _ => exact False.elim (nonempty empty)
  · simp only [if_neg empty]
    constructor
    · intro read
      obtain ⟨events, decoded⟩ := chunkRead_iff.mp read
      exact ⟨events, .read heap events word empty decoded⟩
    · rintro ⟨_, read⟩
      cases read with
      | empty impossible => exact False.elim (empty impossible)
      | read _ _ _ decoded => exact chunkRead_iff.mpr ⟨_, decoded⟩

theorem readShortWord_iff : readShortWord heap length source.reader = .ok word ↔
    ∃ events, SmallRead source length heap events word := smallRead_iff

abbrev ByteCleanup (target : Reference) (length : Nat) :=
  CopyFold (fun heap index events after => StoredWord target.region
    (StorageBytes.dataSlot target (StorageBytes.slotCount length+index)) 0 heap events after)

/-- Bulk byte copying records destination cleanup before source payload reads
and publishes the new header last. The read transcript retains actual source
packets even when physical addresses overlap the destination. -/
inductive BytesTransfer (source : ByteSource) (target : Reference) (length budget : Nat) :
    Heap → List StorageEvent → Heap × Nat → Prop where
  | short (before cleaned written : Heap) (header word : Word) (oldLength available : Nat)
      (clearEvents readEvents : List StorageEvent)
      (bounded : length ≤ StorageBytes.maximumCopyLength) (short : length < 32)
      (loaded : HeaderRead before target header oldLength)
      (reserved : reserve budget (length+StorageBytes.slotCount length+
        (StorageBytes.slotCount oldLength-StorageBytes.slotCount length)+1) = .ok available)
      (cleared : ByteCleanup target length before
        (List.range (StorageBytes.slotCount oldLength-StorageBytes.slotCount length)) clearEvents cleaned)
      (read : SmallRead source length cleaned readEvents word)
      (stored : Slot.write cleaned target.region target.address
        (StorageBytes.shortFromWord word ⟨length, short⟩) = .ok written) :
      BytesTransfer source target length budget before
        (.load target.region target.address header ::
          (clearEvents ++ readEvents ++ [.store target.region target.address
            (StorageBytes.shortFromWord word ⟨length, short⟩),
            .resize target.region target.address oldLength length true]))
        (written.journalResize target.region target.address oldLength length true, available)
  | long (before cleaned payload written : Heap) (header : Word) (oldLength available : Nat)
      (clearEvents payloadEvents : List StorageEvent)
      (bounded : length ≤ StorageBytes.maximumCopyLength) (long : 32 ≤ length)
      (loaded : HeaderRead before target header oldLength)
      (reserved : reserve budget (length+StorageBytes.slotCount length+
        (StorageBytes.slotCount oldLength-StorageBytes.slotCount length)+1) = .ok available)
      (cleared : ByteCleanup target length before
        (List.range (StorageBytes.slotCount oldLength-StorageBytes.slotCount length)) clearEvents cleaned)
      (copied : CopyFold (ByteWordStore source target length) cleaned
        (List.range (StorageBytes.slotCount length)) payloadEvents payload)
      (stored : Slot.write payload target.region target.address (StorageBytes.longHeader length) = .ok written) :
      BytesTransfer source target length budget before
        (.load target.region target.address header ::
          (clearEvents ++ payloadEvents ++ [.store target.region target.address (StorageBytes.longHeader length),
            .resize target.region target.address oldLength length true]))
        (written.journalResize target.region target.address oldLength length true, available)

theorem ByteCleanup.trace (cleared : ByteCleanup target length before indices events after) :
    StorageTrace before events after :=
  CopyFold.trace id (fun _ _ _ _ stored => StoredWord.trace stored) cleared

theorem BytesTransfer.trace (copied : BytesTransfer source target length budget before events after) :
    StorageTrace before events after.1 := by
  cases copied with
  | short _ _ _ _ _ _ _ _ _ _ loaded _ cleared read stored =>
      exact .load loaded.read (((ByteCleanup.trace cleared).append read.trace).append
        (.store stored (.resize (.nil _))))
  | long _ _ _ _ _ _ _ _ _ _ loaded _ cleared payload stored =>
      exact .load loaded.read (((ByteCleanup.trace cleared).append
        (payload.trace id (fun _ _ _ _ item => item.trace))).append (.store stored (.resize (.nil _))))

theorem byteCleanup_iff (indices : List Nat) :
    indices.foldlM (fun heap index => Slot.write heap target.region
      (StorageBytes.dataSlot target (StorageBytes.slotCount length+index)) 0) before = .ok after ↔
    ∃ events, ByteCleanup target length before indices events after :=
  CopyFold.iff_foldlM _ (fun _ _ _ => storedWord_iff) indices before after

theorem bytePayload_iff (indices : List Nat) :
    indices.foldlM (writeByteWord source target length) before = .ok after ↔
    ∃ events, CopyFold (ByteWordStore source target length) before indices events after :=
  CopyFold.iff_foldlM _ (fun _ _ _ => writeByteWord_iff) indices before after

theorem writeBytesFrom_iff : writeBytesFrom before budget target length source.reader = .ok after ↔
    ∃ events, BytesTransfer source target length budget before events after := by
  unfold writeBytesFrom prepareBytes
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  constructor
  · intro finished
    by_cases tooLong : StorageBytes.maximumCopyLength < length
    · simp [tooLong] at finished
    · have bounded : length ≤ StorageBytes.maximumCopyLength := by omega
      simp only [if_neg tooLong] at finished
      cases loaded : StorageBytes.loadHeader before target with
      | error failure => simp [loaded] at finished
      | ok result =>
          rcases result with ⟨header, oldLength⟩
          simp only [loaded] at finished
          cases reserved : reserve budget (length+StorageBytes.slotCount length+
              (StorageBytes.slotCount oldLength-StorageBytes.slotCount length)+1) with
          | error failure => simp [reserved] at finished
          | ok available =>
              simp only [reserved] at finished
              cases cleared : (List.range (StorageBytes.slotCount oldLength-StorageBytes.slotCount length)).foldlM
                  (fun heap index => Slot.write heap target.region
                    (StorageBytes.dataSlot target (StorageBytes.slotCount length+index)) 0) before with
              | error failure =>
                  change (List.range (StorageBytes.slotCount oldLength-StorageBytes.slotCount length)).foldlM
                    (fun heap index => Slot.write heap target.region
                      (StorageBytes.dataSlot target (StorageBytes.slotCount length+index)) 0#256) before = .error failure at cleared
                  simp [cleared] at finished
              | ok cleanHeap =>
                  simp only [cleared] at finished
                  obtain ⟨clearEvents, clearTrace⟩ := (byteCleanup_iff _).mp cleared
                  have checked := loadHeader_iff.mp loaded
                  unfold finishBytes at finished
                  simp only [Bind.bind, Except.bind, pure, Except.pure] at finished
                  split at finished
                  · rename_i short
                    cases read : readShortWord cleanHeap length source.reader with
                    | error failure => simp [read] at finished
                    | ok word =>
                        simp only [read] at finished
                        cases stored : Slot.write cleanHeap target.region target.address
                            (StorageBytes.shortFromWord word ⟨length, short⟩) with
                        | error failure => simp [stored] at finished
                        | ok written =>
                            simp only [stored] at finished
                            cases finished
                            obtain ⟨readEvents, observed⟩ := readShortWord_iff.mp read
                            exact ⟨_, .short before cleanHeap written header word oldLength available clearEvents
                              readEvents bounded short checked reserved clearTrace observed stored⟩
                  · rename_i long
                    cases copied : (List.range (StorageBytes.slotCount length)).foldlM
                        (writeByteWord source target length) cleanHeap with
                    | error failure =>
                        have copiedError : (List.range (StorageBytes.slotCount length)).foldlM
                            (fun heap index => do
                              let word ← source.reader heap (index*32) (min 32 (length-index*32))
                              Slot.write heap target.region (StorageBytes.dataSlot target index) word) cleanHeap =
                              .error failure := copied
                        simp only [Bind.bind, Except.bind] at copiedError
                        simp [copiedError] at finished
                    | ok payload =>
                        have copiedBody : (List.range (StorageBytes.slotCount length)).foldlM
                            (fun heap index => do
                              let word ← source.reader heap (index*32) (min 32 (length-index*32))
                              Slot.write heap target.region (StorageBytes.dataSlot target index) word) cleanHeap = .ok payload := copied
                        simp only [Bind.bind, Except.bind] at copiedBody
                        simp only [copiedBody] at finished
                        cases stored : Slot.write payload target.region target.address (StorageBytes.longHeader length) with
                        | error failure => simp [stored] at finished
                        | ok written =>
                            simp only [stored] at finished
                            cases finished
                            obtain ⟨payloadEvents, payloadTrace⟩ := (bytePayload_iff _).mp copied
                            exact ⟨_, .long before cleanHeap payload written header oldLength available clearEvents
                              payloadEvents bounded (by omega) checked reserved clearTrace payloadTrace stored⟩
  · rintro ⟨_, copied⟩
    cases copied with
    | short _ _ _ _ _ _ _ _ bounded short loaded reserved cleared read stored =>
        have clearedBody := (byteCleanup_iff _).mpr ⟨_, cleared⟩
        have readBody := readShortWord_iff.mpr ⟨_, read⟩
        simp only [if_neg (Nat.not_lt.mpr bounded), loadHeader_iff.mpr loaded,
          Bind.bind, Except.bind, reserved, clearedBody, finishBytes, dif_pos short, readBody, stored, pure, Except.pure]
    | long cleaned payloadHeap _ _ _ _ _ _ bounded long loaded reserved cleared payload stored =>
        have clearedBody := (byteCleanup_iff _).mpr ⟨_, cleared⟩
        have copiedBody : (List.range (StorageBytes.slotCount length)).foldlM
            (fun heap index => do
              let word ← source.reader heap (index*32) (min 32 (length-index*32))
              Slot.write heap target.region (StorageBytes.dataSlot target index) word) cleaned = .ok payloadHeap :=
          (bytePayload_iff _).mpr ⟨_, payload⟩
        simp only [Bind.bind, Except.bind] at copiedBody
        simp only [if_neg (Nat.not_lt.mpr bounded), loadHeader_iff.mpr loaded,
          Bind.bind, Except.bind, reserved, clearedBody, finishBytes, dif_neg (Nat.not_lt.mpr long), copiedBody, stored,
          pure, Except.pure]

end Copy

end Solidity.Aggregates
