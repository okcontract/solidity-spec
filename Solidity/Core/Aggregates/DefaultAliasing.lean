/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.DefaultConstructionRepresentation
import Solidity.Core.Aggregates.Representation.Construction

/-! Constructor alias contracts retain the intermediate allocation frontier.
The final packet predicate alone need not record construction history: each
staged child begins beyond the allocated packets of its predecessors. Empty
default dynamic objects deliberately share the checked header at96. -/
namespace Solidity.Aggregates.Defaults.Representation
open Static
open Contract.Interaction (Word)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

/-- Root packets only; recursively represented children have their own spans. -/
def rootSpan (type : SType) (contents : Contents) : Nat :=
  match type, contents with
  | .array _ size _ _, .array _ values => Copy.rootSize size values.length
  | .structType _ _ _, .structure _ values => 32*values.length
  | .bytes _ _, .bytes _ values | .string _ _, .bytes _ values => 32+values.length
  | _, _ => 0

theorem Object.root_extent (represented : Object registry heap lower type address contents) :
    heap.allocated address.toNat (rootSpan type contents) = true := by
  cases represented with
  | emptyArray element pointer extent header => exact extent
  | emptyBytes string pointer extent header => cases string <;> exact extent
  | array element size pointer address values base bounded extent length header cells => exact extent
  | «structure» identity pointer address fields values base bounded extent definition length cells =>
      simpa only [rootSpan, ← length] using extent
  | bytes string pointer address values base bounded extent header payload => cases string <;> exact extent

theorem Object.base_or_shared (represented : Object registry heap lower type address contents) :
    address = 96 ∨ lower ≤ address.toNat := by
  cases represented with
  | emptyArray => exact Or.inl rfl
  | emptyBytes => exact Or.inl rfl
  | array element size pointer address values base => exact Or.inr base
  | «structure» identity pointer address fields values base => exact Or.inr base
  | bytes string pointer address values base => exact Or.inr base

theorem allocated_end_le_frontier (valid : MemoryOps.validFrontier heap = true)
    (extent : heap.allocated address count = true) : address+count ≤ heap.nextMemory := by
  simp only [Heap.allocated, List.any_eq_true] at extent
  rcases extent with ⟨allocation, member, bounds⟩
  have old := MemoryOps.validFrontier_old_separate heap allocation valid member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at bounds
  omega

theorem Object.root_end_le_frontier (represented : Object registry heap lower type address contents)
    (valid : MemoryOps.validFrontier heap = true) :
    address.toNat+rootSpan type contents ≤ heap.nextMemory :=
  allocated_end_le_frontier valid represented.root_extent

theorem Object.separate_oldAllocation
    (represented : Object registry after before.nextMemory type address contents)
    (valid : MemoryOps.validFrontier before = true)
    (old : allocation ∈ before.allocations) :
    address = 96 ∨ allocation.start+allocation.size ≤ address.toNat := by
  rcases represented.base_or_shared with shared | fresh
  · exact Or.inl shared
  · exact Or.inr (Nat.le_trans (MemoryOps.validFrontier_old_separate before allocation valid old) fresh)

/-- Earlier root packets end below the intermediate frontier. Every later
nonshared root begins above it, even when both arise as recursive siblings. -/
theorem Object.staged_roots_separate
    (old : Object registry middle lower oldType oldAddress oldContents)
    (fresh : Object registry after middle.nextMemory type address contents)
    (valid : MemoryOps.validFrontier middle = true) :
    address = 96 ∨ oldAddress.toNat+rootSpan oldType oldContents ≤ address.toNat := by
  rcases fresh.base_or_shared with shared | starts
  · exact Or.inl shared
  · exact Or.inr (Nat.le_trans (old.root_end_le_frontier valid) starts)

theorem Object.staged_nonshared_distinct
    (old : Object registry middle lower oldType oldAddress oldContents)
    (fresh : Object registry after middle.nextMemory type address contents)
    (valid : MemoryOps.validFrontier middle = true) (nonshared : address ≠ 96)
    (nonempty : 0 < rootSpan oldType oldContents) : oldAddress ≠ address := by
  rcases old.staged_roots_separate fresh valid with shared | separate
  · exact False.elim (nonshared shared)
  · intro equal
    subst oldAddress
    omega

theorem Cell.child_follows_cell
    (represented : Cell registry heap lower floor type address contents)
    (packet : heap.execution.memory.read address 32 = Contract.Interaction.wordBytes target)
    (reference : isReference type = true) : target = 96 ∨ address+32 ≤ target.toNat := by
  cases represented with
  | scalar type address contents range scalar =>
      rcases scalar with ⟨source, value, word, same, converted, encoded, extent, bytes⟩
      have supported := Copy.convertScalar_supported converted
      cases type <;> simp_all [isReference, referenceLocation, SType.scalarSupported]
  | pointer type address actual contents range extent bytes object =>
      have same : actual = target := by
        have equal := congrArg Contract.Interaction.bytesWord (bytes.symm.trans packet)
        simpa only [Contract.Interaction.bytesWord_wordBytes] using equal
      subst actual
      rcases object.base_or_shared with shared | base
      · exact Or.inl shared
      · exact Or.inr (Nat.le_trans range.2 base)

theorem ValueRep.of_fresh (represented : Copy.ValueRep registry heap lower type contents value) :
    ValueRep registry heap lower type contents value := by
  cases contents with
  | scalar source => exact represented
  | array source values | «structure» identity values | bytes string values =>
      rcases represented with ⟨address, tagged, tree⟩
      exact ⟨address, tagged, Object.of_fresh tree⟩

theorem ValueRep.object (represented : ValueRep registry heap lower type contents value)
    (reference : isReference type = true) :
    ∃ address, Copy.retag type (Copy.memoryReference heap address) = .ok value ∧
      Object registry heap lower type address contents := by
  cases contents with
  | scalar source =>
      have supported := Copy.convertScalar_supported represented
      cases type <;> simp_all [isReference, referenceLocation, SType.scalarSupported]
  | array | «structure» | bytes => exact represented

theorem Object.after_defaultValue (represented : Object registry before lower type address contents)
    (above : 96 ≤ lower) (valid : MemoryOps.validFrontier before = true)
    (written : defaultValue registry fuel budget before builtType = .ok (value, after, remaining)) :
    Object registry after lower type address contents :=
  represented.frame (Frame.of_packetFrame ((defaultValue_extension written).packetFrame valid) above)

theorem Cell.after_defaultValue (represented : Cell registry before lower floor type address contents)
    (above : 96 ≤ lower) (valid : MemoryOps.validFrontier before = true)
    (written : defaultValue registry fuel budget before builtType = .ok (value, after, remaining)) :
    Cell registry after lower floor type address contents :=
  represented.frame (Frame.of_packetFrame ((defaultValue_extension written).packetFrame valid) above)

theorem Object.after_materialization (represented : Object registry before lower type address contents)
    (above : 96 ≤ lower) (valid : MemoryOps.validFrontier before = true)
    (written : Copy.materializeMemory registry fuel budget before builtType builtContents = .ok (value, after, remaining)) :
    Object registry after lower type address contents :=
  represented.frame (Frame.of_packetFrame ((Copy.materializeMemory_extension written).packetFrame valid) above)

theorem Cell.after_materialization (represented : Cell registry before lower floor type address contents)
    (above : 96 ≤ lower) (valid : MemoryOps.validFrontier before = true)
    (written : Copy.materializeMemory registry fuel budget before builtType builtContents = .ok (value, after, remaining)) :
    Cell registry after lower floor type address contents :=
  represented.frame (Frame.of_packetFrame ((Copy.materializeMemory_extension written).packetFrame valid) above)

theorem defaultValue_staged_root
    (old : Object registry middle lower oldType oldAddress oldContents)
    (above : 96 ≤ lower) (valid : MemoryOps.validFrontier middle = true)
    (reference : isReference (normalizedType type) = true)
    (written : defaultValue registry fuel budget middle type = .ok (value, after, remaining)) :
    Object registry after lower oldType oldAddress oldContents ∧
      ∃ contents address, DefaultContents registry (normalizedType type) contents ∧
        Copy.retag (normalizedType type) (Copy.memoryReference after address) = .ok value ∧
        Object registry after middle.nextMemory (normalizedType type) address contents ∧
        (address = 96 ∨ oldAddress.toNat+rootSpan oldType oldContents ≤ address.toNat) := by
  rcases defaultValue_rep valid written with ⟨contents, defaults, represented⟩
  rcases represented.object reference with ⟨address, tagged, object⟩
  exact ⟨old.after_defaultValue above valid written, contents, address, defaults, tagged, object,
    old.staged_roots_separate object valid⟩

theorem materializeMemory_staged_root
    (old : Object registry middle lower oldType oldAddress oldContents)
    (above : 96 ≤ lower) (valid : MemoryOps.validFrontier middle = true)
    (reference : isReference type = true)
    (written : Copy.materializeMemory registry fuel budget middle type contents = .ok (value, after, remaining)) :
    Object registry after lower oldType oldAddress oldContents ∧
      ∃ address, Copy.retag type (Copy.memoryReference after address) = .ok value ∧
        Object registry after middle.nextMemory type address contents ∧
        oldAddress.toNat+rootSpan oldType oldContents ≤ address.toNat := by
  have fresh := Copy.materializeMemory_rep valid written
  rcases (ValueRep.of_fresh fresh).object reference with ⟨address, tagged, object⟩
  have base : middle.nextMemory ≤ address.toNat := by
    cases contents with
    | scalar source =>
        have supported := Copy.convertScalar_supported fresh
        cases type <;> simp_all [isReference, referenceLocation, SType.scalarSupported]
    | array | «structure» | bytes =>
        rcases fresh with ⟨original, originalTag, tree⟩
        have originalReference := Copy.retag_reference originalTag
        have targetReference := Copy.retag_reference tagged
        have equal : original = address := by
          have refs := Option.some.inj (originalReference.symm.trans targetReference)
          exact congrArg Reference.address refs
        subst original
        exact tree.base
  exact ⟨old.after_materialization above valid written, address, tagged, object,
    Nat.le_trans (old.root_end_le_frontier valid) base⟩

/-- The array constructor always returns the root it allocated at entry. Its
zero-length dynamic result is fresh too; it does not use the default zero slot. -/
theorem allocateArray_reference
    (written : allocateArray makeDefault heap budget element count dynamic pointer = .ok (value, after, remaining)) :
    ∃ reference, value.reference = some reference ∧ reference.address.toNat = heap.nextMemory := by
  unfold allocateArray at written
  cases sized : MemoryOps.arraySize count false dynamic with
  | error failure => simp [sized] at written
  | ok bytes =>
      simp only [sized, Bind.bind, Except.bind] at written
      cases allocated : MemoryOps.allocate heap budget bytes with
      | error failure => simp [allocated] at written
      | ok result =>
          rcases result with ⟨reference, fresh, available⟩
          have position := Copy.allocate_extension allocated (Nat.le_refl heap.nextMemory)
          simp only [allocated] at written
          cases initialized : initializeLength fresh available reference count dynamic with
          | error failure => simp [initialized] at written
          | ok result =>
              rcases result with ⟨populated, rest⟩
              simp only [initialized] at written
              cases advanced : arrayDataReference reference dynamic with
              | error failure => simp [advanced] at written
              | ok data =>
                  simp only [advanced] at written
                  cases reserved : reserve rest count with
                  | error failure => simp [reserved] at written
                  | ok allowance =>
                      simp only [reserved] at written
                      cases filled : initializeCells makeDefault populated allowance data (List.replicate count element) with
                      | error failure => simp [filled] at written
                      | ok result =>
                          rcases result with ⟨final, unused⟩
                          simp only [filled] at written
                          cases written
                          exact ⟨reference, rfl, position.2.2⟩

theorem newArray_reference
    (written : newArray registry fuel budget heap element count dynamic = .ok (value, after, remaining)) :
    ∃ reference, value.reference = some reference ∧ reference.address.toNat = heap.nextMemory := by
  unfold newArray at written
  cases eligible : memoryEligible registry fuel
      (.array (atLocation element .memory false) (if dynamic then none else some count) .memory true) with
  | error failure => simp [eligible] at written
  | ok _ =>
      simp only [eligible] at written
      exact allocateArray_reference written

theorem newArray_staged_root
    (old : Object registry middle lower oldType oldAddress oldContents)
    (above : 96 ≤ lower) (valid : MemoryOps.validFrontier middle = true)
    (written : newArray registry fuel budget middle element count dynamic = .ok (value, after, remaining)) :
    Object registry after lower oldType oldAddress oldContents ∧
      ∃ values address, values.length = count ∧
        (∀ (index : Nat) contents, values[index]? = some contents →
          DefaultContents registry (atLocation element .memory false) contents) ∧
        Copy.retag (.array (atLocation element .memory false) (if dynamic then none else some count) .memory true)
          (Copy.memoryReference after address) = .ok value ∧
        Object registry after middle.nextMemory
          (.array (atLocation element .memory false) (if dynamic then none else some count) .memory true)
          address (.array (atLocation element .memory false) values) ∧
        oldAddress.toNat+rootSpan oldType oldContents ≤ address.toNat := by
  rcases newArray_rep valid written with ⟨values, length, defaults, address, tagged, object⟩
  rcases newArray_reference written with ⟨reference, extracted, position⟩
  have source := Copy.retag_reference tagged
  have equal := Option.some.inj (source.symm.trans extracted)
  have base : address.toNat = middle.nextMemory := by
    simpa only [Copy.memoryReference] using (congrArg (fun r : Reference => r.address.toNat) equal).trans position
  have preserved := old.frame
    (Frame.of_packetFrame ((newArray_extension written).packetFrame valid) above)
  exact ⟨preserved, values, address, length, defaults, tagged, object,
    by rw [base]; exact old.root_end_le_frontier valid⟩

/-- Two actual sequential defaults preserve the first represented object and
separate their nonshared root packets. The exception names the intentional
shared default header, rather than assuming a disjointness invariant. -/
theorem defaultValue_two_roots
    (valid : MemoryOps.validFrontier before = true)
    (firstReference : isReference (normalizedType firstType) = true)
    (secondReference : isReference (normalizedType secondType) = true)
    (first : defaultValue registry firstFuel firstBudget before firstType = .ok (firstValue, middle, firstRemaining))
    (second : defaultValue registry secondFuel secondBudget middle secondType = .ok (secondValue, after, secondRemaining)) :
    ∃ firstContents secondContents firstAddress secondAddress,
      DefaultContents registry (normalizedType firstType) firstContents ∧
      DefaultContents registry (normalizedType secondType) secondContents ∧
      Copy.retag (normalizedType firstType) (Copy.memoryReference middle firstAddress) = .ok firstValue ∧
      Copy.retag (normalizedType secondType) (Copy.memoryReference after secondAddress) = .ok secondValue ∧
      Object registry after before.nextMemory (normalizedType firstType) firstAddress firstContents ∧
      Object registry after middle.nextMemory (normalizedType secondType) secondAddress secondContents ∧
      (secondAddress = 96 ∨ firstAddress.toNat+rootSpan (normalizedType firstType) firstContents ≤ secondAddress.toNat) := by
  rcases defaultValue_rep valid first with ⟨firstContents, firstDefaults, firstRep⟩
  rcases firstRep.object firstReference with ⟨firstAddress, firstTag, firstObject⟩
  have middleValid := (defaultValue_extension first).valid valid
  have above := Copy.validFrontier_minimum valid
  rcases defaultValue_staged_root firstObject (by omega) middleValid secondReference second with
    ⟨preserved, secondContents, secondAddress, secondDefaults, secondTag, secondObject, separated⟩
  exact ⟨firstContents, secondContents, firstAddress, secondAddress, firstDefaults, secondDefaults,
    firstTag, secondTag, preserved, secondObject, separated⟩

theorem materializeMemory_two_roots
    (valid : MemoryOps.validFrontier before = true)
    (firstReference : isReference firstType = true) (secondReference : isReference secondType = true)
    (first : Copy.materializeMemory registry firstFuel firstBudget before firstType firstContents =
      .ok (firstValue, middle, firstRemaining))
    (second : Copy.materializeMemory registry secondFuel secondBudget middle secondType secondContents =
      .ok (secondValue, after, secondRemaining)) :
    ∃ firstAddress secondAddress,
      Copy.retag firstType (Copy.memoryReference middle firstAddress) = .ok firstValue ∧
      Copy.retag secondType (Copy.memoryReference after secondAddress) = .ok secondValue ∧
      Object registry after before.nextMemory firstType firstAddress firstContents ∧
      Object registry after middle.nextMemory secondType secondAddress secondContents ∧
      firstAddress.toNat+rootSpan firstType firstContents ≤ secondAddress.toNat := by
  have firstRep := ValueRep.of_fresh (Copy.materializeMemory_rep valid first)
  rcases firstRep.object firstReference with ⟨firstAddress, firstTag, firstObject⟩
  have middleValid := (Copy.materializeMemory_extension first).valid valid
  have above := Copy.validFrontier_minimum valid
  rcases materializeMemory_staged_root firstObject (by omega) middleValid secondReference second with
    ⟨preserved, secondAddress, secondTag, secondObject, separated⟩
  exact ⟨firstAddress, secondAddress, firstTag, secondTag, preserved, secondObject, separated⟩

theorem newArray_two_roots
    (valid : MemoryOps.validFrontier before = true)
    (first : newArray registry firstFuel firstBudget before firstElement firstCount firstDynamic =
      .ok (firstValue, middle, firstRemaining))
    (second : newArray registry secondFuel secondBudget middle secondElement secondCount secondDynamic =
      .ok (secondValue, after, secondRemaining)) :
    ∃ firstValues secondValues firstAddress secondAddress,
      firstValues.length = firstCount ∧ secondValues.length = secondCount ∧
      Copy.retag (.array (atLocation firstElement .memory false)
        (if firstDynamic then none else some firstCount) .memory true)
        (Copy.memoryReference middle firstAddress) = .ok firstValue ∧
      Copy.retag (.array (atLocation secondElement .memory false)
        (if secondDynamic then none else some secondCount) .memory true)
        (Copy.memoryReference after secondAddress) = .ok secondValue ∧
      Object registry after before.nextMemory
        (.array (atLocation firstElement .memory false) (if firstDynamic then none else some firstCount) .memory true)
        firstAddress (.array (atLocation firstElement .memory false) firstValues) ∧
      Object registry after middle.nextMemory
        (.array (atLocation secondElement .memory false) (if secondDynamic then none else some secondCount) .memory true)
        secondAddress (.array (atLocation secondElement .memory false) secondValues) ∧
      firstAddress.toNat+Copy.rootSize (if firstDynamic then none else some firstCount) firstValues.length ≤
        secondAddress.toNat := by
  rcases newArray_rep valid first with ⟨firstValues, firstLength, _, firstAddress, firstTag, firstObject⟩
  have middleValid := (newArray_extension first).valid valid
  have above := Copy.validFrontier_minimum valid
  rcases newArray_staged_root firstObject (by omega) middleValid second with
    ⟨preserved, secondValues, secondAddress, secondLength, _, secondTag, secondObject, separated⟩
  exact ⟨firstValues, secondValues, firstAddress, secondAddress, firstLength, secondLength,
    firstTag, secondTag, preserved, secondObject, separated⟩

end Solidity.Aggregates.Defaults.Representation
