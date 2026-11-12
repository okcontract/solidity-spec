/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.DefaultAllocationRepresentation
import Solidity.Core.Aggregates.DefaultLeafRepresentation

namespace Solidity.Aggregates.Defaults.Representation
open Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

/-- Every successful recursive default has actual scalar, pointer and used
payload packets. Empty dynamic objects may share the checked zero header. -/
theorem build_rep (registry : Registry) (fuel : Nat) : MakesDefaultRep registry (build registry fuel) := by
  induction fuel with
  | zero => intro heap budget type value after remaining valid written; cases written
  | succ fuel ih =>
      intro heap budget type value after remaining valid written
      have invocation := build_preserves_invocation written
      cases zero : defaultScalar type with
      | some scalar =>
          have normalized : normalizedType type = type := by
            cases type <;> simp_all [defaultScalar, normalizedType]
          simp only [build, zero] at written
          cases written
          rw [normalized]
          exact ⟨.scalar ⟨type, scalar⟩, defaultScalar_rep zero⟩
      | none =>
          simp only [build, zero] at written
          cases type with
          | array element size location pointer =>
              cases location with
              | storage => cases size <;> cases written
              | calldata => cases size <;> cases written
              | memory =>
                  cases size with
                  | none =>
                      cases empty : emptyReference heap with
                      | error failure => simp [empty] at written
                      | ok reference =>
                          simp only [empty] at written
                          cases written
                          exact emptyArray_rep empty rfl
                  | some count =>
                      rcases allocateArray_rep (build registry fuel) ih (build_extension registry fuel)
                        valid invocation written with ⟨values, length, defaults, represented⟩
                      exact ⟨.array (atLocation element .memory false) values,
                        .arrayFixed (atLocation element .memory false) count pointer values length defaults,
                        represented⟩
          | bytes location pointer | string location pointer =>
              cases location with
              | storage => cases written
              | calldata => cases written
              | memory =>
                  cases empty : emptyReference heap with
                  | error failure => simp [empty] at written
                  | ok reference =>
                      simp only [empty] at written
                      cases written
                      first
                      | exact emptyBytes_rep (string := false) empty rfl
                      | exact emptyBytes_rep (string := true) empty rfl
          | structType identity location pointer =>
              cases location with
              | storage => cases written
              | calldata => cases written
              | memory =>
                  exact allocateStruct_rep (build registry fuel) ih (build_extension registry fuel)
                    valid invocation written
          | _ => cases written

theorem defaultValue_rep
    (valid : MemoryOps.validFrontier heap = true)
    (written : defaultValue registry fuel budget heap type = .ok (value, after, remaining)) :
    ∃ contents, DefaultContents registry (normalizedType type) contents ∧
      ValueRep registry after heap.nextMemory (normalizedType type) contents value := by
  unfold defaultValue at written
  cases eligible : memoryEligible registry fuel type with
  | error failure => simp [eligible] at written
  | ok _ =>
      simp only [eligible] at written
      exact build_rep registry fuel heap budget type value after remaining valid written

theorem newArray_rep
    (valid : MemoryOps.validFrontier heap = true)
    (written : newArray registry fuel budget heap element count dynamic = .ok (value, after, remaining)) :
    ∃ values, values.length = count ∧
      (∀ (index : Nat) contents, values[index]? = some contents →
        DefaultContents registry (atLocation element .memory false) contents) ∧
      ValueRep registry after heap.nextMemory
        (.array (atLocation element .memory false) (if dynamic then none else some count) .memory true)
        (.array (atLocation element .memory false) values) value := by
  have invocation := (newArray_frame registry fuel budget remaining count heap after element dynamic value written).2
  unfold newArray at written
  cases eligible : memoryEligible registry fuel
      (.array (atLocation element .memory false) (if dynamic then none else some count) .memory true) with
  | error failure => simp [eligible] at written
  | ok _ =>
      simp only [eligible] at written
      simpa only [Copy.atLocation_repeat] using
        allocateArray_rep (build registry fuel) (build_rep registry fuel) (build_extension registry fuel)
          valid invocation written

/-- The representation exposes the physical element packet at every admitted
index. The shared empty-header case cannot supply a spurious element. -/
theorem Object.arrayCell
    (represented : Object registry heap lower (.array element size .memory pointer) address (.array source values))
    (member : values[index]? = some contents) :
    Cell registry heap lower (address.toNat+Copy.rootSize size values.length)
      (atLocation element .memory false) (Copy.dataStart address size+index*32) contents := by
  generalize typeEq : SType.array element size .memory pointer = type at represented
  generalize contentsEq : Contents.array source values = objectContents at represented
  cases represented with
  | emptyArray => cases contentsEq; simp at member
  | emptyBytes string pointer => cases string <;> cases typeEq
  | array element size pointer address values base bounded extent length header cells =>
      cases typeEq
      cases contentsEq
      exact cells index contents member
  | «structure» => cases typeEq
  | bytes string pointer => cases string <;> cases typeEq

theorem Object.structCell
    (represented : Object registry heap lower (.structType identity .memory pointer) address (.structure identity values))
    (definition : registry.structFields identity = some fields)
    (member : fields[index]? = some field) (entry : values[index]? = some contents) :
    Cell registry heap lower (address.toNat+32*fields.length)
      (atLocation field.2 .memory false) (address.toNat+index*32) contents := by
  generalize typeEq : SType.structType identity .memory pointer = type at represented
  generalize contentsEq : Contents.structure identity values = objectContents at represented
  cases represented with
  | emptyArray => cases typeEq
  | emptyBytes string pointer => cases string <;> cases typeEq
  | array => cases typeEq
  | «structure» identity pointer address fields' values base bounded extent resolved length cells =>
      cases typeEq
      cases contentsEq
      have equal := Option.some.inj (resolved.symm.trans definition)
      subst fields'
      exact cells index field contents member entry
  | bytes string pointer => cases string <;> cases typeEq

theorem Cell.scalarPacket
    (represented : Cell registry heap lower floor type address (.scalar source)) :
    Copy.ScalarPacket heap type address (.scalar source) := by
  cases represented with
  | scalar type address contents range packet => exact packet
  | pointer type address target contents range extent packet object => cases object

/-- Scalar leaves produced by default construction are consumable by the same
physical read used by source execution, with no invented read oracle. -/
theorem Cell.scalarRead
    (represented : Cell registry heap lower floor type address (.scalar source))
    (bound : address < 2^256) :
    ∃ value, Copy.convertScalar type source = .ok value ∧
      Access.read heap ⟨type, Copy.memoryReference heap (BitVec.ofNat 256 address)⟩ = .ok value := by
  rcases represented.scalarPacket.accessRead bound with ⟨original, value, same, converted, read⟩
  cases same
  exact ⟨value, converted, read⟩

end Solidity.Aggregates.Defaults.Representation
