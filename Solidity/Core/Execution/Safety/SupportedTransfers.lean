/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Configuration
import Solidity.Core.Execution.Safety.WordArrayResources
import Solidity.Core.Execution.Safety.SupportedEligibility

/-! Actual scalar conversions and canonical memory aliases for the initialized
safety profile. All permissions are inherited from the existing source rules;
none of the progress leaves assumes that the requested binding succeeds. -/
namespace Solidity.Execution.Safety.SupportedTransfers
open Static Aggregates
open WordArena
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem implicit_coerce_total (source target : SType) (value : source.Value)
    (allowed : Static.Implicit source target) :
    ∃ converted, Static.coerce source target value = .ok converted := by
  rcases allowed with same | allowed
  · cases same; exact ⟨value,by simp [Static.coerce]⟩
  · cases source <;> cases target <;> simp_all only
    all_goals unfold Static.coerce
    all_goals split
    all_goals try exact ⟨_,rfl⟩
    all_goals simp_all

theorem implicit_convert_total (source target : SType) (value : source.Value)
    (sourceSupported : source.scalarSupported = true) (targetSupported : target.scalarSupported = true)
    (allowed : Static.Implicit source target) :
    ∃ converted, Static.convert .implicit source target value = .ok converted := by
  obtain ⟨converted,coerced⟩ := implicit_coerce_total source target value allowed
  exact ⟨converted,by simp [Static.convert,sourceSupported,targetSupported,
    (Static.allows_iff .implicit source target).mpr allowed,coerced]⟩

theorem scalar_cast_of_conversion
    (converted : Static.convert .implicit source.type target source.value = .ok value) :
    Effects.scalarCast .implicit target source = .ok ⟨target,value⟩ := by
  unfold Static.convert at converted
  split at converted
  · cases converted
  · have support : source.type.scalarSupported = true ∧ target.scalarSupported = true := by
      cases a : source.type.scalarSupported <;> cases b : target.scalarSupported <;> simp_all
    split at converted
    · rename_i allowed
      simp [Effects.scalarCast,allowed,Static.convert,converted,Effects.liftConversion,support.1,support.2]
    · cases converted

theorem conversion_closed (program : Program Key) (source : Value) (target : SType) (value : target.Value)
    (closed : ScalarProgress.ClosedFunction program source)
    (allowed : Static.Implicit source.type target)
    (converted : Static.convert .implicit source.type target source.value = .ok value) :
    ScalarProgress.ClosedFunction program ⟨target,value⟩ := by
  cases target <;> try trivial
  case function visibility mutability parameters returns =>
    cases visibility with
    | external => trivial
    | internal =>
        rcases source with ⟨sourceType,sourceValue⟩
        rcases allowed with same | allowed
        · cases same
          have identity := Static.convert_identity .implicit (.function .internal mutability parameters returns)
            sourceValue rfl (Or.inl rfl)
          have equal := Except.ok.inj (identity.symm.trans converted)
          cases equal
          exact closed
        · cases sourceType <;> try contradiction
          case function visibility sourceMutability sourceParameters sourceReturns =>
            rcases allowed with ⟨same,sourceParametersEq,sourceReturnsEq,allowed⟩
            cases same
            let actual : FunctionSignature := ⟨sourceMutability,sourceParameters,sourceReturns⟩
            let expected : FunctionSignature := ⟨mutability,parameters,returns⟩
            have permission : Static.Allowed .implicit actual.type expected.type :=
              Or.inr ⟨rfl,sourceParametersEq,sourceReturnsEq,allowed⟩
            obtain ⟨casted,represented⟩ := ScalarProgress.function_implicit_closed
              (actual := actual) (expected := expected) closed permission
            have performed := scalar_cast_of_conversion converted
            have equal := Except.ok.inj (performed.symm.trans casted)
            rw [equal]
            exact represented

theorem scalar_value_total (program : Program Key) (heap : Heap) (objects : List Object)
    (source : Value) (target : SType) (sourceSupported : source.type.scalarSupported = true)
    (targetSupported : target.scalarSupported = true) (allowed : Static.Implicit source.type target)
    (closed : ScalarProgress.ClosedFunction program source) :
    ∃ value, Copy.convertScalar target source = .ok value ∧ ValueRep program heap objects value := by
  obtain ⟨value,converted⟩ := implicit_convert_total source.type target source.value sourceSupported targetSupported allowed
  exact ⟨⟨target,value⟩,by simp [Copy.convertScalar,converted],
    .scalar targetSupported (conversion_closed program source target value closed allowed converted)⟩

theorem scalar_reference_none (supported : type.scalarSupported = true) : referenceLocation type = none := by
  cases type <;> simp_all [SType.scalarSupported,referenceLocation]

theorem transfer_classification (sourceSupported : Supported source) (targetSupported : Supported target)
    (rule : TransferRule true source target kind) :
    (source.scalarSupported = true ∧ target.scalarSupported = true ∧ kind = .scalarConversion ∧
      Static.Implicit source target) ∨
    ∃ sourcePointer targetPointer,
      source = arrayType sourcePointer ∧ target = arrayType targetPointer ∧ kind = .memoryAlias := by
  rcases sourceSupported with scalar | ⟨sourcePointer,rfl⟩
  · have origin := scalar_reference_none scalar
    cases kind <;> simp_all [TransferRule]
    rcases targetSupported with targetScalar | ⟨targetPointer,rfl⟩
    · exact targetScalar
    · simp [arrayType,referenceLocation] at rule
  · rcases targetSupported with scalar | ⟨targetPointer,rfl⟩
    · have origin := scalar_reference_none scalar
      cases kind <;> simp_all [TransferRule,arrayType,referenceLocation]
    · cases kind <;> simp_all [TransferRule,arrayType,referenceLocation]

theorem alias_array (heapRep : HeapRep heap objects)
    (represented : ValueRep program heap objects ⟨arrayType sourcePointer,reference⟩) (targetPointer : Bool) :
    Copy.alias heap (arrayType targetPointer) ⟨arrayType sourcePointer,reference⟩ =
      .ok ⟨arrayType targetPointer,reference⟩ := by
  obtain ⟨object,physical,rfl⟩ := represented.array_object heapRep
  have validated := Copy.memory_validate_reference (heap := heap) (type := arrayType sourcePointer)
    (address := object.address) (by rfl)
  have extent : heap.allocated object.address.toNat 0 = true :=
    Copy.allocated_subrange _ _ _ _ _ physical.extent (Nat.le_refl _) (by simp [Object.bytes])
  unfold arrayType at validated
  simp only [Copy.alias,Value.reference,arrayType,Object.reference,Bind.bind,Except.bind]
  rw [validated]
  simp [Copy.memoryReference,checkExtent,extent,Copy.retag,referenceValue]

theorem array_retag_rep (represented : ValueRep program heap objects ⟨arrayType sourcePointer,reference⟩)
    (targetPointer : Bool) : ValueRep program heap objects ⟨arrayType targetPointer,reference⟩ := by
  cases represented with
  | scalar support _ => simp [arrayType,SType.scalarSupported] at support
  | array _ object member => exact .array targetPointer object member
  | emptyArray _ => exact .emptyArray targetPointer

theorem scalar_default (program : Program Key) (type : SType) (supported : type.scalarSupported = true) :
    ∃ value, Static.defaultScalar type = some value ∧ ScalarProgress.ClosedFunction program ⟨type,value⟩ := by
  cases type <;> simp only [SType.scalarSupported] at supported <;> try contradiction
  all_goals try exact ⟨_,rfl,trivial⟩
  case valueType identity base =>
    cases base with
    | scalar core => cases core <;> exact ⟨_,rfl,trivial⟩
    | payableAddress => exact ⟨_,rfl,trivial⟩
  case function visibility mutability parameters returns =>
    cases visibility with
    | external => exact ⟨_,rfl,trivial⟩
    | internal => exact ⟨_,rfl,ScalarProgress.null_closed program ⟨mutability,parameters,returns⟩⟩

theorem build_default_total (program : Program Key) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (objects : List Object) (type : SType) (supported : Supported type)
    (physical : HeapRep heap objects) :
    ∃ value, Defaults.build registry (fuel+2) heap budget type = .ok (⟨type,value⟩,heap,budget) ∧
      ValueRep program heap objects ⟨type,value⟩ := by
  rcases supported with scalar | ⟨pointer,rfl⟩
  · obtain ⟨value,default,closed⟩ := scalar_default program type scalar
    exact ⟨value,by simp only [Defaults.build,default],.scalar scalar closed⟩
  · refine ⟨Copy.memoryReference heap 96,?_,.emptyArray pointer⟩
    simp [Defaults.build,arrayType,Static.defaultScalar,WordArrayResources.emptyReference_total physical,atLocation]

theorem plan_rule_total (sourceReady : TypeReady registry source) (targetReady : TypeReady registry target)
    (rule : TransferRule true source target kind) (fuel : Nat) :
    planTransfer registry (fuel+2) true source target = .ok kind := by
  have selected := (selectTransfer_iff true source target kind).mpr rule
  have kinds : kind = .scalarConversion ∨ kind = .memoryAlias := by
    rcases transfer_classification sourceReady.1 targetReady.1 rule with scalar | ⟨_,_,_,_,same⟩
    · exact Or.inl scalar.2.2.1
    · exact Or.inr same
  rcases kinds with rfl | rfl <;>
    simp only [planTransfer,SupportedEligibility.eligible_total sourceReady fuel,
      SupportedEligibility.eligible_total targetReady fuel,selected,Bind.bind,Except.bind] <;> rfl

theorem scalar_closed (represented : ValueRep program heap objects source)
    (scalar : source.type.scalarSupported = true) : ScalarProgress.ClosedFunction program source := by
  cases represented with
  | scalar _ closed => exact closed
  | array | emptyArray => simp [arrayType,SType.scalarSupported] at scalar

theorem self_ready (ready : TypeReady registry type) : TransferReady registry type type := by
  refine ⟨ready,ready,?_⟩
  rcases ready.1 with scalar | ⟨pointer,rfl⟩
  · exact ⟨.scalarConversion,scalar_reference_none scalar,scalar_reference_none scalar,Or.inl rfl⟩
  · exact ⟨.memoryAlias,rfl,rfl,by simp [SameShape,arrayType]⟩

/-- Binding a supported initialized value performs the actual permitted scalar
conversion or memory alias. Neither case allocates or consumes host work. -/
theorem bind_total (program : Program Key) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (objects : List Object) (source : Value) (target : SType)
    (ready : TransferReady registry source.type target) (physical : HeapRep heap objects)
    (represented : ValueRep program heap objects source) :
    ∃ value, Copy.bind registry (fuel+2) budget heap target source = .ok (value,heap,budget) ∧
      ValueRep program heap objects value ∧ value.type = target := by
  rcases ready with ⟨sourceReady,targetReady,kind,rule⟩
  have planned := plan_rule_total sourceReady targetReady rule fuel
  rcases transfer_classification sourceReady.1 targetReady.1 rule with
    ⟨sourceScalar,targetScalar,rfl,allowed⟩ | ⟨sourcePointer,targetPointer,sourceEq,targetEq,rfl⟩
  · obtain ⟨value,converted,rep⟩ := scalar_value_total program heap objects source target sourceScalar targetScalar
      allowed (scalar_closed represented sourceScalar)
    exact ⟨value,Copy.bind_scalar planned converted,rep,Copy.convertScalar_type converted⟩
  · rcases source with ⟨sourceType,reference⟩
    dsimp only at sourceEq
    cases sourceEq
    cases targetEq
    exact ⟨⟨arrayType targetPointer,reference⟩,
      Copy.bind_alias planned (Or.inr (Or.inl rfl)) (alias_array physical represented targetPointer),
      array_retag_rep represented targetPointer,rfl⟩

theorem defaultValue_total (program : Program Key) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (objects : List Object) (type : SType) (ready : TypeReady registry type)
    (physical : HeapRep heap objects) :
    ∃ value, Defaults.defaultValue registry (fuel+2) budget heap type = .ok (⟨type,value⟩,heap,budget) ∧
      ValueRep program heap objects ⟨type,value⟩ := by
  obtain ⟨value,built,rep⟩ := build_default_total program registry fuel budget heap objects type ready.1 physical
  exact ⟨value,by simp [Defaults.defaultValue,SupportedEligibility.memoryEligible_total ready fuel,built],rep⟩

theorem defaultLocal_total (program : Program Key) (registry : Registry) (fuel budget : Nat)
    (heap : Heap) (objects : List Object) (type : SType) (ready : TypeReady registry type)
    (physical : HeapRep heap objects) :
    ∃ value, Effects.defaultLocal registry (fuel+2) budget heap type = .ok (some ⟨type,value⟩,heap,budget) ∧
      ValueRep program heap objects ⟨type,value⟩ := by
  obtain ⟨value,default,rep⟩ := defaultValue_total program registry fuel budget heap objects type ready physical
  refine ⟨value,?_,rep⟩
  have eligible := SupportedEligibility.eligible_total ready fuel
  rcases ready.1 with scalar | ⟨pointer,rfl⟩
  · cases type <;> simp_all [SType.scalarSupported,Effects.defaultLocal,referenceLocation]
  · unfold arrayType at eligible default ⊢
    simp [Effects.defaultLocal,eligible,referenceLocation,default]

end Solidity.Execution.Safety.SupportedTransfers
