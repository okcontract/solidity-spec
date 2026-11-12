/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Administrative
import Solidity.Core.Execution.Safety.ConfigurationFrames
import Solidity.Core.Execution.Safety.WordArrayResources
import Solidity.Core.Execution.Safety.ProfileLaws

namespace Solidity.Execution.Safety
open Static Aggregates

/-- An intentionally conservative uniform host-work bound for one transition
in this profile. It is neither gas nor a physical-memory availability claim.
Only new uint256[] materialization consumes work; typed aliases/transfers and
default zero-slot references consume none. -/
def materializationStepBound : Nat := WordArrayResources.cost (2^256-1)

def prefixMaterializationBound (steps : Nat) : Nat := (steps+1)*materializationStepBound

theorem unsigned_cost_bound {width : Core.Width} (count : BitVec width.bits) :
    WordArrayResources.cost count.toNat ≤ materializationStepBound := by
  have power : 2^width.bits ≤ 2^256 := Nat.pow_le_pow_right (by decide : 0 < 2) width.bits_le
  have bounded := count.isLt
  unfold materializationStepBound WordArrayResources.cost
  omega

theorem materializationStepBound_positive : 0 < materializationStepBound := by
  unfold materializationStepBound WordArrayResources.cost
  omega

theorem StateRep.extend_heap (represented : StateRep program oldObjects environment state)
    (physical : HeapRep after newObjects) (invocation : after.invocation = state.heap.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) (remaining : Nat) :
    StateRep program newObjects environment {state with heap := after, materializationRemaining := remaining} :=
  ⟨physical,represented.cells.extend invocation objects,represented.shape,represented.nonempty⟩

theorem DatumRep.atom_of_supported {type : SType} (represented : DatumRep program heap objects datum type)
    (supported : Supported type) :
    ∃ value, datum = .atom value ∧ value.type = type ∧ ValueRep program heap objects value := by
  cases represented with
  | atom value => exact ⟨_,rfl,rfl,value⟩
  | tuple values =>
      rcases supported with scalar | ⟨pointer,shape⟩
      · cases scalar
      · cases shape

theorem ofList_typesList (types : Types) : Types.ofList (typesList types) = types := by
  cases types with
  | nil => rfl
  | cons first rest => simp [typesList,Types.ofList,ofList_typesList rest]
termination_by sizeOf types

theorem DatumRep.asPacket_typed {type : SType} (represented : DatumRep program heap objects datum type) :
    PacketRep program heap objects datum.asPacket (Types.ofList (Admission.resultComponents type)) := by
  cases represented with
  | atom value =>
      rw [Profile.supported_components value.supported]
      exact .cons (.atom value) .nil
  | tuple members => simpa only [Datum.asPacket,Admission.resultComponents,ofList_typesList] using members

def packetResultType : Types → SType
  | .cons type .nil => type
  | types => .tuple types

theorem PacketRep.ofPacket {types : Types} (represented : PacketRep program heap objects values types) :
    DatumRep program heap objects (Datum.ofPacket values) (packetResultType types) := by
  cases represented with
  | nil => exact .tuple .nil
  | cons first rest =>
      cases rest with
      | nil => exact first
      | cons next rest => exact .tuple (.cons first (.cons next rest))

/-- The semantic finite-prefix result distinguishes source termination from a
still-typed prefix. Suspension/model failures do not satisfy this predicate. -/
def StepRep (registry : Registry) (program : Program EmptyKey) (before : Config Unit EmptyKey) :
    Progress (Config Unit EmptyKey) (Observation Unit) → Prop
  | .next after => ConfigurationRep registry program after ∧
      after.entry = before.entry ∧
      before.state.materializationRemaining ≤ after.state.materializationRemaining+materializationStepBound
  | .done result => ObservationRep program before.entry result
  | .suspended _ => False

end Solidity.Execution.Safety
