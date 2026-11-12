/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Configuration

namespace Solidity.Execution.Safety.SupportedEligibility
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem eligibleFrom_wellFormed
    {inlined : List Nat}
    (checked : eligibleFrom registry fuel region seen inlined type = .ok ()) :
    Static.wellFormed registry type = true := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases formed : Static.wellFormed registry type with
      | false => simp [eligibleFrom, formed] at checked
      | true => rfl

theorem eligibleAt_wellFormed
    (checked : eligibleAt registry fuel region type = .ok ()) :
    Static.wellFormed registry type = true := by
  cases placed : eligibleFrom registry fuel region [] [] type with
  | error failure => simp [eligibleAt, placed] at checked
  | ok value => exact eligibleFrom_wellFormed placed

theorem eligible_wellFormed
    (checked : eligibleType registry fuel type = .ok ()) :
    Static.wellFormed registry type = true :=
  eligibleAt_wellFormed checked

theorem checkType_wellFormed
    (checked : Admission.checkType registry fuel type = .ok ()) :
    Static.wellFormed registry type = true :=
  eligible_wellFormed checked

theorem planTransfer_wellFormed
    (checked : planTransfer registry fuel localBinding source target = .ok kind) :
    Static.wellFormed registry source = true ∧ Static.wellFormed registry target = true := by
  cases first : eligibleType registry fuel source with
  | error failure => simp [planTransfer, first] at checked
  | ok value =>
      cases second : eligibleType registry fuel target with
      | error failure => simp [planTransfer, first, second] at checked
      | ok value => exact ⟨eligible_wellFormed first, eligible_wellFormed second⟩

private theorem scalar_bytes (supported : type.scalarSupported = true) :
    ∃ bytes, storageBytes type = some bytes := by
  cases type <;> simp_all [SType.scalarSupported, storageBytes]
  case valueType identity base =>
    cases base with
    | payableAddress => exact ⟨20, rfl⟩
    | scalar elementary => cases elementary <;> exact ⟨_, rfl⟩
  case function visibility mutability parameters returns =>
    cases visibility <;> exact ⟨_, rfl⟩

private theorem scalar_location (supported : type.scalarSupported = true) :
    referenceLocation type = none := by
  cases type <;> simp_all [SType.scalarSupported, referenceLocation]

private theorem scalar_placed (formed : Static.wellFormed registry type = true)
    (sized : storageBytes type = some bytes) (fuel : Nat) (memory : Bool) :
    eligibleFrom registry (fuel + 2) (if memory then .memory 0 else .storage 0) [] [] type = .ok () := by
  cases memory <;> simp [eligibleFrom, formed, sized] <;>
    intro impossible <;> change false = true at impossible <;> cases impossible

private theorem scalar_eligible (supported : type.scalarSupported = true)
    (formed : Static.wellFormed registry type = true) (fuel : Nat) :
    eligibleType registry (fuel + 2) type = .ok () := by
  obtain ⟨bytes, sized⟩ := scalar_bytes supported
  have placed : eligibleFrom registry (fuel + 2) (.storage 0) [] [] type = .ok () := by
    simpa using (scalar_placed formed sized fuel false)
  have extent := storageSize_scalar registry (fuel + 1) type sized
  change eligibleAt registry (fuel + 2)
    (match referenceLocation type with
      | some .memory => .memory 0
      | some .calldata => .calldata 0
      | _ => .storage 0) type = .ok ()
  rw [scalar_location supported]
  change (do
    eligibleFrom registry (fuel + 2) (.storage 0) [] [] type
    let _ ← storageSize registry (fuel + 2) type
    pure ()) = .ok ()
  rw [placed, extent]
  rfl

private theorem array_placed (registry : Registry) (fuel : Nat) (pointer : Bool) :
    eligibleFrom registry (fuel + 2) (.memory 0) [] [] (WordArena.arrayType pointer) = .ok () := by
  change (do
    eligibleFrom registry (fuel + 1) (.memory 0) [] [] (.uint 31)
    pure ()) = .ok ()
  have leaf : eligibleFrom registry (fuel + 1) (.memory 0) [] [] (.uint 31) = .ok () := rfl
  rw [leaf]
  rfl

/-- Static readiness of a profile type suffices for the real placement check.
The bound covers the array node and its scalar word element, not merely an
interpreter transition allowance. -/
theorem eligible_total (ready : TypeReady registry type) (fuel : Nat) :
    eligibleType registry (fuel + 2) type = .ok () := by
  rcases ready with ⟨supported, formed⟩
  rcases supported with scalar | ⟨pointer, rfl⟩
  · exact scalar_eligible scalar formed fuel
  · change (do
      eligibleFrom registry (fuel + 2) (.memory 0) [] [] (WordArena.arrayType pointer)
      pure ()) = .ok ()
    rw [array_placed]
    rfl

theorem memoryEligible_total (ready : TypeReady registry type) (fuel : Nat) :
    Defaults.memoryEligible registry (fuel + 2) type = .ok () := by
  rcases ready with ⟨supported, formed⟩
  rcases supported with scalar | ⟨pointer, rfl⟩
  · obtain ⟨bytes, sized⟩ := scalar_bytes scalar
    have placed : eligibleFrom registry (fuel + 2) (.memory 0) [] [] type = .ok () := by
      simpa using (scalar_placed formed sized fuel true)
    change (do
      eligibleFrom registry (fuel + 2) (.memory 0) [] [] type
      pure ()) = .ok ()
    rw [placed]
    rfl
  · change (do
      eligibleFrom registry (fuel + 2) (.memory 0) [] [] (WordArena.arrayType pointer)
      pure ()) = .ok ()
    rw [array_placed]
    rfl

end Solidity.Execution.Safety.SupportedEligibility
