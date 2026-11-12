/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.PacketTransfers
import Solidity.Core.Execution.EffectsLaws
import Solidity.Core.Execution.ConstructorLaws

namespace Solidity.Execution.PacketTransfers
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem retag_type (tagged : Copy.retag type reference = .ok value) : value.type = type := by
  cases type <;> simp only [Copy.retag, referenceValue, Bind.bind, Except.bind, Pure.pure, Except.pure] at tagged <;>
    cases tagged <;> rfl

private theorem valueRep_type (represented : Copy.ValueRep registry heap lower type contents value) : value.type = type := by
  cases contents with
  | scalar source => exact Copy.convertScalar_type represented
  | array _ _ | «structure» _ _ | bytes _ _ =>
      obtain ⟨_, tagged, _⟩ := represented
      exact retag_type tagged

private theorem bind_type (valid : MemoryOps.validFrontier heap = true)
    (bound : Copy.bind registry fuel budget heap type source = .ok (value, after, remaining)) : value.type = type := by
  unfold Copy.bind at bound
  cases planned : planTransfer registry fuel true source.type type with
  | error failure => simp [planned] at bound
  | ok kind =>
      simp only [planned, Bind.bind, Except.bind] at bound
      cases kind with
      | scalarConversion =>
          change (do let value ← Copy.convertScalar type source; pure (value, heap, budget)) = .ok (value, after, remaining) at bound
          cases converted : Copy.convertScalar type source with
          | error failure => simp [converted] at bound
          | ok convertedValue =>
              simp only [converted, Bind.bind, Except.bind, Pure.pure, Except.pure] at bound
              cases bound
              exact Copy.convertScalar_type converted
      | storageAlias | memoryAlias | calldataAlias =>
          change (do let value ← Copy.alias heap type source; pure (value, heap, budget)) = .ok (value, after, remaining) at bound
          cases aliased : Copy.alias heap type source with
          | error failure => simp [aliased] at bound
          | ok convertedValue =>
              simp only [aliased, Bind.bind, Except.bind, Pure.pure, Except.pure] at bound
              cases bound
              unfold Copy.alias at aliased
              cases extracted : source.reference with
              | none => simp [extracted] at aliased
              | some reference =>
                  simp only [extracted, Bind.bind, Except.bind] at aliased
                  cases checked : Access.validate heap ⟨source.type, reference⟩ with
                  | error failure => simp [checked] at aliased
                  | ok _ =>
                      simp only [checked] at aliased
                      cases extent : checkExtent heap reference 0 with
                      | error failure => simp [extent] at aliased
                      | ok _ => simp only [extent] at aliased; exact retag_type aliased
      | memoryCopy =>
          change (do
            let (contents, allowance) ← Copy.snapshotValue registry fuel budget heap source
            Copy.materializeMemory registry fuel allowance heap type contents) = .ok (value, after, remaining) at bound
          cases frozen : Copy.snapshotValue registry fuel budget heap source with
          | error failure => simp [frozen] at bound
          | ok result =>
              rcases result with ⟨contents, allowance⟩
              simp only [frozen, Bind.bind, Except.bind] at bound
              exact valueRep_type (Copy.materializeMemory_rep valid bound)
      | storageCopy => cases bound

def Frame (before after : Heap) : Prop :=
  after.execution.world = before.execution.world ∧ after.invocation = before.invocation ∧
    MemoryOps.validFrontier after = true

def Correct (target : SType) (before : Heap) (value : Datum) (after : Heap) : Prop :=
  value.type = target ∧ Frame before after

private theorem convert_correct (valid : MemoryOps.validFrontier heap = true)
    (converted : Effects.convert registry fuel budget heap mode target source = .ok (value, after, remaining)) :
    value.type = target ∧ Frame heap after := by
  cases mode with
  | implicit =>
      exact ⟨bind_type valid converted, (Copy.bind_frame converted).1, (Copy.bind_frame converted).2,
        (Constructors.bind_extension converted).valid valid⟩
  | explicit kind =>
      cases kind with
      | ordinary =>
          simp only [Effects.convert] at converted
          split at converted
          · cases casted : ReferenceCasts.cast registry fuel budget heap target source with
            | error failure => simp [casted] at converted
            | ok result =>
                rcases result with ⟨result, remaining⟩
                simp only [casted, Bind.bind, Except.bind, Pure.pure, Except.pure] at converted
                cases converted
                exact ⟨ReferenceCasts.cast_type casted, rfl, rfl, valid⟩
          · cases casted : Effects.scalarCast (.explicit .ordinary) target source with
            | error failure => simp [casted] at converted
            | ok result =>
                simp only [casted, Bind.bind, Except.bind, Pure.pure, Except.pure] at converted
                cases converted
                exact ⟨Effects.scalarCast_type casted, rfl, rfl, valid⟩
      | payable =>
          simp only [Effects.convert] at converted
          cases casted : Effects.scalarCast (.explicit .payable) target source with
          | error failure => simp [casted] at converted
          | ok result =>
              simp only [casted, Bind.bind, Except.bind, Pure.pure, Except.pure] at converted
              cases converted
              exact ⟨Effects.scalarCast_type casted, rfl, rfl, valid⟩

private theorem packet_correct (convert : Convert)
    (leaf : ∀ budget heap target source value after remaining,
      MemoryOps.validFrontier heap = true → convert budget heap target source = .ok (value, after, remaining) →
        Correct target heap value after)
    (valid : MemoryOps.validFrontier heap = true)
    (converted : packet convert budget heap targets sources = .ok (values, after, remaining)) :
    packetTypes values = targets ∧ Frame heap after := by
  induction sources generalizing targets heap budget values after remaining with
  | nil =>
      cases targets with
      | nil => cases converted; exact ⟨rfl, rfl, rfl, valid⟩
      | cons _ _ => cases converted
  | cons source sources ih =>
      cases targets with
      | nil => cases converted
      | cons target targets =>
          simp only [packet] at converted
          cases head : convert budget heap target source with
          | error failure => simp [head] at converted
          | ok result =>
              rcases result with ⟨value, middle, allowance⟩
              have first := leaf budget heap target source value middle allowance valid head
              simp only [head, Bind.bind, Except.bind] at converted
              cases tail : packet convert allowance middle targets sources with
              | error failure => simp [tail] at converted
              | ok result =>
                  rcases result with ⟨rest, final, left⟩
                  have last := ih first.2.2.2 tail
                  simp only [tail, Pure.pure, Except.pure] at converted
                  cases converted
                  exact ⟨by simp only [packetTypes, first.1, last.1],
                    last.2.1.trans first.2.1, last.2.2.1.trans first.2.2.1, last.2.2.2⟩

theorem transfer_correct (registry : Registry) (fuel : Nat) :
    ∀ budget heap mode target source value after remaining,
      MemoryOps.validFrontier heap = true →
      transfer registry fuel budget heap mode target source = .ok (value, after, remaining) →
      Correct target heap value after := by
  induction fuel with
  | zero =>
      intro budget heap mode target source value after remaining valid converted
      cases source with
      | atom source =>
          rw [transfer_atom] at converted
          cases leaf : Effects.convert registry 0 budget heap mode target source with
          | error failure => simp [leaf] at converted
          | ok result =>
              rcases result with ⟨result, next, available⟩
              simp only [leaf, Bind.bind, Except.bind, Pure.pure, Except.pure] at converted
              cases converted
              exact convert_correct valid leaf
      | tuple sources => cases mode <;> cases target <;> cases converted
  | succ fuel ih =>
      intro budget heap mode target source value after remaining valid converted
      cases source with
      | atom source =>
          rw [transfer_atom] at converted
          cases leaf : Effects.convert registry (fuel + 1) budget heap mode target source with
          | error failure => simp [leaf] at converted
          | ok result =>
              rcases result with ⟨result, next, available⟩
              simp only [leaf, Bind.bind, Except.bind, Pure.pure, Except.pure] at converted
              cases converted
              exact convert_correct valid leaf
      | tuple sources =>
          cases mode <;> cases target <;> try cases converted
          case implicit.tuple targets =>
            simp only [transfer] at converted
            cases grouped : packet
                (fun budget heap target source => transfer registry fuel budget heap .implicit target source)
                budget heap targets sources with
            | error failure => simp [grouped] at converted
            | ok result =>
                rcases result with ⟨results, next, available⟩
                have packetLaws := packet_correct _
                  (fun budget heap target source value after remaining valid converted =>
                    ih budget heap .implicit target source value after remaining valid converted) valid grouped
                simp only [grouped, Bind.bind, Except.bind, Pure.pure, Except.pure] at converted
                cases converted
                exact ⟨congrArg SType.tuple packetLaws.1, packetLaws.2⟩

end Solidity.Execution.PacketTransfers
