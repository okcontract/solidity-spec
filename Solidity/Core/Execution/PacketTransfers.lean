/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Effects

/-! Implicit conversions of already evaluated tuple groups. Component effects
have completed before this stage starts. Grouping is represented by Datum,
never by a fabricated SType.tuple.Value. Atomic conversion remains exactly the
existing effect adapter, including its failure and resource behavior. -/
namespace Solidity.Execution.PacketTransfers
open Static
open Aggregates (Heap Result)

abbrev Convert := Nat → Heap → SType → Datum → Result (Datum × Heap × Nat)

def packet (convert : Convert) : Nat → Heap → Types → Packet → Result (Packet × Heap × Nat)
  | budget, heap, .nil, [] => .ok ([], heap, budget)
  | budget, heap, .cons target targets, source :: sources => do
      let (value, heap, remaining) ← convert budget heap target source
      let (values, heap, remaining) ← packet convert remaining heap targets sources
      return (value :: values, heap, remaining)
  | _, _, _, _ => .error .rejected

def transfer (registry : Registry) : Nat → Nat → Heap → ConversionMode → SType → Datum →
    Result (Datum × Heap × Nat)
  | fuel, budget, heap, mode, target, .atom source => do
      let (value, heap, remaining) ← Effects.convert registry fuel budget heap mode target source
      return (.atom value, heap, remaining)
  | fuel, budget, heap, mode, target, .tuple sources =>
      match mode, target with
      | .implicit, .tuple targets =>
          match fuel with
          | 0 => .error .exhausted
          | fuel + 1 => do
              let (values, heap, remaining) ← packet
                (fun budget heap target source => transfer registry fuel budget heap .implicit target source)
                budget heap targets sources
              return (.tuple values, heap, remaining)
      | _, _ => .error .rejected

@[simp] theorem transfer_atom (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (mode : ConversionMode) (target : SType) (source : Value) :
    transfer registry fuel budget heap mode target (.atom source) = (do
      let (value, heap, remaining) ← Effects.convert registry fuel budget heap mode target source
      return (.atom value, heap, remaining)) := by cases fuel <;> rfl

theorem explicit_group_rejected (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (kind : CastKind) (target : SType) (sources : Packet) :
    transfer registry fuel budget heap (.explicit kind) target (.tuple sources) = .error .rejected := by
  cases fuel <;> rfl

theorem group_exhausted (registry : Registry) (budget : Nat) (heap : Heap)
    (targets : Types) (sources : Packet) :
    transfer registry 0 budget heap .implicit (.tuple targets) (.tuple sources) = .error .exhausted := rfl

end Solidity.Execution.PacketTransfers
