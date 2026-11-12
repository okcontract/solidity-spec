/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Access
import Solidity.Core.Aggregates.Memory

/-! Finite value snapshots used by explicit aggregate copies. A reference
assignment itself does not call this materializer. Mappings are never enumerated
or converted into a finite list of observed keys. -/
namespace Solidity.Aggregates
open Core Static

inductive Contents where
  | scalar (value : Value)
  | bytes (string : Bool) (value : List UInt8)
  | array (element : SType) (values : List Contents)
  | structure (identity : Nat) (values : List Contents)

private def checkCopyLength (copy : Bool) (count : Nat) (bytes dynamic : Bool) : Result Unit := do
  if copy then
    let _ ← MemoryOps.arraySize count bytes dynamic
    return ()
  else return ()

def snapshotWithPolicy (copy : Bool) (registry : Registry) : Nat → Nat → Heap → Place → Result (Contents × Nat)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, budget, heap, place => do
      Access.validate heap place
      match place.type with
      | .array element _ _ _ =>
          let count ← Access.length heap place
          checkCopyLength copy count false (match place.type with | .array _ none _ _ => true | _ => false)
          let budget ← reserve budget (count+1)
          let (values, remaining) ← (List.range count).foldlM (fun (values, budget) index => do
            let child ← Access.index registry fuel heap place index
            let (value, budget) ← snapshotWithPolicy copy registry fuel budget heap child
            return (value :: values, budget)) ([], budget)
          return (.array element values.reverse, remaining)
      | .bytes location pointer | .string location pointer =>
          let count ← Access.length heap place
          checkCopyLength copy count true true
          let budget ← reserve budget (count+1)
          let bytesPlace : Place := ⟨.bytes location pointer, place.reference⟩
          let values ← (List.range count).mapM (fun index => do
            let child ← Access.index registry fuel heap bytesPlace index
            let byte ← readScalar heap child
            match child.type, byte with
            | .fixedBytes width, byte =>
                if width = 0 then return byte.toNat.toUInt8 else throw .rejected
            | _, _ => throw .rejected)
          return (.bytes (match place.type with | .string _ _ => true | _ => false) values, budget)
      | .structType identity _ _ =>
          let some fields := registry.structFields identity |
            throw (.invalidContext "missing struct definition during copy")
          let budget ← reserve budget (fields.length+1)
          let (values, remaining) ← (List.range fields.length).foldlM (fun (values, budget) index => do
            let child ← Access.field registry fuel heap place index
            let (value, budget) ← snapshotWithPolicy copy registry fuel budget heap child
            return (value :: values, budget)) ([], budget)
          return (.structure identity values.reverse, remaining)
      | .mapping _ _ => throw .rejected
      | _ =>
          let budget ← reserve budget 1
          return (.scalar (← Access.read heap place), budget)

/-- Raw read-only inspection may run on arbitrary word-sized lengths, with
host allowance reported separately. Materialization additionally checks every
nested native allocation length before constructing its host traversal. -/
def snapshot (registry : Registry) := snapshotWithPolicy false registry

def snapshotForCopy (registry : Registry) := snapshotWithPolicy true registry

theorem snapshot_exhausted (registry : Registry) (budget : Nat) (heap : Heap) (place : Place) :
    snapshot registry 0 budget heap place = .error .exhausted := rfl

/-- Materialization is read-only: its result contains values and remaining
allowance, never a mutated heap that could hide copy-source side effects. -/
def snapshotSource (registry : Registry) (fuel budget : Nat) (heap : Heap) (place : Place) :
    Result (Contents × Heap × Nat) := do
  let (value, remaining) ← snapshot registry fuel budget heap place
  return (value, heap, remaining)

theorem snapshot_preserves_heap
    (finished : snapshotSource registry fuel budget heap place = .ok (value, after, remaining)) :
    after = heap := by
  unfold snapshotSource at finished
  cases h : snapshot registry fuel budget heap place with
  | error failure => simp [h, bind, Except.bind] at finished
  | ok result =>
      rcases result with ⟨contents, rest⟩
      simp [h, bind, Except.bind] at finished
      exact (congrArg (fun result : Contents × Heap × Nat => result.2.1)
        (Except.ok.inj finished)).symm

end Solidity.Aggregates
