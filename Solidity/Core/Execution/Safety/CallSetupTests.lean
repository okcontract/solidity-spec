/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.CallSetup

namespace Solidity.Execution.Safety.CallSetup.Tests
open Static Aggregates
open Contract.Interaction (Word wordBytes)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def registry : Registry := {
  enumerations := fun _ => none,valueTypes := fun _ => none,
  contracts := fun _ => none,structures := fun _ => false }
private def initial : MachineState Unit := {
  external := (),heap := MemoryOps.initialHeap,materializationRemaining := 0 }
private def parameters : List Binder := [⟨0,.uint 31,none⟩,⟨1,WordArena.arrayType true,none⟩]
private def returns : List Binder := [⟨2,.bool,none⟩,⟨3,WordArena.arrayType false,none⟩]
private def arguments : Packet := [.atom ⟨.uint 0,37⟩,
  .atom ⟨WordArena.arrayType false,Copy.memoryReference initial.heap 96⟩]

private def setup (fuel : Nat) : Aggregates.Result (MachineState Unit) := do
  let (arguments,prepared) ← Machine.prepareArguments registry ⟨fuel,none⟩ initial
    (parameters.map Binder.type) arguments
  let bound ← Machine.bindArguments physicalBackend registry ⟨fuel,none⟩ prepared parameters arguments
  returns.foldlM (Machine.declareReturn registry ⟨fuel,none⟩) bound

private def summary : Aggregates.Result (MachineState Unit) → Option (List Nat)
  | .error _ => none
  | .ok state => do
      let ⟨.uint _,word⟩ ← (state.locals.read 0 (.uint 31)).toOption | none
      let ⟨.array _ _ _ _,array⟩ ← (state.locals.read 1 (WordArena.arrayType true)).toOption | none
      let ⟨.bool,boolean⟩ ← (state.locals.read 2 .bool).toOption | none
      let ⟨.array _ _ _ _,empty⟩ ← (state.locals.read 3 (WordArena.arrayType false)).toOption | none
      return [word.toNat,array.address.toNat,if boolean then 1 else 0,empty.address.toNat,
        state.heap.nextMemory,state.materializationRemaining] ++ state.locals.flatten.map Prod.fst

/-- Widening, canonical aliasing and initialized defaults require no host
materialization allowance. Runtime cells retain reverse declaration order. -/
example : summary (setup 2) = some [37,96,0,96,128,0,3,2,1,0] := by decide +kernel
example : (setup 1).toOption.isNone = true := by decide +kernel

private def signature (mode : Mutability) : SType := .function .internal mode .nil .nil
private def functionPrepared : Option (Option Nat) :=
  match Machine.prepareArguments registry ⟨2,none⟩ initial [signature .view]
      [.atom ⟨signature .pure,some 7⟩] with
  | .ok ([.atom ⟨.function .internal _ _ _,handle⟩],_) => some handle
  | _ => none
example : functionPrepared = some (some 7) := by decide +kernel

private def nullDefault : Option (Option Nat) := do
  let after ← (Machine.declareReturn registry ⟨2,none⟩ initial ⟨5,signature .view,none⟩).toOption
  let ⟨.function .internal _ _ _,handle⟩ ← (after.locals.read 5 (signature .view)).toOption | none
  return handle
example : nullDefault = some none := by decide +kernel

private def duplicateRejected : Bool :=
  match Machine.bindArguments physicalBackend registry ⟨2,none⟩ initial
      [⟨0,.uint 31,none⟩,⟨0,.bool,none⟩] [.atom ⟨.uint 0,37⟩,.atom ⟨.bool,true⟩] with
  | .error (.invalidContext _) => true
  | _ => false
example : duplicateRejected = true := by decide +kernel

private def mutableAlias : Option (Nat × Nat) := do
  let (array,heap,_) ← (Defaults.newArray registry 2 162 initial.heap (.uint 31) 1).toOption
  let source ← array.reference
  let bound ← (Machine.bindArguments physicalBackend registry ⟨2,none⟩ {initial with heap}
    [⟨1,WordArena.arrayType true,none⟩] [.atom array]).toOption
  let ⟨.array _ _ _ _,reference⟩ ← (bound.locals.read 1 (WordArena.arrayType true)).toOption | none
  let cell ← (Access.index registry 2 bound.heap ⟨WordArena.arrayType true,reference⟩ 0).toOption
  let after ← (Access.write bound.heap cell ⟨.uint 31,91⟩).toOption
  let original ← (Access.index registry 2 after ⟨WordArena.arrayType true,source⟩ 0).toOption
  let ⟨.uint _,value⟩ ← (Access.read after original).toOption | none
  return (value.toNat,bound.materializationRemaining)
example : mutableAlias = some (91,0) := by decide +kernel

private theorem initial_rep : HeapRep initial.heap [] := by
  refine ⟨⟨MemoryOps.initialHeap_allocationContext _ _,?_,by simp,by simp⟩,by decide +kernel⟩
  have packet : wordBytes (0 : Word) = List.replicate 32 0 := by decide +kernel
  exact (MemoryOps.initialHeap_zeroSlot _ _).trans packet.symm

/-- A concrete use of universal setup derives execution and represented
initialized cells from physical input, without an operation-success premise. -/
example : ∃ bound entered,
    Machine.bindArguments physicalBackend registry ⟨2,none⟩
      {initial with locals := Locals.empty,mode := .checked} parameters
      [.atom ⟨.uint 31,37⟩,.atom ⟨WordArena.arrayType true,Copy.memoryReference initial.heap 96⟩] = .ok bound ∧
    returns.foldlM (Machine.declareReturn registry ⟨2,none⟩) bound = .ok entered ∧
    StateRep ({} : Program EmptyKey) []
      [((parameters ++ returns).map fun binder => (binder.id,binder.type)).reverse] entered ∧
    entered.external = initial.external ∧ entered.heap = initial.heap ∧ entered.mode = .checked ∧
    entered.materializationRemaining = initial.materializationRemaining := by
  exact initializeFunction_total physicalBackend ({} : Program EmptyKey) registry 0 initial [] parameters returns _
    (by intro binder member; simp only [parameters,returns,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with ((rfl | rfl) | (rfl | rfl)) <;> exact ⟨by first | exact .inl rfl | exact .inr ⟨_,rfl⟩,rfl⟩)
    initial_rep (.cons (.atom (ValueRep.word _ _ _ 37)) (.cons (.atom (.emptyArray true)) .nil))
    (by decide +kernel)

end Solidity.Execution.Safety.CallSetup.Tests
