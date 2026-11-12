/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Access
import Solidity.Core.Aggregates.Memory

namespace Solidity.Aggregates.Access.Tests
open Core Static
open Contract.Interaction (Word wordBytes)

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun a b =>
  match a, b with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun id => id == 1
  structFields := fun id => if id == 1 then
    some [("flag", .bool), ("amount", .uint 2), ("values", .array (.uint 0) none .storage false)] else none }

private def root (type : SType) (address : Word := 0) : Place :=
  ⟨type, {region := .storage 0, address}⟩

private def datum (heap : Heap) (place : Place) : Result Nat := do
  let value ← read heap place
  match value.type, value.value with
  | .uint _, value | .sint _, value | .fixedBytes _, value => return value.toNat
  | .bool, value => return if value then 1 else 0
  | _, _ => throw .rejected

private def packedHeap : Heap :=
  {execution := {world := ({} : Contract.Interaction.World).store 0 0 (1 + 7*256)}}

example : (do datum packedHeap (← field registry 20 packedHeap (root (.structType 1 .storage false)) 1)) = .ok 7 := by decide +kernel
example : (do let place ← field registry 20 packedHeap (root (.structType 1 .storage false)) 2
              pure (place.reference.address.toNat, place.reference.byte.val)) = .ok (1, 0) := by decide +kernel

private def arrayPlace : Place := root (.array (.uint 2) none .storage false)
private def arrayHeap : Heap :=
  let world := (({} : Contract.Interaction.World).store 0 0 11).store 0 (dataArea arrayPlace.reference).address (BitVec.ofNat 256 (5 + 8*2^24))
  {execution := {world}}

example : (do datum arrayHeap (← index registry 20 arrayHeap arrayPlace 1)) = .ok 8 := by decide +kernel
example : (do let place ← index registry 20 arrayHeap arrayPlace 10
              pure (place.reference.address == (dataArea arrayPlace.reference).address + 1,
                place.reference.byte.val)) = .ok (true, 0) := by decide +kernel
example : (do let place ← index registry 20 arrayHeap arrayPlace 11
              datum arrayHeap place) = .error (.panic 0x32) := by decide +kernel

private def dangling : Result Unit := do
  let place ← index registry 20 arrayHeap arrayPlace 0
  let after : Heap := {arrayHeap with execution := {arrayHeap.execution with
    world := arrayHeap.execution.world.store 0 0 0}}
  validate after place

example : dangling = .error (.undefinedBehavior "dangling storage reference after array removal") := by decide +kernel

-- Runtime strides wrap even though static declaration extents may not.
private def wrappingStride : Result Bool := do
  let place := root (.array (.array (.uint 31) (some 2) .storage false) none .storage false)
  let heap : Heap := {execution := {world :=
    ({} : Contract.Interaction.World).store 0 0 (BitVec.ofNat 256 (2^255+1))}}
  let child ← index registry 20 heap place (2^255)
  return child.reference.address == (dataArea place.reference).address

example : wrappingStride = .ok true := by decide +kernel

private def calldataNested (bytes : List UInt8) : Heap :=
  {execution := {context := {calldata := bytes}}}

private def nestedCalldata : Place :=
  ⟨.array (.array (.uint 31) none .calldata false) none .calldata false,
    {region := .calldata 0, address := 0}⟩

example : (Access.index registry 20
    (calldataNested (wordBytes 1 ++ wordBytes 32)) nestedCalldata 0).isOk = false := by decide +kernel

private def tailResult (bytes : List UInt8) : Result (Nat × Option Nat) := do
  let child ← Access.index registry 20 (calldataNested bytes) nestedCalldata 0
  return (child.reference.address.toNat, child.reference.viewLength)

-- A complete parent head still requires the selected child's length and heads.
example : tailResult (wordBytes 1 ++ wordBytes 32) = .error (.revert []) := by decide +kernel
example : tailResult (wordBytes 1 ++ wordBytes 32 ++ wordBytes 2) =
    .error (.revert []) := by decide +kernel
example : tailResult (wordBytes 1 ++ wordBytes 32 ++ wordBytes 1 ++ wordBytes 7) =
    .ok (96, some 1) := by decide +kernel

-- Signed offset checks and Word addition permit an in-buffer backward alias.
example : tailResult (wordBytes 1 ++ wordBytes (BitVec.ofNat 256 (2^256-32))) =
    .ok (32, some 1) := by decide +kernel

-- Native-passing synthetic views outside the physical domain are inconclusive.
example : tailResult (wordBytes 1 ++ wordBytes (BitVec.ofNat 256 (2^255))) =
    .error (.invalidContext "native calldata view outside typed physical extent") := by decide +kernel

private def missingParent : Result Place :=
  let place : Place := ⟨.array (.bytes .calldata false) none .calldata false,
    {region := .calldata 0, address := 0, viewLength := some 2}⟩
  Access.index registry 20 (calldataNested (wordBytes 0)) place 1

example : missingParent = .error (.invalidContext
    "source calldata head outside typed physical extent") := by decide +kernel
example : validate packedHeap ⟨.structType 1 .storage false,
    {region := .storage 0, address := 0, byte := 1}⟩ = .error .rejected := by decide +kernel
example : validate packedHeap ⟨.array (.uint 0) none .storage false,
    {region := .transient 0, address := 0}⟩ = .error .rejected := by decide +kernel
example : byteLength 64 = .error (.panic 0x22) := by decide +kernel
example : byteLength 63 = .error (.panic 0x22) := by decide +kernel
example : byteLength 62 = .ok 31 := by decide +kernel
example : byteLength 65 = .ok 32 := by decide +kernel

private def calldataHeap : Heap := {execution := {context := {
  calldata := wordBytes 3 ++ wordBytes 4 ++ wordBytes 5 ++ wordBytes 6}}}
private def calldataPlace : Place := ⟨.array (.uint 0) none .calldata true,
  {region := .calldata 0, address := 0}⟩

example : (do let view ← slice registry 20 calldataHeap calldataPlace 1 3
              datum calldataHeap (← index registry 20 calldataHeap view 0)) = .ok 5 := by decide +kernel
example : (do let view ← slice registry 20 calldataHeap calldataPlace 1 3
              datum calldataHeap (← index registry 20 calldataHeap view 2)) = .error (.panic 0x32) := by decide +kernel
example : (do let view ← slice registry 20 calldataHeap calldataPlace 2 1
              length calldataHeap view) = .error (.revert []) := by decide +kernel
example : (do let view ← slice registry 20 calldataHeap
                ⟨.array (.bytes .calldata false) none .calldata true, calldataPlace.reference⟩ 0 1
              length calldataHeap view) = .error .rejected := by decide +kernel

private def mappingPlace : Place := root (.mapping (.uint 31) (.array (.uint 0) none .storage false)) 7
example : (do let place ← mapping packedHeap mappingPlace (.scalar ⟨.uint 31, 4⟩)
              pure (place.reference.address == Contract.Interaction.mappingKey 4 7)) = .ok true := by decide +kernel

end Solidity.Aggregates.Access.Tests
