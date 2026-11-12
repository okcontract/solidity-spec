/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Progress

namespace Solidity.Execution.Safety.Tests
open Static Aggregates
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def registry : Registry := {
  enumerations := fun _ => none,valueTypes := fun _ => none,
  contracts := fun _ => none,structures := fun _ => false }
private def program : Program EmptyKey := ⟨[]⟩
private def state (budget : Nat) : MachineState Unit := {
  external := (),heap := MemoryOps.initialHeap,materializationRemaining := budget }
private def allocate (count budget : Nat) : Config Unit EmptyKey :=
  ⟨.apply (.newArray (.uint 31)) [.atom ⟨.uint 31,BitVec.ofNat 256 count⟩],[],state budget,state budget⟩
private def tag : Progress (Config Unit EmptyKey) (Observation Unit) → Nat
  | .next _ => 0 | .suspended _ => 1 | .done (.returned _ _) => 2
  | .done (.failed _ _) => 3 | .done (.inconclusive _ _) => 4 | .done (.resourceLimit _ _) => 5
private def panic : Progress (Config Unit EmptyKey) (Observation Unit) → Option UInt8
  | .done (.failed (.panic code) _) => some code | _ => none

-- Enough transition fuel cannot repair insufficient aggregate traversal fuel
-- or materialization work. These are host suspensions, never source reverts.
example : tag (Machine.step physicalBackend registry ⟨1,none⟩ program 0 (allocate 1 162)) = 1 := by decide +kernel
example : tag (Machine.step physicalBackend registry ⟨2,none⟩ program 0 (allocate 1 161)) = 1 := by decide +kernel
example : tag (Machine.step physicalBackend registry ⟨2,none⟩ program 0 (allocate 1 162)) = 0 := by decide +kernel
-- The native extent panic precedes host work for this oversized allocation.
example : panic (Machine.step physicalBackend registry ⟨2,none⟩ program 0 (allocate (2^64) 0)) = some 0x41 := by decide +kernel

/-- A mode frame cannot consume a captured target. This excludes the genuinely
invalid artificial configuration exposed by the final composition review. -/
example (target : Execution.Target EmptyKey) :
    ¬ConfigurationRep registry program ⟨.target target,.mode mode :: stack,current,entry⟩ := by
  rintro ⟨witness⟩
  rcases witness with ⟨_,objects,environment,resultEnvironment,kind,_,taskRep,stackRep,_⟩
  cases taskRep with
  | target represented =>
      cases stackRep with
      | cons frame continuation =>
          cases frame with
          | mode permitted => exact permitted

-- Arbitrary reference literals are outside the source profile; references
-- enter through represented locals, actual defaults/construction and access.
example : ¬Profile.Expression program (.literal ⟨WordArena.arrayType true,reference⟩) := by
  intro form
  cases form with
  | literal supported _ => cases supported

end Solidity.Execution.Safety.Tests
