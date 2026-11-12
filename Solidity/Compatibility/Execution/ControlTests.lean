/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Control

namespace Solidity.Execution.Compatibility.Tests
open Core Static
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

/- Retained legacy fixtures belong to the compatibility tests. Their original
computations and assertions stay independent of the migrated primary corpus. -/
private abbrev LoopTypes : List Ty := [.uint 0]
private abbrev LoopRef := Var LoopTypes

private def loopStore : Store LoopRef LoopRef (Env LoopTypes) where
  read state := state.get
  write state := fun {_} place value => some (state.set place value)

private def increment : Block LoopRef LoopRef := .assign .here
  (.binary (.uintArithmetic 0 .checked .add) (.read .here) (.literal 1))
private def belowThree : Core.Expr LoopRef .bool :=
  .binary (.uintCompare 0 .lt) (.read .here) (.literal 3)

private def loopOutcomes (command : Control.Command LoopRef LoopRef) (initial : BitVec 8 := 0) :
    List (Result (BitVec 256)) :=
  let registry : Static.Registry := {
    enumerations := fun _ => none, valueTypes := fun _ => none,
    contracts := fun _ => none, structures := fun _ => false }
  let state : Execution.MachineState (Env LoopTypes) := {external := .cons initial .nil}
  match Execution.Machine.execute (Execution.Compatibility.backend loopStore) registry
      Execution.Compatibility.legacyLimits {} 10000 []
      (Execution.Config.start state (Execution.Compatibility.controlBody command)) with
  | .finished observed => match Execution.Compatibility.controlObservation observed with
    | some (.completed (.next (.cons value .nil))) => [.ok (BitVec.ofNat 256 value.toNat)]
    | some (.completed (.halt (.reverted bytes))) => [.error bytes]
    | _ => []
  | _ => []

private def resultView (values : List (Core.Result (BitVec 256))) : List (Bool × List UInt8 × Nat) :=
  values.map fun | .ok value => (true, [], value.toNat) | .error bytes => (false, bytes, 0)

example : resultView (loopOutcomes (.loop belowThree (.block increment) .skip)) = [(true, [], 3)] := by decide +kernel
example : resultView (loopOutcomes (.loop belowThree .continue_ increment)) = [(true, [], 3)] := by decide +kernel
example : resultView (loopOutcomes (.loop (.literal true) .break_ increment)) = [(true, [], 0)] := by decide +kernel
example : resultView (loopOutcomes (.loop belowThree (.loop (.literal true) .break_ .skip) increment)) = [(true, [], 3)] := by decide +kernel
example : resultView (loopOutcomes (.loop (.literal true) (.block increment) .skip) 254) = [(false, Contract.panic 0x11, 0)] := by decide +kernel

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }

private def runControl (body : Core.Control.Command LoopRef LoopRef) (fuel : Nat := 1000) :=
  let state : MachineState (Core.Env LoopTypes) := {external := .cons 0 .nil}
  Machine.execute (backend loopStore) registry legacyLimits {} fuel [] (Config.start state (controlBody body))

private def observed (body : Core.Control.Command LoopRef LoopRef) : Option (Core.Control.Observation (Core.Env LoopTypes)) :=
  match runControl body with
  | .finished result => controlObservation result
  | .exhausted _ _ => none

/-- A return skips both the increment and the remaining outer statement. -/
example : observed (.seq (.loop (.literal true) (.block (.ret (.literal 7))) increment)
    (.block (.revert [42]))) = some (.completed (.halt (.returned (Contract.Interaction.wordBytes 7) (.cons 0 .nil)))) := by
  rfl

example : observed (.loop (.literal true) (.block (.revert [9])) increment) =
    some (.completed (.halt (.reverted [9]))) := by rfl

example : observed (.seq .break_ (.block increment)) = some .invalidControl := by rfl
example : observed .continue_ = some .invalidControl := by rfl

example : (match runControl (.loop (.literal true) (.block .skip) .skip) 12 with
    | .exhausted _ _ => true | _ => false) = true := by decide +kernel

/-- The universal bridge consumes a finite relational proof, rather than a
particular target fuel bound. This instance includes a continue/post cycle. -/
example : ∃ result, Executes (transition (backend loopStore) registry {})
    (Config.start ({external := .cons 0 .nil} : MachineState (Core.Env LoopTypes))
      (controlBody (.loop belowThree .continue_ increment))) result ∧
    controlObservation result = some (.completed (.next (.cons 3 .nil))) := by
  apply control_machine loopStore registry {} _ _
  exact Core.Control.run_sound loopStore .leftFirst 100 _ _ (by rfl)

end Solidity.Execution.Compatibility.Tests
