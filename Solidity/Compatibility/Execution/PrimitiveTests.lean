/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Primitives
import Solidity.Proofs.Storage

namespace Solidity.Execution.Compatibility.Tests
open Core Static
open Compiler.Validation
open Contract.Interaction (Word)

set_option maxRecDepth 16384
set_option maxHeartbeats 800000

private def answer : Aggregates.Result α → Option α
  | .ok value => some value
  | .error _ => none

private def failure : Aggregates.Result α → Option Aggregates.Failure
  | .ok _ => none
  | .error value => some value

private def variables : SolidityStorage.Layout := [⟨"first", .boolean⟩, ⟨"second", .boolean⟩]

private def source : SolidityFunction.Source :=
  {name := "f", parameters := [], body := .literal 0, checked := true}

private def dirty : Contract.Evm.Stateful.Slots := fun _ => 0x0502

private def legacyStore (static : Bool := false) :=
  Solidity.Compatibility.Storage.store variables source {} static

/-- Existing source certificates quantify over dirty words too. The old codec
cleans a nonzero Boolean byte rather than requiring a typed-store invariant. -/
example : answer ((read legacyStore dirty (.read (.name "first"))).map
    (fun value => (coreValue .word value).toNat)) = some 1 := by
  decide +kernel

private def clearFirst : Aggregates.Result Nat := do
  let after ← write legacyStore dirty
    (.place (Solidity.Compatibility.Storage.Place.boolField 0)) (scalarValue .bool false)
  return (after 0).toNat

/-- The neighboring dirty byte survives canonicalization of the written byte. -/
example : answer clearFirst = some 0x0500 := by decide +kernel

example : failure (write (legacyStore true) dirty
    (.place (Solidity.Compatibility.Storage.Place.boolField 0)) (scalarValue .bool false)) =
      some .exceptional := by decide +kernel

example : failure (read legacyStore dirty
    (.place (Solidity.Compatibility.Storage.Place.boolField 0))) =
      some (.invalidContext "legacy write place has no read codec") := by decide +kernel

inductive Logical : Core.Ty → Type where
  | cell : Nat → Logical .word

private def logicalStore : Core.Store Logical Logical (Nat → Word) where
  read cells := fun {_} reference => match reference with | .cell index => cells index
  write cells := fun {_} place value => match place with
    | .cell index => some (fun selected => if selected = index then value else cells selected)

private def distinctLogicalSlots : Aggregates.Result (Nat × Nat) := do
  let after ← write logicalStore (fun _ => 8) (.place (.cell (2^256+1))) (scalarValue .word 9)
  let near ← read logicalStore after (.read (.cell 1))
  let far ← read logicalStore after (.read (.cell (2^256+1)))
  return (near.toNat, far.toNat)

/-- The generic legacy-state guarantee has no implicit Word-address quotient.
A physical heap correspondence is an additional, separately checked bridge. -/
example : answer distinctLogicalSlots = some (8, 9) := by decide +kernel

end Solidity.Execution.Compatibility.Tests
