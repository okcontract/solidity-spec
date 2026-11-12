/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.DeclarationLayout

namespace Solidity.Aggregates.DeclarationLayout.Tests
open Static

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun a b =>
  match a, b with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }

private def bundle : List (Nat × List StorageDeclaration) := [
  (1, [⟨"baseFlag", .bool, .persistent⟩, ⟨"constantWord", .uint 31, .constant⟩]),
  (2, [⟨"derivedFlag", .bool, .persistent⟩, ⟨"temporary", .uint 31, .transient⟩])]

private def positions : Result (List (Nat × String × Nat × Nat)) := do
  let layout ← checkedDeclarationLayout registry 20 10 bundle
  return layout.fields.map fun field =>
    (field.contract, field.declaration.name, field.position.slot, field.position.byte.val)

example : positions = .ok [(1, "baseFlag", 10, 0), (2, "derivedFlag", 10, 1),
    (2, "temporary", 0, 0)] := by decide +kernel

example : (checkedDeclarationLayout registry 20 0 [(1, [
    ⟨"wrongRegion", .array (.uint 0) none .memory false, .persistent⟩])]).isOk = false := by decide +kernel
example : (checkedDeclarationLayout registry 20 0 [(1, [
    ⟨"transientArray", .array (.uint 0) none .storage false, .transient⟩])]).isOk = false := by decide +kernel
example : (checkedDeclarationLayout registry 20 0 [(1, [
    ⟨"unknownStruct", .structType 1 .storage false, .persistent⟩])]).isOk = false := by decide +kernel
example : (checkedDeclarationLayout registry 20 (2^256) bundle).isOk = false := by decide +kernel

end Solidity.Aggregates.DeclarationLayout.Tests
