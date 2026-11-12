/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Layout

namespace Solidity.Aggregates.LayoutTests
open Static Core

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun _ => none
  valueTypes := fun _ => none
  contracts := fun _ => none
  structures := fun identity => [1, 2, 3, 4, 5, 6, 7, 8, 9].contains identity
  structFields := fun identity => match identity with
    | 1 => some [("a", .uint 1), ("b", .uint 1), ("c", .uint 31)]
    | 2 => some [("x", .sint 3), ("y", .bool)]
    | 3 => some [("cycle", .structType 3 .storage true)]
    | 4 => some [("children", .array (.structType 4 .storage true) none .storage true)]
    | 5 => some [("children", .array (.structType 5 .storage true) none .storage true),
        ("hidden", .mapping (.uint 31) (.uint 31))]
    | 6 => some [("children", .array (.structType 6 .storage true) none .storage true),
        ("hidden", .function .internal .pure .nil .nil)]
    | 7 => some [("missing", .array (.structType 999 .storage true) none .storage true)]
    | 8 => some [("next", .structType 9 .storage true)]
    | 9 => some [("children", .array (.structType 8 .storage true) none .storage true)]
    | _ => none }

example : storageSize registry 16 (.structType 1 .storage true) = .ok 2 := by decide +kernel
example : fieldOffset registry 16 1 0 = .ok (.uint 1, 0, 0) := by decide +kernel
example : fieldOffset registry 16 1 1 = .ok (.uint 1, 0, 2) := by decide +kernel
example : fieldOffset registry 16 1 2 = .ok (.uint 31, 1, 0) := by decide +kernel
example : fieldOffset registry 16 1 3 = .error .rejected := by decide +kernel
example : fieldOffset registry 16 999 0 = .error (.invalidContext "missing resolved struct fields") := by decide +kernel

-- A 24-bit element never crosses a storage word; the top two bytes stay unused.
example : storageSize registry 8 (.array (.uint 2) (some 10) .storage true) = .ok 1 := by decide +kernel
example : storageSize registry 8 (.array (.uint 2) (some 11) .storage true) = .ok 2 := by decide +kernel
example : elementOffset registry 8 (.uint 2) 9 = .ok (0, 27) := by decide +kernel
example : elementOffset registry 8 (.uint 2) 10 = .ok (1, 0) := by decide +kernel
example : elementOffset registry 16 (.structType 1 .storage true) 3 = .ok (6, 0) := by decide +kernel
example : storageSize registry 16 (.array (.structType 1 .memory true) (some 3) .memory true) = .ok 6 := by decide +kernel
example : storageSize registry 8 (.array (.uint 31) (some 0) .storage true) = .error .rejected := by decide +kernel
example : storageSize registry 8 (.array (.uint 31) (some storageLimit) .storage true) = .error .rejected := by decide +kernel
example : storageSize registry 8 (.array (.uint 0) (some storageLimit) .storage true) = .error .rejected := by decide +kernel
example : elementOffset registry 8 (.uint 31) storageLimit = .error .rejected := by decide +kernel

-- Dynamic headers cut storage recursion; a direct recursive static extent is inconclusive.
example : storageSize registry 8 (.structType 3 .storage true) = .error .exhausted := by decide +kernel
example : storageSize registry 8 (.structType 4 .storage true) = .ok 1 := by decide +kernel
example : storageSize registry 0 (.uint 0) = .error .exhausted := by decide +kernel
example : fieldOffset registry 0 1 0 = .error .exhausted := by decide +kernel

example : calldataDynamic registry 16 (.structType 1 .calldata true) = .ok false := by decide +kernel
example : calldataHeadSize registry 16 (.structType 1 .calldata true) = .ok 96 := by decide +kernel
example : calldataHeadSize registry 16 (.array (.structType 1 .calldata true) (some 2) .calldata true) = .ok 192 := by decide +kernel
example : calldataHeadSize registry 8 (.array (.uint 0) (some 10) .calldata true) = .ok 320 := by decide +kernel
example : calldataHeadSize registry 8 (.array (.bytes .calldata true) (some 2) .calldata true) = .ok 32 := by decide +kernel
example : calldataDynamic registry 8 (.mapping (.uint 0) (.uint 0)) = .error .rejected := by decide +kernel
example : calldataDynamic registry 8 (.function .internal .pure .nil .nil) = .error .rejected := by decide +kernel
example : calldataDynamic registry 8 (.array (.bytes .calldata true) (some storageLimit) .calldata true) = .error .rejected := by decide +kernel
example : calldataDynamic registry 8 (.array (.mapping (.uint 0) (.uint 0)) none .calldata true) = .error .rejected := by decide +kernel
example : calldataDynamic registry 8 (.structType 4 .calldata true) = .ok true := by decide +kernel
example : calldataHeadSize registry 8 (.structType 4 .calldata true) = .ok 32 := by decide +kernel
example : calldataDynamic registry 8 (.structType 3 .calldata true) = .error .rejected := by decide +kernel
example : calldataHeadSize registry 8 (.structType 3 .calldata true) = .error .rejected := by decide +kernel
example : calldataDynamic registry 8 (.structType 5 .calldata true) = .error .rejected := by decide +kernel
example : calldataDynamic registry 8 (.structType 6 .calldata true) = .error .rejected := by decide +kernel
example : calldataDynamic registry 8 (.structType 7 .calldata true) =
    .error (.invalidContext "missing resolved struct fields") := by decide +kernel
example : calldataDynamic registry 8 (.structType 8 .calldata true) = .ok true := by decide +kernel
example : calldataHeadSize registry 8 (.structType 8 .calldata true) = .ok 32 := by decide +kernel
example : calldataDynamic registry 1 (.structType 4 .calldata true) = .error .exhausted := by decide +kernel
example : calldataHeadSize registry 0 (.uint 0) = .error .exhausted := by decide +kernel

-- This is the complete layout example from the retained storage-layout reference.
private def declarations : List (Nat × List StorageDeclaration) := [
  (1, [⟨"a", .uint 31, .persistent⟩, ⟨"b", .uint 15, .transient⟩,
    ⟨"c", .uint 31, .constant⟩, ⟨"d", .uint 31, .immutable⟩]),
  (2, [⟨"e", .array (.uint 0) none .storage false, .persistent⟩,
    ⟨"f", .mapping (.uint 31) (.structType 2 .storage false), .persistent⟩,
    ⟨"g", .uint 1, .persistent⟩, ⟨"h", .uint 1, .persistent⟩,
    ⟨"i", .fixedBytes 15, .transient⟩, ⟨"s", .structType 2 .storage false, .persistent⟩,
    ⟨"k", .sint 0, .persistent⟩]),
  (3, [⟨"l", .fixedBytes 20, .persistent⟩,
    ⟨"m", .array (.uint 0) (some 10) .storage false, .persistent⟩,
    ⟨"n", .array (.fixedBytes 4) (some 8) .storage false, .persistent⟩,
    ⟨"o", .fixedBytes 4, .persistent⟩])]

private def positions : Result (List (String × Nat × Nat)) := do
  let layout ← declarationLayout registry 64 42 declarations
  return layout.fields.map fun field =>
    (field.declaration.name, field.position.slot, field.position.byte.val)

example : positions = .ok [
    ("a", 42, 0), ("b", 0, 0), ("e", 43, 0), ("f", 44, 0),
    ("g", 45, 0), ("h", 45, 2), ("i", 0, 16), ("s", 46, 0),
    ("k", 47, 0), ("l", 47, 1), ("m", 48, 0), ("n", 49, 0), ("o", 51, 0)] := by decide +kernel

example : (declarationLayout registry 8 42 [
    (1, [⟨"base", .uint 0, .persistent⟩]),
    (2, [⟨"derived", .uint 0, .persistent⟩])]).map
      (fun layout => layout.fields.map (fun field => (field.position.slot, field.position.byte.val))) =
    .ok [(42, 0), (42, 1)] := by decide +kernel

example : declarationLayout registry 8 0 [(1, [⟨"bad", .bytes .storage false, .transient⟩])] =
    .error .rejected := by decide +kernel

-- Neither a custom base nor an aggregate extent may wrap past the checked layout domain.
example : declarationLayout registry 8 storageLimit [] = .error .rejected := by decide +kernel
example : declarationLayout registry 8 (storageLimit - 1) [(1, [⟨"last", .uint 0, .persistent⟩])] =
    .error .rejected := by decide +kernel
example : declarationLayout registry 8 0 [(1, [⟨"huge", .array (.uint 31) (some storageLimit) .storage false, .persistent⟩])] =
    .error .rejected := by decide +kernel

end Solidity.Aggregates.LayoutTests
