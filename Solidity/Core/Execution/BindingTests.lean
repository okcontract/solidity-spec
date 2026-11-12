/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.BindingsLaws
import Solidity.Core.Execution.Syntax

namespace Solidity.Execution.Tests
open Static Aggregates

private def failure : Aggregates.Result α → Option Failure
  | .ok _ => none
  | .error reason => some reason

private def readNat (locals : Locals) (id : Nat) : Aggregates.Result Nat := do
  let value ← locals.read id (.uint 31)
  match value with
  | ⟨.uint _, word⟩ => return word.toNat
  | _ => throw .rejected

private def answer : Aggregates.Result α → Option α
  | .ok value => some value
  | .error _ => none

private def shadow : Aggregates.Result Nat := do
  let outer ← Locals.empty.declare ⟨0, .uint 31, some "x"⟩ (some ⟨.uint 31, 7⟩)
  let inner ← outer.enter.declare ⟨1, .uint 31, some "x"⟩ (some ⟨.uint 31, 9⟩)
  let inner ← inner.write 1 (.uint 31) ⟨.uint 31, 11⟩
  readNat (← inner.leave) 0

private def outerWrite : Aggregates.Result Nat := do
  let outer ← Locals.empty.declare ⟨0, .uint 31, none⟩ (some ⟨.uint 31, 7⟩)
  let inner ← outer.enter.declare ⟨1, .uint 31, none⟩ (some ⟨.uint 31, 9⟩)
  let inner ← inner.write 0 (.uint 31) ⟨.uint 31, 17⟩
  readNat (← inner.leave) 0

example : answer shadow = some 7 := by decide +kernel
example : answer outerWrite = some 17 := by decide +kernel

example : failure (Locals.empty.read 4 (.uint 31)) = some (.invalidContext "unbound local cell") := by decide +kernel
example : failure (Locals.leave []) = some (.invalidContext "local scope stack is empty") := by decide +kernel

private def unset : Aggregates.Result Value := do
  let locals ← Locals.empty.declare ⟨0, .bytes .storage true, none⟩
  locals.read 0 (.bytes .storage true)

example : failure unset = some (.invalidContext "uninitialized local reference") := by decide +kernel

private def mismatchedRead : Aggregates.Result Value := do
  let locals ← Locals.empty.declare ⟨0, .uint 31, none⟩ (some ⟨.uint 31, 7⟩)
  locals.read 0 .bool

example : failure mismatchedRead = some (.invalidContext "local cell type mismatch") := by decide +kernel

private def mismatchedWrite : Aggregates.Result Locals := do
  let locals ← Locals.empty.declare ⟨0, .uint 31, none⟩ (some ⟨.uint 31, 7⟩)
  locals.write 0 (.uint 31) ⟨.bool, true⟩

example : failure mismatchedWrite = some (.invalidContext "local cell value type mismatch") := by decide +kernel

private def duplicate : Aggregates.Result Locals := do
  let locals ← Locals.empty.declare ⟨0, .uint 31, none⟩ (some ⟨.uint 31, 7⟩)
  locals.enter.declare ⟨0, .bool, none⟩ (some ⟨.bool, true⟩)

example : failure duplicate = some (.invalidContext "duplicate active local declaration ID") := by decide +kernel

private def grouped : Datum := .tuple [.atom ⟨.uint 0, 1⟩,
  .tuple [.atom ⟨.bool, true⟩, .atom ⟨.address false, 2⟩]]

example : grouped.type = .tuple (.cons (.uint 0) (.cons
    (.tuple (.cons .bool (.cons (.address false) .nil))) .nil)) := by decide +kernel
example : failure grouped.asAtom = some (.invalidContext "tuple grouping used as a single stored value") := by decide +kernel

private def EmptyKey (_ : SType) := Empty
private def function : FunctionDefinition EmptyKey := ⟨.pure, [], [], .skip⟩

example : (Program.valid ⟨[(0, function)]⟩) = true := by decide +kernel
example : failure (Program.lookup ⟨[(0, function), (0, function)]⟩ 0) =
    some (.invalidContext "invalid internal function table") := by decide +kernel
example : failure (Program.lookup (⟨[]⟩ : Program EmptyKey) 3) =
    some (.invalidContext "unresolved internal function handle") := by decide +kernel

end Solidity.Execution.Tests
