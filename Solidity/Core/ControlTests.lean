/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Control
import Solidity.Core.Bindings

namespace Solidity.Core.Control.Tests

abbrev Types : List Ty := [.uint 0]
abbrev Refs := Var Types

def localStore : Store Refs Refs (Env Types) where
  read state := state.get
  write state := fun {_} place value => some (state.set place value)

def start : Env Types := .cons 0 .nil

def increment : Block Refs Refs := .assign .here
  (.binary (.uintArithmetic 0 .checked .add) (.read .here) (.literal 1))

def belowThree : Expr Refs .bool :=
  .binary (.uintCompare 0 .lt) (.read .here) (.literal 3)

def countingWhile : Command Refs Refs := .loop belowThree (.block increment) .skip

def countingFor : Command Refs Refs :=
  .loop belowThree (.seq .continue_ (.block (.revert [99]))) increment

example : run localStore .leftFirst 100 (.exec countingWhile [] start) =
    .finished (.completed (.next (.cons 3 .nil))) := by rfl

/-- Continue skips the remaining body but still executes a for-loop increment. -/
example : run localStore .leftFirst 100 (.exec countingFor [] start) =
    .finished (.completed (.next (.cons 3 .nil))) := by rfl

/-- Break exits the nearest loop without its increment block. -/
example : run localStore .leftFirst 20
    (.exec (.loop (.literal true) .break_ increment) [] start) =
    .finished (.completed (.next start)) := by rfl

/-- An inner break does not escape an enclosing loop. -/
example : run localStore .leftFirst 100
    (.exec (.loop belowThree (.loop (.literal true) .break_ .skip) increment) [] start) =
    .finished (.completed (.next (.cons 3 .nil))) := by rfl

/-- Returning skips the loop increment and all enclosing continuations. -/
example : run localStore .leftFirst 20
    (.exec (.seq (.loop (.literal true) (.block (.ret (.literal 7))) increment)
      (.block (.revert [99]))) [] start) =
    .finished (.completed (.halt (.returned (Contract.Interaction.wordBytes 7) start))) := by rfl

/-- Fuel exhaustion is not a Solidity revert, success, or exceptional halt. -/
example : match run localStore .leftFirst 20
    (.exec (.loop (.literal true) (.block .skip) .skip) [] start) with
    | .exhausted _ => True
    | .finished _ => False := by trivial

example : run localStore .leftFirst 5 (.exec .break_ [] start) =
    .finished .invalidControl := by rfl

/-- A panic during a later iteration exposes no successful state. -/
example : run localStore .leftFirst 100
    (.exec (.loop (.literal true) (.block increment) .skip) [] (.cons 254 .nil)) =
    .finished (.completed (.halt (.reverted (Contract.panic 0x11)))) := by rfl

end Solidity.Core.Control.Tests
