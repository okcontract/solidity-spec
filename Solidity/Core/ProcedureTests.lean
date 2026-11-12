/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Proofs.TypedStatements

namespace Solidity.Core.ProcedureTests
open Solidity.Core

private def store : Store (fun _ => Empty) (fun _ => Empty) Unit where
  read _ := fun {_t} ref => nomatch ref
  write _ := fun {_t} ref _ => nomatch ref

private def overflow : Procedure (fun _ => Empty) (fun _ => Empty) [] [] :=
  .let_ (.binary (.uintArithmetic 0 .checked .add) (.literal 255) (.literal 1)) (.ret .nil)

example : overflow.eval store 0 .leftFirst () .nil = .reverted (Contract.panic 0x11) := by rfl

private def logThenRevert : Procedure (fun _ => Empty) (fun _ => Empty) [] [] :=
  .emit (topics := [.word]) (by decide) (.cons (.literal 9) .nil) .nil (.revert [0xab])

example : (logThenRevert.eval store 7 .leftFirst () .nil).logs = [] := by rfl
example : (logThenRevert.eval store 7 .leftFirst () .nil).observe = .reverted [0xab] := by rfl

private def helper : Procedure (fun _ => Empty) (fun _ => Empty) [.word] [.word] :=
  .ret (.cons (.binary (.uintArithmetic 31 .unchecked .add) (.read (.local .here)) (.literal 1)) .nil)

private def caller : Procedure (fun _ => Empty) (fun _ => Empty) [.word] [.word] :=
  .call helper (.cons (.literal 5) .nil)
    (.ret (.cons (.binary (.uintArithmetic 31 .unchecked .add)
      (.read (.local .here)) (.read (.local (.there .here)))) .nil))

example : (caller.eval store 0 .leftFirst () (.cons 40 .nil)).observe =
    .returned (Contract.Interaction.wordBytes 46) () := by rfl

end Solidity.Core.ProcedureTests
