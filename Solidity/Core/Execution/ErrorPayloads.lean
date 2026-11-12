/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Syntax
import Solidity.Core.Execution.Effects

/-! The resolved error boundary keeps eager argument effects separate from
conditional ABI encoding. Static scalar custom errors and Error(string) are
executable here. General aggregate ABI encoding is unsupported by this interface. -/
namespace Solidity.Execution.ErrorPayloads
open Static
open Aggregates (Result Failure Heap)
open Contract.Interaction (wordBytes)

def selectorBytes (selector : BitVec 32) : List UInt8 :=
  (wordBytes (selector.setWidth 256)).drop 28

def scalarArguments : List SType → List Value → Result (List UInt8)
  | [], [] => .ok []
  | type :: types, value :: values => do
      if Aggregates.isReference type || Aggregates.isReference value.type then
        throw (.unsupported "aggregate custom-error ABI encoding is unsupported")
      if let .function .internal _ _ _ := type then throw .rejected
      let value ← Effects.scalarCast .implicit type value
      let word ← Aggregates.encodeMemory value.type value.value
      return wordBytes word ++ (← scalarArguments types values)
  | _, _ => .error .rejected

def encode (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (encoding : ErrorEncoding) (arguments : List Value) : Result (List UInt8) := do
  match encoding, arguments with
  | .empty, [] => return []
  | .string, [value] =>
      match value.type with
      | .string _ _ =>
          let (contents, _) ← Aggregates.snapshot registry fuel budget heap (← Effects.asPlace value)
          let .bytes true bytes := contents | throw (.invalidContext "error-string snapshot has another shape")
          return selectorBytes 0x08c379a0 ++ wordBytes 32 ++ wordBytes (BitVec.ofNat 256 bytes.length) ++
            bytes ++ List.replicate ((32 - bytes.length % 32) % 32) 0
      | _ => throw .rejected
  | .custom selector parameters, arguments =>
      let _ ← Aggregates.reserve budget (arguments.length * 32)
      return selectorBytes selector ++ (← scalarArguments (typesList parameters) arguments)
  | _, _ => throw .rejected

theorem empty : encode registry fuel budget heap .empty [] = .ok [] := rfl

end Solidity.Execution.ErrorPayloads
