/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Transfers

namespace Solidity.Aggregates.Tests
open Static Core

set_option maxRecDepth 16384

local instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

private def registry : Registry := {
  enumerations := fun identity => if identity == 1 then some 1 else none
  valueTypes := fun identity => if identity == 1 then some (.scalar (.uint 0)) else none
  contracts := fun _ => none
  structures := fun identity => 1 ≤ identity && identity ≤ 10
  structFields := fun identity => match identity with
    | 1 => some [("value", .uint 0)]
    | 2 => some [("data", .mapping (.uint 0) (.uint 31))]
    | 3 => some [("next", .array (.structType 3 .storage false) none .storage false)]
    | 4 => some [("next", .structType 4 .storage false)]
    | 5 => some [("next", .array (.structType 5 .storage false) none .storage false),
        ("data", .mapping (.uint 0) (.uint 31))]
    | 7 => some [("next", .array (.structType 8 .storage false) none .storage false)]
    | 8 => some [("previous", .structType 7 .storage false), ("data", .mapping (.uint 0) (.uint 31))]
    | 9 => some [("callback", .function .internal .pure .nil .nil)]
    | 10 => some []
    | _ => none }

private def array (type : SType) (length : Option Nat) (location : Location)
    (pointer : Bool := true) : SType := .array type length location pointer
private def plan := planTransfer registry 64

example : plan false (.uint 0) (.uint 1) = .ok .scalarConversion := by decide +kernel
example : plan true (.sint 0) (.uint 0) = .error .rejected := by decide +kernel
example : plan false (array (.uint 0) (some 3) .memory) (array (.uint 0) (some 3) .memory) = .ok .memoryAlias := by decide +kernel
example : plan true (array (.uint 0) none .storage) (array (.uint 0) none .storage) = .ok .storageAlias := by decide +kernel
example : plan false (array (.uint 0) none .storage) (array (.uint 0) none .storage false) = .ok .storageCopy := by decide +kernel
example : plan true (array (.uint 0) none .memory) (array (.uint 0) none .storage) = .error .rejected := by decide +kernel
example : plan false (array (.uint 0) (some 3) .memory) (array (.uint 1) none .storage false) = .ok .storageCopy := by decide +kernel
example : plan false (array (.uint 0) (some 3) .storage) (array (.uint 1) (some 5) .storage false) = .ok .storageCopy := by decide +kernel
example : plan false (array (.uint 0) none .storage) (array (.uint 0) (some 5) .storage false) = .error .rejected := by decide +kernel
example : plan false (array (.uint 0) (some 3) .storage) (array (.uint 0) (some 2) .storage false) = .error .rejected := by decide +kernel
example : plan false (array (.uint 0) (some 3) .storage) (array (.uint 0) none .memory) = .error .rejected := by decide +kernel
example : plan false (array (.uint 0) (some 3) .memory) (array (.uint 1) (some 3) .memory) = .error .rejected := by decide +kernel
example : plan false (array (.uint 0) none .calldata) (array (.uint 0) none .memory) = .ok .memoryCopy := by decide +kernel
example : plan true (array (.uint 0) none .calldata) (array (.uint 0) none .calldata) = .ok .calldataAlias := by decide +kernel
example : plan false (array (.uint 0) none .calldata) (array (.uint 0) none .calldata) = .error .rejected := by decide +kernel
example : plan true (array (.uint 0) none .memory) (array (.uint 0) none .calldata) = .error .rejected := by decide +kernel
example : plan false (.string .memory true) (.bytes .storage false) = .error .rejected := by decide +kernel
example : plan false (.bytes .calldata true) (.bytes .storage false) = .ok .storageCopy := by decide +kernel
example : plan false (.structType 1 .memory true) (.structType 1 .storage false) = .ok .storageCopy := by decide +kernel
example : plan false (.structType 1 .storage true) (.structType 1 .memory true) = .ok .memoryCopy := by decide +kernel

-- A reference to a mapping-containing object is legal; copying its contents is not.
example : plan true (.mapping (.uint 0) (.uint 31)) (.mapping (.uint 0) (.uint 31)) = .ok .storageAlias := by decide +kernel
example : plan false (.mapping (.uint 0) (.uint 31)) (.mapping (.uint 0) (.uint 31)) = .error .rejected := by decide +kernel
example : plan true (.structType 2 .storage true) (.structType 2 .storage true) = .ok .storageAlias := by decide +kernel
example : plan false (.structType 2 .storage true) (.structType 2 .storage false) = .error .rejected := by decide +kernel
example : eligibleAt registry 64 (.memory 0) (.structType 2 .memory true) = .error .rejected := by decide +kernel
example : eligibleAt registry 64 (.transient 0) (array (.uint 0) none .storage) = .error .rejected := by decide +kernel
example : eligibleAt registry 64 (.transient 0) (.uint 0) = .ok () := by decide +kernel
example : eligibleAt registry 64 (.calldata 0) (.function .internal .pure .nil .nil) = .error .rejected := by decide +kernel
example : eligibleAt registry 64 (.calldata 0) (.function .external .pure .nil .nil) = .ok () := by decide +kernel
example : eligibleAt registry 64 (.calldata 0) (.structType 9 .calldata true) = .error .rejected := by decide +kernel

-- Empty metadata cannot admit a declaration rejected by the source syntax.
example : eligibleAt registry 64 (.storage 0) (.structType 10 .storage true) = .error .rejected := by decide +kernel
example : eligibleAt registry 64 (.memory 0) (.structType 10 .memory true) = .error .rejected := by decide +kernel
example : eligibleAt registry 64 (.calldata 0) (.structType 10 .calldata true) = .error .rejected := by decide +kernel

-- Back edges do not hide later mapping fields, including across multiple structs.
example : containsMapping registry 64 (.structType 3 .storage true) = .ok false := by decide +kernel
example : containsMapping registry 64 (.structType 5 .storage true) = .ok true := by decide +kernel
example : containsMapping registry 64 (.structType 7 .storage true) = .ok true := by decide +kernel
example : eligibleAt registry 64 (.storage 0) (.structType 3 .storage true) = .ok () := by decide +kernel
example : eligibleAt registry 64 (.storage 0) (.structType 4 .storage true) = .error .rejected := by decide +kernel
example : eligibleAt registry 64 (.memory 0) (.structType 3 .memory true) = .ok () := by decide +kernel
example : eligibleAt registry 64 (.calldata 0) (.structType 3 .calldata true) = .ok () := by decide +kernel
example : eligibleAt registry 64 (.memory 0) (.structType 4 .memory true) = .error .rejected := by decide +kernel
example : eligibleAt registry 64 (.calldata 0) (.structType 4 .calldata true) = .error .rejected := by decide +kernel
example : plan true (.structType 3 .storage true) (.structType 3 .storage true) = .ok .storageAlias := by decide +kernel
example : containsMapping registry 64 (.structType 6 .storage true) = .error (.invalidContext "missing resolved struct fields") := by decide +kernel
example : containsMapping registry 1 (.structType 3 .storage true) = .error .exhausted := by decide +kernel
example : planTransfer registry 0 false (.uint 0) (.uint 0) = .error .exhausted := by decide +kernel

-- Static type size rejection is distinct from allocation or interpreter exhaustion.
example : eligibleAt registry 64 (.memory 0) (array (.uint 31) (some (2^27)) .memory) = .error .rejected := by decide +kernel
example : eligibleAt registry 64 (.memory 0) (array (.uint 31) (some (2^27-1)) .memory) = .ok () := by decide +kernel
example : eligibleAt registry 64 (.calldata 0) (array (.uint 31) (some (2^27)) .calldata) = .error .rejected := by decide +kernel

end Solidity.Aggregates.Tests
