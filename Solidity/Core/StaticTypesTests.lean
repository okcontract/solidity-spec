/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.OperatorBindings

namespace Solidity.Static.Tests

-- Structural type recognition does not grant scalar execution support.
example : SType.scalarSupported (.tuple (.cons (.uint 0) .nil)) = false := by decide +kernel
example : SType.scalarSupported (.metaType (.uint 0)) = false := by decide +kernel
example : SType.scalarSupported (.fixedPoint true 15 18) = false := by decide +kernel
example : SType.scalarSupported (.array (.uint 0) (some 4) .memory true) = false := by decide +kernel
example : SType.scalarSupported (.function .external .pure (.cons (.uint 0) .nil) .nil) = true := by decide +kernel

private def registry : Registry := {
  enumerations := fun identity => if identity == 1 then some 1 else none
  valueTypes := fun identity => if identity == 1 then some (.scalar (.uint 0)) else none
  contracts := fun identity => if identity == 1 then some (false, []) else none
  structures := fun identity => identity == 1 }

example : wellFormed registry (.enumType 1 1) = true := by decide +kernel
example : wellFormed registry (.enumType 1 2) = false := by decide +kernel
example : wellFormed registry (.valueType 1 (.scalar (.uint 1))) = false := by decide +kernel
example : wellFormed registry (.contract 1 true []) = false := by decide +kernel
example : wellFormed registry (.function .internal .payable .nil .nil) = false := by decide +kernel
example : wellFormed registry (.array (.uint 0) (some 0) .memory true) = false := by decide +kernel
example : wellFormed registry (.tuple (.cons (.enumType 1 1) .nil)) = true := by decide +kernel
example : wellFormed registry (.metaType (.enumType 1 2)) = false := by decide +kernel
example : wellFormed registry (.fixedPoint true 15 18) = true := by decide +kernel

end Solidity.Static.Tests
