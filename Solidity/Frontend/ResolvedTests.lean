/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Frontend.Resolved

namespace Solidity.Frontend.Inference.Tests
open Static

private def registry : Registry := {
  enumerations := fun identity => if identity == 1 then some 1 else none
  valueTypes := fun identity => if identity == 1 then some (.scalar (.uint 0)) else none
  contracts := fun _ => none
  structures := fun _ => false }

private def context : Context := fun name =>
  if name == "good" then some (.enumType 1 1)
  else if name == "bad" then some (.enumType 1 2) else none

private def accepts (source : Source) : Bool :=
  match inferResolved registry context source with | .ok _ => true | .error _ => false

example : accepts (.name "good") = true := by decide +kernel
example : accepts (.name "bad") = false := by decide +kernel
example : accepts (.wrap 1 (.scalar (.uint 0)) (.number "1" .none)) = true := by decide +kernel
example : accepts (.wrap 1 (.scalar (.uint 1)) (.number "1" .none)) = false := by decide +kernel
example : accepts (.ite (.bool true) (.number "0" .none)
    (.cast .ordinary (.enumType 1 2) (.number "0" .none))) = false := by decide +kernel
example : typesResolved registry context (.binary .and (.bool false)
    (.binary (.compare .eq) (.name "bad") (.name "bad"))) = false := by decide +kernel
example : accepts (.number "_1" .none) = false := by decide +kernel
example : accepts (.number "0_x01" .none) = false := by decide +kernel
example : accepts (.ite (.bool true) (.number "1" .none)
    (.number "_1" .none)) = false := by decide +kernel

end Solidity.Frontend.Inference.Tests
