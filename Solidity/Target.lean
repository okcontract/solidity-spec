/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
/-! The immutable language/fork target of this package. The profile check binds
these values to target.json and oksolc's compatibility version. A source pragma
constrains admission; it never selects another semantics at runtime. -/
namespace Solidity.Target

def solidityVersion : String := "0.8.36"
def referenceCompilerVersion : String := "0.8.36+commit.8a079791"
def evmVersion : String := "cancun"
def leanVersion : String := "4.29.0"

/-- Compiler compatibility is scoped to the IR pipeline. Legacy code generation
can copy aggregate arguments before later argument effects. These settings do
not fix the machine's permitted raw-child schedules. -/
def viaIR : Bool := true
def optimizerRuns : Nat := 200
def optimizerEnabled : List Bool := [false, true]

end Solidity.Target
