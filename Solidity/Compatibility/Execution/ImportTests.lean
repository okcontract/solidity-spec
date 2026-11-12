/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Execution
import Solidity.Compatibility.Execution
import Solidity.Core.Execution.CompatibilityTypedStatements
import Solidity.Core.Execution.CompatibilityClients
import Solidity.Core.Execution.CompatibilityControl

/-! Both compatibility and owning import paths coexist without duplicate logical
declarations. These are the actual universal certificate bridge contracts. -/
#check Solidity.Execution.Compatibility.control_machine
#check Solidity.Execution.Compatibility.procedure_machine
#check Solidity.Compatibility.Typed.statement_machine
#check Solidity.Compatibility.Storage.certified_body_machine
