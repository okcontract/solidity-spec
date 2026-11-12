/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Execution

/-! An executable client imports only the lightweight public entry. Dependency
absence is checked separately by test_semantics_interfaces.py. -/
#check Solidity.Execution.SourceFacade.executeExpression
#check Solidity.Execution.SourceFacade.executeFunction
#check Solidity.Execution.Checked.prepareExpression
#check Solidity.Execution.Checked.Expression.execute
#check Solidity.Execution.Machine.execute
