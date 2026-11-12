/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.ReadinessLaws
import Solidity.Core.Execution.PacketTransferLaws
import Solidity.Core.Execution.ParameterTransfers
import Solidity.Core.Execution.ParameterReturnTransfers
import Solidity.Core.Execution.EffectsLaws
import Solidity.Core.Execution.MachineProofs
import Solidity.Core.Execution.SelectionLaws
import Solidity.Core.Execution.ConstructorLaws
import Solidity.Core.Execution.BindingsLaws
import Solidity.Core.Execution.SyntaxLaws
import Solidity.Core.Execution.ValueOperationLaws

/-! Additional execution laws, separate from the lightweight executable entry
and the admitted-state safety profile. Public declaration names are unchanged. -/
