/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy.Operations
import Solidity.Core.Aggregates.Copy.Laws
import Solidity.Core.Aggregates.Copy.Frames

/-! Compatibility facade for checked aggregate copying. Executable transfers,
local operational laws and world-frame proofs have separate owners. Recursive
physical representation and ordered storage effects remain separate proof layers.
-/
