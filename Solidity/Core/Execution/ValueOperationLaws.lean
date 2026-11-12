/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.ValueOperations

namespace Solidity.Execution.ValueOperations
open Static

theorem unwrap_wrap (identity : Nat) (base : Elementary) (value : base.source.Value) :
    (wrap identity base ⟨base.source, value⟩ >>= unwrap identity base) = .ok ⟨base.source, value⟩ := by
  simp [wrap, unwrap, Elementary.out_into, Bind.bind, Except.bind]


end Solidity.Execution.ValueOperations
