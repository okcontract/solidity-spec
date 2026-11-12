/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Lake
open Lake DSL

package oksolcSemantics where
  leanOptions := #[⟨`warningAsError, true⟩]

@[default_target]
lean_lib Contract where
  -- Both packages extend the Contract namespace. Claim only the shared files.
  roots := #[]
  globs := #[
    `Contract.Check.Axioms, `Contract.Check.Declarations, `Contract.Evm.Execution,
    `Contract.Evm.Frames, `Contract.Evm.Guarded, `Contract.Evm.Projection,
    `Contract.Evm.Storage, `Contract.Evm.StorageFrames, `Contract.Evm.Subset,
    `Contract.Export.Keccak, `Contract.Interaction.Basic, `Contract.Interaction.Bytes,
    `Contract.Interaction.Calls, `Contract.Interaction.CodeHash, `Contract.Interaction.Creation,
    `Contract.Interaction.Eval, `Contract.Interaction.MemoryProofs, `Contract.Interaction.WordPower,
    `Contract.Interaction.World, `Contract.Language.Basic, `Contract.Language.Word,
    `Contract.Proofs.Words, `Contract.Semantics.Eval, `Contract.Yul.Expression].map Glob.one

-- Declarations retain their existing names for certificate compatibility.
@[default_target]
lean_lib SoliditySemantics where
  roots := #[`Solidity]
  globs := #[.one `Solidity, .submodules `Solidity]
