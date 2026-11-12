/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Bindings
import Solidity.Core.SourceExpression

namespace Solidity.Execution.ValueOperations
open Static
open Aggregates (Result)

def wrap (identity : Nat) (base : Elementary) (source : Value) : Result Value :=
  if same : source.type = base.source then
    .ok ⟨.valueType identity base, base.into (same ▸ source.value)⟩
  else .error .rejected

def unwrap (identity : Nat) (base : Elementary) (source : Value) : Result Value :=
  if same : source.type = .valueType identity base then
    let value := Eq.mp (congrArg SType.Value same) source.value
    .ok ⟨base.source, base.out value⟩
  else .error .rejected

def functionAddress : Value → Result Value
  | ⟨.function .external _ _ _, (address, _)⟩ => .ok ⟨.address false, address⟩
  | _ => .error .rejected

def functionSelector : Value → Result Value
  | ⟨.function .external _ _ _, (_, selector)⟩ => .ok ⟨.fixedBytes 3, selector⟩
  | _ => .error .rejected

end Solidity.Execution.ValueOperations
