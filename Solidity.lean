/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Target
import Solidity.Observation
import Solidity.Core.Bindings
import Solidity.Core.Statement
import Solidity.Core.Control
import Solidity.Core.Procedure
import Solidity.Core.StaticABI
import Solidity.Frontend.Resolve
import Solidity.Frontend.Prepare
import Solidity.Proofs.Word
import Solidity.Proofs.TypedExpressions
import Solidity.Proofs.TypedStatements
import Solidity.Proofs.Clients
import Solidity.Proofs.Conditions
import Solidity.Proofs.Storage
import Solidity.Proofs.Initialization

import Solidity.Core.Power
import Solidity.Core.StaticTypes
import Solidity.Core.Conversions
import Solidity.Core.Operators
import Solidity.Core.Unary
import Solidity.Core.Registry
import Solidity.Core.OperatorBindings
import Solidity.Core.SourceExpression
import Solidity.Core.SourceProgress
import Solidity.Frontend.Lexical
import Solidity.Frontend.StringLiteral
import Solidity.Frontend.Mobility
import Solidity.Frontend.Inference
import Solidity.Frontend.Materialization
import Solidity.Frontend.NodeTyping
import Solidity.Frontend.BinaryTyping
import Solidity.Frontend.InferenceProofs
import Solidity.Frontend.Assignment
import Solidity.Frontend.Resolved
import Solidity.Proofs.Power
import Solidity.Core.Aggregates.Mutation
import Solidity.Core.Aggregates.LayoutCompatibility
import Solidity.Core.Aggregates.ScalarRepresentation
import Solidity.Core.Aggregates.MemoryConstructionFrame
import Solidity.Core.Aggregates.Raw
import Solidity.Core.Aggregates.Lifetime
import Solidity.Core.Aggregates.Representation
import Solidity.Core.Aggregates.MemoryRepresentationBoundary
import Solidity.Core.Aggregates.DefaultLeafRepresentation
import Solidity.Core.Aggregates.StorageMutationRepresentation
import Solidity.Core.Aggregates.StorageCopyTraversal
import Solidity.Core.Aggregates.DeclarationLayout
import Solidity.Core.Aggregates.DefaultConstructionRepresentation
import Solidity.Core.Aggregates.DefaultAliasing
import Solidity.Core.Aggregates.DeletionRepresentation
import Solidity.Core.Aggregates.StorageCopyEffects
import Solidity.Core.Aggregates.ReferenceCastProofs


import Solidity.Execution
import Solidity.Execution.Proofs
import Solidity.Execution.Safety
import Solidity.Compatibility.Execution

/-! Public entry point for the executable semantics and their proved
connections to certificate models. The paper describes the supported domains
and the assumptions of the exported theorems. -/
