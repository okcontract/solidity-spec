/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Lean.Elab.Command
import Contract.Check.Declarations

/-! Inspect compiled declarations, including their complete transitive logical
dependencies. The committed manifest selects roots and expected contracts.
This development audit does not replace independent kernel replay or establish
model adequacy. Unsafe/partial dependencies and nonstandard axioms fail closed.
-/
open Lean Elab Command Contract.Check in
elab "#audit_semantics_theorem " id:ident : command => do
  let root ← resolveGlobalConstNoOverload id
  let info ← getConstInfo root
  unless info matches .thmInfo _ do throwError "{root} is not a theorem"
  let .ok dependencies := Declarations.closure (← getEnv) #[root]
    | throwError "{root}: invalid dependency closure"
  let .ok axioms := Declarations.axioms dependencies
    | throwError "{root}: disallowed axiom"
  let statement ← liftTermElabM <| Meta.ppExpr info.type
  liftIO <| IO.println <| (Json.mkObj [
    ("name", .str root.toString),
    ("statement", .str statement.pretty),
    ("kernelStatement", Declarations.expression info.type),
    ("axioms", toJson axioms),
    ("dependencyCount", toJson dependencies.size)]).compress
