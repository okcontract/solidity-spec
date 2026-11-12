/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Execution
import Solidity.Conformance.Scalar
import Solidity.Core.Expression
import Contract.Check.Declarations
import Lean.Elab.Command

/-! The default SoliditySemantics library builds this check. Runtime exports
remain independent of the auditor and compatibility fixtures. Primitive scalar
operations are shared; legacy expression/control/procedure interpreters are
forbidden in the transitive executable declarations below. -/
namespace Solidity.Execution.PrimaryDependencyTests
open Lean Elab Command

private def forbidden : Array Name := #[
  `Solidity.Core.Expr.eval, `Solidity.Core.Expr.Evaluates,
  `Solidity.Core.Exprs.eval, `Solidity.Core.Block.eval, `Solidity.Core.Procedure.eval,
  `Solidity.Core.Control.step, `Solidity.Core.Control.run, `Solidity.Static.SourceExpr.eval]

private def legacyFree (environment : Environment) (roots : Array Name) : Except String Unit := do
  let declarations ← Contract.Check.Declarations.closure environment roots
  if let some legacy := declarations.find? (fun declaration => forbidden.any (·.isPrefixOf declaration.name)) then
    throw s!"legacy runtime dependency: {legacy.name}"

private def legacyAlias := @Core.Expr.eval
private def indirectLegacyAlias := @legacyAlias

run_cmd do
  let environment ← getEnv
  let roots := #[``Machine.step, ``Machine.execute, ``SourceFacade.prepareExpression,
    ``SourceFacade.executeExpression, ``SourceFacade.executeFunction,
    ``SourceFacade.prepareStatement, ``SourceFacade.executeStatement,
    ``Checked.prepareExpression, ``Checked.prepareStatement, ``Checked.Expression.execute, ``Checked.Statement.execute,
    ``Solidity.Conformance.ScalarMachine.expressionRun,
    ``Solidity.Conformance.ScalarMachine.loopRun, ``Solidity.Conformance.ScalarMachine.outcomes]
  match legacyFree environment roots with
  | .error reason => throwError "{reason}"
  | .ok () => pure ()
  match legacyFree environment #[``indirectLegacyAlias] with
  | .error reason =>
      unless reason.startsWith "legacy runtime dependency:" do throwError "invalid alias negative control: {reason}"
  | .ok () => throwError "indirect legacy alias escaped the declaration dependency guard"

end Solidity.Execution.PrimaryDependencyTests
