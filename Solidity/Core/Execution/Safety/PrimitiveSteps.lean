/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.StepLaws

namespace Solidity.Execution.Safety
open Static Aggregates

/-- A specification of a real transition primitive's result. This predicate
contains no executable callback and does not presume that an operation succeeds. -/
def PrimitiveRep (registry : Registry) (program : Program EmptyKey) (before : Config Unit EmptyKey) :
    Machine.StepResult Unit EmptyKey → Prop
  | .ok progress => StepRep registry program before progress
  | .error failure => isSourceFailure failure = true

theorem primitive_step
    (represented : PrimitiveRep registry program before
      (Machine.transition physicalBackend registry ⟨fuel+2,none⟩ program choice before)) :
    StepRep registry program before (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice before) := by
  cases changed : Machine.transition physicalBackend registry ⟨fuel+2,none⟩ program choice before with
  | error failure =>
      rw [changed] at represented
      exact stepRep_source changed represented
  | ok progress =>
      rw [changed] at represented
      cases progress with
      | next after => simpa only [Machine.step,changed] using represented
      | done result => simpa only [Machine.step,changed] using represented
      | suspended after => exact False.elim represented

end Solidity.Execution.Safety
