/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.CaptureSteps
import Solidity.Core.Execution.Safety.StepLaws

namespace Solidity.Execution.Safety
open Static Aggregates

theorem capture_progress (witness : ConfigurationWitness registry program config)
    (taskEq : config.task = .capture target) :
    StepRep registry program config (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice config) := by
  rcases config with ⟨task,stack,state,entry⟩
  change task = .capture target at taskEq
  subst task
  rcases witness with ⟨closed,objects,environment,resultEnvironment,kind,stateRep,taskRep,stackRep,checkpoint⟩
  cases taskRep with
  | capture code =>
      have context : EvaluationContext registry program objects environment state entry stack (.target target.type) :=
        ⟨closed,stateRep,stackRep,checkpoint⟩
      cases code.form with
      | «local» supported => exact stepRep_of_unchanged (capture_local_progress context code)
      | heap physical => exact stepRep_of_unchanged (capture_heap_progress context code)
      | index sourceForm array indexForm => exact stepRep_of_unchanged (capture_index_progress context code)

end Solidity.Execution.Safety
