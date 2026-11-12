/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.TargetSteps
import Solidity.Core.Execution.Safety.UpdateSteps

namespace Solidity.Execution.Safety
open Static Aggregates

/-- Every captured place is consumed by a compatible typed continuation. -/
theorem target_progress (witness : ConfigurationWitness registry program config)
    (taskEq : config.task = .target destination) :
    StepRep registry program config (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice config) := by
  rcases config with ⟨task,stack,state,entry⟩
  change task = .target destination at taskEq
  subst task
  rcases witness with ⟨closed,objects,environment,resultEnvironment,kind,stateRep,taskRep,stackRep,checkpoint⟩
  cases taskRep with
  | target represented =>
      cases stackRep with
      | cons frame continuation =>
          cases frame with
          | mode permitted => exact False.elim permitted
          | readTarget => exact target_read_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented
          | update nondelete allowed => exact update_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented nondelete allowed
          | assignLeft right allowed => exact target_assignLeft_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented right allowed
          | commitValue right allowed => exact target_commit_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented right allowed
          | compoundLeft right leftSupport rightSupport token allowed =>
              exact target_compoundLeft_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented right leftSupport rightSupport token allowed
          | compoundReadFirst right leftSupport rightSupport token allowed =>
              exact target_compoundReadFirst_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented right leftSupport rightSupport token allowed
          | compoundValue right leftSupport rightSupport token allowed =>
              exact target_compoundCommit_progress ⟨closed,stateRep,continuation,checkpoint⟩ represented right leftSupport rightSupport token allowed

end Solidity.Execution.Safety
