/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.ApplyRemaining
import Solidity.Core.Execution.Safety.ApplyCalls

namespace Solidity.Execution.Safety
open Static Aggregates

/-- Completion covers every represented scalar/array primitive and actual
closed dispatch, including reordered named operands. -/
theorem apply_progress
    (context : EvaluationContext registry program objects environment state entry stack kind)
    (packet : PacketRep program state.heap objects values (Types.ofList types))
    (completion : CompletionRep registry finish types kind)
    (budget : materializationStepBound ≤ state.materializationRemaining) :
    StepRep registry program ⟨.apply finish values,stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply finish values,stack,state,entry⟩) := by
  have original := completion
  cases completion
  case call => exact apply_call_progress context packet original
  case namedCall => exact apply_namedCall_progress context packet original
  all_goals
    exact apply_noncall_progress context packet original
      ⟨by intro signature; simp,by intro signature order;simp⟩ budget

end Solidity.Execution.Safety
