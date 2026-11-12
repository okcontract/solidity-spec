/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Configuration
import Solidity.Core.Execution.Safety.EnvironmentLaws
import Solidity.Core.Execution.Safety.SourceFormation
import Solidity.Core.Execution.Safety.ProfileLaws

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem ExpressionCode.formed (code : ExpressionCode registry program environment expression) :
    Static.wellFormed registry expression.type = true := by
  obtain ⟨_,_,_,_,checked⟩ := code.admitted
  exact SourceFormation.expression_wellFormed code.form checked

theorem ExpressionCode.scalar_ready (code : ExpressionCode registry program environment expression)
    (supported : expression.type.scalarSupported = true) : TypeReady registry expression.type :=
  ⟨.inl supported,code.formed⟩

theorem TargetCode.ready (code : TargetCode registry program environment target) : TypeReady registry target.type := by
  obtain ⟨_,_,_,_,_,checked⟩ := code.admitted
  exact ⟨Profile.target_supported code.form,SourceFormation.target_wellFormed code.form checked⟩

theorem TargetCode.local_bound {localId : LocalId}
    (code : TargetCode registry program environment (.local localId type)) :
    Environment.find environment localId = some type := by
  obtain ⟨sourceFuel,incoming,after,writable,shape,checked⟩ := code.admitted
  cases sourceFuel with
  | zero => cases checked
  | succ sourceFuel =>
      obtain ⟨bound,_,_⟩ := SourceTyping.local_target_checked checked
      obtain ⟨binder,find,same,_⟩ := Admission.Context.local_checked _ _ _ _ bound
      simpa only [same] using shape.context_find find

theorem ExpressionCode.local_bound {localId : LocalId}
    (code : ExpressionCode registry program environment (.local localId type)) :
    Environment.find environment localId = some type := by
  obtain ⟨sourceFuel,incoming,after,shape,checked⟩ := code.admitted
  cases sourceFuel with
  | zero => cases checked
  | succ sourceFuel =>
      simp only [Admission.checkExpression] at checked
      obtain ⟨done,bound,_⟩ := SourceTyping.bind_checked checked
      cases done
      obtain ⟨binder,find,same,_⟩ := Admission.Context.local_checked _ _ _ _ bound
      simpa only [same] using shape.context_find find

theorem ExpressionCode.transfer_source_ready (code : ExpressionCode registry program environment expression)
    (targetSupport : Supported target) (permission : TransferRule localBinding expression.type target kind) :
    TypeReady registry expression.type :=
  ⟨Profile.transfer_source_supported (Profile.expression_output expression code.form) targetSupport permission,code.formed⟩

end Solidity.Execution.Safety
