/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.SourceControlScopes
import Solidity.Core.Execution.Safety.EnvironmentLaws

namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem Environment.find_declare_other (different : binder.id ≠ key) :
    Environment.find (Environment.declare environment binder) key = Environment.find environment key := by
  cases environment with
  | nil => rfl
  | cons scope rest =>
      rw [Environment.find_declare (scope :: rest) (by simp) binder key]
      simp [different]

private theorem declare_absent
    (checked : Admission.Context.declare incoming binder initialized = .ok after) :
    incoming.find binder.id = none := by
  unfold Admission.Context.declare at checked
  obtain ⟨done,checked,_⟩ := SourceTyping.bind_checked checked
  cases done
  have absent := SourceTyping.ensure_checked checked
  cases found : incoming.find binder.id <;> simp_all

theorem declaration_absent (form : Profile.Declaration program (.declare [some binder] initializer))
    (checked : Admission.checkStatement registry fuel incoming returns loops unchecked
      (.declare [some binder] initializer) = .ok flow) :
    Environment.find (Profile.scopesEnvironment incoming.scopes) binder.id = none := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      simp only [Admission.checkStatement] at checked
      obtain ⟨after,declared,_⟩ := SourceTyping.bind_checked checked
      cases form with
      | default supported =>
          have absent := declare_absent (SourceControl.default_declaration_checked declared).2.2
          rw [context_environment_find,absent]
          rfl
      | value supported valueForm =>
          obtain ⟨evaluated,source,child,_,_,declared⟩ := SourceControl.initialized_declaration_checked declared
          have absent := declare_absent declared
          have scopes := SourceTyping.checkExpression_scopes valueForm child
          have erased : Environment.find (Profile.scopesEnvironment evaluated.scopes) binder.id = none := by
            rw [context_environment_find,absent]
            rfl
          simpa only [scopes] using erased

/-- Prefix bindings cannot shadow an existing parameter/return cell. This is
derived from actual source declaration checks, including initialized prefixes;
it is not a desired lookup result assumed of the executable body. -/
theorem body_prefix_preserves_bound (body : Stmt EmptyKey) (form : Profile.Body program body)
    (checked : Admission.checkStatement registry fuel incoming returns loops unchecked body = .ok flow)
    (equivalent : Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment)
    (bound : Environment.find environment key = some type) :
    Environment.find (prefixEnvironment environment body) key = some type := by
  cases form with
  | statement statementForm =>
      rw [SourceControl.statement_prefix statementForm]
      exact bound
  | declaration declarationForm restForm =>
      rename_i declaration tailBody
      cases fuel with
      | zero => cases checked
      | succ fuel =>
          simp only [Admission.checkStatement] at checked
          obtain ⟨first,declared,continuationCheck⟩ := SourceTyping.bind_checked checked
          obtain ⟨second,bodyChecked,_⟩ := SourceTyping.bind_checked continuationCheck
          obtain ⟨binder,initializer,after,declarationEq,firstShape,afterShape⟩ :=
            SourceControl.declaration_environment declarationForm declared
          cases declarationEq
          have absent := declaration_absent declarationForm declared
          have actualAbsent : Environment.find environment binder.id = none :=
            (equivalent.find binder.id).symm.trans absent
          have different : binder.id ≠ key := by
            intro same
            rw [same,bound] at actualAbsent
            cases actualAbsent
          have boundAfter : Environment.find (Environment.declare environment binder) key = some type := by
            rw [Environment.find_declare_other different]
            exact bound
          have afterEquivalent : Environment.Equivalent (Profile.scopesEnvironment after.scopes)
              (Environment.declare environment binder) :=
            (Environment.Equivalent.of_eq afterShape).trans (equivalent.declare binder)
          have bodyChecked : Admission.checkStatement registry fuel after returns loops unchecked tailBody = .ok second := by
            simpa only [firstShape,Admission.Flow.next,Option.getD_some] using bodyChecked
          exact body_prefix_preserves_bound tailBody restForm bodyChecked afterEquivalent boundAfter
termination_by sizeOf body

end Solidity.Execution.Safety
