/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.FinitePrefixes
import Solidity.Pilots.AliasCallRollbackSafety

/-! A quantified application to an eager group whose children are genuinely
effectful. Both aliases are initialized before the group; either child order
is permitted, and the generic invariant does not require their values to agree. -/
namespace Solidity.Pilots.AliasCallRollback.GroupSafety
open Static Aggregates Execution Execution.Safety
open Contract.Interaction (Word)

private def grouped (value : Word) : Expr EmptyKey :=
  .binary (.arithmetic .add) word (.assign (element 0) (number value)) (.read (element 1))

private theorem element_form (program : Program EmptyKey) (id : Nat) : Profile.Target program (element id) :=
  .index (.local (.inr ⟨true,rfl⟩)) ⟨true,rfl⟩ (.literal rfl trivial)

private theorem grouped_form (owner : BitVec 160) (value : Word) :
    Profile.Expression (entryProgram owner) (grouped value) :=
  .binary (.assign (element_form _ 0) (.literal rfl trivial))
    (.read (element_form _ 1)) rfl rfl rfl

private theorem grouped_admitted (heap : Heap) (value : Word) (budget : Nat) :
    Admission.admitExpression registry 16 (entryState heap value false budget).locals (grouped value) = .ok () := by
  rfl

/-- The real finite runner preserves represented state or source rollback for
both assignment/read schedules, every input word and every represented input
heap. Arithmetic overflow remains a source outcome. -/
theorem eager_alias_group_prefix (physical : HeapRep heap [object]) (owner : BitVec 160)
    (value : Word) (budget : Nat) (enough : prefixMaterializationBound steps ≤ budget) :
    PrefixRep registry (entryProgram owner) (entryState heap value false budget)
      (Machine.execute physicalBackend registry ⟨aggregateFuel+2,none⟩ (entryProgram owner) steps choices
        (Config.expression (entryState heap value false budget) (grouped value))) := by
  have base := entry_state_rep physical owner value false
  have represented : StateRep (entryProgram owner) [object]
      (Execution.Safety.Locals.environment (entryLocals heap value false)) (entryState heap value false budget) :=
    ⟨base.heap,base.cells,base.shape,base.nonempty⟩
  have initial := configuration_expression (entry_closed owner) represented (grouped_form owner value)
    (grouped_admitted heap value budget)
  exact execute_prefix initial enough

end Solidity.Pilots.AliasCallRollback.GroupSafety
