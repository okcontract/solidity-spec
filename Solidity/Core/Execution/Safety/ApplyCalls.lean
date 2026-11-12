/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.InvokeSteps

/-! Generic application of ordinary and named calls. Static type-position
selection constructs the actual selected value packet; every selected datum
retains its independent physical representation before invocation proceeds. -/
namespace Solidity.Execution.Safety
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

private theorem call_packet_length
    (packet : PacketRep program heap objects values (Types.ofList sourceTypes)) :
    values.length = sourceTypes.length := by
  induction sourceTypes generalizing values with
  | nil => cases packet; rfl
  | cons type types ih =>
      cases packet with
      | cons head tail => simpa only [List.length_cons] using congrArg Nat.succ (ih tail)

private theorem call_packet_lookup {index : Nat}
    (packet : PacketRep program heap objects values (Types.ofList sourceTypes))
    (selected : sourceTypes[index]? = some type) :
    ∃ value,values[index]? = some value ∧ DatumRep program heap objects value type := by
  induction sourceTypes generalizing values index with
  | nil => simp at selected
  | cons head rest ih =>
      cases packet with
      | cons first tail =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
              subst type
              exact ⟨_,rfl,first⟩
          | succ index => simpa only [List.getElem?_cons_succ] using ih tail selected

private theorem call_packet_selects
    (packet : PacketRep program heap objects values (Types.ofList sourceTypes))
    (selection : ArgumentOrder.Selects sourceTypes order reordered) :
    ∃ selected,ArgumentOrder.Selects values order selected ∧
      PacketRep program heap objects selected (Types.ofList reordered) := by
  induction selection with
  | nil => exact ⟨[],.nil,.nil⟩
  | cons entry rest ih =>
      obtain ⟨value,present,represented⟩ := call_packet_lookup packet entry
      obtain ⟨selected,selection,selectedRep⟩ := ih
      exact ⟨value :: selected,.cons present selection,.cons represented selectedRep⟩

/-- Actual named-argument selection is total from the selected type positions
and the represented raw packet. No value-selection success is assumed. -/
theorem selectPacket_total
    (packet : PacketRep program heap objects values (Types.ofList sourceTypes))
    (selectedTypes : ArgumentOrder.select order sourceTypes = .ok reordered) :
    ∃ selected,ArgumentOrder.select order values = .ok selected ∧
      PacketRep program heap objects selected (Types.ofList reordered) := by
  obtain ⟨valid,positions⟩ := (ArgumentOrder.select_iff _ _ _).mp selectedTypes
  obtain ⟨selected,selection,represented⟩ := call_packet_selects packet positions
  exact ⟨selected,(ArgumentOrder.select_iff _ _ _).mpr
    ⟨by rw [call_packet_length packet]; exact valid,selection⟩,represented⟩

theorem apply_call_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value signature.resultType))
    (packet : PacketRep program state.heap objects values (Types.ofList types))
    (completion : CompletionRep registry (.call signature) types (.value signature.resultType)) :
    StepRep registry program ⟨.apply (.call signature) values,stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.call signature) values,stack,state,entry⟩) := by
  cases completion with
  | call functionReady allowed argsReady =>
      cases packet with
      | @cons headValue headType rawArguments rawTypes head arguments =>
          obtain ⟨callee,rfl,typeEq,represented⟩ := head.atom_of_supported functionReady.1
          exact invoke_progress context represented arguments (by rw [typeEq];exact functionReady)
            (by rw [typeEq];exact allowed) argsReady

theorem apply_namedCall_progress
    (context : EvaluationContext registry program objects environment state entry stack (.value signature.resultType))
    (packet : PacketRep program state.heap objects values (Types.ofList types))
    (completion : CompletionRep registry (.namedCall signature order) types (.value signature.resultType)) :
    StepRep registry program ⟨.apply (.namedCall signature order) values,stack,state,entry⟩
      (Machine.step physicalBackend registry ⟨fuel+2,none⟩ program choice
        ⟨.apply (.namedCall signature order) values,stack,state,entry⟩) := by
  cases completion with
  | namedCall functionReady allowed _ argsReady =>
      cases packet with
      | @cons headValue headType rawArguments rawTypes head arguments =>
          obtain ⟨callee,rfl,typeEq,represented⟩ := head.atom_of_supported functionReady.1
          obtain ⟨reordered,selectedTypes,argsReady⟩ := argsReady
          obtain ⟨selected,selection,selectedRep⟩ := selectPacket_total arguments selectedTypes
          let config : Config Unit EmptyKey :=
            ⟨.apply (.namedCall signature order) (.atom callee :: rawArguments),stack,state,entry⟩
          have ready : TypeReady registry callee.type := by rw [typeEq]; exact functionReady
          have permission : Static.Allowed .implicit callee.type signature.type := by rw [typeEq];exact allowed
          rcases invoke_total config context represented selectedRep ready permission argsReady with
            failed | ⟨after,invoked,represented,sameEntry,sameBudget⟩
          · apply stepRep_source (failure := .panic 0x51)
            · simpa only [Machine.transition,Machine.apply,Datum.asAtom,selection,Bind.bind,Except.bind] using failed
            · rfl
          · apply stepRep_next (after := after)
            · apply step_of_transition
              simpa only [Machine.transition,Machine.apply,Datum.asAtom,selection,Bind.bind,Except.bind] using invoked
            · exact represented
            · exact sameEntry
            · change config.state.materializationRemaining ≤ after.state.materializationRemaining+materializationStepBound
              rw [sameBudget]
              omega

end Solidity.Execution.Safety
