/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Evm.StorageFrames
import Solidity.Core.Aggregates.ScalarRepresentation

/-! Independent target half of the manually paired alias/call pilot. This is
one hand-authored Cancun artifact. Gas is obtained from its actual guarded
execution; no compiler output or general lowering theorem is asserted. -/
namespace Solidity.Pilots.AliasCallRollback.Target
open Contract Evm
open Contract.Interaction (Word Memory bytesWord wordBytes)

def code : List UInt8 :=
  [0x5f,0x35,0x80,0x60,0xa0,0x52,0x5f,0x55,0x60,0x20,0x35,0x60,0x13,0x57,
    0x60,0x20,0x60,0xa0,0xf3,0x5b,0x5f,0x5f,0xfd]

def input (value : Word) (fail : Bool) : Input :=
  {calldata := wordBytes value ++ wordBytes (if fail then 1 else 0)}

def initial (storage : Stateful.Slots) (memory : Memory) (warm : Word → Bool) (refund : Int) : Stateful.State :=
  {storage,machine := {memory,memoryWords := 6},warm,refund}

/-- Physical byte coherence for the entry's fixed six-word high-water mark.
The generic raw target trace below does not derive entry reachability. Its
source/target consumer supplies this independent related-state condition. -/
def MemoryCoherent (memory : Memory) : Prop := ∀ address, 192 ≤ address → memory address = 0

theorem MemoryCoherent.payload (coherent : MemoryCoherent memory) (value : Word) :
    MemoryCoherent (memory.write 160 (wordBytes value)) := by
  intro address above
  simpa [Memory.write,Contract.Interaction.wordBytes_length,
    show ¬address < 160+32 by omega] using coherent address above

def finalState (storage : Stateful.Slots) (memory : Memory) (original : Stateful.Slots)
    (warm : Word → Bool) (refund : Int) (value : Word) (fail : Bool) : Stateful.State := {
  machine := {
    pc := if fail then 22 else 18
    stack := if fail then [0,0] else [160,32]
    memory := memory.write 160 (wordBytes value)
    memoryWords := 6 },
  storage := Stateful.write storage 0 value, warm := Stateful.warmKey warm 0,
  refund := refund + Stateful.refundDelta (original 0) (storage 0) value }

def result (storage : Stateful.Slots) (memory : Memory) (original : Stateful.Slots)
    (warm : Word → Bool) (refund : Int) (value : Word) (fail : Bool) : Stateful.Result :=
  ⟨if fail then .reverted [] else .returned (wordBytes value),finalState storage memory original warm refund value fail⟩

theorem padded_append_left (left right : List UInt8) : Evm.padded (left ++ right) 0 left.length = left := by
  apply List.ext_getElem
  · simp [Evm.padded,Memory.read]
  · intro index inside actual
    simp only [Evm.padded,Memory.read,List.getElem_map,List.getElem_range]
    simp [List.getElem?_append_left actual,actual]

theorem padded_append_right (left right : List UInt8) : Evm.padded (left ++ right) left.length right.length = right := by
  apply List.ext_getElem
  · simp [Evm.padded,Memory.read]
  · intro index inside actual
    simp only [Evm.padded,Memory.read,List.getElem_map,List.getElem_range]
    simp [actual]

theorem input_value (value : Word) (fail : Bool) : Evm.loadWord (input value fail).calldata 0 = value := by
  unfold Evm.loadWord input
  rw [← Contract.Interaction.wordBytes_length value,padded_append_left,Contract.Interaction.bytesWord_wordBytes]

theorem input_flag (value : Word) (fail : Bool) :
    Evm.loadWord (input value fail).calldata 32 = if fail then 1 else 0 := by
  change bytesWord (Evm.padded (wordBytes value ++ wordBytes (if fail then 1 else 0))
    (wordBytes value).length (wordBytes (if fail then 1 else 0)).length) = _
  rw [padded_append_right,Contract.Interaction.bytesWord_wordBytes]

theorem payload_read (memory : Memory) (value : Word) :
    (memory.write 160 (wordBytes value)).read 160 32 = wordBytes value := by
  rw [← Contract.Interaction.wordBytes_length value]
  exact Memory.read_write _ _ _

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem target_trace (storage original : Stateful.Slots) (memory : Memory) (warm : Word → Bool)
    (refund : Int) (value : Word) (fail : Bool) :
    ∃ used needed, Stateful.run code (input value fail) ⟨original,false⟩ 24 (initial storage memory warm refund) =
      .finished used needed (result storage memory original warm refund value fail) := by
  cases fail
  all_goals
    simp [Stateful.run,Guarded.run,Stateful.step,Stateful.coreStep,Evm.step,Evm.push,
      code,initial,input_value,input_flag,Guarded.Trace.charge,Evm.pushWidth,Evm.padded,
      Evm.scanJumps,Evm.jumpDestinations,Memory.read,bytesWord,
      Evm.expansionCost,Evm.expandedWords,Evm.memoryCost,
      result,finalState,payload_read]
    all_goals exact payload_read memory value

theorem target_metered (storage original : Stateful.Slots) (memory : Memory) (warm : Word → Bool)
    (refund : Int) (value : Word) (fail : Bool) :
    ∃ used needed, used ≤ needed ∧ ∀ gas,
      Stateful.runMetered code (input value fail) ⟨original,false⟩ 24 gas (initial storage memory warm refund) =
        if needed ≤ gas then .finished (gas-used) (result storage memory original warm refund value fail)
        else .exceptional := by
  obtain ⟨used,needed,trace⟩ := target_trace storage original memory warm refund value fail
  exact ⟨used,needed,Guarded.used_le_needed _ _ _ _ _ _ trace,
    fun gas => Guarded.metered_of_run _ _ _ _ _ _ gas trace⟩

end Solidity.Pilots.AliasCallRollback.Target
