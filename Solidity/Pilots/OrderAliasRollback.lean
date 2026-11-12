/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Pilots.AliasCallRollback

/-! An order-sensitive prepared-body experiment. Both memory references point
to one initially zero word. The body writes storage, evaluates
`(a[0] = x) + b[0]`, then either returns or explicitly reverts. The write-first
schedule can overflow; the read-first schedule cannot. -/
namespace Solidity.Pilots.OrderAliasRollback
open Static Aggregates Execution Execution.Safety
open Contract.Interaction (Word Memory wordBytes bytesWord)
open AliasCallRollback
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def result (writeFirst : Bool) (value : Word) : Word := if writeFirst then value+value else value
def overflows (writeFirst : Bool) (value : Word) : Bool := writeFirst && decide (2^255 ≤ value.toNat)

def expression (value : Word) : Expr EmptyKey :=
  .binary (.arithmetic .add) word (.assign (element 0) (number value)) (.read (element 1))

def body (owner : BitVec 160) (value : Word) (fail : Bool) : Stmt EmptyKey :=
  .seq (.expr (.assign (persistent owner) (number value)))
    (.seq (.declare [some ⟨2,word,none⟩] (some (expression value)))
      (.if_ (.literal ⟨.bool,fail⟩) (.revert []) (.return_ (some (.local 2 word)))))

def state (heap : Heap) (budget : Nat) : MachineState Unit :=
  {AliasCallRollback.initial heap with materializationRemaining := budget}

def after (heap : Heap) (owner : BitVec 160) (value answer : Word) (budget : Nat) : MachineState Unit :=
  {state heap budget with
    heap := updatedHeap heap owner value
    locals := [[(2,⟨word,some answer⟩),(1,⟨array,some (reference heap)⟩),(0,⟨array,some (reference heap)⟩)]]}

def observation (heap : Heap) (owner : BitVec 160) (value : Word) (writeFirst fail : Bool) (budget : Nat) : Observation Unit :=
  if overflows writeFirst value then .failed (.panic 0x11) (state heap budget)
  else if fail then .failed (.revert []) (state heap budget)
  else .returned [.atom ⟨word,result writeFirst value⟩] (after heap owner value (result writeFirst value) budget)

def source (heap : Heap) (owner : BitVec 160) (value : Word) (writeFirst fail : Bool) (budget : Nat) :=
  Machine.execute physicalBackend registry {} (program owner) 80
    (List.replicate 80 (if writeFirst then 0 else 1)) (Config.start (state heap budget) (body owner value fail))

theorem admitted (heap : Heap) (owner : BitVec 160) (value : Word) (fail : Bool) (budget : Nat) :
    Admission.admitStatement registry 128 (state heap budget).locals [⟨999,word,none⟩] (body owner value fail) = .ok () := by
  rfl

theorem add_word (left right : Word) :
    Effects.binary .checked (.arithmetic .add) ⟨word,left⟩ ⟨word,right⟩ =
      if left.toNat+right.toNat < 2^256 then .ok ⟨word,left+right⟩ else .error (.panic 0x11) := by
  change (Effects.liftCore (Core.unsigned 31 .checked .add left right) >>=
    fun value => Except.ok (⟨word,value⟩ : Execution.Value)) = _
  have equation : Core.unsigned 31 .checked .add left right =
      (if left.toNat+right.toNat < 2^256 then .ok (left+right) else .error (Contract.panic 0x11)) := by
    simp only [Core.unsigned, show (31 : Core.Width).bits = 256 from rfl,
      show (Core.ArithmeticMode.checked == Core.ArithmeticMode.unchecked) = false from rfl,
      Bool.false_or,decide_eq_true_eq]
    rfl
  rw [equation]
  split <;> simp [Effects.liftCore,Effects.failureOfBytes_panic]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
theorem source_execution (represented : WordArena.Represents heap object)
    (zero : heap.execution.memory.read 160 32 = wordBytes 0)
    (writable : heap.execution.context.readOnly = false)
    (owner : BitVec 160) (value : Word) (writeFirst fail : Bool) (budget : Nat) :
    source heap owner value writeFirst fail budget =
      .finished (observation heap owner value writeFirst fail budget) := by
  let stored : Heap := {heap with execution := {heap.execution with
    world := heap.execution.world.store (owner.setWidth 256) (BitVec.ofNat 256 0) value}}
  have storedRep : WordArena.Represents stored object :=
    ⟨represented.above,represented.bounded,represented.extent,represented.header⟩
  have indexed := index_zero storedRep
  have writeMemory (locals : Locals) (budget : Nat) := write_cell storedRep locals budget value
  have localStored0 : Effects.readCaptured registry 128 (aliases heap) stored (.local 0 array) =
      .ok ⟨array,reference stored⟩ := read_reference (by rfl)
  have localStored1 : Effects.readCaptured registry 128 (aliases heap) stored (.local 1 array) =
      .ok ⟨array,reference stored⟩ := read_reference (by rfl)
  have localAfter1 : Effects.readCaptured registry 128 (aliases heap) (updatedHeap heap owner value) (.local 1 array) =
      .ok ⟨array,reference (updatedHeap heap owner value)⟩ := read_reference (by rfl)
  dsimp only [stored,updatedHeap,aliases] at localStored0 localStored1 localAfter1
  have representedAfter := updated_represents represented owner value
  have indexedAfter := index_zero representedAfter
  have readBefore (locals : Locals) := WordEffects.read_cell (registry := registry) (fuel := 127)
    (locals := locals) storedRep (index := 0) (by decide)
  have readAfter (locals : Locals) := WordEffects.read_cell (registry := registry) (fuel := 127)
    (locals := locals) representedAfter (index := 0) (by decide)
  dsimp only [stored,updatedHeap] at indexed writeMemory indexedAfter readBefore readAfter
  simp only [object_offset_zero,zero,show bytesWord (wordBytes (0 : Word)) = 0 from by decide] at readBefore
  simp only [object_offset_zero,Memory.bytesWord_read_word_write] at readAfter
  have bounded := value.isLt
  unfold source Machine.execute
  cases writeFirst <;> cases fail <;> by_cases small : value.toNat < 2^255
  all_goals
    have doubling : (value.toNat+value.toNat < 2^256) ↔ (value.toNat < 2^255) := by omega
    alias_pilot_steps [body,state,expression,after,observation,overflows,result,
      indexed,writeMemory,indexedAfter,readBefore,readAfter,localStored0,localStored1,localAfter1,writable,add_word,small,doubling,bounded]

/-- The concrete trace is also a witness in the machine's permitted-execution
relation; no target equality or successful execution is an input premise. -/
theorem source_permitted (represented : WordArena.Represents heap object)
    (zero : heap.execution.memory.read 160 32 = wordBytes 0)
    (writable : heap.execution.context.readOnly = false)
    (owner : BitVec 160) (value : Word) (writeFirst fail : Bool) (budget : Nat) :
    Executes (Machine.step physicalBackend registry {} (program owner))
      (Config.start (state heap budget) (body owner value fail))
      (observation heap owner value writeFirst fail budget) :=
  Machine.execute_sound (source_execution represented zero writable owner value writeFirst fail budget)

end Solidity.Pilots.OrderAliasRollback
