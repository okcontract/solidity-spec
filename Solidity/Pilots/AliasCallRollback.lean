/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.WordEffects
import Solidity.Core.Execution.Safety.SupportedTransfers
import Solidity.Core.Execution.MachineProofs
import Solidity.Core.Execution.SourceFacade
import Solidity.Pilots.AliasCallRollbackTarget
import Contract.Evm.StorageFrames

/-! A manually paired, hand-authored artifact pilot. The source contains a
real internal call and two references to one preallocated memory array. The
target is a fixed Cancun byte program, not compiler-produced code. Inputs and
related stores are quantified; neither side assumes successful evaluation.
Source parsing, allocation of the entry packet and general compiler
preservation remain outside this deliberately narrow theorem. -/
namespace Solidity.Pilots.AliasCallRollback
open Static Aggregates Execution
open Execution.Safety
open Contract.Interaction (Word Memory wordBytes bytesWord)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }

abbrev word : SType := .uint 31
abbrev array : SType := WordArena.arrayType true
def object : WordArena.Object := ⟨128,1⟩
def reference (heap : Heap) : Reference := object.reference heap
def aliases (heap : Heap) : Locals :=
  [[(1,⟨array,some (reference heap)⟩),(0,⟨array,some (reference heap)⟩)]]
def initial (heap : Heap) : MachineState Unit := {external := (),heap,locals := aliases heap}

def number (value : Word) : Expr EmptyKey := .literal ⟨word,value⟩
def arrayLocal (id : Nat) : Expr EmptyKey := .local id array
def element (id : Nat) : LValue EmptyKey := .index word (arrayLocal id) (number 0)
def persistent (owner : BitVec 160) : LValue EmptyKey := .heap (WordEffects.persistent owner 0)

def helper (owner : BitVec 160) : FunctionDefinition EmptyKey := {
  parameters := [⟨10,array,none⟩,⟨11,word,none⟩], returns := [],
  body := .seq (.expr (.assign (element 10) (.local 11 word)))
    (.seq (.expr (.assign (persistent owner) (.local 11 word))) (.return_ none)) }
def signature : FunctionSignature := (helper 0).signature
def program (owner : BitVec 160) : Program EmptyKey := ⟨[(7,helper owner)]⟩

def body (value : Word) (fail : Bool) : Stmt EmptyKey :=
  .seq (.expr (.call signature (.literal ⟨signature.type,some 7⟩) [arrayLocal 0,number value]))
    (.if_ (.literal ⟨.bool,fail⟩) (.revert []) (.return_ (some (.read (element 1)))))

def updatedHeap (heap : Heap) (owner : BitVec 160) (value : Word) : Heap :=
  {heap with execution := {heap.execution with
    memory := heap.execution.memory.write 160 (wordBytes value),
    world := heap.execution.world.store (owner.setWidth 256) (BitVec.ofNat 256 0) value}}

def updatedState (heap : Heap) (owner : BitVec 160) (value : Word) : MachineState Unit :=
  {initial heap with heap := updatedHeap heap owner value}

theorem alias_equality (heap : Heap) :
    (aliases heap).read 0 array = .ok ⟨array,reference heap⟩ ∧
      (aliases heap).read 1 array = .ok ⟨array,reference heap⟩ := ⟨rfl,rfl⟩

private theorem eligible_array : eligibleType registry 128 array = .ok () := rfl

theorem read_reference {locals : Locals} {id : LocalId} {heap : Heap}
    (localRead : locals.read id array = .ok ⟨array,reference heap⟩) :
    Effects.readCaptured registry 128 locals heap (.local id array) = .ok ⟨array,reference heap⟩ := by
  have eligible : eligibleAt registry 128 (.memory heap.invocation) array = .ok () := rfl
  have valid : Access.validate heap ⟨array,reference heap⟩ = .ok () :=
    Copy.memory_validate_reference (by rfl)
  simp only [Effects.readCaptured,eligible_array,localRead,Bind.bind,Except.bind]
  change Access.readChecked registry 128 heap ⟨array,reference heap⟩ = .ok ⟨array,reference heap⟩
  simp only [Access.readChecked,show (reference heap).region = .memory heap.invocation from rfl,eligible,
    Bind.bind,Except.bind,Access.read,valid]
  rfl

theorem read_alias (heap : Heap) (id : Nat) (inside : id = 0 ∨ id = 1) :
    Effects.readCaptured registry 128 (aliases heap) heap (.local id array) = .ok ⟨array,reference heap⟩ := by
  apply read_reference
  rcases inside with rfl | rfl
  · exact (alias_equality heap).1
  · exact (alias_equality heap).2

theorem bind_alias (represented : WordArena.Represents heap object) (budget : Nat) :
    Copy.bind registry 128 budget heap array ⟨array,reference heap⟩ =
      .ok (⟨array,reference heap⟩,heap,budget) := by
  have planned : planTransfer registry 128 true array array = .ok .memoryAlias := rfl
  have extent : heap.allocated 128 0 = true :=
    Copy.allocated_subrange heap 128 64 128 0 represented.extent (by omega) (by omega)
  apply Copy.bind_alias planned (Or.inr (Or.inl rfl))
  have valid : Access.validate heap ⟨array,reference heap⟩ = .ok () :=
    Copy.memory_validate_reference (by rfl)
  change (do Access.validate heap ⟨array,reference heap⟩
             checkExtent heap (reference heap) 0
             Copy.retag array {reference heap with bindingCell := none}) = _
  simp only [valid,Bind.bind,Except.bind]
  have extentChecked : checkExtent heap (reference heap) 0 = .ok () := by
    simp [checkExtent,reference,object,WordArena.Object.reference,Copy.memoryReference,extent]
  simp only [extentChecked]
  rfl

def sourceRun (heap : Heap) (owner : BitVec 160) (value : Word) (fail : Bool) :=
  Machine.execute physicalBackend registry {} (program owner) 128 [] (Config.start (initial heap) (body value fail))

theorem bind_word (heap : Heap) (budget : Nat) (value : Word) :
    Copy.bind registry 128 budget heap word ⟨word,value⟩ = .ok (⟨word,value⟩,heap,budget) :=
  Copy.bind_scalar (WordEffects.plan_word registry 127 true) (by rfl)

theorem read_word {locals : Locals} {id : LocalId} {value : Word}
    (localRead : locals.read id word = .ok ⟨word,value⟩) :
    Effects.readCaptured registry 128 locals heap (.local id word) = .ok ⟨word,value⟩ := by
  simp only [Effects.readCaptured,show eligibleType registry 128 word = .ok () from rfl,
    Bind.bind,Except.bind,localRead]
  rfl

theorem write_persistent (heap : Heap) (owner : BitVec 160) (value : Word) (locals : Locals) (budget : Nat)
    (writable : heap.execution.context.readOnly = false) :
    Effects.writeCaptured registry 128 budget locals heap (.heap (WordEffects.persistent owner (BitVec.ofNat 256 0))) ⟨word,value⟩ =
      .ok (locals,{heap with execution := {heap.execution with
        world := heap.execution.world.store (owner.setWidth 256) 0 value}},budget) := by
  rw [WordEffects.write_persistent (fuel := 127)]
  simp [Slot.write,writable]

private theorem write_local (locals : Locals) (heap : Heap) (id : LocalId) (type : SType) (source : Aggregates.Value) (budget : Nat) :
    Effects.writeCaptured registry 128 budget locals heap (.local id type) source = (do
      let current ← locals.typeOf id
      if current != type then throw (Aggregates.Failure.invalidContext "captured local type mismatch")
      let (value,after,remaining) ← Copy.bind registry 128 budget heap type source
      return (← locals.write id type value,after,remaining)) := rfl

theorem write_cell (represented : WordArena.Represents heap object) (locals : Locals) (budget : Nat) (value : Word) :
    Effects.writeCaptured registry 128 budget locals heap (.heap (object.cell heap 0)) ⟨word,value⟩ =
      .ok (locals,MemoryOps.snapshotCopy heap 160 (wordBytes value),budget) :=
  WordEffects.write_cell (fuel := 127) represented (by decide) value

theorem cell_type (heap : Heap) : (object.cell heap 0).type = word := rfl

theorem persistent_type (owner : BitVec 160) (address : Word) : (WordEffects.persistent owner address).type = word := rfl

theorem object_offset_zero : object.offset 0 = 160 := rfl

theorem updated_represents (represented : WordArena.Represents heap object) (owner : BitVec 160) (value : Word) :
    WordArena.Represents (updatedHeap heap owner value) object where
  above := represented.above
  bounded := represented.bounded
  extent := represented.extent
  header := (Memory.read_write_disjoint heap.execution.memory 128 32 160 (wordBytes value)
    (Or.inl (by decide))).trans represented.header

theorem lookup_helper (owner : BitVec 160) : (program owner).lookup 7 = .ok (helper owner) := by rfl

theorem callee_cast : Effects.scalarCast .implicit
    (.function .internal .nonpayable (.cons array (.cons word .nil)) .nil)
    ⟨.function .internal .nonpayable (.cons array (.cons word .nil)) .nil,some 7⟩ =
      .ok ⟨.function .internal .nonpayable (.cons array (.cons word .nil)) .nil,some 7⟩ := by rfl

theorem word_cast (value : Word) : Effects.scalarCast .implicit word ⟨word,value⟩ = .ok ⟨word,value⟩ := by rfl

theorem index_zero (represented : WordArena.Represents heap object) :
    Effects.index registry 128 heap ⟨array,reference heap⟩ ⟨word,BitVec.ofNat 256 0⟩ = .ok (object.cell heap 0) :=
  WordEffects.index_inside (fuel := 126) (index := (0 : BitVec (31 : Core.Width).bits)) represented (by decide) true

theorem checked_cell (heap : Heap) : Machine.checkedTarget (Key := EmptyKey) word (object.cell heap 0) =
    .ok (.captured (.heap (object.cell heap 0))) := by rfl

/-- The public entry passes references from initialized caller cells; no
reference-valued literal is used as a Solidity source expression. -/
def entryLocals (heap : Heap) (value : Word) (fail : Bool) : Locals :=
  [[(3,⟨.bool,some fail⟩),(2,⟨word,some value⟩),
    (1,⟨array,some (reference heap)⟩),(0,⟨array,some (reference heap)⟩)]]
def entryState (heap : Heap) (value : Word) (fail : Bool) (budget : Nat := 4096) : MachineState Unit :=
  {external := (),heap,locals := entryLocals heap value fail,materializationRemaining := budget}
def entryFunction : FunctionDefinition EmptyKey := {
  parameters := [⟨0,array,none⟩,⟨1,array,none⟩,⟨2,word,none⟩,⟨3,.bool,none⟩],
  returns := [⟨4,word,none⟩],
  body := .seq (.expr (.call signature (.literal ⟨signature.type,some 7⟩) [arrayLocal 0,.local 2 word]))
    (.if_ (.local 3 .bool) (.revert []) (.return_ (some (.read (element 1))))) }
def entrySignature : FunctionSignature := entryFunction.signature
def entryProgram (owner : BitVec 160) : Program EmptyKey := ⟨[(7,helper owner),(8,entryFunction)]⟩
def entryExpression : Expr EmptyKey :=
  .call entrySignature (.literal ⟨entrySignature.type,some 8⟩)
    [arrayLocal 0,arrayLocal 1,.local 2 word,.local 3 .bool]

theorem lookup_entry (owner : BitVec 160) : (entryProgram owner).lookup 8 = .ok entryFunction := by rfl
theorem entry_lookup_helper (owner : BitVec 160) : (entryProgram owner).lookup 7 = .ok (helper owner) := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem checked_entry (heap : Heap) (owner : BitVec 160) (value : Word) (fail : Bool) (budget : Nat := 4096) :
    SourceFacade.prepareExpression registry {} (entryProgram owner) (entryState heap value fail budget) entryExpression =
      .ok (Config.expression (entryState heap value fail budget) entryExpression) := by rfl

theorem bind_bool (heap : Heap) (budget : Nat) (value : Bool) :
    Copy.bind registry 128 budget heap .bool ⟨.bool,value⟩ = .ok (⟨.bool,value⟩,heap,budget) := by rfl

theorem read_bool {locals : Locals} {id : LocalId} {value : Bool}
    (localRead : locals.read id .bool = .ok ⟨.bool,value⟩) :
    Effects.readCaptured registry 128 locals heap (.local id .bool) = .ok ⟨.bool,value⟩ := by
  simp only [Effects.readCaptured,show eligibleType registry 128 .bool = .ok () from rfl,
    Bind.bind,Except.bind,localRead]
  rfl

theorem default_word (heap : Heap) (budget : Nat) :
    Effects.defaultLocal registry 128 budget heap word = .ok (some ⟨word,0⟩,heap,budget) := by rfl

theorem entry_callee_cast : Effects.scalarCast .implicit
    (.function .internal .nonpayable (.cons array (.cons array (.cons word (.cons .bool .nil)))) (.cons word .nil))
    ⟨.function .internal .nonpayable (.cons array (.cons array (.cons word (.cons .bool .nil)))) (.cons word .nil),some 8⟩ =
      .ok ⟨.function .internal .nonpayable (.cons array (.cons array (.cons word (.cons .bool .nil)))) (.cons word .nil),some 8⟩ := by rfl

/- Each iteration reduces one actual head transition. Keeping `run` out of
the simplifier prevents reduction of unreachable runner branches. The same
normalizer is shared by the body and the checked ordinary-call entry proofs. -/
macro "alias_pilot_steps" "[" facts:term,* "]" : tactic =>
  `(tactic|
    repeat
      rw [run]
      simp [Config.start,Config.expression,body,initial,entryExpression,entryState,entryLocals,entryFunction,entrySignature,
        Machine.step,Machine.transition,Machine.next,Machine.gather,Machine.apply,Machine.commit,
        Machine.readTarget,Machine.typed,checked_cell,Machine.pick,Machine.ordered,Machine.orderPairs,Machine.insertOrdered,
        Machine.invoke,Machine.prepareArguments,Machine.bindArguments,Machine.declareValues,Machine.declareUnset,Machine.declareReturn,
        Machine.collectResults,Machine.finishCall,Machine.assignmentResult,Machine.writeTarget,Machine.resultWrites,Machine.boolean,
        lookup_helper,lookup_entry,entry_lookup_helper,callee_cast,entry_callee_cast,word_cast,signature,helper,FunctionDefinition.signature,
        FunctionSignature.type,FunctionSignature.accepts,FunctionSignature.resultType,Types.ofList,typesList,Mutability.allows,
        arrayLocal,element,number,persistent,aliases,Locals.read,Locals.find,Scope.find,Locals.declare,Locals.empty,
        Locals.typeOf,Locals.write,Locals.replace,Scope.replace,
        Datum.asAtom,Datum.asPacket,Datum.ofPacket,Datum.type,Effects.convert,Effects.declareLocal,Effects.declareReturn,default_word,
        read_reference,read_word,read_bool,eligible_array,bind_word,bind_bool,write_persistent,
        write_local,Captured.type,cell_type,persistent_type,
        WordEffects.plan_word,WordEffects.convert_word,
        Effects.assignmentResult,isReference,referenceLocation,updatedState,updatedHeap,MemoryOps.snapshotCopy,
        Memory.bytesWord_read_word_write,object_offset_zero,
        WordEffects.eligible_persistent,WordEffects.validate_persistent,
        Execution.isSourceFailure,Execution.fail,Bind.bind,Except.bind,Pure.pure,Except.pure,$[$facts:term],*]
      try simp only [Bind.bind,Except.bind,checked_cell,$[$facts:term],*])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem source_run (represented : WordArena.Represents heap object)
    (writable : heap.execution.context.readOnly = false) (owner : BitVec 160) (value : Word) (fail : Bool) :
    sourceRun heap owner value fail = .finished (if fail then .failed (.revert []) (initial heap)
      else .returned [.atom ⟨word,value⟩] (updatedState heap owner value)) := by
  have bind := bind_alias represented
  have indexed := index_zero represented
  have writeMemory (locals : Locals) (budget : Nat) := write_cell represented locals budget value
  have representedAfter := updated_represents represented owner value
  have indexedAfter := index_zero representedAfter
  dsimp only [updatedHeap] at indexedAfter
  have readMemory (locals : Locals) := WordEffects.read_cell (registry := registry) (fuel := 127)
    (locals := locals) representedAfter (index := 0) (by decide)
  dsimp only [updatedHeap] at readMemory
  simp only [object_offset_zero] at readMemory
  have readAliasAfter : Effects.readCaptured registry 128 (aliases heap) (updatedHeap heap owner value) (.local 1 array) =
      .ok ⟨array,reference (updatedHeap heap owner value)⟩ := by
    apply read_reference
    rfl
  dsimp only [aliases,updatedHeap] at readAliasAfter
  unfold sourceRun Machine.execute
  cases fail
  all_goals
    alias_pilot_steps [bind,indexed,writeMemory,indexedAfter,readMemory,readAliasAfter,writable]

def updatedEntry (heap : Heap) (owner : BitVec 160) (value : Word) (fail : Bool) (budget : Nat := 4096) : MachineState Unit :=
  {entryState heap value fail budget with heap := updatedHeap heap owner value}

def entryRun (heap : Heap) (owner : BitVec 160) (value : Word) (fail : Bool) (budget : Nat := 4096) :=
  SourceFacade.executeExpression physicalBackend registry {} (entryProgram owner) 160 []
    (entryState heap value fail budget) entryExpression

/- The primary source witness starts at the checked public expression entry.
Both ordinary calls, all reference/scalar parameters, the named result cell and
caller restoration execute through the actual continuation machine. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
theorem entry_run (represented : WordArena.Represents heap object)
    (writable : heap.execution.context.readOnly = false) (owner : BitVec 160) (value : Word) (fail : Bool)
    (budget : Nat := 4096) :
    entryRun heap owner value fail budget = .ok (.finished (if fail then .failed (.revert []) (entryState heap value fail budget)
      else .returned [.atom ⟨word,value⟩] (updatedEntry heap owner value fail budget))) := by
  have bind := bind_alias represented
  have indexed := index_zero represented
  have writeMemory (locals : Locals) (budget : Nat) := write_cell represented locals budget value
  have representedAfter := updated_represents represented owner value
  have indexedAfter := index_zero representedAfter
  dsimp only [updatedHeap] at indexedAfter
  have readMemory (locals : Locals) := WordEffects.read_cell (registry := registry) (fuel := 127)
    (locals := locals) representedAfter (index := 0) (by decide)
  dsimp only [updatedHeap] at readMemory
  simp only [object_offset_zero] at readMemory
  have readAliasAfter (locals : Locals) (id : Nat)
      (read : locals.read id array = .ok ⟨array,reference heap⟩) :
      Effects.readCaptured registry 128 locals (updatedHeap heap owner value) (.local id array) =
        .ok ⟨array,reference (updatedHeap heap owner value)⟩ := by
    apply read_reference
    exact read
  dsimp only [updatedHeap] at readAliasAfter
  unfold entryRun SourceFacade.executeExpression
  rw [checked_entry (budget := budget)]
  simp only [Bind.bind,Except.bind]
  apply congrArg Except.ok
  unfold Machine.execute
  cases fail
  all_goals
    dsimp only [updatedEntry]
    alias_pilot_steps [bind,indexed,writeMemory,indexedAfter,readMemory,readAliasAfter,writable]

theorem entry_alias_equality (heap : Heap) (value : Word) (fail : Bool) :
    (entryState heap value fail).locals.read 0 array = .ok ⟨array,reference heap⟩ ∧
      (entryState heap value fail).locals.read 1 array = .ok ⟨array,reference heap⟩ := ⟨rfl,rfl⟩

theorem entry_executes (represented : WordArena.Represents heap object)
    (writable : heap.execution.context.readOnly = false) (owner : BitVec 160) (value : Word) (fail : Bool) :
    Executes (Machine.step physicalBackend registry {} (entryProgram owner))
      (Config.expression (entryState heap value fail) entryExpression)
      (if fail then .failed (.revert []) (entryState heap value fail)
        else .returned [.atom ⟨word,value⟩] (updatedEntry heap owner value fail)) := by
  have checked := entry_run represented writable owner value fail
  unfold entryRun SourceFacade.executeExpression at checked
  rw [checked_entry] at checked
  simp only [Bind.bind,Except.bind,Pure.pure,Except.pure,Except.ok.injEq] at checked
  exact Machine.execute_sound checked

/-- Persistent world observations shared by the two existing models. The EVM
account map has 160-bit keys, so source storage at noncanonical wider addresses
is covered by the separate source frame law rather than silently identified.
Transient storage is preserved by the source program; this target subset does
not contain transient instructions. -/
structure Related (heap : Heap) (world : Contract.Evm.World) : Prop where
  storage : ∀ owner slot, heap.execution.world.storage (owner.setWidth 256) slot = world.storage owner slot
  logs : heap.execution.world.logs = world.logs
  other : heap.execution.world.other = world.other
  balances : ∀ owner, (heap.execution.world.accounts owner).balance.toNat = world.balances owner
  nonces : ∀ owner, (heap.execution.world.accounts owner).nonce.toNat = world.nonces owner
  code : ∀ owner, (heap.execution.world.accounts owner).code = world.code owner
  /-- The target entry has exactly six active memory words. -/
  memory : Target.MemoryCoherent heap.execution.memory

private theorem widened_owner (a b : BitVec 160) : a.setWidth 256 = b.setWidth 256 ↔ a = b := by
  constructor
  · intro same
    have narrowed := congrArg (BitVec.setWidth 160) same
    simpa [BitVec.setWidth_setWidth_of_le _ (by decide : 160 ≤ 256)] using narrowed
  · rintro rfl; rfl

theorem Related.updated (related : Related heap world) (owner : BitVec 160) (value : Word) :
    Related (updatedHeap heap owner value)
      (Contract.Evm.Stateful.World.store world owner (Contract.Evm.Stateful.write (world.storage owner) 0 value)) := by
  refine ⟨?_,related.logs,related.other,related.balances,related.nonces,related.code,
    related.memory.payload value⟩
  intro account key
  by_cases same : account = owner
  · subst account
    simp [updatedHeap,Contract.Interaction.World.store,Contract.Evm.Stateful.World.store,
      Contract.Evm.Stateful.write,related.storage]
  · have different : account.setWidth 256 ≠ owner.setWidth 256 := fun equal => same ((widened_owner _ _).mp equal)
    simp [updatedHeap,Contract.Interaction.World.store,Contract.Evm.Stateful.World.store,
      different,same,related.storage]

def targetObservation (world : Contract.Evm.World) (transaction : Contract.Evm.Stateful.Transaction)
    (context : Contract.Context) (memory : Memory) (value : Word) (fail : Bool) (gas : Nat) : Contract.Evm.Stateful.Frame :=
  Contract.Evm.Stateful.observe world transaction context (Target.input value fail)
    (Contract.Evm.Stateful.runMetered Target.code (Target.input value fail)
      ⟨transaction.original context.self,false⟩ 24 gas
      (Target.initial (world.storage context.self) memory (transaction.warm context.self) transaction.refund))

def Observes (source : Observation Unit) (target : Contract.Evm.Stateful.Frame) : Prop :=
  match source with
  | .returned [.atom ⟨.uint 31,value⟩] after =>
      target.status = .returned ∧ target.bytes = wordBytes value ∧ Related after.heap target.world
  | .failed (.revert bytes) before =>
      target.status = .reverted ∧ target.bytes = bytes ∧ Related before.heap target.world
  | _ => False

theorem target_revert_rollback (world : Contract.Evm.World) (transaction : Contract.Evm.Stateful.Transaction)
    (context : Contract.Context) (memory : Memory) (value : Word) :
    ∃ used needed, ∀ gas, needed ≤ gas → targetObservation world transaction context memory value true gas =
      ⟨⟨.reverted,[],world,gas-used⟩,transaction⟩ := by
  obtain ⟨used,needed,_,metered⟩ := Target.target_metered
    (world.storage context.self) (transaction.original context.self) memory
    (transaction.warm context.self) transaction.refund value true
  refine ⟨used,needed,?_⟩
  intro gas enough
  unfold targetObservation
  rw [metered gas,if_pos enough]
  rfl

/-- All target executions with sufficient gas have the derived permitted source
explanation. Insufficient gas is a separate target-only exceptional observation;
it restores the complete target world and transaction snapshot. -/
theorem refines (represented : WordArena.Represents heap object)
    (writable : heap.execution.context.readOnly = false) (related : Related heap world)
    (transaction : Contract.Evm.Stateful.Transaction) (context : Contract.Context) (value : Word) (fail : Bool)
    (budget : Nat := 4096) :
    ∃ observed used needed,
      entryRun heap context.self value fail budget = .ok (.finished observed) ∧ used ≤ needed ∧
      (∀ gas, needed ≤ gas → Observes observed (targetObservation world transaction context heap.execution.memory value fail gas)) ∧
      (∀ gas, needed ≤ gas →
        (targetObservation world transaction context heap.execution.memory value fail gas).gasRemaining = gas-used) ∧
      (∀ gas, gas < needed → targetObservation world transaction context heap.execution.memory value fail gas =
        ⟨⟨.exceptional,[],world,0⟩,transaction⟩) := by
  obtain ⟨used,needed,bounded,metered⟩ := Target.target_metered
    (world.storage context.self) (transaction.original context.self) heap.execution.memory
    (transaction.warm context.self) transaction.refund value fail
  refine ⟨_,used,needed,entry_run represented writable context.self value fail budget,bounded,?_,?_,?_⟩
  · intro gas enough
    unfold targetObservation
    rw [metered gas,if_pos enough]
    cases fail with
    | false =>
        simpa [Target.result,Target.finalState,Contract.Evm.Stateful.observe,
          Contract.Evm.World.transfer,Target.input,Observes] using related.updated context.self value
    | true =>
        simpa [Target.result,Target.finalState,Contract.Evm.Stateful.observe,
          Contract.Evm.World.transfer,Target.input,Observes] using related
  · intro gas enough
    unfold targetObservation
    rw [metered gas,if_pos enough]
    cases fail <;> rfl
  · intro gas insufficient
    unfold targetObservation
    rw [metered gas,if_neg (by omega)]
    rfl

theorem updated_other_slot (heap : Heap) (owner : BitVec 160) (value key : Word) (different : key ≠ 0) :
    (updatedHeap heap owner value).execution.world.storage (owner.setWidth 256) key =
      heap.execution.world.storage (owner.setWidth 256) key := by
  simp [updatedHeap,Contract.Interaction.World.store]
  intro equal
  exact False.elim (different equal)

theorem updated_other_owner (heap : Heap) (owner : BitVec 160) (value other key : Word)
    (different : other ≠ owner.setWidth 256) :
    (updatedHeap heap owner value).execution.world.storage other key = heap.execution.world.storage other key := by
  simp [updatedHeap,Contract.Interaction.World.store,different]

theorem updated_memory_frame (heap : Heap) (owner : BitVec 160) (value : Word) (offset size : Nat)
    (separate : offset+size ≤ 160 ∨ 192 ≤ offset) :
    (updatedHeap heap owner value).execution.memory.read offset size = heap.execution.memory.read offset size := by
  exact Memory.read_write_disjoint _ _ _ _ _ (by simpa using separate)

end Solidity.Pilots.AliasCallRollback
