/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.WordArena
import Solidity.Core.Execution.Safety.ScalarProgress
import Solidity.Core.Execution.BindingsLaws

/-! A physical, initialized state profile for source-machine safety. Memory
references are actual descriptors of allocated uint256[] objects; aliases are
intentional. The predicate is independent of stepping and successful execution.
Other aggregate families have heap operations but are outside this
preservation/progress profile. -/
namespace Solidity.Execution.Safety
open Static Aggregates
open Contract.Interaction (Word)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

def Supported (type : SType) : Prop :=
  type.scalarSupported = true ∨ ∃ pointer, type = WordArena.arrayType pointer

inductive ValueRep (program : Program Key) (heap : Heap) (objects : List WordArena.Object) : Value → Prop where
  | scalar (supported : value.type.scalarSupported = true)
      (closed : ScalarProgress.ClosedFunction program value) : ValueRep program heap objects value
  | array (pointer : Bool) (object : WordArena.Object) (member : object ∈ objects) :
      ValueRep program heap objects ⟨WordArena.arrayType pointer, object.reference heap⟩
  | emptyArray (pointer : Bool) :
      ValueRep program heap objects ⟨WordArena.arrayType pointer, Copy.memoryReference heap 96⟩

theorem ValueRep.supported (represented : ValueRep program heap objects value) : Supported value.type := by
  cases represented with
  | scalar support _ => exact .inl support
  | array pointer _ _ => exact .inr ⟨pointer,rfl⟩
  | emptyArray pointer => exact .inr ⟨pointer,rfl⟩

theorem ValueRep.word (program : Program Key) (heap : Heap) (objects : List WordArena.Object) (word : Word) :
    ValueRep program heap objects ⟨.uint 31,word⟩ := .scalar rfl trivial

theorem ValueRep.boolean (program : Program Key) (heap : Heap) (objects : List WordArena.Object) (boolean : Bool) :
    ValueRep program heap objects ⟨.bool,boolean⟩ := .scalar rfl trivial

theorem ValueRep.extend (represented : ValueRep program before oldObjects value)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    ValueRep program after newObjects value := by
  cases represented with
  | scalar support closed => exact .scalar support closed
  | array pointer object member =>
      simpa only [WordArena.Object.reference,Copy.memoryReference,invocation] using
        (ValueRep.array (heap := after) pointer object (objects object member))
  | emptyArray pointer =>
      simpa only [Copy.memoryReference,invocation] using (ValueRep.emptyArray (heap := after) (objects := newObjects) pointer)

structure HeapRep (heap : Heap) (objects : List WordArena.Object) : Prop where
  arena : WordArena.WellFormed heap objects
  sharedZero : heap.allocated 96 32 = true

theorem HeapRep.empty (represented : HeapRep heap objects) : WordArena.Represents heap ⟨96,0⟩ where
  above := by decide
  bounded := by decide
  extent := represented.sharedZero
  header := represented.arena.zero

theorem ValueRep.array_object (represented : ValueRep program heap objects ⟨WordArena.arrayType pointer,reference⟩)
    (heapRep : HeapRep heap objects) :
    ∃ object, WordArena.Represents heap object ∧ reference = object.reference heap := by
  cases represented with
  | scalar support _ => simp [WordArena.arrayType,SType.scalarSupported] at support
  | array _ object member => exact ⟨object,heapRep.arena.represented object member,rfl⟩
  | emptyArray _ => exact ⟨⟨96,0⟩,heapRep.empty,rfl⟩

mutual
inductive DatumRep (program : Program Key) (heap : Heap) (objects : List WordArena.Object) : Datum → SType → Prop where
  | atom : ValueRep program heap objects value → DatumRep program heap objects (.atom value) value.type
  | tuple : PacketRep program heap objects values types → DatumRep program heap objects (.tuple values) (.tuple types)
inductive PacketRep (program : Program Key) (heap : Heap) (objects : List WordArena.Object) : Packet → Types → Prop where
  | nil : PacketRep program heap objects [] .nil
  | cons : DatumRep program heap objects value type → PacketRep program heap objects values types →
      PacketRep program heap objects (value :: values) (.cons type types)
end

mutual
theorem DatumRep.type (represented : DatumRep program heap objects value expected) : value.type = expected := by
  cases represented with
  | atom _ => rfl
  | tuple members => exact congrArg SType.tuple (PacketRep.types members)
theorem PacketRep.types (represented : PacketRep program heap objects values expected) : packetTypes values = expected := by
  cases represented with
  | nil => rfl
  | cons first rest => change Types.cons _ _ = _; rw [first.type,rest.types]
end

mutual
theorem DatumRep.extend (represented : DatumRep program before oldObjects value type)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    DatumRep program after newObjects value type := by
  cases represented with
  | atom value => exact .atom (value.extend invocation objects)
  | tuple members => exact .tuple (members.extend invocation objects)
theorem PacketRep.extend (represented : PacketRep program before oldObjects values types)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    PacketRep program after newObjects values types := by
  cases represented with
  | nil => exact .nil
  | cons first rest => exact .cons (first.extend invocation objects) (rest.extend invocation objects)
end

abbrev Environment := List (List (LocalId × SType))

def Scope.environment (scope : Scope) : List (LocalId × SType) :=
  scope.map fun (id,cell) => (id,cell.type)

def Locals.environment (locals : Locals) : Environment := locals.map Scope.environment

/-- Every live cell is initialized, including saved callers. The source
checker supplies declaration/type consistency; this predicate supplies the
physical content and closed-handle obligation that admission cannot inspect. -/
structure LocalsRep (program : Program Key) (heap : Heap) (objects : List WordArena.Object)
    (environment : Environment) (locals : Locals) : Prop where
  shape : Locals.environment locals = environment
  nonempty : locals ≠ []
  initialized : ∀ id cell, locals.find id = some cell →
    ∃ value, cell.value = some value ∧ ValueRep program heap objects ⟨cell.type,value⟩

theorem LocalsRep.read {id : LocalId} (represented : LocalsRep program heap objects environment locals)
    (bound : locals.find id = some cell) :
    ∃ value, locals.read id cell.type = .ok value ∧ ValueRep program heap objects value := by
  obtain ⟨value,initialized,rep⟩ := represented.initialized id cell bound
  exact ⟨⟨cell.type,value⟩,by simp [Locals.read,bound,initialized],rep⟩

theorem LocalsRep.extend (represented : LocalsRep program before oldObjects environment locals)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    LocalsRep program after newObjects environment locals := by
  refine ⟨represented.shape,represented.nonempty,?_⟩
  intro id cell bound
  obtain ⟨value,initialized,rep⟩ := represented.initialized id cell bound
  exact ⟨value,initialized,rep.extend invocation objects⟩

private theorem Scope.environment_find (scope : Scope) (id : LocalId) :
    ((scope.map fun (key,cell) => (⟨key,cell.type,none⟩ : Binder)).find? (fun binder => binder.id == id)) =
      (scope.find id).map (fun cell => (⟨id,cell.type,none⟩ : Binder)) := by
  induction scope with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key,cell⟩
      by_cases same : key = id
      · subst key; simp [Scope.find]
      · simp [Scope.find,same,ih]

theorem admission_find (locals : Locals) (id : LocalId) :
    (Admission.Context.ofLocals locals).find id =
      (locals.find id).map (fun cell => (⟨id,cell.type,none⟩ : Binder)) := by
  induction locals with
  | nil => rfl
  | cons scope rest ih =>
      simp only [Admission.Context.ofLocals,Admission.Context.find,List.map_cons,List.flatten_cons,List.find?_append]
      rw [Scope.environment_find]
      cases bound : scope.find id <;> simp_all [Locals.find,Admission.Context.ofLocals,Admission.Context.find]

/-- Actual admission lookup is connected to a represented local cell, rather
than a second unrelated symbol table. -/
theorem admission_local_read {id : LocalId} (represented : LocalsRep program heap objects environment locals)
    (bound : (Admission.Context.ofLocals locals).find id = some binder) :
    ∃ value, locals.read id binder.type = .ok value ∧ ValueRep program heap objects value := by
  rw [admission_find] at bound
  cases found : locals.find id with
  | none => simp [found] at bound
  | some cell =>
      simp only [found,Option.map_some,Option.some.injEq] at bound
      cases bound
      exact represented.read found

def CellRep (program : Program Key) (heap : Heap) (objects : List WordArena.Object) (cell : LocalCell) : Prop :=
  ∃ value, cell.value = some value ∧ ValueRep program heap objects ⟨cell.type,value⟩

def ScopeCellsRep (program : Program Key) (heap : Heap) (objects : List WordArena.Object) (scope : Scope) : Prop :=
  ∀ entry ∈ scope, CellRep program heap objects entry.2

def CellsRep (program : Program Key) (heap : Heap) (objects : List WordArena.Object) (locals : Locals) : Prop :=
  ∀ scope ∈ locals, ScopeCellsRep program heap objects scope

private theorem Scope.find_cell (represented : ScopeCellsRep program heap objects scope)
    (bound : scope.find key = some cell) : CellRep program heap objects cell := by
  induction scope with
  | nil => cases bound
  | cons entry rest ih =>
      rcases entry with ⟨id,old⟩
      by_cases same : id = key
      · simp only [Scope.find,same,↓reduceIte,Option.some.injEq] at bound
        cases bound
        exact represented (id,cell) (by simp)
      · simp only [Scope.find,same,↓reduceIte] at bound
        exact ih (fun entry member => represented entry (by simp [member])) bound

theorem CellsRep.find (represented : CellsRep program heap objects locals)
    (bound : locals.find key = some cell) : CellRep program heap objects cell := by
  induction locals with
  | nil => cases bound
  | cons scope rest ih =>
      cases here : scope.find key with
      | some found =>
          simp only [Locals.find,here,Option.orElse_some,Option.some.injEq] at bound
          cases bound
          exact Scope.find_cell (represented scope (by simp)) here
      | none =>
          simp only [Locals.find,here,Option.orElse_none] at bound
          exact ih (fun scope member => represented scope (by simp [member])) bound

theorem CellsRep.toLocals {locals : Execution.Locals} (represented : CellsRep program heap objects locals)
    (nonempty : locals ≠ []) : LocalsRep program heap objects (Locals.environment locals) locals :=
  ⟨rfl,nonempty,fun _ _ bound => represented.find bound⟩

theorem CellsRep.enter (represented : CellsRep program heap objects locals) :
    CellsRep program heap objects locals.enter := by
  intro scope member
  rcases List.mem_cons.mp member with rfl | member
  · intro entry impossible; cases impossible
  · exact represented scope member

theorem CellsRep.leave (represented : CellsRep program heap objects (scope :: rest)) :
    CellsRep program heap objects rest := fun next member => represented next (by simp [member])

theorem CellsRep.extend (represented : CellsRep program before oldObjects locals)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    CellsRep program after newObjects locals := by
  intro scope member entry found
  obtain ⟨value,initialized,rep⟩ := represented scope member entry found
  exact ⟨value,initialized,rep.extend invocation objects⟩

private theorem ScopeCellsRep.replace (represented : ScopeCellsRep program heap objects scope)
    (next : CellRep program heap objects cell) :
    ScopeCellsRep program heap objects (scope.replace key cell) := by
  induction scope with
  | nil => intro entry member; cases member
  | cons entry rest ih =>
      rcases entry with ⟨id,old⟩
      simp only [Scope.replace]
      split
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact next
        · exact represented entry (by simp [member])
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact represented _ (by simp)
        · exact ih (fun entry found => represented entry (by simp [found])) entry member

theorem CellsRep.replace (represented : CellsRep program heap objects locals)
    (next : CellRep program heap objects cell) :
    CellsRep program heap objects (locals.replace key cell) := by
  induction locals with
  | nil => intro scope member; cases member
  | cons scope rest ih =>
      simp only [Locals.replace]
      cases here : scope.find key with
      | none =>
          intro scope member
          rcases List.mem_cons.mp member with rfl | member
          · exact represented _ (by simp)
          · exact ih (fun scope found => represented scope (by simp [found])) scope member
      | some found =>
          intro current member
          rcases List.mem_cons.mp member with rfl | member
          · exact (represented scope (by simp)).replace next
          · exact represented current (by simp [member])

theorem CellsRep.write (represented : CellsRep program heap objects locals)
    (source : ValueRep program heap objects value)
    (written : locals.write key type value = .ok after) :
    CellsRep program heap objects after := by
  unfold Locals.write at written
  cases bound : locals.find key with
  | none => simp [bound] at written
  | some cell =>
      simp only [bound] at written
      split at written
      · cases written
      · split at written
        · rename_i same
          cases value with
          | mk actual data =>
              dsimp only at same
              cases same
              simp only at written
              cases written
              exact represented.replace ⟨_,rfl,source⟩
        · cases written

theorem CellsRep.declare (represented : CellsRep program heap objects locals)
    (source : ValueRep program heap objects value)
    (declared : locals.declare binder (some value) = .ok after) :
    CellsRep program heap objects after := by
  cases locals with
  | nil =>
      by_cases same : value.type = binder.type <;>
        simp [Execution.Locals.declare,Execution.Locals.find,same] at declared
  | cons scope rest =>
      by_cases duplicate : (Execution.Locals.find (scope :: rest) binder.id).isSome = true
      · simp [Execution.Locals.declare,duplicate] at declared
      · by_cases same : value.type = binder.type
        · cases value with
          | mk actual data =>
              dsimp only at same
              cases same
              simp [Execution.Locals.declare,duplicate] at declared
              subst after
              intro selected member entry found
              rcases List.mem_cons.mp member with rfl | member
              · rcases List.mem_cons.mp found with rfl | found
                · exact ⟨_,rfl,source⟩
                · exact represented scope (by simp) entry found
              · exact represented selected (by simp [member]) entry found
        · simp [Execution.Locals.declare,duplicate,same] at declared

end Solidity.Execution.Safety
