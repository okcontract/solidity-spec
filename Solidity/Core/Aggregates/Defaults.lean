/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Access
import Solidity.Core.Aggregates.Memory
import Solidity.Core.Aggregates.Transfers

/-! Type-directed memory defaults use the local codegen's `zeroValueFunction`:
empty dynamic arrays/bytes/string point at the zero slot, while fixed arrays
and structs receive fresh recursively initialized objects. A memory member
holding a reference stores its pointer, so later assignments can rebind the
captured cell without changing the previously aliased object. -/
namespace Solidity.Aggregates.Defaults
open Static
open Contract.Interaction (Word wordBytes bytesWord)

def writeMemoryValue (heap : Heap) (cell : Reference) (value : Value) : Result Heap :=
  match cell.region with
  | .memory invocation =>
      if invocation != heap.invocation then .error (.invalidContext "foreign memory reference")
      else if cell.byte != 0 then .error .rejected
      else match value.reference with
      | none => writeScalar heap ⟨value.type, cell⟩ value.value
      | some pointer =>
          if referenceLocation value.type != some .memory || cell.byteCell then .error .rejected
          else if pointer.byte != 0 || pointer.byteCell || pointer.viewLength.isSome ||
              pointer.relativeBase.isSome || !pointer.guards.isEmpty then .error .rejected
          else if pointer.region != .memory heap.invocation then
            .error (.invalidContext "foreign memory pointer value")
          else match checkExtent heap pointer 0 with
          | .error failure => .error failure
          | .ok _ => match checkExtent heap cell 32 with
            | .error failure => .error failure
            | .ok _ =>
                let memory := heap.execution.memory.write cell.address.toNat (wordBytes pointer.address)
                .ok { heap with execution := { heap.execution with memory } }
  | _ => .error .rejected

theorem writeMemoryValue_frame (heap after : Heap) (cell : Reference) (value : Value)
    (written : writeMemoryValue heap cell value = .ok after) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation ∧
    after.nextMemory = heap.nextMemory ∧ after.allocations = heap.allocations := by
  unfold writeMemoryValue at written
  cases region : cell.region with
  | storage owner => simp [region] at written
  | transient owner => simp [region] at written
  | calldata invocation => simp [region] at written
  | memory invocation =>
      simp only [region] at written
      split at written
      · cases written
      · split at written
        · cases written
        · cases valueReference : value.reference with
          | none =>
              simp only [valueReference] at written
              exact writeScalar_memory_frame heap after ⟨value.type, cell⟩ value.value invocation region written
          | some pointer =>
              simp only [valueReference] at written
              split at written
              · cases written
              · split at written
                · cases written
                · split at written
                  · cases written
                  · cases pointerExtent : checkExtent heap pointer 0 with
                    | error failure => simp [pointerExtent] at written
                    | ok _ =>
                        simp only [pointerExtent] at written
                        cases cellExtent : checkExtent heap cell 32 with
                        | error failure => simp [cellExtent] at written
                        | ok _ =>
                            simp only [cellExtent] at written
                            cases written
                            exact ⟨rfl, rfl, rfl, rfl⟩

/-- Memory construction consumes the canonical placement judgment used by
assignment planning. It inspects empty aggregate element types as well. -/
def memoryEligible (registry : Registry) (fuel : Nat) (type : SType) : Result Unit :=
  eligibleAt registry fuel (.memory 0) type

def emptyReference (heap : Heap) : Result Reference := do
  let reference : Reference := { region := .memory heap.invocation, address := 96 }
  let _ ← checkExtent heap reference 32
  if bytesWord (heap.execution.memory.read 96 32) != 0 then
    throw (.invalidContext "modified memory zero slot")
  return reference

abbrev MakeDefault := Heap → Nat → SType → Result (Value × Heap × Nat)

def initializeCell (makeDefault : MakeDefault) (data : Reference)
    (state : Heap × Nat) (entry : SType × Nat) : Result (Heap × Nat) := do
  let (heap, budget) := state
  let (type, index) := entry
  let (value, heap, budget) ← makeDefault heap budget (atLocation type .memory false)
  let budget ← reserve budget 32
  let cell ← Access.advance data (index * 32)
  let heap ← writeMemoryValue heap cell value
  return (heap, budget)

/-- The callback is the structurally decreasing default builder below, never
a caller-supplied semantic oracle. Cells are initialized in declaration order. -/
def initializeCells (makeDefault : MakeDefault) (heap : Heap) (budget : Nat)
    (data : Reference) (types : List SType) : Result (Heap × Nat) := do
  let budget ← reserve budget types.length
  types.zipIdx.foldlM (initializeCell makeDefault data) (heap, budget)

def initializeLength (heap : Heap) (budget : Nat) (reference : Reference)
    (count : Nat) (dynamic : Bool) : Result (Heap × Nat) :=
  if dynamic then do
    let budget ← reserve budget 32
    let heap ← writeMemoryValue heap reference ⟨.uint 31, BitVec.ofNat 256 count⟩
    return (heap, budget)
  else .ok (heap, budget)

def arrayDataReference (reference : Reference) (dynamic : Bool) : Result Reference :=
  if dynamic then Access.advance reference 32 else .ok reference

def allocateArray (makeDefault : MakeDefault) (heap : Heap) (budget : Nat)
    (element : SType) (count : Nat) (dynamic : Bool) (pointer : Bool := true) : Result (Value × Heap × Nat) := do
  let size ← MemoryOps.arraySize count false dynamic
  let (reference, heap, budget) ← MemoryOps.allocate heap budget size
  let (heap, budget) ← initializeLength heap budget reference count dynamic
  let data ← arrayDataReference reference dynamic
  -- Reserve the list traversal before constructing an element-type list.
  let budget ← reserve budget count
  let (heap, budget) ← initializeCells makeDefault heap budget data (List.replicate count element)
  return (⟨.array element (if dynamic then none else some count) .memory pointer, reference⟩, heap, budget)

def allocateStruct (makeDefault : MakeDefault) (registry : Registry)
    (heap : Heap) (budget identity : Nat) (pointer : Bool) : Result (Value × Heap × Nat) := do
  let some fields := registry.structFields identity |
    throw (.invalidContext "missing resolved struct members")
  let size ← MemoryOps.arraySize fields.length false false
  let (reference, heap, budget) ← MemoryOps.allocate heap budget size
  let (heap, budget) ← initializeCells makeDefault heap budget reference (fields.map Prod.snd)
  return (⟨.structType identity .memory pointer, reference⟩, heap, budget)

private def Frame (before after : Heap) : Prop :=
  after.execution.world = before.execution.world ∧ after.invocation = before.invocation

private theorem Frame.refl (heap : Heap) : Frame heap heap := ⟨rfl, rfl⟩

private theorem Frame.trans (a : Frame before middle) (b : Frame middle after) : Frame before after :=
  ⟨b.1.trans a.1, b.2.trans a.2⟩

private def MakesFrame (makeDefault : MakeDefault) : Prop :=
  ∀ heap budget type value after remaining,
    makeDefault heap budget type = .ok (value, after, remaining) → Frame heap after

private theorem result_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem result_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] result_map_error result_map_ok

private theorem initializeCell_frame (makeDefault : MakeDefault) (safe : MakesFrame makeDefault)
    (data : Reference) (heap after : Heap) (budget remaining : Nat) (entry : SType × Nat)
    (written : initializeCell makeDefault data (heap, budget) entry = .ok (after, remaining)) :
    Frame heap after := by
  unfold initializeCell at written
  cases made : makeDefault heap budget (atLocation entry.1 .memory false) with
  | error failure => simp [made] at written <;> cases written
  | ok result =>
      rcases result with ⟨value, next, rest⟩
      have first := safe heap budget _ value next rest made
      simp only [made, bind, Except.bind] at written
      cases reserved : reserve rest 32 with
      | error failure => simp [reserved] at written <;> cases written
      | ok available =>
          simp only [reserved] at written
          cases advanced : Access.advance data (entry.2 * 32) with
          | error failure => simp [advanced] at written <;> cases written
          | ok cell =>
              simp only [advanced] at written
              cases stored : writeMemoryValue next cell value with
              | error failure => simp [stored] at written <;> cases written
              | ok final =>
                  simp only [stored] at written
                  have last := writeMemoryValue_frame next final cell value stored
                  cases written
                  exact first.trans ⟨last.1, last.2.1⟩

private theorem fold_frame (step : (Heap × Nat) → α → Result (Heap × Nat))
    (safe : ∀ heap budget item after remaining,
      step (heap, budget) item = .ok (after, remaining) → Frame heap after)
    (items : List α) (heap after : Heap) (budget remaining : Nat)
    (written : items.foldlM step (heap, budget) = .ok (after, remaining)) : Frame heap after := by
  induction items generalizing heap budget with
  | nil => cases written; exact Frame.refl after
  | cons item rest ih =>
      rw [List.foldlM_cons] at written
      cases first : step (heap, budget) item with
      | error failure => simp [first] at written <;> cases written
      | ok result =>
          rcases result with ⟨next, available⟩
          simp only [first, bind, Except.bind] at written
          exact (safe heap budget item next available first).trans (ih next available written)

private theorem initializeCells_frame (makeDefault : MakeDefault) (safe : MakesFrame makeDefault)
    (heap after : Heap) (budget remaining : Nat) (data : Reference) (types : List SType)
    (written : initializeCells makeDefault heap budget data types = .ok (after, remaining)) :
    Frame heap after := by
  unfold initializeCells at written
  cases reserved : reserve budget types.length with
  | error failure => simp [reserved] at written <;> cases written
  | ok available =>
      simp only [reserved] at written
      exact fold_frame (initializeCell makeDefault data)
        (fun heap budget item after remaining h =>
          initializeCell_frame makeDefault safe data heap after budget remaining item h)
        _ heap after available remaining written

private theorem initializeLength_frame (heap after : Heap) (budget remaining count : Nat)
    (reference : Reference) (dynamic : Bool)
    (written : initializeLength heap budget reference count dynamic = .ok (after, remaining)) :
    Frame heap after := by
  cases dynamic with
  | false =>
      have same := Frame.refl heap
      cases written
      exact same
  | true =>
      unfold initializeLength at written
      cases reserved : reserve budget 32 with
      | error failure => simp [reserved] at written <;> cases written
      | ok available =>
          simp only [reserved] at written
          cases stored : writeMemoryValue heap reference ⟨.uint 31, BitVec.ofNat 256 count⟩ with
          | error failure => simp [stored] at written <;> cases written
          | ok final =>
              simp only [stored] at written
              have frame := writeMemoryValue_frame heap final reference _ stored
              cases written
              exact ⟨frame.1, frame.2.1⟩

private theorem allocateArray_frame (makeDefault : MakeDefault) (safe : MakesFrame makeDefault)
    (heap after : Heap) (budget remaining count : Nat) (element : SType) (dynamic pointer : Bool)
    (value : Value)
    (written : allocateArray makeDefault heap budget element count dynamic pointer = .ok (value, after, remaining)) :
    Frame heap after := by
  unfold allocateArray at written
  cases sized : MemoryOps.arraySize count false dynamic with
  | error failure => simp [sized] at written <;> cases written
  | ok size =>
      simp only [sized, bind, Except.bind] at written
      cases allocated : MemoryOps.allocate heap budget size with
      | error failure => simp [allocated] at written <;> cases written
      | ok result =>
          rcases result with ⟨reference, next, available⟩
          have first : Frame heap next := MemoryOps.allocate_frame heap next budget size available reference allocated
          simp only [allocated] at written
          cases header : initializeLength next available reference count dynamic with
          | error failure => simp [header] at written <;> cases written
          | ok result =>
              rcases result with ⟨middle, available'⟩
              have second := initializeLength_frame next middle available available' count reference dynamic header
              simp only [header] at written
              cases advanced : arrayDataReference reference dynamic with
              | error failure => simp [advanced] at written <;> cases written
              | ok data =>
                  simp only [advanced] at written
                  cases reserved : reserve available' count with
                  | error failure => simp [reserved] at written <;> cases written
                  | ok available'' =>
                      simp only [reserved] at written
                      cases initialized : initializeCells makeDefault middle available'' data (List.replicate count element) with
                      | error failure => simp [initialized] at written <;> cases written
                      | ok result =>
                          rcases result with ⟨final, rest⟩
                          have third := initializeCells_frame makeDefault safe middle final available'' rest data _ initialized
                          simp only [initialized] at written
                          cases written
                          exact (first.trans second).trans third

private theorem allocateStruct_frame (makeDefault : MakeDefault) (safe : MakesFrame makeDefault)
    (registry : Registry) (heap after : Heap) (budget remaining identity : Nat) (pointer : Bool)
    (value : Value)
    (written : allocateStruct makeDefault registry heap budget identity pointer = .ok (value, after, remaining)) :
    Frame heap after := by
  unfold allocateStruct at written
  cases fields : registry.structFields identity with
  | none => simp [fields] at written <;> cases written
  | some members =>
      simp only [fields] at written
      cases sized : MemoryOps.arraySize members.length false false with
      | error failure => simp [sized] at written <;> cases written
      | ok size =>
          simp only [sized, bind, Except.bind] at written
          cases allocated : MemoryOps.allocate heap budget size with
          | error failure => simp [allocated] at written <;> cases written
          | ok result =>
              rcases result with ⟨reference, next, available⟩
              have first : Frame heap next := MemoryOps.allocate_frame heap next budget size available reference allocated
              simp only [allocated] at written
              cases initialized : initializeCells makeDefault next available reference (members.map Prod.snd) with
              | error failure => simp [initialized] at written <;> cases written
              | ok result =>
                  rcases result with ⟨final, rest⟩
                  have last := initializeCells_frame makeDefault safe next final available rest reference _ initialized
                  simp only [initialized] at written
                  cases written
                  exact first.trans last

def build (registry : Registry) : Nat → Heap → Nat → SType → Result (Value × Heap × Nat)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, heap, budget, type =>
      match Static.defaultScalar type with
      | some value => .ok (⟨type, value⟩, heap, budget)
      | none => do
          match type with
          | .array element none .memory pointer =>
              let reference ← emptyReference heap
              return (⟨.array (atLocation element .memory false) none .memory pointer, reference⟩, heap, budget)
          | .array element (some count) .memory pointer =>
              allocateArray (build registry fuel) heap budget
                (atLocation element .memory false) count false pointer
          | .bytes .memory pointer =>
              let reference ← emptyReference heap
              return (⟨.bytes .memory pointer, reference⟩, heap, budget)
          | .string .memory pointer =>
              let reference ← emptyReference heap
              return (⟨.string .memory pointer, reference⟩, heap, budget)
          | .structType identity .memory pointer =>
              allocateStruct (build registry fuel) registry heap budget identity pointer
          | .fixedPoint _ _ _ => throw (.unsupported "fixed-point runtime initialization")
          | _ => throw .rejected

private theorem build_frame (registry : Registry) (fuel : Nat) : MakesFrame (build registry fuel) := by
  induction fuel with
  | zero => intro heap budget type value after remaining written; cases written
  | succ fuel ih =>
      intro heap budget type value after remaining written
      cases zero : Static.defaultScalar type with
      | some scalar =>
          simp only [build, zero] at written
          have same := Frame.refl heap
          cases written
          exact same
      | none =>
          simp only [build, zero] at written
          cases type with
          | array element size location pointer =>
              cases location with
              | storage => cases size <;> cases written
              | calldata => cases size <;> cases written
              | memory =>
                  cases size with
                  | none =>
                      cases empty : emptyReference heap with
                      | error failure => simp [empty] at written <;> cases written
                      | ok reference =>
                          simp only [empty, bind, Except.bind] at written
                          have same := Frame.refl heap
                          cases written
                          exact same
                  | some count =>
                      exact allocateArray_frame (build registry fuel) ih heap after budget remaining count
                        (atLocation element .memory false) false pointer value written
          | bytes location pointer | string location pointer =>
              cases location with
              | storage => cases written
              | calldata => cases written
              | memory =>
                  cases empty : emptyReference heap with
                  | error failure => simp [empty] at written <;> cases written
                  | ok reference =>
                      simp only [empty, bind, Except.bind] at written
                      have same := Frame.refl heap
                      cases written
                      exact same
          | structType identity location pointer =>
              cases location with
              | storage => cases written
              | calldata => cases written
              | memory =>
                  exact allocateStruct_frame (build registry fuel) ih registry heap after budget remaining identity
                    pointer value written
          | _ => cases written

def defaultValue (registry : Registry) (fuel budget : Nat) (heap : Heap) (type : SType) :
    Result (Value × Heap × Nat) := do
  memoryEligible registry fuel type
  build registry fuel heap budget type

theorem build_preserves_invocation
    (written : build registry fuel heap budget type = .ok (value, after, remaining)) :
    after.invocation = heap.invocation :=
  (build_frame registry fuel heap budget type value after remaining written).2

def newArray (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (element : SType) (count : Nat) (dynamic : Bool := true) : Result (Value × Heap × Nat) := do
  let element := atLocation element .memory false
  let type := SType.array element (if dynamic then none else some count) .memory true
  memoryEligible registry fuel type
  allocateArray (build registry fuel) heap budget element count dynamic

def newBytes (budget : Nat) (heap : Heap) (count : Nat) (string : Bool := false) :
    Result (Value × Heap × Nat) := do
  let size ← MemoryOps.arraySize count true true
  let (reference, heap, budget) ← MemoryOps.allocate heap budget size
  let (heap, budget) ← initializeLength heap budget reference count true
  let value : Value := if string then ⟨.string .memory true, reference⟩ else ⟨.bytes .memory true, reference⟩
  return (value, heap, budget)

def asPlace (value : Value) : Result Place :=
  match value.reference with
  | some reference => .ok ⟨value.type, reference⟩
  | none => .error .rejected

theorem memoryEligible_exhausted (registry : Registry) (type : SType) :
    memoryEligible registry 0 type = .error .exhausted := rfl

theorem defaultValue_exhausted (registry : Registry) (budget : Nat) (heap : Heap) (type : SType) :
    defaultValue registry 0 budget heap type = .error .exhausted := rfl

theorem memoryEligible_is_placement (registry : Registry) (fuel : Nat) (type : SType) :
    memoryEligible registry fuel type = eligibleAt registry fuel (.memory 0) type := rfl

theorem defaultValue_scalar (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (type : SType) (zero : type.Value) (default : Static.defaultScalar type = some zero)
    (eligible : memoryEligible registry (fuel+1) type = .ok ()) :
    defaultValue registry (fuel+1) budget heap type = .ok (⟨type, zero⟩, heap, budget) := by
  simp [defaultValue, eligible, build, default]
  rfl

/-- Initialization changes only frame-local memory and its allocation metadata.
This is quantified over all successful recursive defaults, not fixture heaps. -/
theorem defaultValue_frame (registry : Registry) (fuel budget remaining : Nat) (heap after : Heap)
    (type : SType) (value : Value)
    (written : defaultValue registry fuel budget heap type = .ok (value, after, remaining)) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  unfold defaultValue at written
  cases eligible : memoryEligible registry fuel type with
  | error failure => simp [eligible] at written <;> cases written
  | ok _ =>
      simp only [eligible, bind, Except.bind] at written
      exact build_frame registry fuel heap budget type value after remaining written

theorem newArray_frame (registry : Registry) (fuel budget remaining count : Nat) (heap after : Heap)
    (element : SType) (dynamic : Bool) (value : Value)
    (written : newArray registry fuel budget heap element count dynamic = .ok (value, after, remaining)) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  unfold newArray at written
  cases eligible : memoryEligible registry fuel
      (.array (atLocation element .memory false) (if dynamic then none else some count) .memory true) with
  | error failure => simp [eligible] at written <;> cases written
  | ok _ =>
      simp only [eligible, bind, Except.bind] at written
      exact allocateArray_frame (build registry fuel) (build_frame registry fuel) heap after budget remaining count
        (atLocation element .memory false) dynamic true value written

theorem newBytes_frame (budget remaining count : Nat) (heap after : Heap) (string : Bool) (value : Value)
    (written : newBytes budget heap count string = .ok (value, after, remaining)) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  unfold newBytes at written
  cases sized : MemoryOps.arraySize count true true with
  | error failure => simp [sized] at written <;> cases written
  | ok size =>
      simp only [sized, bind, Except.bind] at written
      cases allocated : MemoryOps.allocate heap budget size with
      | error failure => simp [allocated] at written <;> cases written
      | ok result =>
          rcases result with ⟨reference, next, available⟩
          have first : Frame heap next := MemoryOps.allocate_frame heap next budget size available reference allocated
          simp only [allocated] at written
          cases header : initializeLength next available reference count true with
          | error failure => simp [header] at written <;> cases written
          | ok result =>
              rcases result with ⟨final, rest⟩
              have last := initializeLength_frame next final available rest count reference true header
              simp only [header] at written
              cases written
              exact first.trans last

end Solidity.Aggregates.Defaults
