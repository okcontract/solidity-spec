/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Bindings
import Solidity.Core.Aggregates.Mutation
import Solidity.Core.Aggregates.ReferenceCasts
import Solidity.Core.Operators
import Solidity.Core.Unary

/-! Primitive effects consumed by the shared continuation machine. Operands
and place selectors have already been evaluated: this module never evaluates
an expression, chooses sibling order, or reconstructs a captured access path. -/
namespace Solidity.Execution.Effects
open Core Static Aggregates
open Contract.Interaction (Word)

/-- Scalar primitives carry ABI panic bytes. Retain their panic classification
when the bytes have the canonical encoding, without confusing arbitrary revert
payloads with panics. -/
def failureOfBytes (bytes : List UInt8) : Failure :=
  let code := (bytes[35]?).getD 0
  if bytes == Contract.panic code then .panic code else .revert bytes

theorem failureOfBytes_panic (code : UInt8) : failureOfBytes (Contract.panic code) = .panic code := by
  simp [failureOfBytes, Contract.panic]

def liftCore : Core.Result α → Aggregates.Result α
  | .ok value => .ok value
  | .error bytes => .error (failureOfBytes bytes)

def liftConversion : Except ConversionFailure α → Aggregates.Result α
  | .ok value => .ok value
  | .error .rejected => .error .rejected
  | .error .unsupported => .error (.unsupported "scalar runtime conversion")
  | .error (.panic bytes) => .error (failureOfBytes bytes)

def evalUnary (mode : ArithmeticMode) (operation : ScalarUnary code type)
    (value : type.Value) : Aggregates.Result type.Value :=
  liftCore (operation.eval mode value)

def evalBinary (mode : ArithmeticMode) (operation : ScalarBinary code a b result)
    (left : a.Value) (right : b.Value) : Aggregates.Result result.Value :=
  liftCore (operation.eval mode left right)

/-- Check source permission before asking the scalar runtime codec to execute.
An unsupported implementation never grants a source conversion permission. -/
def scalarCast (mode : ConversionMode) (target : SType) (source : Value) : Aggregates.Result Value := do
  if !Static.allows mode source.type target then throw .rejected
  return ⟨target, ← liftConversion (Static.convert mode source.type target source.value)⟩

def unary (mode : ArithmeticMode) (code : UnaryCode) (source : Value) : Aggregates.Result Value := do
  let some operation := checkUnary code source.type | throw .rejected
  return ⟨source.type, ← evalUnary mode operation source.value⟩

/-- Binary operands arrive with the source type checker's literal/contextual
materializations already inserted. Common-type conversion uses scalar conversion rules; asymmetric
power/shift operands retain their distinct unsigned count type. -/
def binary (mode : ArithmeticMode) (code : BinaryCode) (left right : Value) : Aggregates.Result Value := do
  if code.asymmetric then
    let some ⟨result, operation⟩ := checkBinary code left.type right.type | throw .rejected
    return ⟨result, ← evalBinary mode operation left.value right.value⟩
  else
    let some type := Static.common left.type right.type | throw .rejected
    let left ← scalarCast .implicit type left
    let right ← scalarCast .implicit type right
    if a : left.type = type then
      if b : right.type = type then
        let some ⟨result, operation⟩ := checkBinary code type type | throw .rejected
        return ⟨result, ← evalBinary mode operation (a ▸ left.value) (b ▸ right.value)⟩
      else throw (.invalidContext "right scalar conversion changed its target type")
    else throw (.invalidContext "left scalar conversion changed its target type")

structure ScalarUpdate where
  next : Value
  result : Option Value

/-- This only computes inc/dec. Delete uses the mutation endpoint without
reading an old typed scalar, so dirty bool/enum representations can be cleared. -/
def scalarUpdate (mode : ArithmeticMode) (code : UpdateCode) (source : Value) : Aggregates.Result ScalarUpdate := do
  match code with
  | .delete => throw .rejected
  | .inc _ | .dec _ =>
      let changed ← liftConversion (Static.updateScalar mode code source.type true source.value)
      return ⟨⟨source.type, changed.next⟩, changed.result.map (fun value => ⟨source.type, value⟩)⟩

/-- Explicit reference casts include source bytes-to-fixed-bytes conversions;
implicit local/parameter/result transfers retain the aggregate alias/copy planner. -/
def convert (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (mode : ConversionMode) (target : SType) (source : Value) : Aggregates.Result (Value × Heap × Nat) :=
  match mode with
  | .implicit => Copy.bind registry fuel budget heap target source
  | .explicit .ordinary =>
      if source.reference.isSome then do
        let (value, remaining) ← ReferenceCasts.cast registry fuel budget heap target source
        return (value, heap, remaining)
      else do return (← scalarCast mode target source, heap, budget)
  | .explicit .payable => do return (← scalarCast mode target source, heap, budget)

/-- Re-read a captured memory reference cell, preserving its captured physical
cell and lifetime guards. Its earlier data pointer may have changed during RHS
or sibling evaluation; the source access path is never evaluated again. -/
def reloadBinding (heap : Heap) (place : Place) : Aggregates.Result Place := do
  Access.validate heap place
  match place.reference.region with
  | .memory _ =>
      if isReference place.type then
        match place.reference.bindingCell with
        | none => pure place
        | some cell =>
            let pointer ← Access.readWord heap (rebase place.reference cell)
            return ⟨place.type, {(rebase place.reference pointer) with bindingCell := some cell}⟩
      else pure place
  | _ => pure place

def readCaptured (registry : Registry) (fuel : Nat) (locals : Locals) (heap : Heap) :
    Captured → Aggregates.Result Value
  | .local id type => do
      eligibleType registry fuel type
      let value ← locals.read id type
      match value.reference with
      | none => pure value
      | some reference => Access.readChecked registry fuel heap ⟨value.type, reference⟩
  | .heap place => do
      eligibleAt registry fuel place.reference.region place.type
      Access.readChecked registry fuel heap (← reloadBinding heap place)

/-- Local assignment transfers a binding; assignment to a physical aggregate
updates its contents or captured memory pointer cell. These are distinct aggregate
operations, including for storage objects containing mappings. -/
def writeCaptured (registry : Registry) (fuel budget : Nat) (locals : Locals) (heap : Heap)
    (target : Captured) (source : Value) : Aggregates.Result (Locals × Heap × Nat) := do
  match target with
  | .local id type =>
      let current ← locals.typeOf id
      if current != type then throw (.invalidContext "captured local type mismatch")
      let (value, after, remaining) ← Copy.bind registry fuel budget heap type source
      return (← locals.write id type value, after, remaining)
  | .heap place =>
      let (after, remaining) ← Copy.assign registry fuel budget heap place source
      return (locals, after, remaining)

/-- A scalar assignment yields its converted RHS. A reference assignment
returns the destination reference after the write, including a newly rebound
memory member. Tuple assignment has a separate empty-packet result. -/
def assignmentResult (registry : Registry) (fuel : Nat) (locals : Locals) (heap : Heap)
    (target : Captured) (source : Value) : Aggregates.Result Value :=
  if isReference target.type then readCaptured registry fuel locals heap target
  else scalarCast .implicit target.type source

/-- An unset local storage/calldata pointer is not a fabricated zero reference.
Definite-assignment admission must reject an access/return before binding it.
Uninitialized mappings themselves are a static rejection in the pinned source. -/
def defaultLocal (registry : Registry) (fuel budget : Nat) (heap : Heap) (type : SType) :
    Aggregates.Result (Option Value × Heap × Nat) := do
  eligibleType registry fuel type
  match type with
  | .mapping _ _ => throw .rejected
  | _ =>
      match referenceLocation type with
      | some .storage | some .calldata => return (none, heap, budget)
      | _ =>
          let (value, after, remaining) ← Defaults.defaultValue registry fuel budget heap type
          return (some value, after, remaining)

def declareLocal (registry : Registry) (fuel budget : Nat) (locals : Locals) (heap : Heap)
    (binder : Binder) (initializer : Option Value) : Aggregates.Result (Locals × Heap × Nat) := do
  match initializer with
  | some source =>
      let (value, after, remaining) ← Copy.bind registry fuel budget heap binder.type source
      return (← locals.declare binder (some value), after, remaining)
  | none =>
      let (value, after, remaining) ← defaultLocal registry fuel budget heap binder.type
      return (← locals.declare binder value, after, remaining)

/-- Named mapping return cells are a distinct declaration role: source permits
an unset return pointer that is assigned before returning, while an ordinary
uninitialized mapping local remains rejected. -/
def declareReturn (registry : Registry) (fuel budget : Nat) (locals : Locals) (heap : Heap)
    (binder : Binder) : Aggregates.Result (Locals × Heap × Nat) := do
  match binder.type with
  | .mapping _ _ =>
      eligibleType registry fuel binder.type
      return (← locals.declare binder none, heap, budget)
  | _ => declareLocal registry fuel budget locals heap binder none

/-- Delete does not decode the old value. In particular, clearing a dirty
bool/enum field does not first invent an invalid typed scalar observation. -/
def deleteCaptured (registry : Registry) (fuel budget : Nat) (locals : Locals) (heap : Heap) :
    Captured → Aggregates.Result (Locals × Heap × Nat)
  | .local id type => do
      let current ← locals.typeOf id
      if current != type then throw (.invalidContext "captured local type mismatch")
      let (value, after, remaining) ← Mutation.deleteValue registry fuel budget heap type
      return (← locals.write id type value, after, remaining)
  | .heap place => do
      let (after, remaining) ← Mutation.delete registry fuel budget heap place
      return (locals, after, remaining)

def updateCaptured (registry : Registry) (fuel budget : Nat) (mode : ArithmeticMode)
    (locals : Locals) (heap : Heap) (target : Captured) (code : UpdateCode) :
    Aggregates.Result (Option Value × Locals × Heap × Nat) := do
  match code with
  | .delete =>
      let (locals, heap, remaining) ← deleteCaptured registry fuel budget locals heap target
      return (none, locals, heap, remaining)
  | .inc _ | .dec _ =>
      let old ← readCaptured registry fuel locals heap target
      let changed ← scalarUpdate mode code old
      let (locals, heap, remaining) ← writeCaptured registry fuel budget locals heap target changed.next
      return (changed.result, locals, heap, remaining)

/-- All expressions selecting a place have completed before these adapters.
Each adapter captures the resulting physical descriptor once and retains its
history guards. No cleanup-only guard stripping is available here. -/
def captureField (registry : Registry) (fuel : Nat) (heap : Heap) (source : Value) (index : Nat) :
    Aggregates.Result Captured := do
  let place ← Defaults.asPlace source
  return .heap (← Access.resolveChecked registry fuel heap place [.field index])

def indexNumber (index : Value) : Aggregates.Result Nat :=
  match index with
  | ⟨.uint _, value⟩ => .ok value.toNat
  | _ => .error .rejected

def captureIndex (registry : Registry) (fuel : Nat) (heap : Heap) (source index : Value) :
    Aggregates.Result Captured := do
  let offset ← indexNumber index
  let place ← Defaults.asPlace source
  return .heap (← Access.resolveChecked registry fuel heap place [.index offset])

def readIndex (registry : Registry) (fuel : Nat) (locals : Locals) (heap : Heap) (source index : Value) :
    Aggregates.Result Value := do
  let offset ← indexNumber index
  match source with
  | ⟨.fixedBytes width, value⟩ =>
      if width.val+1 ≤ offset then throw (.panic 0x32)
      return ⟨.fixedBytes 0, (value >>> (8*(width.val-offset))).setWidth 8⟩
  | _ => readCaptured registry fuel locals heap (← captureIndex registry fuel heap source index)

def mappingKey (registry : Registry) (fuel budget : Nat) (heap : Heap) (source : Value) :
    Aggregates.Result (Access.MappingKey × Nat) := do
  match source.type with
  | .bytes _ _ | .string _ _ =>
      let (contents, remaining) ← Aggregates.snapshot registry fuel budget heap (← Defaults.asPlace source)
      match contents with
      | .bytes string bytes => return (.bytes string bytes, remaining)
      | _ => throw (.invalidContext "byte key snapshot has an unexpected shape")
  | _ =>
      if source.type.scalarSupported then return (.scalar source, budget)
      else throw .rejected

/-- Scalar mapping keys undergo their declared implicit conversion before
canonical word encoding. Byte/string keys keep their raw used payload; their
location difference never requests a memory copy or padded scalar encoding. -/
def mappingKeyFor (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (expected : SType) (source : Value) : Aggregates.Result (Access.MappingKey × Nat) := do
  match source.type with
  | .bytes _ _ | .string _ _ => mappingKey registry fuel budget heap source
  | _ => mappingKey registry fuel budget heap (← scalarCast .implicit expected source)

def captureMapping (registry : Registry) (fuel budget : Nat) (heap : Heap) (source key : Value) :
    Aggregates.Result (Captured × Nat) := do
  let .mapping keyType _ := source.type | throw .rejected
  let (key, remaining) ← mappingKeyFor registry fuel budget heap keyType key
  let place ← Defaults.asPlace source
  return (.heap (← Access.resolveChecked registry fuel heap place [.mapping key]), remaining)

def capturePushZero (registry : Registry) (fuel budget : Nat) (heap : Heap) (source : Value) :
    Aggregates.Result (Captured × Heap × Nat) := do
  let (place, heap, remaining) ← Mutation.pushZero registry fuel budget heap (← Defaults.asPlace source)
  return (.heap place, heap, remaining)

def length (registry : Registry) (fuel : Nat) (heap : Heap) (source : Value) : Aggregates.Result Value := do
  match source.type with
  | .fixedBytes width => return ⟨.uint 0, BitVec.ofNat 8 (width.val+1)⟩
  | _ =>
      let count ← Access.sourceLength registry fuel heap (← Defaults.asPlace source)
      return ⟨.uint 31, BitVec.ofNat 256 count⟩

def slice (registry : Registry) (fuel : Nat) (heap : Heap) (source : Value) (start stop : Nat) :
    Aggregates.Result Value := do
  let place ← Access.resolveChecked registry fuel heap (← Defaults.asPlace source) [.slice start stop]
  Access.readChecked registry fuel heap place

abbrev asPlace := Defaults.asPlace
abbrev unsignedNat := indexNumber

def field (registry : Registry) (fuel : Nat) (heap : Heap) (source : Value) (offset : Nat) :
    Aggregates.Result Place := do
  Access.resolveChecked registry fuel heap (← asPlace source) [.field offset]

def index (registry : Registry) (fuel : Nat) (heap : Heap) (source offset : Value) :
    Aggregates.Result Place := do
  Access.resolveChecked registry fuel heap (← asPlace source) [.index (← unsignedNat offset)]

def mapping (registry : Registry) (fuel budget : Nat) (heap : Heap) (source key : Value) :
    Aggregates.Result (Place × Nat) := do
  let .mapping keyType _ := source.type | throw .rejected
  let (key, remaining) ← mappingKeyFor registry fuel budget heap keyType key
  return (← Access.resolveChecked registry fuel heap (← asPlace source) [.mapping key], remaining)

def newArray (registry : Registry) (fuel budget : Nat) (heap : Heap) (element : SType) (count : Value) :
    Aggregates.Result (Value × Heap × Nat) := do
  Defaults.newArray registry fuel budget heap element (← unsignedNat count)

def newBytes (budget : Nat) (heap : Heap) (string : Bool) (count : Value) :
    Aggregates.Result (Value × Heap × Nat) := do
  Defaults.newBytes budget heap (← unsignedNat count) string

def push (registry : Registry) (fuel budget : Nat) (heap : Heap) (source value : Value) :
    Aggregates.Result (Heap × Nat) := do
  Mutation.push registry fuel budget heap (← asPlace source) value

def pop (registry : Registry) (fuel budget : Nat) (heap : Heap) (source : Value) :
    Aggregates.Result (Heap × Nat) := do
  Mutation.pop registry fuel budget heap (← asPlace source)

/-- This interface encodes scalar events. Source-valid aggregate arguments,
including indexed aggregate hashing, are unsupported here; they are not
rejected as though Solidity forbade them. -/
def eventWord (value : Value) : Aggregates.Result Word :=
  match value.type with
  | .function .internal _ _ _ => .error .rejected
  | _ =>
      if isReference value.type then .error (.unsupported "aggregate event ABI encoding")
      else encodeMemory value.type value.value

def eventWords (values : List Value) : Aggregates.Result (List Word) := values.mapM eventWord

/-- Event ABI construction belongs to the resolved event boundary. This
primitive consumes concrete topics/data, shares the ordinary heap's log, and
implements the runtime static restriction. -/
def emit (heap : Heap) (topics : List Word) (data : List UInt8) : Aggregates.Result Heap :=
  if 4 < topics.length then .error .rejected else
  if heap.execution.context.readOnly then .error .exceptional else
  .ok {heap with execution := {heap.execution with
    world := {heap.execution.world with logs := heap.execution.world.logs ++
      [⟨heap.execution.context.self, topics, data⟩]}}}

def emitWords (heap : Heap) (topics data : List Value) : Aggregates.Result Heap := do
  let topics ← eventWords topics
  let data ← eventWords data
  emit heap topics (data.flatMap Contract.Interaction.wordBytes)

theorem emit_static (heap : Heap) (topics : List Word) (data : List UInt8)
    (bounded : topics.length ≤ 4) (readonly : heap.execution.context.readOnly = true) :
    emit heap topics data = .error .exceptional := by
  simp [emit, Nat.not_lt.mpr bounded, readonly]

theorem emit_logs (emitted : emit heap topics data = .ok after) :
    after.execution.world.logs = heap.execution.world.logs ++
      [⟨heap.execution.context.self, topics, data⟩] := by
  unfold emit at emitted
  split at emitted
  · cases emitted
  · split at emitted
    · cases emitted
    · cases emitted; rfl

end Solidity.Execution.Effects
