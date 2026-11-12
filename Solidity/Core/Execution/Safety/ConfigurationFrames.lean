/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Configuration

/-! Heap/object growth preserves every saved operand of the continuation
typing relation. These are representation lemmas, not successful-step premises.
They do not infer physical HeapRep after a write or allocation; those facts must
come from the actual primitive's construction/frame theorem. -/
namespace Solidity.Execution.Safety
open Static Aggregates

theorem HeapTargetRep.extend (represented : HeapTargetRep before oldObjects place)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) : HeapTargetRep after newObjects place := by
  cases represented with
  | persistent owner address => exact .persistent owner address
  | transient owner address => exact .transient owner address
  | cell object member index inside =>
      simpa only [WordArena.Object.cell,Copy.memoryReference,invocation] using
        (HeapTargetRep.cell (heap := after) object (objects object member) index inside)

theorem TargetRep.extend (represented : TargetRep registry before oldObjects environment target type)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    TargetRep registry after newObjects environment target type := by
  cases represented with
  | «local» bound ready => exact .local bound ready
  | heap physical => exact .heap (physical.extend invocation objects)

theorem WritesRep.extend (represented : WritesRep registry program before oldObjects environment writes)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    WritesRep registry program after newObjects environment writes := by
  induction represented with
  | nil => exact .nil
  | cons target value transfer rest ih =>
      exact .cons (target.extend invocation objects) (value.extend invocation objects) transfer ih

theorem SignalRep.extend (represented : SignalRep registry program before oldObjects flowContext signal)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    SignalRep registry program after newObjects flowContext signal := by
  cases represented with
  | next => exact .next
  | break_ allowed => exact .break_ allowed
  | continue_ allowed => exact .continue_ allowed
  | return_ => exact .return_
  | values value allowed => exact .values (value.extend invocation objects) allowed

theorem TaskRep.extend (represented : TaskRep registry program before oldObjects environment task afterEnvironment kind)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    TaskRep registry program after newObjects environment task afterEnvironment kind := by
  cases represented with
  | eval code => exact .eval code
  | capture code => exact .capture code
  | value value => exact .value (value.extend invocation objects)
  | target target => exact .target (target.extend invocation objects)
  | collect values finish => exact .collect (values.extend invocation objects) finish
  | apply packet finish => exact .apply (packet.extend invocation objects) finish
  | statement code => exact .statement code
  | body code => exact .body code
  | declaration code => exact .declaration code
  | resume signal => exact .resume (signal.extend invocation objects)
  | next => exact .next
  | loop test boolean body post => exact .loop test boolean body post
  | writes writes => exact .writes (writes.extend invocation objects)

theorem FrameRep.extend (represented : FrameRep registry program before oldObjects environment kind frame afterEnvironment afterKind)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    FrameRep registry program after newObjects environment kind frame afterEnvironment afterKind := by
  cases represented with
  | mode permitted => exact .mode permitted
  | scope outer => exact .scope outer
  | next code => exact .next code
  | «prefix» code => exact .prefix code
  | discard => exact .discard
  | returnValue allowed => exact .returnValue allowed
  | readTarget => exact .readTarget
  | collect values finish => exact .collect (values.extend invocation objects) finish
  | select yes no same => exact .select yes no same
  | branch yes no => exact .branch yes no
  | lazy right boolean => exact .lazy right boolean
  | assignRight target allowed => exact .assignRight target allowed
  | assignLeft right allowed => exact .assignLeft right allowed
  | commitValue value allowed => exact .commitValue (value.extend invocation objects) allowed
  | commitTarget target allowed => exact .commitTarget (target.extend invocation objects) allowed
  | compoundRight target left right token operation => exact .compoundRight target left right token operation
  | compoundLeft right leftSupport rightSupport token operation =>
      exact .compoundLeft right leftSupport rightSupport token operation
  | compoundReadFirst right leftSupport rightSupport token operation =>
      exact .compoundReadFirst right leftSupport rightSupport token operation
  | compoundValue value left right token operation =>
      exact .compoundValue (value.extend invocation objects) left right token operation
  | compoundTarget target left right token operation =>
      exact .compoundTarget (target.extend invocation objects) left right token operation
  | commitOld target old oldType left right token operation =>
      exact .commitOld (target.extend invocation objects) (old.extend invocation objects) oldType left right token operation
  | update nondelete allowed => exact .update nondelete allowed
  | declare ready allowed fresh => exact .declare ready allowed fresh
  | loopCondition test boolean body post => exact .loopCondition test boolean body post
  | forInit test boolean body post => exact .forInit test boolean body post
  | forInitNext test boolean body post => exact .forInitNext test boolean body post
  | loopBody test boolean body post => exact .loopBody test boolean body post
  | loopPost test boolean body post => exact .loopPost test boolean body post
  | doBody body test boolean => exact .doBody body test boolean
  | doCondition body test boolean => exact .doCondition body test boolean
  | call caller shape nonempty cells ready => exact .call (caller.extend invocation objects) shape nonempty cells ready
  | resultTransfer caller shape nonempty cells ready =>
      exact .resultTransfer (caller.extend invocation objects) shape nonempty cells ready

theorem StackRep.extend (represented : StackRep registry program before oldObjects environment kind stack)
    (invocation : after.invocation = before.invocation)
    (objects : ∀ object ∈ oldObjects, object ∈ newObjects) :
    StackRep registry program after newObjects environment kind stack := by
  induction represented with
  | value => exact .value
  | signal => exact .signal
  | next => exact .next
  | cons frame rest ih => exact .cons (frame.extend invocation objects) ih

end Solidity.Execution.Safety
