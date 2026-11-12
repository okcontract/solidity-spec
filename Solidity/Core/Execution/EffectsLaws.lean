/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Effects
import Solidity.Core.Aggregates.Copy.Frames

namespace Solidity.Execution.Effects
open Core Static Aggregates

variable {registry : Registry} {fuel budget remaining : Nat} {heap after : Heap}
  {locals afterLocals : Locals} {place : Place} {source value : Value} {target : Captured}
  {type : SType} {id other : Nat}

private theorem effects_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Aggregates.Result α) = .error failure := rfl
private theorem effects_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Aggregates.Result α) = .ok (f value) := rfl
attribute [local simp] effects_map_error effects_map_ok Bind.bind Except.bind Pure.pure Except.pure

theorem scalarCast_type (casted : scalarCast mode type source = .ok value) : value.type = type := by
  unfold scalarCast at casted
  split at casted
  · cases casted
  · cases converted : liftConversion (Static.convert mode source.type type source.value) with
    | error failure => simp [converted] at casted
    | ok result => simp [converted] at casted; cases casted; rfl

theorem unary_type (evaluated : unary mode code source = .ok value) : value.type = source.type := by
  unfold unary at evaluated
  cases checked : checkUnary code source.type with
  | none => simp [checked] at evaluated
  | some operation =>
      simp only [checked] at evaluated
      cases result : evalUnary mode operation source.value with
      | error failure => simp [result] at evaluated
      | ok next => simp [result] at evaluated; cases evaluated; rfl

private theorem local_read_type (read : locals.read id type = .ok value) : value.type = type := by
  unfold Locals.read at read
  cases found : locals.find id with
  | none => simp [found] at read
  | some cell =>
      simp only [found] at read
      split at read
      · cases read
      · rename_i same
        have declared : cell.type = type := by simpa using same
        cases initialized : cell.value with
        | none => simp [initialized] at read
        | some data => simp [initialized] at read; cases read; exact declared

private theorem asValue_type (read : place.asValue = .ok value) : value.type = place.type := by
  cases place with | mk type reference =>
    cases type <;> simp only [Place.asValue, referenceValue, Except.map] at read <;> cases read <;> rfl

private theorem access_read_type (read : Access.read heap place = .ok value) : value.type = place.type := by
  unfold Access.read at read
  cases checked : Access.validate heap place with
  | error failure => simp [checked] at read
  | ok _ =>
      simp only [checked] at read
      split at read
      · exact asValue_type read
      · cases result : readScalar heap place with
        | error failure => simp [result] at read
        | ok next => simp [result] at read; cases read; rfl

private theorem checked_read_type (read : Access.readChecked registry fuel heap place = .ok value) : value.type = place.type := by
  unfold Access.readChecked at read
  cases checked : eligibleAt registry fuel place.reference.region place.type with
  | error failure => simp [checked] at read
  | ok _ => simp only [checked] at read; exact access_read_type read

/-- Reloading may change a memory data pointer, but never changes its source
type, physical region, captured pointer cell or liveness guards. -/
theorem reloadBinding_descriptor {loadedPlace : Place} (loaded : reloadBinding heap place = .ok loadedPlace) :
    loadedPlace.type = place.type ∧ loadedPlace.reference.region = place.reference.region ∧
      loadedPlace.reference.bindingCell = place.reference.bindingCell ∧ loadedPlace.reference.guards = place.reference.guards := by
  unfold reloadBinding at loaded
  cases checked : Access.validate heap place with
  | error failure => simp [checked] at loaded
  | ok _ =>
      simp only [checked] at loaded
      cases region : place.reference.region with
      | storage owner | transient owner | calldata invocation =>
          simp only [region] at loaded
          cases loaded
          exact ⟨rfl, region, rfl, rfl⟩
      | memory invocation =>
          simp only [region] at loaded
          split at loaded
          · cases cell : place.reference.bindingCell with
            | none => simp only [cell] at loaded; cases loaded; exact ⟨rfl, region, cell, rfl⟩
            | some address =>
                simp only [cell] at loaded
                cases read : Access.readWord heap (rebase place.reference address) with
                | error failure => simp [read] at loaded
                | ok pointer =>
                    simp only [read] at loaded
                    cases loaded
                    exact ⟨rfl, region, rfl, rfl⟩
          · cases loaded; exact ⟨rfl, region, rfl, rfl⟩

theorem readCaptured_type (read : readCaptured registry fuel locals heap target = .ok value) : value.type = target.type := by
  cases target with
  | «local» id type =>
      simp only [readCaptured] at read
      cases eligible : eligibleType registry fuel type with
      | error failure => simp [eligible] at read
      | ok _ =>
          simp only [eligible, Bind.bind, Except.bind] at read
          cases observed : locals.read id type with
          | error failure => simp [observed] at read
          | ok source =>
              have sourceType := local_read_type observed
              simp only [observed] at read
              cases extracted : source.reference with
              | none => simp only [extracted] at read; cases read; exact sourceType
              | some reference =>
                  simp only [extracted] at read
                  exact (checked_read_type read).trans sourceType
  | heap place =>
      simp only [readCaptured] at read
      cases eligible : eligibleAt registry fuel place.reference.region place.type with
      | error failure => simp [eligible] at read
      | ok _ =>
          simp only [eligible, Bind.bind, Except.bind] at read
          cases loaded : reloadBinding heap place with
          | error failure => simp [loaded] at read
          | ok after =>
              simp only [loaded] at read
              exact (checked_read_type read).trans (reloadBinding_descriptor loaded).1

/-- A heap destination never changes lexical bindings. -/
theorem writeCaptured_heap_locals
    (written : writeCaptured registry fuel budget locals heap (.heap place) source = .ok (afterLocals, after, remaining)) :
    afterLocals = locals := by
  unfold writeCaptured at written
  cases copied : Copy.assign registry fuel budget heap place source with
  | error failure => simp [copied] at written
  | ok pair =>
      rcases pair with ⟨next, available⟩
      simp only [copied, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
      cases written
      rfl

/-- A local binding transfer uses the actual copy/alias planner; all other
active binding IDs retain their cells. -/
theorem writeCaptured_local_other (different : id ≠ other)
    (written : writeCaptured registry fuel budget locals heap (.local id type) source = .ok (afterLocals, after, remaining)) :
    afterLocals.find other = locals.find other := by
  unfold writeCaptured at written
  cases found : locals.typeOf id with
  | error failure => simp [found] at written
  | ok actual =>
      simp only [found, Bind.bind, Except.bind] at written
      split at written
      · cases written
      · cases copied : Copy.bind registry fuel budget heap type source with
        | error failure => simp [copied] at written
        | ok result =>
            rcases result with ⟨value, next, available⟩
            simp only [copied] at written
            cases stored : locals.write id type value with
            | error failure => simp [stored] at written
            | ok nextLocals =>
                simp only [stored] at written
                cases written
                exact Locals.write_frames_other different stored

/-- Successful local transfers, including all reference families, expose the
actual aggregate binding computation and readable stored result. -/
theorem writeCaptured_local_transfer
    (written : writeCaptured registry fuel budget locals heap (.local id type) source =
      .ok (afterLocals, after, remaining)) :
    ∃ converted, Copy.bind registry fuel budget heap type source = .ok (converted, after, remaining) ∧
      afterLocals.read id type = .ok converted := by
  unfold writeCaptured at written
  cases found : locals.typeOf id with
  | error failure => simp [found] at written
  | ok actual =>
      simp only [found, Bind.bind, Except.bind] at written
      split at written
      · cases written
      · cases copied : Copy.bind registry fuel budget heap type source with
        | error failure => simp [copied] at written
        | ok result =>
            rcases result with ⟨value, next, available⟩
            simp only [copied] at written
            cases stored : locals.write id type value with
            | error failure => simp [stored] at written
            | ok nextLocals =>
                simp only [stored] at written
                cases written
                exact ⟨value, rfl, Locals.read_after_write stored⟩

/-- Binding a scalar/reference parameter or result does not change the shared
world or invocation. A required fresh memory copy may allocate in that same
invocation, according to the aggregate construction frame theorem. -/
theorem writeCaptured_local_world
    (written : writeCaptured registry fuel budget locals heap (.local id type) source = .ok (afterLocals, after, remaining)) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation := by
  unfold writeCaptured at written
  cases found : locals.typeOf id with
  | error failure => simp [found] at written
  | ok actual =>
      simp only [found, Bind.bind, Except.bind] at written
      split at written
      · cases written
      · cases copied : Copy.bind registry fuel budget heap type source with
        | error failure => simp [copied] at written
        | ok result =>
            rcases result with ⟨value, next, available⟩
            simp only [copied] at written
            cases stored : locals.write id type value with
            | error failure => simp [stored] at written
            | ok nextLocals =>
                simp only [stored] at written
                cases written
                exact Copy.bind_frame copied

/-- Appending a log leaves every other heap component unchanged. -/
theorem emit_frame (emitted : emit heap topics data = .ok after) :
    {after with execution := {after.execution with world := {after.execution.world with logs := heap.execution.world.logs}}} = heap := by
  unfold emit at emitted
  split at emitted
  · cases emitted
  · split at emitted
    · cases emitted
    · cases emitted; rfl

end Solidity.Execution.Effects
