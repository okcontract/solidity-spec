/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Types

/-! Runtime binding cells use resolved declaration IDs and the full source
value family. This differs from the legacy scalar Core.Env: reference cells
may be unset, and tuple groupings are packets rather than storable values. -/
namespace Solidity.Execution
open Static
open Aggregates (Heap Place Result Failure)

abbrev Value := Aggregates.Value
abbrev LocalId := Nat

inductive Datum where
  | atom : Value → Datum
  | tuple : List Datum → Datum

abbrev Packet := List Datum

mutual
def Datum.type : Datum → SType
  | .atom value => value.type
  | .tuple values => .tuple (packetTypes values)

def packetTypes : Packet → Types
  | [] => .nil
  | value :: rest => .cons value.type (packetTypes rest)
end

def Datum.asAtom : Datum → Result Value
  | .atom value => .ok value
  | .tuple _ => .error (.invalidContext "tuple grouping used as a single stored value")

def Datum.asPacket : Datum → Packet
  | .atom value => [.atom value]
  | .tuple values => values

def Datum.ofPacket : Packet → Datum
  | [value] => value
  | values => .tuple values

def Datum.hasType (value : Datum) (type : SType) : Bool := value.type == type

structure Binder where
  id : LocalId
  type : SType
  name : Option String := none
  deriving DecidableEq, Repr

structure LocalCell where
  type : SType
  value : Option type.Value := none

abbrev Scope := List (LocalId × LocalCell)
abbrev Locals := List Scope

def Scope.find : Scope → LocalId → Option LocalCell
  | [], _ => none
  | (found, cell) :: rest, id => if found = id then some cell else Scope.find rest id

def Scope.replace : Scope → LocalId → LocalCell → Scope
  | [], _, _ => []
  | (found, cell) :: rest, id, next =>
      if found = id then (found, next) :: rest else (found, cell) :: Scope.replace rest id next

def Locals.empty : Locals := [[]]
def Locals.enter (locals : Locals) : Locals := [] :: locals

def Locals.leave : Locals → Result Locals
  | [] => .error (.invalidContext "local scope stack is empty")
  | _ :: rest => .ok rest

def Locals.find : Locals → LocalId → Option LocalCell
  | [], _ => none
  | scope :: rest, id => (Scope.find scope id).orElse fun _ => Locals.find rest id

def Locals.replace : Locals → LocalId → LocalCell → Locals
  | [], _, _ => []
  | scope :: rest, id, next => match Scope.find scope id with
      | some _ => Scope.replace scope id next :: rest
      | none => scope :: Locals.replace rest id next

def Locals.typeOf (locals : Locals) (id : LocalId) : Result SType := do
  let some cell := locals.find id | throw (.invalidContext "unbound local cell")
  return cell.type

def Locals.read (locals : Locals) (id : LocalId) (expected : SType) : Result Value := do
  let some cell := locals.find id | throw (.invalidContext "unbound local cell")
  if cell.type != expected then throw (.invalidContext "local cell type mismatch")
  let some value := cell.value | throw (.invalidContext "uninitialized local reference")
  return ⟨cell.type, value⟩

/-- Conversion and reference transfer happen in Effects before this cell
store. The captured declaration type must still match the live binding. -/
def Locals.write (locals : Locals) (id : LocalId) (expected : SType) (source : Value) : Result Locals := do
  let some cell := locals.find id | throw (.invalidContext "unbound local cell")
  if cell.type != expected then throw (.invalidContext "local cell type mismatch")
  if same : source.type = cell.type then
    return locals.replace id ⟨cell.type, some (same ▸ source.value)⟩
  else throw (.invalidContext "local cell value type mismatch")

/-- IDs are unique among active scopes. Shadowed source names receive distinct
resolved IDs; recursive invocations have separate Locals values. -/
def Locals.declare (locals : Locals) (binder : Binder) (value : Option Value := none) : Result Locals := do
  if (locals.find binder.id).isSome then throw (.invalidContext "duplicate active local declaration ID")
  let cell ← match value with
    | none => pure (⟨binder.type, none⟩ : LocalCell)
    | some source =>
        if same : source.type = binder.type then
          pure (⟨binder.type, some (same ▸ source.value)⟩ : LocalCell)
        else throw (.invalidContext "local initializer type mismatch")
  match locals with
  | [] => throw (.invalidContext "local scope stack is empty")
  | scope :: rest => return ((binder.id, cell) :: scope) :: rest

inductive Captured where
  | local : LocalId → SType → Captured
  | heap : Place → Captured

def Captured.type : Captured → SType
  | .local _ type => type
  | .heap place => place.type

theorem Locals.leave_enter (locals : Locals) : locals.enter.leave = .ok locals := rfl

theorem Locals.find_enter (locals : Locals) (id : LocalId) : locals.enter.find id = locals.find id := rfl

theorem Scope.find_replace_self {scope : Scope} {id : LocalId} {old next : LocalCell}
    (found : Scope.find scope id = some old) :
    Scope.find (Scope.replace scope id next) id = some next := by
  induction scope with
  | nil => cases found
  | cons entry rest ih =>
      rcases entry with ⟨key, cell⟩
      by_cases same : key = id
      · simp [Scope.find, Scope.replace, same]
      · simp only [Scope.find, same, ↓reduceIte] at found
        simpa only [Scope.find, Scope.replace, same, ↓reduceIte] using ih found

theorem Locals.find_replace_self {locals : Locals} {id : LocalId} {old next : LocalCell}
    (found : locals.find id = some old) :
    (locals.replace id next).find id = some next := by
  induction locals with
  | nil => cases found
  | cons scope rest ih =>
      cases position : Scope.find scope id with
      | none =>
          simp only [Locals.find, position, Option.orElse_none] at found
          simpa only [Locals.find, Locals.replace, position, Option.orElse_none] using ih found
      | some cell =>
          simp only [Locals.replace, position, Locals.find, Scope.find_replace_self position, Option.orElse_some]

theorem Scope.find_replace_other {scope : Scope} {id other : LocalId} {next : LocalCell}
    (different : id ≠ other) : Scope.find (scope.replace id next) other = scope.find other := by
  induction scope with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, cell⟩
      by_cases selected : key = id
      · subst key
        simp [Scope.find, Scope.replace, different]
      · simp only [Scope.find, Scope.replace, selected, ↓reduceIte]
        by_cases observed : key = other
        · simp [observed]
        · simp [observed, ih]

theorem Locals.find_replace_other {locals : Locals} {id other : LocalId} {next : LocalCell}
    (different : id ≠ other) : (locals.replace id next).find other = locals.find other := by
  induction locals with
  | nil => rfl
  | cons scope rest ih =>
      cases position : scope.find id with
      | none => simp only [Locals.find, Locals.replace, position, ih]
      | some cell => simp only [Locals.replace, position, Locals.find, Scope.find_replace_other different]

attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem Locals.read_after_write {locals after : Locals} {id : LocalId} {type : SType} {value : Value}
    (written : Locals.write locals id type value = .ok after) : after.read id type = .ok value := by
  unfold Locals.write at written
  cases position : locals.find id with
  | none => simp [position] at written
  | some cell =>
      simp only [position] at written
      split at written
      · cases written
      · rename_i correct
        have declared : cell.type = type := by simpa using correct
        split at written
        · rename_i same
          rcases value with ⟨actual, data⟩
          dsimp only at same
          cases same
          simp only at written
          cases written
          simp [Locals.read, Locals.find_replace_self position, declared]
        · cases written

theorem Locals.write_frames_other {locals after : Locals} {id other : LocalId}
    (different : id ≠ other)
    (written : locals.write id type value = .ok after) : after.find other = locals.find other := by
  unfold Locals.write at written
  cases position : locals.find id with
  | none => simp [position] at written
  | some cell =>
      simp only [position] at written
      split at written
      · cases written
      · split at written
        · cases written; exact Locals.find_replace_other different
        · cases written

theorem Locals.inner_write_frames_outer {inner : Scope} {outer after : Locals} {id : LocalId}
    (bound : inner.find id = some cell)
    (written : Locals.write (inner :: outer) id type value = .ok after) :
    ∃ next, after = next :: outer := by
  unfold Locals.write at written
  simp only [Locals.find, bound, Option.orElse_some] at written
  split at written
  · cases written
  · split at written
    · rename_i same
      cases written
      exact ⟨inner.replace id ⟨cell.type, some (same ▸ value.value)⟩, by simp [Locals.replace, bound]⟩
    · cases written

theorem Locals.read_eq_of_find_eq {before after : Locals} {id : LocalId}
    (same : before.find id = after.find id) : before.read id type = after.read id type := by
  unfold Locals.read
  rw [same]

theorem Locals.read_frames_other {locals after : Locals} {id other : LocalId}
    (different : id ≠ other) (written : locals.write id type value = .ok after) :
    after.read other expected = locals.read other expected :=
  Locals.read_eq_of_find_eq (Locals.write_frames_other different written)

end Solidity.Execution
