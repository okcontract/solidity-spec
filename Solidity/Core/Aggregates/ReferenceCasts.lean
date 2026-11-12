/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Copy.Laws

/-! Explicit reference conversions, separate from implicit assignment planning.
Pinned `types.zig` admits same-location bytes/string reinterprets and bytes to
fixed bytes (including calldata slices). The source type checker resolves a
reference cast target to the argument's location. A reinterpret preserves its
physical descriptor; a fixed-byte conversion observes only a bounded used prefix
and right-pads with zero, even if native unused padding is dirty. -/
namespace Solidity.Aggregates.ReferenceCasts
open Core Static
open Contract.Interaction (Word bytesWord)

inductive Kind where
  | alias
  | prefix
  deriving DecidableEq, Repr

/-- Source permission, stated independently of the executable selector. Slice
identity lives in Reference.viewLength; it does not erase the underlying bytes
family or permit conversion of an ordinary uint8[] array to bytes/string. -/
def Permission (source target : SType) : Kind → Prop
  | .alias => match source, target with
      | .bytes a _, .bytes b _ | .bytes a _, .string b _ |
        .string a _, .bytes b _ | .string a _, .string b _ => a = b
      | .array _ _ a _, .array _ _ b _ => a = b ∧ SameShape source target
      | _, _ => False
  | .prefix => match source, target with
      | .bytes _ _, .fixedBytes _ => True
      | _, _ => False

def select : SType → SType → Option Kind
  | .bytes a _, .bytes b _ | .bytes a _, .string b _ |
    .string a _, .bytes b _ | .string a _, .string b _ =>
      if a == b then some .alias else none
  | a@(.array _ _ origin _), b@(.array _ _ destination _) =>
      if origin == destination && sameShape a b then some .alias else none
  | .bytes _ _, .fixedBytes _ => some .prefix
  | _, _ => none

theorem select_iff (source target : SType) (kind : Kind) :
    select source target = some kind ↔ Permission source target kind := by
  cases source <;> cases target <;> cases kind <;> simp [select, Permission, sameShape_iff]

/-- Surface bytes(...) / string(...) cannot request a location change. The
resolved result descriptor uses the argument's location and the reference
pointer marker of ordinary type-conversion syntax. Rvalue binding-cell clearing
is a separate operation. -/
def resolveTarget (requested source : SType) : Result SType :=
  match requested, referenceLocation source with
  | .bytes _ _, some location => .ok (.bytes location true)
  | .string _ _, some location => .ok (.string location true)
  | type@(.array _ _ _ _), some location => .ok (atLocation type location true)
  | .fixedBytes width, _ => .ok (.fixedBytes width)
  | _, _ => .error .rejected

/-- Fixed bytes are represented right-aligned in their width-indexed source
value. Only the observed prefix is supplied here; appended zero bytes are part
of the typed cast, not an assumption about unused raw memory. -/
def prefixValue (width : Width) (bytes : List UInt8) : BitVec width.bits :=
  (bytesWord (bytes ++ List.replicate (width.val+1-bytes.length) 0)).setWidth width.bits

/-- At most 32 used bytes are materialized. Length decoding and byte reads keep
the source region's own validation and failure outcomes. -/
def toFixedBytes (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (source : Place) (width : Width) : Result (Value × Nat) := do
  let length ← Access.sourceLength registry fuel heap source
  let count := min (width.val+1) length
  let remaining ← reserve budget (count+1)
  let bytes ← Copy.sourceBytes registry fuel heap source 0 count
  return (⟨.fixedBytes width, prefixValue width bytes⟩, remaining)

def run (registry : Registry) (fuel budget : Nat) (heap : Heap) (target : SType)
    (source : Place) : Kind → Result (Value × Nat)
  | .alias => do
      return (← Copy.retag target {source.reference with bindingCell := none}, budget)
  | .prefix => match target with
      | .fixedBytes width => toFixedBytes registry fuel budget heap source width
      | _ => .error .rejected

/-- A checked source endpoint. Descriptor casts perform no heap reads or
allocation beyond source lifetime validation; payload extent is checked when a
payload operation actually consumes it. This preserves native cast ordering. -/
def cast (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (target : SType) (source : Value) : Result (Value × Nat) := do
  let some kind := select source.type target | throw .rejected
  let some reference := source.reference | throw .rejected
  eligibleAt registry fuel reference.region source.type
  eligibleAt registry fuel reference.region target
  Access.validate heap ⟨source.type, reference⟩
  run registry fuel budget heap target ⟨source.type, reference⟩ kind

/-- Syntax-level target resolution followed by the same checked endpoint. -/
def castRequested (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (requested : SType) (source : Value) : Result (Value × Nat) := do
  let target ← resolveTarget requested source.type
  cast registry fuel budget heap target source

private theorem cast_map_error (failure : Failure) (f : α → β) :
    f <$> (Except.error failure : Result α) = .error failure := rfl
private theorem cast_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Result α) = .ok (f value) := rfl
attribute [local simp] cast_map_error cast_map_ok Bind.bind Except.bind Pure.pure Except.pure

theorem cast_iff : cast registry fuel budget heap target source = .ok result ↔
    ∃ kind reference, Permission source.type target kind ∧ source.reference = some reference ∧
      eligibleAt registry fuel reference.region source.type = .ok () ∧
      eligibleAt registry fuel reference.region target = .ok () ∧
      Access.validate heap ⟨source.type, reference⟩ = .ok () ∧
      run registry fuel budget heap target ⟨source.type, reference⟩ kind = .ok result := by
  unfold cast
  constructor
  · intro finished
    cases selected : select source.type target with
    | none => simp [selected] at finished
    | some kind =>
        simp only [selected, Bind.bind, Except.bind] at finished
        cases extracted : source.reference with
        | none => simp [extracted] at finished
        | some reference =>
            simp only [extracted] at finished
            cases a : eligibleAt registry fuel reference.region source.type with
            | error failure => simp [a] at finished
            | ok firstCheck =>
                cases firstCheck
                simp only [a] at finished
                cases b : eligibleAt registry fuel reference.region target with
                | error failure => simp [b] at finished
                | ok secondCheck =>
                    cases secondCheck
                    simp only [b] at finished
                    cases c : Access.validate heap ⟨source.type, reference⟩ with
                    | error failure => simp [c] at finished
                    | ok checkedValue =>
                        cases checkedValue
                        simp only [c] at finished
                        exact ⟨kind, reference, (select_iff _ _ _).mp selected, rfl, a, b, c, finished⟩
  · rintro ⟨kind, reference, permitted, extracted, a, b, c, finished⟩
    simp only [(select_iff _ _ _).mpr permitted, extracted, Bind.bind, Except.bind, a, b, c]
    exact finished

/-- This is the exact alias theorem: address, region, slice length/base,
byte offset and lifetime guards survive; the former pointer-cell binding does
not turn an rvalue cast into an assignment to the original local. -/
theorem cast_alias_reference
    (alias : select source.type target = some .alias)
    (casted : cast registry fuel budget heap target source = .ok (value, remaining)) :
    remaining = budget ∧ ∃ reference, source.reference = some reference ∧
      value.reference = some {reference with bindingCell := none} := by
  obtain ⟨kind, reference, permission, extracted, _, _, _, finished⟩ := cast_iff.mp casted
  have same : kind = .alias := by rw [(select_iff _ _ _).mpr permission] at alias; exact Option.some.inj alias
  subst kind
  simp only [run, Bind.bind, Except.bind, Pure.pure, Except.pure] at finished
  cases tagged : Copy.retag target {reference with bindingCell := none} with
  | error failure => simp [tagged] at finished
  | ok found =>
      simp only [tagged] at finished
      cases finished
      exact ⟨rfl, reference, extracted, Copy.retag_reference tagged⟩

/-- The physical result law is a bounded used-prefix read. No byte outside the
actual length, and no dirty unused padding, enters the converted scalar. -/
theorem toFixedBytes_iff : toFixedBytes registry fuel budget heap source width = .ok (value, remaining) ↔
    ∃ length bytes, Access.sourceLength registry fuel heap source = .ok length ∧
      reserve budget (min (width.val+1) length+1) = .ok remaining ∧
      Copy.sourceBytes registry fuel heap source 0 (min (width.val+1) length) = .ok bytes ∧
      value = ⟨.fixedBytes width, prefixValue width bytes⟩ := by
  unfold toFixedBytes
  constructor
  · intro finished
    cases length : Access.sourceLength registry fuel heap source with
    | error failure => simp [length] at finished
    | ok count =>
        simp only [length, Bind.bind, Except.bind] at finished
        cases reserved : reserve budget (min (width.val+1) count+1) with
        | error failure => simp [reserved] at finished
        | ok available =>
            simp only [reserved] at finished
            cases read : Copy.sourceBytes registry fuel heap source 0 (min (width.val+1) count) with
            | error failure => simp [read] at finished
            | ok bytes =>
                simp only [read, Pure.pure, Except.pure] at finished
                cases finished
                exact ⟨count, bytes, rfl, reserved, read, rfl⟩
  · rintro ⟨length, bytes, lengthRead, reserved, read, rfl⟩
    simp only [lengthRead, Bind.bind, Except.bind, reserved, read, Pure.pure, Except.pure]

private theorem retag_type (tagged : Copy.retag type reference = .ok value) : value.type = type := by
  cases type <;> simp only [Copy.retag, referenceValue, Bind.bind, Except.bind, Pure.pure, Except.pure] at tagged <;>
    cases tagged <;> rfl

theorem run_type
    (ran : run registry fuel budget heap target source kind = .ok (value, remaining)) : value.type = target := by
  cases kind with
  | alias =>
      simp only [run, Bind.bind, Except.bind, Pure.pure, Except.pure] at ran
      cases tagged : Copy.retag target {source.reference with bindingCell := none} with
      | error failure => simp [tagged] at ran
      | ok found =>
          simp only [tagged] at ran
          cases ran
          exact retag_type tagged
  | «prefix» =>
      cases target <;> simp only [run] at ran
      all_goals try cases ran
      case fixedBytes width =>
        obtain ⟨_, _, _, _, _, rfl⟩ := toFixedBytes_iff.mp ran
        rfl

theorem cast_type
    (casted : cast registry fuel budget heap target source = .ok (value, remaining)) : value.type = target := by
  obtain ⟨_, _, _, _, _, _, _, ran⟩ := cast_iff.mp casted
  exact run_type ran

theorem prefix_work_bounded (width : Width) (length : Nat) : min (width.val+1) length ≤ 32 := by
  have := width.isLt
  have := Nat.min_le_left (width.val+1) length
  omega

/-- State clients get the same heap exactly; this wrapper does not hide any
storage write, memory allocation, log, invocation or lifetime change. -/
def castState (registry : Registry) (fuel budget : Nat) (heap : Heap)
    (target : SType) (source : Value) : Result (Value × Heap × Nat) := do
  let (value, remaining) ← cast registry fuel budget heap target source
  return (value, heap, remaining)

theorem castState_frame
    (casted : castState registry fuel budget heap target source = .ok (value, after, remaining)) : after = heap := by
  unfold castState at casted
  cases result : cast registry fuel budget heap target source with
  | error failure => simp [result] at casted
  | ok pair =>
      rcases pair with ⟨found, available⟩
      simp only [result, Bind.bind, Except.bind, Pure.pure, Except.pure] at casted
      cases casted
      rfl

end Solidity.Aggregates.ReferenceCasts
