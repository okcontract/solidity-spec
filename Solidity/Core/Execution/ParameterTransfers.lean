/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Machine
import Solidity.Core.Execution.EffectsLaws
import Solidity.Core.Execution.ConstructorLaws
import Solidity.Core.Execution.BindingsLaws
import Solidity.Core.Execution.TransitionRelations

/-! Parameter and result transfer contracts quantify over every `SType`.
Independent traces record the actual aggregate scalar/alias/snapshot/construction
primitives and real lexical declarations/writes. No callee execution or
desired transfer postcondition is assumed. -/
namespace Solidity.Execution.ParameterTransfers
open Static Aggregates
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure
variable {σ : Type} {Key : SType → Type} {backend : Backend σ Key}

inductive Bound (registry : Registry) (fuel budget : Nat) (heap : Heap) (type : SType) (source : Value) :
    Value → Heap → Nat → Prop where
  | scalar (planned : planTransfer registry fuel true source.type type = .ok .scalarConversion)
      (converted : Copy.convertScalar type source = .ok value) : Bound registry fuel budget heap type source value heap budget
  | alias (kind : TransferKind) (alias : kind = .storageAlias ∨ kind = .memoryAlias ∨ kind = .calldataAlias)
      (planned : planTransfer registry fuel true source.type type = .ok kind)
      (converted : Copy.alias heap type source = .ok value) : Bound registry fuel budget heap type source value heap budget
  | memoryCopy (planned : planTransfer registry fuel true source.type type = .ok .memoryCopy)
      (frozen : Copy.snapshotValue registry fuel budget heap source = .ok (contents, allowance))
      (built : Copy.materializeMemory registry fuel allowance heap type contents = .ok (value, after, remaining)) :
      Bound registry fuel budget heap type source value after remaining

theorem bound_iff : Copy.bind registry fuel budget heap type source = .ok (value, after, remaining) ↔
    Bound registry fuel budget heap type source value after remaining := by
  constructor
  · intro bound
    unfold Copy.bind at bound
    cases planned : planTransfer registry fuel true source.type type with
    | error failure => simp [planned] at bound
    | ok kind =>
        simp only [planned] at bound
        cases kind with
        | scalarConversion =>
            change (do let value ← Copy.convertScalar type source; pure (value, heap, budget)) = .ok (value, after, remaining) at bound
            cases converted : Copy.convertScalar type source with
            | error failure => simp [converted] at bound
            | ok result => simp only [converted] at bound; cases bound; exact .scalar planned converted
        | storageAlias | memoryAlias | calldataAlias =>
            all_goals
              change (do let value ← Copy.alias heap type source; pure (value, heap, budget)) = .ok (value, after, remaining) at bound
              cases converted : Copy.alias heap type source with
              | error failure => simp [converted] at bound
              | ok result =>
                  simp only [converted] at bound
                  cases bound
                  exact .alias _ (by simp) planned converted
        | memoryCopy =>
            change (do let (contents, allowance) ← Copy.snapshotValue registry fuel budget heap source
                       Copy.materializeMemory registry fuel allowance heap type contents) = .ok (value, after, remaining) at bound
            cases frozen : Copy.snapshotValue registry fuel budget heap source with
            | error failure => simp [frozen] at bound
            | ok result =>
                rcases result with ⟨contents, allowance⟩
                simp only [frozen] at bound
                exact .memoryCopy planned frozen bound
        | storageCopy => cases bound
  · intro bound
    cases bound with
    | scalar planned converted => exact Copy.bind_scalar planned converted
    | alias kind alias planned converted => exact Copy.bind_alias planned alias converted
    | memoryCopy planned frozen built =>
        rw [Copy.bind_memoryCopy planned]
        simp only [frozen]
        exact built

theorem Bound.runtime (bound : Bound registry fuel budget heap type source value after remaining) :
    Copy.bind registry fuel budget heap type source = .ok (value, after, remaining) := bound_iff.mpr bound

theorem Bound.permission (bound : Bound registry fuel budget heap type source value after remaining) :
    ∃ kind, planTransfer registry fuel true source.type type = .ok kind ∧ TransferRule true source.type type kind := by
  cases bound with
  | scalar planned _ => exact ⟨_, planned, planTransfer_rule planned⟩
  | alias _ _ planned _ => exact ⟨_, planned, planTransfer_rule planned⟩
  | memoryCopy planned _ _ => exact ⟨_, planned, planTransfer_rule planned⟩

theorem Bound.frame (bound : Bound registry fuel budget heap type source value after remaining) :
    after.execution.world = heap.execution.world ∧ after.invocation = heap.invocation :=
  Copy.bind_frame bound.runtime

theorem Bound.extension (bound : Bound registry fuel budget heap type source value after remaining) :
    Copy.MemoryExtension heap.nextMemory heap after := Constructors.bind_extension bound.runtime

theorem Bound.alias_reference (bound : Bound registry fuel budget heap type source value after remaining)
    (planned : planTransfer registry fuel true source.type type = .ok kind)
    (alias : kind = .storageAlias ∨ kind = .memoryAlias ∨ kind = .calldataAlias) :
    after = heap ∧ remaining = budget ∧ ∃ reference, source.reference = some reference ∧
      value.reference = some {reference with bindingCell := none} :=
  Constructors.bind_alias_reference planned alias bound.runtime

theorem Bound.memoryCopy_rep (bound : Bound registry fuel budget heap type source value after remaining)
    (valid : MemoryOps.validFrontier heap = true)
    (planned : planTransfer registry fuel true source.type type = .ok .memoryCopy)
    (frozen : Copy.snapshotValue registry fuel budget heap source = .ok (contents, allowance)) :
    Copy.ValueRep registry after heap.nextMemory type contents value ∧ Copy.MemoryExtension heap.nextMemory heap after :=
  Copy.bind_memoryCopy_rep valid planned frozen bound.runtime

private theorem retag_type (tagged : Copy.retag type reference = .ok value) : value.type = type := by
  unfold Copy.retag at tagged
  cases converted : referenceValue type reference with
  | error failure => simp [converted] at tagged
  | ok result => simp only [converted] at tagged; cases tagged; rfl

private theorem alias_type (aliased : Copy.alias heap type source = .ok value) : value.type = type := by
  unfold Copy.alias at aliased
  cases found : source.reference with
  | none => simp [found] at aliased
  | some reference =>
      simp only [found, Bind.bind, Except.bind] at aliased
      cases checked : Access.validate heap ⟨source.type, reference⟩ with
      | error failure => simp [checked] at aliased
      | ok token =>
          simp only [checked] at aliased
          cases extent : checkExtent heap reference 0 with
          | error failure => simp [extent] at aliased
          | ok token => simp only [extent] at aliased; exact retag_type aliased

private theorem represented_type (represented : Copy.ValueRep registry heap lower type contents value) : value.type = type := by
  cases contents with
  | scalar source => exact Copy.convertScalar_type represented
  | bytes _ _ | array _ _ | «structure» _ _ =>
      rcases represented with ⟨address, tagged, _⟩
      exact retag_type tagged

theorem Bound.result_type (bound : Bound registry fuel budget heap type source value after remaining)
    (valid : MemoryOps.validFrontier heap = true) : value.type = type := by
  cases bound with
  | scalar _ converted => exact Copy.convertScalar_type converted
  | alias _ _ _ converted => exact alias_type converted
  | memoryCopy _ _ built => exact represented_type (Copy.materializeMemory_rep valid built)

inductive Prepared (registry : Registry) (fuel : Nat) :
    MachineState σ → List SType → Packet → Packet → MachineState σ → Prop where
  | nil (state) : Prepared registry fuel state [] [] [] state
  | cons (atom : source.asAtom = .ok actual)
      (bound : Bound registry fuel state.materializationRemaining state.heap type actual value heap remaining)
      (tail : Prepared registry fuel {state with heap, materializationRemaining := remaining} types sources values after) :
      Prepared registry fuel state (type :: types) (source :: sources) (.atom value :: values) after

theorem prepareArguments_iff :
    Machine.prepareArguments registry limits state types sources = .ok (values, after) ↔
      Prepared registry limits.aggregateFuel state types sources values after := by
  induction types generalizing state sources values after with
  | nil =>
      cases sources with
      | nil =>
          constructor
          · intro same; cases same; exact .nil _
          · intro trace; cases trace; rfl
      | cons source sources =>
          constructor
          · intro same; cases same
          · intro trace; cases trace
  | cons type types ih =>
      cases sources with
      | nil =>
          constructor
          · intro same; cases same
          · intro trace; cases trace
      | cons source sources =>
          constructor
          · intro prepared
            change (do
              let actual ← source.asAtom
              let (value, heap, remaining) ← Copy.bind registry limits.aggregateFuel state.materializationRemaining state.heap type actual
              let (values, after) ← Machine.prepareArguments registry limits {state with heap, materializationRemaining := remaining} types sources
              pure (Datum.atom value :: values, after)) = .ok (values, after) at prepared
            cases atom : source.asAtom with
            | error failure => simp [atom] at prepared
            | ok actual =>
                simp only [atom, Bind.bind, Except.bind] at prepared
                cases converted : Copy.bind registry limits.aggregateFuel state.materializationRemaining state.heap type actual with
                | error failure => simp [converted] at prepared
                | ok result =>
                    rcases result with ⟨value, heap, remaining⟩
                    simp only [converted] at prepared
                    cases rest : Machine.prepareArguments registry limits {state with heap, materializationRemaining := remaining} types sources with
                    | error failure => simp [rest] at prepared
                    | ok result =>
                        rcases result with ⟨values, after⟩
                        simp only [rest, Pure.pure, Except.pure] at prepared
                        cases prepared
                        exact .cons atom (bound_iff.mp converted) (ih.mp rest)
          · intro trace
            cases trace with
            | cons atom bound tail =>
                simp [Machine.prepareArguments, atom, Effects.convert, bound.runtime, (ih.mpr tail)]

theorem Prepared.frame (trace : Prepared registry fuel state types sources values after) :
    after.external = state.external ∧ after.locals = state.locals ∧ after.mode = state.mode ∧
      after.heap.execution.world = state.heap.execution.world ∧ after.heap.invocation = state.heap.invocation := by
  induction trace with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons _ bound _ ih => exact ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2.1.trans bound.frame.1, ih.2.2.2.2.trans bound.frame.2⟩

theorem Prepared.extension (trace : Prepared registry fuel state types sources values after) :
    Copy.MemoryExtension state.heap.nextMemory state.heap after.heap := by
  induction trace with
  | nil => exact .refl _ _
  | cons _ bound _ ih => exact bound.extension.trans (ih.weaken bound.extension.grows)

theorem Prepared.result_types (trace : Prepared registry fuel state types sources values after)
    (valid : MemoryOps.validFrontier state.heap = true) : values.map Datum.type = types := by
  induction trace with
  | nil => rfl
  | cons _ bound _ ih => simp [Datum.type, bound.result_type valid, ih (bound.extension.valid valid)]

inductive Stored (registry : Registry) (fuel : Nat) :
    MachineState σ → Binder → Value → Value → MachineState σ → Prop where
  | intro (declared : state.locals.typeOf binder.id = .ok binder.type)
      (bound : Bound registry fuel state.materializationRemaining state.heap binder.type source value heap remaining)
      (written : state.locals.write binder.id binder.type value = .ok locals) :
      Stored registry fuel state binder source value {state with locals, heap, materializationRemaining := remaining}

theorem stored_iff :
    Machine.writeTarget backend registry limits state (.captured (.local binder.id binder.type)) source = .ok after ↔
      ∃ value, Stored registry limits.aggregateFuel state binder source value after := by
  constructor
  · intro stored
    unfold Machine.writeTarget Effects.writeCaptured at stored
    cases declared : state.locals.typeOf binder.id with
    | error failure => simp [declared] at stored
    | ok actual =>
        simp only [declared, Bind.bind, Except.bind] at stored
        by_cases same : actual = binder.type
        ·
          subst actual
          simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at stored
          cases bound : Copy.bind registry limits.aggregateFuel state.materializationRemaining state.heap binder.type source with
          | error failure => simp [bound] at stored
          | ok result =>
              rcases result with ⟨value, heap, remaining⟩
              simp only [bound] at stored
              cases written : state.locals.write binder.id binder.type value with
              | error failure => simp [written] at stored
              | ok locals =>
                  simp only [written] at stored
                  cases stored
                  exact ⟨value, .intro declared (bound_iff.mp bound) written⟩
        · simp [same] at stored
  · rintro ⟨value, stored⟩
    cases stored with
    | intro declared bound written =>
        simp [Machine.writeTarget, Effects.writeCaptured, declared, bound.runtime, written]

theorem Stored.runtime (stored : Stored registry limits.aggregateFuel state binder source value after) :
    Machine.writeTarget backend registry limits state (.captured (.local binder.id binder.type)) source = .ok after :=
  stored_iff.mpr ⟨value, stored⟩

theorem Stored.readback (stored : Stored registry fuel state binder source value after) :
    after.locals.read binder.id binder.type = .ok value := by
  cases stored with
  | intro _ _ written => exact Locals.read_after_write written

theorem Stored.bind (stored : Stored registry fuel state binder source value after) :
    Bound registry fuel state.materializationRemaining state.heap binder.type source value after.heap after.materializationRemaining := by
  cases stored with | intro _ bound _ => exact bound

theorem Stored.frames_other (stored : Stored registry fuel state binder source value after) (different : binder.id ≠ other) :
    after.locals.find other = state.locals.find other := by
  cases stored with | intro _ _ written => exact Locals.write_frames_other different written

theorem Stored.frame (stored : Stored registry fuel state binder source value after) :
    after.external = state.external ∧ after.mode = state.mode ∧
      after.heap.execution.world = state.heap.execution.world ∧ after.heap.invocation = state.heap.invocation := by
  cases stored with | intro _ bound _ => exact ⟨rfl, rfl, bound.frame⟩

/-- Parameter cells are declared unset before binding. Return cells already
exist; result transfer writes those cells without redeclaring or defaulting. -/
def openCell (declare : Bool) (locals : Locals) (binder : Binder) : Result Locals :=
  if declare then locals.declare binder else .ok locals

theorem openCell_other (opened : openCell declare locals binder = .ok after) (different : binder.id ≠ other) :
    after.find other = locals.find other := by
  cases declare with
  | false => cases opened; rfl
  | true => exact Locals.declare_frames_other (value := none) different (by simpa only [openCell] using opened)

inductive Transferred (registry : Registry) (fuel : Nat) (declare : Bool) :
    MachineState σ → List Binder → Packet → List (Binder × Value) → MachineState σ → Prop where
  | nil (state) : Transferred registry fuel declare state [] [] [] state
  | cons (atom : source.asAtom = .ok actual)
      (opened : openCell declare state.locals binder = .ok locals)
      (stored : Stored registry fuel {state with locals} binder actual value middle)
      (tail : Transferred registry fuel declare middle binders sources values after) :
      Transferred registry fuel declare state (binder :: binders) (source :: sources) ((binder, value) :: values) after

theorem bindArguments_iff :
    Machine.bindArguments backend registry limits state binders sources = .ok after ↔
      ∃ values, Transferred registry limits.aggregateFuel true state binders sources values after := by
  induction binders generalizing state sources after with
  | nil =>
      cases sources with
      | nil =>
          constructor
          · intro same; cases same; exact ⟨[], .nil _⟩
          · rintro ⟨values, trace⟩; cases trace; rfl
      | cons source sources =>
          constructor
          · intro same; cases same
          · rintro ⟨values, trace⟩; cases trace
  | cons binder binders ih =>
      cases sources with
      | nil =>
          constructor
          · intro same; cases same
          · rintro ⟨values, trace⟩; cases trace
      | cons source sources =>
          constructor
          · intro bound
            simp only [Machine.bindArguments, Machine.declareUnset] at bound
            cases opened : state.locals.declare binder with
            | error failure => simp [opened] at bound
            | ok locals =>
                simp only [opened, Bind.bind, Except.bind, Pure.pure, Except.pure] at bound
                cases atom : source.asAtom with
                | error failure => simp [atom] at bound
                | ok actual =>
                    simp only [atom] at bound
                    cases written : Machine.writeTarget backend registry limits {state with locals}
                        (.captured (.local binder.id binder.type)) actual with
                    | error failure => simp [written] at bound
                    | ok middle =>
                        simp only [written] at bound
                        obtain ⟨value, stored⟩ := stored_iff.mp written
                        obtain ⟨values, tail⟩ := ih.mp bound
                        exact ⟨_, .cons atom opened stored tail⟩
          · rintro ⟨values, trace⟩
            cases trace with
            | cons atom opened stored tail =>
                simp only [openCell, ↓reduceIte] at opened
                simp [Machine.bindArguments, Machine.declareUnset, opened, atom, stored.runtime, ih.mpr ⟨_, tail⟩]

theorem Transferred.output_binders (trace : Transferred registry fuel declare state binders sources values after) :
    values.map Prod.fst = binders := by
  induction trace with | nil => rfl | cons _ _ _ _ ih => simp [ih]

theorem Transferred.frame (trace : Transferred registry fuel declare state binders sources values after) :
    after.external = state.external ∧ after.mode = state.mode ∧
      after.heap.execution.world = state.heap.execution.world ∧ after.heap.invocation = state.heap.invocation := by
  induction trace with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons _ _ stored _ ih =>
      exact ⟨ih.1.trans stored.frame.1, ih.2.1.trans stored.frame.2.1,
        ih.2.2.1.trans stored.frame.2.2.1, ih.2.2.2.trans stored.frame.2.2.2⟩

theorem Transferred.extension (trace : Transferred registry fuel declare state binders sources values after) :
    Copy.MemoryExtension state.heap.nextMemory state.heap after.heap := by
  induction trace with
  | nil => exact .refl _ _
  | cons _ _ stored _ ih => exact stored.bind.extension.trans (ih.weaken stored.bind.extension.grows)

theorem Transferred.frames_other (trace : Transferred registry fuel declare state binders sources values after)
    (different : other ∉ binders.map Binder.id) : after.locals.find other = state.locals.find other := by
  induction trace with
  | nil => rfl
  | cons _ opened stored _ ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at different
      have unequal : _ ≠ other := Ne.symm different.1
      exact (ih different.2).trans ((stored.frames_other unequal).trans (openCell_other opened unequal))

theorem Transferred.readback (trace : Transferred registry fuel declare state binders sources values after)
    (distinct : (binders.map Binder.id).Nodup) :
    ∀ binder value, (binder, value) ∈ values → after.locals.read binder.id binder.type = .ok value := by
  induction trace with
  | nil => simp
  | cons atom opened stored tail ih =>
      simp only [List.map_cons, List.nodup_cons] at distinct
      intro binder value member
      rcases List.mem_cons.mp member with same | rest
      · cases same
        exact (Locals.read_eq_of_find_eq (tail.frames_other distinct.1)).trans stored.readback
      · exact ih distinct.2 binder value rest

theorem Transferred.result_types (trace : Transferred registry fuel declare state binders sources values after)
    (valid : MemoryOps.validFrontier state.heap = true) :
    ∀ binder value, (binder, value) ∈ values → value.type = binder.type := by
  induction trace with
  | nil => simp
  | cons atom opened stored tail ih =>
      intro binder value member
      rcases List.mem_cons.mp member with same | rest
      · cases same; exact stored.bind.result_type valid
      · exact ih (stored.bind.extension.valid valid) binder value rest

inductive ResultArguments : List Binder → Packet → List (Binder × Value) → Prop where
  | nil : ResultArguments [] [] []
  | cons (atom : source.asAtom = .ok actual) (tail : ResultArguments binders sources values) :
      ResultArguments (binder :: binders) (source :: sources) ((binder, actual) :: values)

def destinations (Key : SType → Type) (values : List (Binder × Value)) : List (Target Key × Value) :=
  values.map fun (binder, value) => (.captured (.local binder.id binder.type), value)

theorem ResultArguments.runtime (arguments : ResultArguments binders sources values) :
    Machine.resultWrites (Key := Key) binders sources = .ok (destinations Key values) := by
  induction arguments with
  | nil => rfl
  | cons atom _ ih => simp [Machine.resultWrites, destinations, atom, ih]

theorem resultWrites_sound
    (written : Machine.resultWrites (Key := Key) binders sources = .ok assignments) :
    ∃ values, ResultArguments binders sources values ∧ assignments = destinations Key values := by
  induction binders generalizing sources assignments with
  | nil =>
      cases sources with
      | nil => cases written; exact ⟨[], .nil, rfl⟩
      | cons source sources => cases written
  | cons binder binders ih =>
      cases sources with
      | nil => cases written
      | cons source sources =>
          simp only [Machine.resultWrites] at written
          cases atom : source.asAtom with
          | error failure => simp [atom] at written
          | ok actual =>
              simp only [atom] at written
              cases tail : Machine.resultWrites (Key := Key) binders sources with
              | error failure => simp [tail] at written
              | ok rest =>
                  simp only [tail] at written
                  cases written
                  obtain ⟨values, arguments, rfl⟩ := ih tail
                  exact ⟨_, .cons atom arguments, rfl⟩

theorem Transferred.arguments (trace : Transferred registry fuel declare state binders sources values after) :
    ∃ arguments, ResultArguments binders sources arguments := by
  induction trace with
  | nil => exact ⟨[], .nil⟩
  | cons atom _ _ _ ih => obtain ⟨arguments, tail⟩ := ih; exact ⟨_, .cons atom tail⟩

theorem resultFold_iff (raw : ResultArguments binders sources arguments) :
    (destinations Key arguments).foldlM
      (fun state item => Machine.writeTarget backend registry limits state item.1 item.2) state = .ok after ↔
      ∃ values, Transferred registry limits.aggregateFuel false state binders sources values after := by
  induction raw generalizing state with
  | nil =>
      constructor
      · intro same; cases same; exact ⟨[], .nil _⟩
      · rintro ⟨values, trace⟩; cases trace; rfl
  | @cons binders sources arguments binder source actual atom tail ih =>
      constructor
      · intro result
        simp only [destinations, List.map_cons, List.foldlM_cons] at result
        cases written : Machine.writeTarget backend registry limits state
            (.captured (.local binder.id binder.type)) actual with
        | error failure => simp [written] at result
        | ok middle =>
            simp only [written] at result
            obtain ⟨value, stored⟩ := stored_iff.mp written
            obtain ⟨values, tail⟩ := ih.mp result
            exact ⟨_, .cons atom rfl stored tail⟩
      · rintro ⟨values, trace⟩
        cases trace with
        | cons atom' opened stored tail =>
            have same := Except.ok.inj (atom.symm.trans atom')
            cases same
            simp only [openCell] at opened
            cases opened
            simp only [destinations, List.map_cons, List.foldlM_cons, stored.runtime]
            exact ih.mpr ⟨_, tail⟩

/-- This is exactly the result-list construction and sequential writes used by
the call continuation, exposed as a proof endpoint rather than a new evaluator. -/
def transferResults (backend : Backend σ Key) (registry : Registry) (limits : Limits)
    (state : MachineState σ) (binders : List Binder) (sources : Packet) : Result (MachineState σ) := do
  let assignments ← Machine.resultWrites (Key := Key) binders sources
  assignments.foldlM (fun state item => Machine.writeTarget backend registry limits state item.1 item.2) state

theorem transferResults_iff : transferResults backend registry limits state binders sources = .ok after ↔
    ∃ values, Transferred registry limits.aggregateFuel false state binders sources values after := by
  constructor
  · intro result
    unfold transferResults at result
    cases written : Machine.resultWrites (Key := Key) binders sources with
    | error failure => simp [written] at result
    | ok assignments =>
        simp only [written] at result
        obtain ⟨arguments, typed, rfl⟩ := resultWrites_sound written
        exact (resultFold_iff typed).mp result
  · rintro ⟨values, trace⟩
    obtain ⟨arguments, typed⟩ := trace.arguments
    simp only [transferResults, typed.runtime]
    exact (resultFold_iff typed).mpr ⟨values, trace⟩

theorem collectResults_readback (values : List (Binder × Value)) (locals : Locals)
    (readback : ∀ binder value, (binder, value) ∈ values → locals.read binder.id binder.type = .ok value) :
    Machine.collectResults locals (values.map Prod.fst) = .ok (values.map (fun item => Datum.atom item.2)) := by
  induction values with
  | nil => rfl
  | cons item values ih =>
      rcases item with ⟨binder, value⟩
      have head := readback binder value (by simp)
      have tail := ih (fun b v member => readback b v (by simp [member]))
      simp only [Machine.collectResults, List.map_cons, List.mapM_cons, head, Bind.bind, Except.bind]
      change (do let rest ← Machine.collectResults locals (values.map Prod.fst)
                 pure (Datum.atom value :: rest)) = .ok (Datum.atom value :: values.map (fun item => Datum.atom item.2))
      rw [tail]
      rfl

theorem Transferred.collectResults (trace : Transferred registry fuel declare state binders sources values after)
    (distinct : (binders.map Binder.id).Nodup) :
    Machine.collectResults after.locals binders = .ok (values.map (fun item => Datum.atom item.2)) := by
  rw [← trace.output_binders]
  exact collectResults_readback values after.locals (trace.readback distinct)

theorem writes_reaches (assignments : List (Target Key × Value))
    (written : assignments.foldlM (fun state item => Machine.writeTarget backend registry limits state item.1 item.2) state = .ok after)
    (host : limits.hostContinuationLimit = none) (program : Program Key) (stack : List (Frame Key)) (entry : MachineState σ) :
    Reaches (Machine.step backend registry limits program)
      ⟨.writes assignments, stack, state, entry⟩ ⟨.value (.tuple []), stack, after, entry⟩ := by
  induction assignments generalizing state with
  | nil =>
      cases written
      exact .single (choice := 0) (by simp [Machine.step, Machine.transition, Machine.next, host])
  | cons item assignments ih =>
      cases first : Machine.writeTarget backend registry limits state item.1 item.2 with
      | error failure => simp [List.foldlM_cons, first] at written
      | ok middle =>
          have tail : assignments.foldlM (fun state item => Machine.writeTarget backend registry limits state item.1 item.2) middle = .ok after := by
            simpa only [List.foldlM_cons, first, Bind.bind, Except.bind] using written
          refine .next (choice := 0) ?_ (ih tail)
          simp [Machine.step, Machine.transition, Machine.next, first, host]

theorem resultTransfer_reaches
    (result : transferResults backend registry limits state binders sources = .ok after)
    (host : limits.hostContinuationLimit = none) (program : Program Key) (stack : List (Frame Key)) (entry : MachineState σ) :
    ∃ assignments, Machine.resultWrites (Key := Key) binders sources = .ok assignments ∧
      Reaches (Machine.step backend registry limits program)
        ⟨.writes assignments, stack, state, entry⟩ ⟨.value (.tuple []), stack, after, entry⟩ := by
  unfold transferResults at result
  cases written : Machine.resultWrites (Key := Key) binders sources with
  | error failure => simp [written] at result
  | ok assignments =>
      simp only [written] at result
      exact ⟨assignments, rfl, writes_reaches assignments result host program stack entry⟩

end Solidity.Execution.ParameterTransfers
