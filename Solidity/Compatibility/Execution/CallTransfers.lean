/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.State

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

theorem except_ok_bind (value : α) (next : α → Aggregates.Result β) :
    (Except.ok value >>= next) = next value := rfl
theorem except_bind_assoc (value : Aggregates.Result α)
    (next : α → Aggregates.Result β) (last : β → Aggregates.Result γ) :
    ((value >>= next) >>= last) = (value >>= fun value => next value >>= last) := by
  cases value <;> rfl

/-- Observable legacy cells plus the freshness needed for future lets/result
bindings. Named return cells occupy odd IDs and may coexist with this frame. -/
structure FrameEnv (locals : Locals) (environment : Core.Env types) : Prop where
  represented : Represents locals environment
  fresh : ∀ index, types.length ≤ index → locals.find (2 * index) = none
  nonempty : locals ≠ []

theorem scope_find_append (before after : Scope) (id : Nat) :
    Scope.find (before ++ after) id = (Scope.find before id).orElse (fun _ => Scope.find after id) := by
  induction before with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, cell⟩
      by_cases same : key = id <;> simp [Scope.find, same, ih]

theorem localScope_reverse_find (environment : Core.Env types) (id : Nat) :
    Scope.find (localScope environment).reverse id = Scope.find (localScope environment) id := by
  induction environment with
  | nil => rfl
  | @cons types type value rest ih =>
      simp only [localScope, List.reverse_cons, scope_find_append, ih]
      by_cases same : 2 * types.length = id
      · subst id
        rw [localScope_outside rest (2 * types.length) (Nat.le_refl _)]
        simp [Scope.find]
      · simp [Scope.find, same]

theorem localEnv_frame (environment : Core.Env types) : FrameEnv (localEnv environment) environment where
  represented := localEnv_represents environment
  fresh := fun index bound => by
    simp only [localEnv, Locals.find, localScope_outside environment (2 * index)
      (Nat.mul_le_mul_left 2 bound), Option.orElse_none]
  nonempty := by simp [localEnv]

theorem reversedLocalEnv_frame (environment : Core.Env types) :
    FrameEnv [(localScope environment).reverse] environment where
  represented := fun var => by
    rw [Locals.read_eq_of_find_eq (show
      Locals.find [(localScope environment).reverse] (localId var) =
        (localEnv environment).find (localId var) by
          simp only [Locals.find, localEnv, localScope_reverse_find])]
    exact localEnv_read environment var
  fresh := fun index bound => by
    simp only [Locals.find, localScope_reverse_find, localScope_outside environment (2 * index)
      (Nat.mul_le_mul_left 2 bound), Option.orElse_none]
  nonempty := by simp

theorem declare_write_scalar (backend : Backend σ Keys) (registry : Registry)
    (state : MachineState σ) (scope : Scope) (outer : Locals)
    (shape : state.locals = scope :: outer) (id : Nat) (type : Core.Ty) (value : type.Value)
    (fresh : state.locals.find id = none) :
    (do
      let next ← Machine.declareUnset state {id, type := SType.ofCore type}
      Machine.writeTarget backend registry legacyLimits next
        (.captured (.local id (SType.ofCore type))) (scalar type value)) =
      .ok {state with locals := ((id, ⟨SType.ofCore type, some (scalarValue type value)⟩) :: scope) :: outer} := by
  have declared : state.locals.declare {id, type := SType.ofCore type} =
      .ok (((id, ⟨SType.ofCore type, none⟩) :: scope) :: outer) := by
    simp only [Locals.declare, fresh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [shape]
  have typed := Locals.declare_type declared
  have written : Locals.write (((id, ⟨SType.ofCore type, none⟩) :: scope) :: outer) id
      (SType.ofCore type) (scalar type value) =
      .ok (((id, ⟨SType.ofCore type, some (scalarValue type value)⟩) :: scope) :: outer) := by
    simp [Locals.write, Locals.find, Scope.find, Locals.replace, Scope.replace, scalar]
  simp only [Machine.declareUnset, declared, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact write_local backend registry {state with
    locals := ((id, ⟨SType.ofCore type, none⟩) :: scope) :: outer} id type value typed written

/-- Real parameter declaration/write steps preserve external state, heap,
mode and materialization allowance exactly. Only their local scope changes. -/
theorem bindArguments_parameterScope (backend : Backend σ Keys) (registry : Registry)
    (environment : Core.Env types) (state : MachineState σ) (scope : Scope) (outer : Locals)
    (shape : state.locals = scope :: outer)
    (fresh : ∀ index, index < types.length → state.locals.find (2 * index) = none) :
    Machine.bindArguments backend registry legacyLimits state (parameterBinders types)
      (environmentPacket environment) =
      .ok {state with locals := ((localScope environment).reverse ++ scope) :: outer} := by
  induction environment generalizing state scope outer with
  | nil =>
      simp only [Machine.bindArguments, parameterBinders, environmentPacket, localScope,
        List.reverse_nil, List.nil_append, Except.ok.injEq]
      rw [← shape]
  | @cons types type value rest ih =>
      let next : MachineState σ := {state with
        locals := ((2 * types.length, ⟨SType.ofCore type, some (scalarValue type value)⟩) :: scope) :: outer}
      have first := declare_write_scalar backend registry state scope outer shape (2 * types.length)
        type value (fresh types.length (by simp))
      simp only [scalar] at first
      have nextFresh : ∀ index, index < types.length → next.locals.find (2 * index) = none := by
        intro index bound
        have different : 2 * types.length ≠ 2 * index := by omega
        simp only [next, Locals.find, Scope.find, different, ↓reduceIte]
        simpa only [shape, Locals.find] using fresh index (by simp; omega)
      have remaining := ih next
        ((2 * types.length, ⟨SType.ofCore type, some (scalarValue type value)⟩) :: scope) outer rfl nextFresh
      simp only [Machine.bindArguments, parameterBinders, environmentPacket, Datum.asAtom, binder, except_ok_bind]
      rw [← except_bind_assoc, first, except_ok_bind]
      rw [remaining]
      simp [next, localScope, List.reverse_cons, List.append_assoc]

theorem bindArguments_packet (backend : Backend σ Keys) (registry : Registry)
    (environment : Core.Env types) (state : MachineState σ) :
    Machine.bindArguments backend registry legacyLimits {state with locals := Locals.empty}
      (parameterBinders types) (environmentPacket environment) =
      .ok {state with locals := [(localScope environment).reverse]} := by
  simpa only [List.append_nil] using bindArguments_parameterScope backend registry environment
    {state with locals := Locals.empty} [] [] rfl (by intro index bound; rfl)

theorem FrameEnv.prepend (frame : FrameEnv (scope :: outer) (environment : Core.Env types))
    (value : type.Value) :
    FrameEnv (((2 * types.length, ⟨SType.ofCore type, some (scalarValue type value)⟩) :: scope) :: outer)
      (Core.Env.cons value environment) where
  represented := by
    intro observedType var
    cases var with
    | here => simp [Locals.read, Locals.find, Scope.find, localId, localIndex, Core.Env.get]
    | there var =>
        have different : 2 * types.length ≠ localId var := Nat.ne_of_gt (localId_lt var)
        rw [Locals.read_eq_of_find_eq (show
          Locals.find (((2 * types.length, ⟨SType.ofCore type, some (scalarValue type value)⟩) :: scope) :: outer)
            (localId (.there (other := type) var)) = Locals.find (scope :: outer) (localId var) by
              simp only [Locals.find, Scope.find, localId_there, different, ↓reduceIte])]
        exact frame.represented var
  fresh := by
    intro index bound
    have different : 2 * types.length ≠ 2 * index := by simp only [List.length_cons] at bound; omega
    simp only [Locals.find, Scope.find, different, ↓reduceIte]
    exact frame.fresh index (by simp only [List.length_cons] at bound; omega)
  nonempty := by simp

theorem FrameEnv.declare_odd {index : Nat} {declaration : Binder} {value : Option Value}
    {locals after : Locals} (frame : FrameEnv locals (environment : Core.Env types))
    (identifier : declaration.id = 2 * index + 1)
    (declared : locals.declare declaration value = .ok after) : FrameEnv after environment where
  represented := Represents.declare_odd frame.represented index identifier declared
  fresh := by
    intro next bound
    have different : declaration.id ≠ 2 * next := by
      intro same
      have parity := congrArg (fun value : Nat => value % 2) same
      simp [identifier, Nat.add_mod] at parity
    rw [Locals.declare_frames_other different declared]
    exact frame.fresh next bound
  nonempty := by
    obtain ⟨scope, outer, cell, _, equal, _⟩ := Locals.declare_shape declared
    rw [equal]
    simp

theorem declareValues_all_some (backend : Backend σ Keys) (registry : Registry)
    (limits : Limits) (binders : List Binder) (state : MachineState σ) (values : Packet) :
    Machine.declareValues backend registry limits state (binders.map some) values =
      Machine.bindArguments backend registry limits state binders values := by
  induction binders generalizing state values with
  | nil => cases values <;> rfl
  | cons binder binders ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [List.map_cons, Machine.declareValues, Machine.bindArguments, ih]

def scalarZero : (type : Core.Ty) → type.Value
  | .uint _ | .sint _ | .fixedBytes _ | .address => 0
  | .bool => false

theorem defaultLocal_scalar (registry : Registry) (state : MachineState σ) (type : Core.Ty) :
    Effects.defaultLocal registry 1 state.materializationRemaining state.heap (SType.ofCore type) =
      .ok (some (scalar type (scalarZero type)), state.heap, state.materializationRemaining) := by
  cases type <;> rfl

theorem declareReturn_scalar (registry : Registry) (state : MachineState σ)
    (scope : Scope) (outer : Locals) (shape : state.locals = scope :: outer)
    (id : Nat) (type : Core.Ty) (fresh : state.locals.find id = none) :
    Machine.declareReturn registry legacyLimits state {id, type := SType.ofCore type} =
      .ok {state with locals :=
        ((id, ⟨SType.ofCore type, some (scalarValue type (scalarZero type))⟩) :: scope) :: outer} := by
  have declared : state.locals.declare {id, type := SType.ofCore type}
      (some (scalar type (scalarZero type))) =
      .ok (((id, ⟨SType.ofCore type, some (scalarValue type (scalarZero type))⟩) :: scope) :: outer) := by
    simp only [Locals.declare, fresh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      scalar, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [shape]
    simp
  have default := defaultLocal_scalar registry state type
  unfold Machine.declareReturn
  cases type <;>
    simp only [SType.ofCore] at default declared <;>
    simp only [Effects.declareReturn, Effects.declareLocal, SType.ofCore, legacyLimits] <;>
    rw [default] <;>
    simp only [except_ok_bind] <;>
    rw [declared] <;> rfl

def returnScope (base : Nat) : (types : List Core.Ty) → Scope
  | [] => []
  | type :: types =>
      (2 * base + 1, ⟨SType.ofCore type, some (scalarValue type (scalarZero type))⟩) :: returnScope (base + 1) types

theorem declareReturn_scope (registry : Registry) (types : List Core.Ty) (base : Nat)
    (state : MachineState σ) (scope : Scope) (outer : Locals) (shape : state.locals = scope :: outer)
    (fresh : ∀ index, base ≤ index → index < base + types.length → state.locals.find (2 * index + 1) = none) :
    (returnBinders base types).foldlM (Machine.declareReturn registry legacyLimits) state =
      .ok {state with locals := ((returnScope base types).reverse ++ scope) :: outer} := by
  induction types generalizing base state scope outer with
  | nil =>
      simp only [returnBinders, List.foldlM_nil, returnScope, List.reverse_nil, List.nil_append,
        Pure.pure, Except.pure, Except.ok.injEq]
      rw [← shape]
  | cons type types ih =>
      let next : MachineState σ := {state with locals :=
        ((2 * base + 1, ⟨SType.ofCore type, some (scalarValue type (scalarZero type))⟩) :: scope) :: outer}
      have first := declareReturn_scalar registry state scope outer shape (2 * base + 1) type
        (fresh base (Nat.le_refl _) (by simp))
      have nextFresh : ∀ index, base + 1 ≤ index → index < base + 1 + types.length →
          next.locals.find (2 * index + 1) = none := by
        intro index lower upper
        have different : 2 * base + 1 ≠ 2 * index + 1 := by omega
        simp only [next, Locals.find, Scope.find, different, ↓reduceIte]
        simpa only [shape, Locals.find] using fresh index (by omega) (by simp; omega)
      have remaining := ih (base + 1) next
        ((2 * base + 1, ⟨SType.ofCore type, some (scalarValue type (scalarZero type))⟩) :: scope) outer rfl nextFresh
      simp only [returnBinders, List.foldlM_cons]
      rw [first]
      simp only [except_ok_bind]
      rw [remaining]
      simp [next, returnScope, List.reverse_cons, List.append_assoc]

def ReturnTypes (locals : Locals) (base : Nat) : List Core.Ty → Prop
  | [] => True
  | type :: types => locals.typeOf (2 * base + 1) = .ok (SType.ofCore type) ∧
      ReturnTypes locals (base + 1) types

def ReturnValues (locals : Locals) (base : Nat) : Core.Env types → Prop
  | .nil => True
  | .cons (type := type) value rest =>
      locals.read (2 * base + 1) (SType.ofCore type) = .ok (scalar type value) ∧
      ReturnValues locals (base + 1) rest

theorem ReturnValues.types {types : List Core.Ty} {locals : Locals} {base : Nat}
    {environment : Core.Env types} (represented : ReturnValues locals base environment) :
    ReturnTypes locals base types := by
  induction environment generalizing base with
  | nil => trivial
  | cons value rest ih =>
      exact ⟨typeOf_of_read _ _ _ represented.1, ih represented.2⟩

theorem ReturnValues.collect {types : List Core.Ty} {locals : Locals} {base : Nat}
    {environment : Core.Env types} (represented : ReturnValues locals base environment) :
    Machine.collectResults locals (returnBinders base types) = .ok (environmentPacket environment) := by
  induction environment generalizing base with
  | nil => rfl
  | @cons types type value rest ih =>
      have tail := ih represented.2
      simp only [Machine.collectResults, Bind.bind, Except.bind, Pure.pure, Except.pure] at tail
      simp [Machine.collectResults, returnBinders, represented.1, tail, environmentPacket, scalar]

private theorem returnScope_below (types : List Core.Ty) (base id : Nat)
    (below : id < 2 * base + 1) : Scope.find (returnScope base types) id = none := by
  induction types generalizing base with
  | nil => rfl
  | cons type types ih =>
      have different : 2 * base + 1 ≠ id := by omega
      simp only [returnScope, Scope.find, different, ↓reduceIte]
      exact ih (base + 1) (by omega)

theorem returnScope_reverse_find (types : List Core.Ty) (base id : Nat) :
    Scope.find (returnScope base types).reverse id = Scope.find (returnScope base types) id := by
  induction types generalizing base with
  | nil => rfl
  | cons type types ih =>
      simp only [returnScope, List.reverse_cons, scope_find_append, ih]
      by_cases same : 2 * base + 1 = id
      · subst id
        rw [returnScope_below types (base + 1) (2 * base + 1) (by omega)]
        simp [Scope.find]
      · simp [Scope.find, same]

theorem returnScope_even (types : List Core.Ty) (base index : Nat) :
    Scope.find (returnScope base types) (2 * index) = none := by
  induction types generalizing base with
  | nil => rfl
  | cons type types ih =>
      have different : 2 * base + 1 ≠ 2 * index := by omega
      simp only [returnScope, Scope.find, different, ↓reduceIte]
      exact ih (base + 1)

theorem returnScope_types (types : List Core.Ty) (base : Nat) (scope : Scope) (outer : Locals) :
    ReturnTypes (((returnScope base types).reverse ++ scope) :: outer) base types := by
  induction types generalizing base scope with
  | nil => trivial
  | cons type types ih =>
      refine ⟨?_, ?_⟩
      · have absent := returnScope_below types (base + 1) (2 * base + 1) (by omega)
        simp [Locals.typeOf, Locals.find, scope_find_append, returnScope_reverse_find,
          returnScope, Scope.find, absent]
      · simpa only [returnScope, List.reverse_cons, List.append_assoc, List.singleton_append] using
          ih (base + 1) ((2 * base + 1,
            ⟨SType.ofCore type, some (scalarValue type (scalarZero type))⟩) :: scope)

theorem returnScope_frame (frame : FrameEnv (scope :: outer) (environment : Core.Env types))
    (returns : List Core.Ty) (base : Nat) :
    FrameEnv (((returnScope base returns).reverse ++ scope) :: outer) environment where
  represented := by
    intro type var
    have even : (localId var) = 2 * localIndex var := rfl
    rw [Locals.read_eq_of_find_eq (show
      Locals.find (((returnScope base returns).reverse ++ scope) :: outer) (localId var) =
        Locals.find (scope :: outer) (localId var) by
          simp only [Locals.find, scope_find_append, returnScope_reverse_find, even,
            returnScope_even, Option.orElse_none])]
    exact frame.represented var
  fresh := by
    intro index bound
    simpa only [Locals.find, scope_find_append, returnScope_reverse_find, returnScope_even,
      Option.orElse_none] using frame.fresh index bound
  nonempty := by simp

theorem initializeReturn_packet (registry : Registry) (state : MachineState σ)
    (environment : Core.Env types) (returns : List Core.Ty) :
    let parameters := {state with locals := [(localScope environment).reverse]}
    let entered := {state with locals := [(returnScope 0 returns).reverse ++ (localScope environment).reverse]}
    (returnBinders 0 returns).foldlM (Machine.declareReturn registry legacyLimits) parameters = .ok entered ∧
      FrameEnv entered.locals environment ∧ ReturnTypes entered.locals 0 returns := by
  dsimp only
  refine ⟨?_, returnScope_frame (reversedLocalEnv_frame environment) returns 0, returnScope_types returns 0 _ []⟩
  exact declareReturn_scope registry returns 0 {state with locals := [(localScope environment).reverse]}
    (localScope environment).reverse [] rfl (by
      intro index lower upper
      simp only [Locals.find, localScope_reverse_find, localScope_odd, Option.orElse_none])

end Solidity.Execution.Compatibility
