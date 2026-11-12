/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Vectors
import Solidity.Compatibility.Execution.State

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure
variable {σ : Type} {Keys : SType → Type} {Ref : Core.Ty → Type}
variable {backend : Backend σ Keys} {registry : Registry} {program : Program Keys}

def environmentValues : Core.Env types → List Value
  | .nil => []
  | .cons (type := type) value rest => scalar type value :: environmentValues rest

@[simp] theorem environmentPacket_append (first : Core.Env types) (second : Core.Env rest) :
    environmentPacket (first.append second) = environmentPacket first ++ environmentPacket second := by
  induction first <;> simp [Core.Env.append, environmentPacket, *]

@[simp] theorem environmentPacket_length (environment : Core.Env types) : (environmentPacket environment).length = types.length := by
  induction environment <;> simp [environmentPacket, *]

@[simp] theorem abiWords_length (environment : Core.Env types) : environment.abiWords.length = types.length := by
  induction environment <;> simp [Core.Env.abiWords, *]

theorem environmentPacket_atoms (environment : Core.Env types) :
    (environmentPacket environment).mapM Datum.asAtom = .ok (environmentValues environment) := by
  induction environment with
  | nil => rfl
  | cons head rest ih => simp [environmentPacket, environmentValues, Datum.asAtom, List.mapM_cons, ih, scalar]

theorem eventWord_scalar (type : Core.Ty) (value : type.Value) :
    Effects.eventWord (scalar type value) = .ok (type.abiWord value) := by
  cases type <;> rfl

theorem eventWords_environment (environment : Core.Env types) :
    Effects.eventWords (environmentValues environment) = .ok environment.abiWords := by
  induction environment with
  | nil => rfl
  | @cons types type head rest ih =>
      simp only [environmentValues, Effects.eventWords, List.mapM_cons, eventWord_scalar]
      change (do let rest ← Effects.eventWords (environmentValues rest); pure (type.abiWord head :: rest)) = _
      rw [ih]
      rfl

def eventState (state : MachineState σ) (topics : Core.Env topicTypes) (data : Core.Env dataTypes) : MachineState σ :=
  {state with heap := {state.heap with execution := {state.heap.execution with
    world := {state.heap.execution.world with logs := state.heap.execution.world.logs ++
      [⟨state.heap.execution.context.self, topics.abiWords, data.abiWords.flatMap Contract.Interaction.wordBytes⟩]}}}}

theorem emit_environment (state : MachineState σ) (topics : Core.Env topicTypes) (data : Core.Env dataTypes)
    (bounded : topicTypes.length ≤ 4) (writable : state.heap.execution.context.readOnly = false) :
    Effects.emitWords state.heap (environmentValues topics) (environmentValues data) =
      .ok (eventState state topics data).heap := by
  simp [Effects.emitWords, eventWords_environment, Effects.emit, abiWords_length,
    Nat.not_lt.mpr bounded, writable, eventState]

def appendExpressions : Core.Exprs Ref first → Core.Exprs Ref second → Core.Exprs Ref (first ++ second)
  | .nil, second => second
  | .cons value rest, second => .cons value (appendExpressions rest second)

@[simp] theorem expressions_append (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (first : Core.Exprs Ref types) (second : Core.Exprs Ref rest) :
    expressions resolve (appendExpressions first second) = expressions resolve first ++ expressions resolve second := by
  induction first <;> simp [appendExpressions, expressions, *]

@[simp] theorem expressions_length (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (values : Core.Exprs Ref types) : (expressions resolve values).length = types.length := by
  induction values <;> simp [expressions, *]

theorem appendExpressions_eval (read : ∀ {type}, Ref type → type.Value) (order : OperandOrder)
    (first : Core.Exprs Ref types) (second : Core.Exprs Ref rest) :
    (appendExpressions first second).eval read order = (do
      let first ← first.eval read order
      let second ← second.eval read order
      pure (first.append second)) := by
  induction first with
  | nil =>
      simp only [appendExpressions, Core.Exprs.eval, Core.Env.append, Bind.bind, Except.bind, Pure.pure, Except.pure]
      have eta (result : Core.Result (Core.Env rest)) : result = (do let value ← result; pure value) := by
        cases result <;> rfl
      exact eta (second.eval read order)
  | cons value rest ih =>
      simp only [appendExpressions, Core.Exprs.eval, ih]
      cases head : value.eval read order with
      | error bytes => rfl
      | ok value =>
          cases tail : rest.eval read order with
          | error bytes => rfl
          | ok values => cases second.eval read order <;> rfl

theorem apply_emit_environment (state : MachineState σ) (topics : Core.Env topicTypes) (data : Core.Env dataTypes)
    (bounded : topicTypes.length ≤ 4) (writable : state.heap.execution.context.readOnly = false)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.apply (.emit topicTypes.length) (environmentPacket (topics.append data)), stack, state, entry⟩
      ⟨.resume .next, stack, eventState state topics data, entry⟩ := by
  have take : (environmentPacket topics ++ environmentPacket data).take topicTypes.length = environmentPacket topics :=
    List.take_left' (environmentPacket_length topics)
  have drop : (environmentPacket topics ++ environmentPacket data).drop topicTypes.length = environmentPacket data :=
    List.drop_left' (environmentPacket_length topics)
  have length : ¬topicTypes.length + dataTypes.length < topicTypes.length := by omega
  apply next_reaches (choice := 0)
  simp [Machine.transition, Machine.apply, environmentPacket_append, length, take, drop,
    environmentPacket_atoms, emit_environment state topics data bounded writable, Machine.next]
  rfl

theorem emit_prefix (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop)
    (reads : ReadsCorrect (backend := backend) (registry := registry) (program := program) resolve read valid)
    (topics : Core.Exprs Ref topicTypes) (data : Core.Exprs Ref dataTypes)
    (state : MachineState σ) (accepted : valid state.external state.locals)
    (topicValues : Core.Env topicTypes) (dataValues : Core.Env dataTypes)
    (readTopics : topics.eval (read state.external state.locals) .leftFirst = .ok topicValues)
    (readData : data.eval (read state.external state.locals) .leftFirst = .ok dataValues)
    (bounded : topicTypes.length ≤ 4) (writable : state.heap.execution.context.readOnly = false)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.exec (.emit (expressions resolve topics) (expressions resolve data)), stack, state, entry⟩
      ⟨.resume .next, stack, eventState state topicValues dataValues, entry⟩ := by
  have completed := expressions_collect resolve read valid reads (appendExpressions topics data) state accepted 0 [] (.emit topicTypes.length)
  have calculated : (appendExpressions topics data).eval (read state.external state.locals) .leftFirst =
      .ok (topicValues.append dataValues) := by
    rw [appendExpressions_eval, readTopics, readData]
    rfl
  simp only [calculated, Effects.liftCore, Except.map] at completed
  have start : Reaches (transition backend registry program)
      ⟨.exec (.emit (expressions resolve topics) (expressions resolve data)), stack, state, entry⟩
      ⟨.collect (indexed (expressions resolve (appendExpressions topics data)) 0) [] (.emit topicTypes.length), stack, state, entry⟩ := by
    apply next_reaches (choice := 0)
    simp [Machine.transition, Machine.gather, Machine.next, indexed, expressions_append, expressions_length]
  apply start.trans
  have packet := completed stack entry
  simp only [List.append_nil] at packet
  apply packet.trans
  let config : Config σ Keys := ⟨.value (.tuple []), stack, state, entry⟩
  have ordered := collect_empty backend registry program config
    (indexed (environmentPacket (topicValues.append dataValues)) 0).reverse (.emit topicTypes.length)
  simp only [indexed, Machine.ordered_reverse_zipIdx] at ordered
  exact ordered.trans (apply_emit_environment state topicValues dataValues bounded writable stack entry)

theorem emit_failure (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop)
    (reads : ReadsCorrect (backend := backend) (registry := registry) (program := program) resolve read valid)
    (topics : Core.Exprs Ref topicTypes) (data : Core.Exprs Ref dataTypes)
    (state : MachineState σ) (accepted : valid state.external state.locals) (bytes : List UInt8)
    (calculated : (appendExpressions topics data).eval (read state.external state.locals) .leftFirst = .error bytes)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Executes (transition backend registry program)
      ⟨.exec (.emit (expressions resolve topics) (expressions resolve data)), stack, state, entry⟩
      (fail entry (Effects.failureOfBytes bytes)) := by
  have completed := expressions_collect resolve read valid reads (appendExpressions topics data) state accepted 0 [] (.emit topicTypes.length)
  simp only [calculated, Effects.liftCore, Except.map] at completed
  have start : Reaches (transition backend registry program)
      ⟨.exec (.emit (expressions resolve topics) (expressions resolve data)), stack, state, entry⟩
      ⟨.collect (indexed (expressions resolve (appendExpressions topics data)) 0) [] (.emit topicTypes.length), stack, state, entry⟩ := by
    apply next_reaches (choice := 0)
    simp [Machine.transition, Machine.gather, Machine.next, indexed, expressions_append, expressions_length]
  exact start.executes (completed stack entry)

end Solidity.Execution.Compatibility
