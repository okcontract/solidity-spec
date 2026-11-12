/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Compatibility.Execution.Expressions
import Solidity.Compatibility.Execution.Observations
import Solidity.Core.Execution.OrderingLaws

namespace Solidity.Execution.Compatibility
open Core Static
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

variable {σ : Type} {Keys : SType → Type} {Ref : Core.Ty → Type}
variable {backend : Backend σ Keys} {registry : Registry} {program : Program Keys}

def indexed (values : List α) (start : Nat := 0) : List (Nat × α) :=
  (values.zipIdx start).map (fun (value, index) => (index, value))

def CollectedResult (backend : Backend σ Keys) (registry : Registry) (program : Program Keys)
    (state : MachineState σ) (pending : List (Nat × Execution.Expr Keys))
    (already : List (Nat × Datum)) (finish : Completion) (start : Nat) : Aggregates.Result Packet → Prop
  | .ok values => ∀ stack entry, Reaches (transition backend registry program)
      ⟨.collect pending already finish, stack, state, entry⟩
      ⟨.collect [] ((indexed values start).reverse ++ already) finish, stack, state, entry⟩
  | .error failure => ∀ stack entry, Executes (transition backend registry program)
      ⟨.collect pending already finish, stack, state, entry⟩ (fail entry failure)

theorem expressions_collect (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop)
    (reads : ReadsCorrect (backend := backend) (registry := registry) (program := program) resolve read valid)
    (values : Core.Exprs Ref types) :
    ∀ state, valid state.external state.locals → ∀ start already finish,
      CollectedResult backend registry program state (indexed (expressions resolve values) start) already finish start
        ((Effects.liftCore (values.eval (read state.external state.locals) .leftFirst)).map environmentPacket) := by
  induction values with
  | nil =>
      intro state _ start already finish stack entry
      exact .refl _
  | @cons type types value rest ih =>
      intro state accepted start already finish
      have evaluated := expression_left resolve read valid reads value state accepted
      cases head : value.eval (read state.external state.locals) .leftFirst with
      | error bytes =>
          simp only [head, coreResult_error] at evaluated
          simp only [Core.Exprs.eval, head, Bind.bind, Except.bind, Effects.liftCore, Except.map]
          intro stack entry
          exact collect_failure state (expression resolve value) (Effects.failureOfBytes bytes) evaluated
            start (indexed (expressions resolve rest) (start+1)) already finish stack entry
      | ok answer =>
          simp only [head, coreResult_ok] at evaluated
          have tail := ih state accepted (start+1) ((start, .atom (scalar type answer)) :: already) finish
          cases last : rest.eval (read state.external state.locals) .leftFirst with
          | error bytes =>
              simp only [last, Effects.liftCore, Except.map] at tail
              simp only [Core.Exprs.eval, head, last, Bind.bind, Except.bind, Effects.liftCore, Except.map]
              intro stack entry
              exact (collect_success state (expression resolve value) (.atom (scalar type answer)) evaluated
                start (indexed (expressions resolve rest) (start+1)) already finish stack entry).executes (tail stack entry)
          | ok answers =>
              simp only [last, Effects.liftCore, Except.map] at tail
              simp only [Core.Exprs.eval, head, last, Bind.bind, Except.bind, Pure.pure, Except.pure,
                Effects.liftCore, Except.map]
              intro stack entry
              have completed := (collect_success state (expression resolve value) (.atom (scalar type answer)) evaluated
                start (indexed (expressions resolve rest) (start+1)) already finish stack entry).trans (tail stack entry)
              simpa only [expressions, environmentPacket, indexed, List.zipIdx_cons,
                List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, scalar] using completed

theorem expressions_tuple (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop)
    (reads : ReadsCorrect (backend := backend) (registry := registry) (program := program) resolve read valid)
    (values : Core.Exprs Ref types) (state : MachineState σ) (accepted : valid state.external state.locals) :
    PureResult backend registry program state (.tuple (expressions resolve values))
      ((Effects.liftCore (values.eval (read state.external state.locals) .leftFirst)).map
        (fun values => Datum.tuple (environmentPacket values))) := by
  have completed := expressions_collect resolve read valid reads values state accepted 0 [] .tuple
  cases calculated : values.eval (read state.external state.locals) .leftFirst with
  | error bytes =>
      simp only [calculated, Effects.liftCore, Except.map] at completed
      intro stack entry
      have start : Reaches (transition backend registry program)
          ⟨.eval (.tuple (expressions resolve values)), stack, state, entry⟩
          ⟨.collect (indexed (expressions resolve values) 0) [] .tuple, stack, state, entry⟩ := next_reaches (choice := 0) rfl
      exact start.executes (completed stack entry)
  | ok answers =>
      simp only [calculated, Effects.liftCore, Except.map] at completed
      intro stack entry
      have start : Reaches (transition backend registry program)
          ⟨.eval (.tuple (expressions resolve values)), stack, state, entry⟩
          ⟨.collect (indexed (expressions resolve values) 0) [] .tuple, stack, state, entry⟩ := next_reaches (choice := 0) rfl
      apply start.trans
      have packet := completed stack entry
      simp only [List.append_nil] at packet
      apply packet.trans
      let config : Config σ Keys := ⟨.value (.tuple []), stack, state, entry⟩
      have ordered := collect_empty backend registry program config (indexed (environmentPacket answers) 0).reverse .tuple
      simp only [indexed, Machine.ordered_reverse_zipIdx] at ordered
      apply ordered.trans
      exact next_reaches (choice := 0) rfl

theorem expressions_return_prefix (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop)
    (reads : ReadsCorrect (backend := backend) (registry := registry) (program := program) resolve read valid)
    (values : Core.Exprs Ref types) (state : MachineState σ) (accepted : valid state.external state.locals)
    (answers : Core.Env types) (calculated : values.eval (read state.external state.locals) .leftFirst = .ok answers)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.exec (.return_ (some (.tuple (expressions resolve values)))), stack, state, entry⟩
      ⟨.resume (.return_ (some (.tuple (environmentPacket answers)))), stack, state, entry⟩ := by
  have evaluated := expressions_tuple resolve read valid reads values state accepted
  simp only [calculated, Effects.liftCore, Except.map] at evaluated
  have start : Reaches (transition backend registry program)
      ⟨.exec (.return_ (some (.tuple (expressions resolve values)))), stack, state, entry⟩
      ⟨.eval (.tuple (expressions resolve values)), .returnValue :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  apply start.trans ((evaluated (.returnValue :: stack) entry).trans ?_)
  exact next_reaches (choice := 0) rfl

theorem expressions_return_failure (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop)
    (reads : ReadsCorrect (backend := backend) (registry := registry) (program := program) resolve read valid)
    (values : Core.Exprs Ref types) (state : MachineState σ) (accepted : valid state.external state.locals)
    (bytes : List UInt8) (calculated : values.eval (read state.external state.locals) .leftFirst = .error bytes)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Executes (transition backend registry program)
      ⟨.exec (.return_ (some (.tuple (expressions resolve values)))), stack, state, entry⟩
      (fail entry (Effects.failureOfBytes bytes)) := by
  have evaluated := expressions_tuple resolve read valid reads values state accepted
  simp only [calculated, Effects.liftCore, Except.map] at evaluated
  have start : Reaches (transition backend registry program)
      ⟨.exec (.return_ (some (.tuple (expressions resolve values)))), stack, state, entry⟩
      ⟨.eval (.tuple (expressions resolve values)), .returnValue :: stack, state, entry⟩ := next_reaches (choice := 0) rfl
  exact start.executes (evaluated (.returnValue :: stack) entry)

theorem expressions_call_prefix (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop)
    (reads : ReadsCorrect (backend := backend) (registry := registry) (program := program) resolve read valid)
    (values : Core.Exprs Ref types) (state : MachineState σ) (accepted : valid state.external state.locals)
    (signature : FunctionSignature) (function : Value) (answers : Core.Env types)
    (calculated : values.eval (read state.external state.locals) .leftFirst = .ok answers)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Reaches (transition backend registry program)
      ⟨.eval (.call signature (.literal function) (expressions resolve values)), stack, state, entry⟩
      ⟨.apply (.call signature) (.atom function :: environmentPacket answers), stack, state, entry⟩ := by
  have completed := expressions_collect resolve read valid reads values state accepted 1 [(0, .atom function)] (.call signature)
  simp only [calculated, Effects.liftCore, Except.map] at completed
  have start : Reaches (transition backend registry program)
      ⟨.eval (.call signature (.literal function) (expressions resolve values)), stack, state, entry⟩
      ⟨.collect ((0, .literal function) :: indexed (expressions resolve values) 1) [] (.call signature), stack, state, entry⟩ :=
    next_reaches (choice := 0) rfl
  apply start.trans
  apply (collect_success state (.literal function) (.atom function) (pure_literal state function)
    0 (indexed (expressions resolve values) 1) [] (.call signature) stack entry).trans
  apply (completed stack entry).trans
  let config : Config σ Keys := ⟨.value (.tuple []), stack, state, entry⟩
  have ordered := collect_empty backend registry program config
    ((indexed (environmentPacket answers) 1).reverse ++ [(0, .atom function)]) (.call signature)
  have packetOrder : Machine.ordered ((indexed (environmentPacket answers) 1).reverse ++ [(0, .atom function)]) =
      .atom function :: environmentPacket answers := by
    simpa only [indexed, List.zipIdx_cons, List.map_cons, List.reverse_cons] using
      Machine.ordered_reverse_zipIdx (.atom function :: environmentPacket answers) 0
  simpa only [packetOrder] using ordered

theorem expressions_call_failure (resolve : ∀ {type}, Ref type → Execution.Expr Keys)
    (read : σ → Locals → ∀ {type}, Ref type → type.Value) (valid : σ → Locals → Prop)
    (reads : ReadsCorrect (backend := backend) (registry := registry) (program := program) resolve read valid)
    (values : Core.Exprs Ref types) (state : MachineState σ) (accepted : valid state.external state.locals)
    (signature : FunctionSignature) (function : Value) (bytes : List UInt8)
    (calculated : values.eval (read state.external state.locals) .leftFirst = .error bytes)
    (stack : List (Frame Keys)) (entry : MachineState σ) :
    Executes (transition backend registry program)
      ⟨.eval (.call signature (.literal function) (expressions resolve values)), stack, state, entry⟩
      (fail entry (Effects.failureOfBytes bytes)) := by
  have completed := expressions_collect resolve read valid reads values state accepted 1 [(0, .atom function)] (.call signature)
  simp only [calculated, Effects.liftCore, Except.map] at completed
  have start : Reaches (transition backend registry program)
      ⟨.eval (.call signature (.literal function) (expressions resolve values)), stack, state, entry⟩
      ⟨.collect ((0, .literal function) :: indexed (expressions resolve values) 1) [] (.call signature), stack, state, entry⟩ :=
    next_reaches (choice := 0) rfl
  apply start.executes
  exact (collect_success state (.literal function) (.atom function) (pure_literal state function)
    0 (indexed (expressions resolve values) 1) [] (.call signature) stack entry).executes (completed stack entry)

end Solidity.Execution.Compatibility
