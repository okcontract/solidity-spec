/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Configuration
import Solidity.Core.Execution.Safety.SourceScopes
import Solidity.Core.Execution.Safety.ProfileLaws

namespace Solidity.Execution.Safety.SourceControl
open Static Aggregates Admission
open SourceTyping (bind_checked checkExpression_scopes)
attribute [local simp] Bind.bind Except.bind Pure.pure Except.pure

structure ShapeFlow (environment : Environment) (flow : Admission.Flow) : Prop where
  dead : Profile.scopesEnvironment flow.dead.scopes = environment
  normal : ∀ context ∈ flow.normal, Profile.scopesEnvironment context.scopes = environment
  breaks : ∀ context ∈ flow.breaks, Profile.scopesEnvironment context.scopes = environment
  continues : ∀ context ∈ flow.continues, Profile.scopesEnvironment context.scopes = environment

private abbrev Env (context : Admission.Context) : Environment := Profile.scopesEnvironment context.scopes

theorem next_shape (context : Admission.Context) : ShapeFlow (Env context) (Flow.next context) := by
  constructor <;> simp [Flow.next]

theorem halt_shape (context : Admission.Context) : ShapeFlow (Env context) (Flow.halt context) := by
  constructor <;> simp [Flow.halt]

theorem enter_environment (context : Admission.Context) : Env context.enter = [] :: Env context := rfl

theorem relax_environment (context : Admission.Context) : Env context.relax = Env context := rfl

theorem meet_environment (left right : Admission.Context) : Env (left.meet right) = Env left := rfl

theorem leave_environment (context : Admission.Context) : Env context.leave = (Env context).tail := by
  cases context with
  | mk scopes assigned unresolved independent => cases scopes <;> rfl

theorem mergeNormal_environment
    (first : ∀ context ∈ left, Env context = environment)
    (second : ∀ context ∈ right, Env context = environment) :
    ∀ context ∈ mergeNormal left right, Env context = environment := by
  cases left <;> cases right <;> simp_all [mergeNormal, Env, Context.meet]

private theorem meet_fold_environment
    {contexts : List Admission.Context} {incoming : Option Admission.Context}
    (members : ∀ context ∈ contexts, Env context = environment)
    (initial : ∀ context ∈ incoming, Env context = environment) :
    ∀ context ∈ contexts.foldl (fun state context => mergeNormal state (some context)) incoming,
      Env context = environment := by
  induction contexts generalizing incoming with
  | nil => exact initial
  | cons head tail induction =>
      apply induction
      · intro context member; exact members context (by simp [member])
      · exact mergeNormal_environment initial (by simpa using members head (by simp))

theorem meetContexts_environment (members : ∀ context ∈ contexts, Env context = environment) :
    ∀ context ∈ meetContexts contexts, Env context = environment :=
  meet_fold_environment members (by simp)

theorem getD_environment {incoming : Option Admission.Context}
    (members : ∀ context ∈ incoming, Env context = environment)
    (fallback : Env alternative = environment) : Env (incoming.getD alternative) = environment := by
  cases incoming <;> simp_all

theorem leave_shape (shaped : ShapeFlow environment flow) : ShapeFlow environment.tail flow.leave := by
  constructor
  · exact (leave_environment flow.dead).trans (congrArg List.tail shaped.dead)
  · intro context member
    cases normal : flow.normal with
    | none => simp [Flow.leave, normal] at member
    | some original =>
        have equal : original.leave = context := by simpa [Flow.leave, normal] using member
        subst context
        exact (leave_environment original).trans (congrArg List.tail (shaped.normal original (by simp [normal])))
  · intro context member
    obtain ⟨original, contained, rfl⟩ := List.mem_map.mp member
    exact (leave_environment original).trans (congrArg List.tail (shaped.breaks original contained))
  · intro context member
    obtain ⟨original, contained, rfl⟩ := List.mem_map.mp member
    exact (leave_environment original).trans (congrArg List.tail (shaped.continues original contained))

theorem declare_environment
    (checked : context.declare binder initialized = .ok after) :
    Env after = Environment.declare (Env context) binder := by
  unfold Admission.Context.declare at checked
  obtain ⟨allowed, permission, rest⟩ := bind_checked checked
  cases allowed
  cases scopes : context.scopes with
  | nil => simp [scopes] at rest
  | cons head tail =>
      simp only [scopes] at rest
      cases initialized with
      | false =>
          have equal : {context with scopes := (binder :: head) :: tail} = after := by simpa using rest
          rw [← equal]
          simp [Environment.declare, Env, Profile.scopesEnvironment, scopes]
      | true =>
          have equal : ({context with scopes := (binder :: head) :: tail}.mark binder.id) = after := by
            simpa using rest
          rw [← equal]
          simp [Context.mark, Environment.declare, Env, Profile.scopesEnvironment, scopes]

theorem default_declaration_checked
    (checked : declareBinders (Key := EmptyKey) registry fuel context [some binder] none = .ok after) :
    checkType registry fuel binder.type = .ok () ∧
      (match binder.type with | .mapping _ _ => false | _ => true) = true ∧
      context.declare binder (!referenceUnset binder.type) = .ok after := by
  simp only [declareBinders, List.all_cons, List.all_nil, List.foldlM] at checked
  obtain ⟨_, _, checked⟩ := bind_checked checked
  obtain ⟨declared, action, checked⟩ := bind_checked checked
  have equal : declared = after := Except.ok.inj checked
  subst after
  obtain ⟨done, typeChecked, rest⟩ := bind_checked action
  cases done
  obtain ⟨done, mappingChecked, action⟩ := bind_checked rest
  cases done
  exact ⟨typeChecked,SourceTyping.ensure_checked mappingChecked,action⟩

theorem default_declaration_environment
    (checked : declareBinders (Key := EmptyKey) registry fuel context [some binder] none = .ok after) :
    Env after = Environment.declare (Env context) binder :=
  declare_environment (default_declaration_checked checked).2.2

theorem initialized_declaration_checked
    (checked : declareBinders registry fuel context [some binder] (some value) = .ok after) :
    ∃ evaluated source,
      checkExpression registry fuel context value = .ok evaluated ∧
      resultComponents value.type = [source] ∧ transfer registry fuel true source binder.type = .ok () ∧
      evaluated.declare binder true = .ok after := by
  simp only [declareBinders] at checked
  obtain ⟨evaluated, child, rest⟩ := bind_checked checked
  obtain ⟨_, count, rest⟩ := bind_checked rest
  have count := SourceTyping.ensure_checked count
  cases components : resultComponents value.type with
  | nil => simp [components] at count
  | cons type tail =>
      have empty : tail = [] := by simpa [components] using count
      subst tail
      simp only [components, List.zip_cons_cons, List.zip_nil_left, List.foldlM] at rest
      obtain ⟨declared, action, done⟩ := bind_checked rest
      have equal : declared = after := Except.ok.inj done
      subst after
      obtain ⟨done, transferred, action⟩ := bind_checked action
      cases done
      exact ⟨evaluated,type,child,rfl,transferred,action⟩

theorem initialized_declaration_environment
    (form : Profile.Expression program value)
    (checked : declareBinders registry fuel context [some binder] (some value) = .ok after) :
    Env after = Environment.declare (Env context) binder := by
  obtain ⟨evaluated,source,child,_,_,declared⟩ := initialized_declaration_checked checked
  exact (declare_environment declared).trans (congrArg (fun environment => Environment.declare environment binder)
    (congrArg Profile.scopesEnvironment (checkExpression_scopes form child)))

theorem declaration_environment (form : Profile.Declaration program declaration)
    (checked : checkStatement registry fuel context returns loops unchecked declaration = .ok flow) :
    ∃ binder initializer after,
      declaration = .declare [some binder] initializer ∧ flow = Flow.next after ∧
      Env after = Environment.declare (Env context) binder := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases form with
      | default supported =>
          simp only [checkStatement] at checked
          obtain ⟨after,declared,done⟩ := bind_checked checked
          exact ⟨_,none,after,rfl,(Except.ok.inj done).symm,default_declaration_environment declared⟩
      | value supported source =>
          simp only [checkStatement] at checked
          obtain ⟨after,declared,done⟩ := bind_checked checked
          exact ⟨_,some _,after,rfl,(Except.ok.inj done).symm,initialized_declaration_environment source declared⟩

theorem initializerEnvironment_tail (environment : Environment) (statement : Stmt EmptyKey) :
    (initializerEnvironment environment statement).tail = environment.tail := by
  cases statement <;> try rfl
  rename_i binders initializer
  cases binders with
  | nil => rfl
  | cons binder rest =>
      cases rest with
      | cons => cases binder <;> rfl
      | nil => cases binder <;> cases environment <;> rfl

theorem prefixEnvironment_tail (environment : Environment) (statement : Stmt EmptyKey) :
    (prefixEnvironment environment statement).tail = environment.tail := by
  cases statement <;> try rfl
  rename_i first rest
  cases first <;> try rfl
  rename_i binders initializer
  cases binders with
  | nil => rfl
  | cons binder tail =>
      cases tail with
      | cons => cases binder <;> rfl
      | nil =>
          cases binder with
          | none => rfl
          | some binder =>
              exact (prefixEnvironment_tail _ rest).trans (by cases environment <;> rfl)
termination_by sizeOf statement

private theorem statement_not_declaration (form : Profile.Statement program statement) :
    ∀ binders initializer, statement ≠ .declare binders initializer := by
  cases form <;> intros <;> intro impossible <;> cases impossible

theorem statement_prefix (form : Profile.Statement program statement) (environment : Environment) :
    prefixEnvironment environment statement = environment := by
  cases form <;> try rfl
  rename_i first rest firstForm restForm
  cases first <;> try rfl
  exact False.elim (statement_not_declaration firstForm _ _ rfl)

theorem statement_initializer (form : Profile.Statement program statement) (environment : Environment) :
    initializerEnvironment environment statement = environment := by
  cases form <;> rfl

private theorem append_environment {first rest : List Admission.Context}
    (left : ∀ context ∈ first, Env context = environment)
    (right : ∀ context ∈ rest, Env context = environment) :
    ∀ context ∈ first ++ rest, Env context = environment := by
  intro context member
  rcases List.mem_append.mp member with member | member
  · exact left context member
  · exact right context member

theorem sequence_shape (first : ShapeFlow environment a) (second : ShapeFlow environment b) :
    ShapeFlow environment (if a.normal.isSome then
      ⟨b.normal,a.breaks ++ b.breaks,a.continues ++ b.continues,b.dead⟩ else {a with dead := b.dead}) := by
  cases normal : a.normal with
  | none =>
      simp only [Option.isSome_none,Bool.false_eq_true,↓reduceIte]
      exact ⟨second.dead,by simp,first.breaks,first.continues⟩
  | some context =>
      simp only [Option.isSome_some,↓reduceIte]
      exact ⟨second.dead,second.normal,append_environment first.breaks second.breaks,
        append_environment first.continues second.continues⟩

theorem branch_shape (initial : Env context = environment)
    (left : ShapeFlow environment a) (right : ShapeFlow environment b) :
    ShapeFlow environment ⟨mergeNormal a.normal b.normal,a.breaks ++ b.breaks,
      a.continues ++ b.continues,context⟩ :=
  ⟨initial,mergeNormal_environment left.normal right.normal,
    append_environment left.breaks right.breaks,append_environment left.continues right.continues⟩

theorem loop_shape (initial : Env context = environment)
    (normalShape : ∀ current ∈ normal, Env current = environment) :
    ShapeFlow environment ⟨normal,[],[],context⟩ :=
  ⟨initial,normalShape,by simp,by simp⟩

theorem expression_environment (form : Profile.Expression program expression)
    (checked : checkExpression registry fuel before expression = .ok after) :
    Env after = Env before := congrArg Profile.scopesEnvironment (checkExpression_scopes form checked)

private theorem next_shape_as (same : Env context = environment) : ShapeFlow environment (Flow.next context) := by
  rw [← same]
  exact next_shape context

private theorem halt_shape_as (same : Env context = environment) : ShapeFlow environment (Flow.halt context) := by
  rw [← same]
  exact halt_shape context

private theorem optional_environment
    (forms : ∀ expression ∈ value, Profile.Expression program expression)
    (checked : checkOptional registry fuel before value = .ok after) : Env after = Env before := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases value with
      | none => exact congrArg Env (Except.ok.inj checked).symm
      | some expression => exact expression_environment (forms expression rfl) checked

private theorem shapes (program : Program EmptyKey) (registry : Registry) (fuel : Nat) :
    (∀ statement, Profile.Statement program statement → ∀ context returns loops unchecked flow,
      checkStatement registry fuel context returns loops unchecked statement = .ok flow →
      ShapeFlow (Env context) flow) ∧
    (∀ body, Profile.Body program body → ∀ context returns loops unchecked flow,
      checkStatement registry fuel context returns loops unchecked body = .ok flow →
      ShapeFlow (prefixEnvironment (Env context) body) flow) ∧
    (∀ initializer, Profile.Initializer program initializer → ∀ context returns loops unchecked flow,
      checkStatement registry fuel context returns loops unchecked initializer = .ok flow →
      ShapeFlow (initializerEnvironment (Env context) initializer) flow) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      cases fuel with
      | zero =>
          constructor
          · intro statement form context returns loops unchecked flow checked; cases checked
          constructor
          · intro body form context returns loops unchecked flow checked; cases checked
          · intro initializer form context returns loops unchecked flow checked; cases checked
      | succ fuel =>
          have statementShape : ∀ statement, Profile.Statement program statement → ∀ context returns loops unchecked flow,
              checkStatement registry (fuel+1) context returns loops unchecked statement = .ok flow →
              ShapeFlow (Env context) flow := by
            intro statement form context returns loops unchecked flow checked
            cases form with
            | skip =>
                have equal : Flow.next context = flow := Except.ok.inj checked
                rw [← equal]
                exact next_shape context
            | expr expression =>
                simp only [checkStatement] at checked
                obtain ⟨after,child,done⟩ := bind_checked checked
                have same := expression_environment expression child
                rw [← Except.ok.inj done]
                split
                · exact halt_shape_as same
                · exact next_shape_as same
            | seq first rest =>
                simp only [checkStatement] at checked
                obtain ⟨a,firstChecked,checked⟩ := bind_checked checked
                obtain ⟨b,restChecked,done⟩ := bind_checked checked
                have firstShape := (ih fuel (by omega)).1 _ first _ _ _ _ _ firstChecked
                have middle := getD_environment firstShape.normal
                  ((relax_environment a.dead).trans firstShape.dead)
                have restShape := (ih fuel (by omega)).1 _ rest _ _ _ _ _ restChecked
                rw [middle] at restShape
                rw [← Except.ok.inj done]
                exact sequence_shape firstShape restShape
            | block body =>
                simp only [checkStatement] at checked
                obtain ⟨after,bodyChecked,done⟩ := bind_checked checked
                have bodyShape := (ih fuel (by omega)).2.1 _ body _ _ _ _ _ bodyChecked
                have left := leave_shape bodyShape
                rw [prefixEnvironment_tail,enter_environment,List.tail_cons] at left
                rw [← Except.ok.inj done]
                exact left
            | if_ test yes no =>
                simp only [checkStatement] at checked
                obtain ⟨tested,testChecked,checked⟩ := bind_checked checked
                have same := expression_environment test testChecked
                obtain ⟨_,_,checked⟩ := bind_checked checked
                obtain ⟨a,yesChecked,checked⟩ := bind_checked checked
                obtain ⟨b,noChecked,checked⟩ := bind_checked checked
                obtain ⟨_,_,done⟩ := bind_checked checked
                have yesShape := (ih fuel (by omega)).1 _ yes _ _ _ _ _ yesChecked
                have noShape := (ih fuel (by omega)).1 _ no _ _ _ _ _ noChecked
                rw [same] at yesShape noShape
                rw [← Except.ok.inj done]
                split
                · exact halt_shape_as same
                · exact branch_shape same yesShape noShape
            | while_ test body =>
                simp only [checkStatement] at checked
                obtain ⟨tested,testChecked,checked⟩ := bind_checked checked
                have same := expression_environment test testChecked
                obtain ⟨_,_,checked⟩ := bind_checked checked
                obtain ⟨bodyFlow,bodyChecked,checked⟩ := bind_checked checked
                obtain ⟨_,_,done⟩ := bind_checked checked
                have bodyShape := (ih fuel (by omega)).1 _ body _ _ _ _ _ bodyChecked
                rw [same] at bodyShape
                rw [← Except.ok.inj done]
                split
                · exact halt_shape_as same
                · exact loop_shape same (mergeNormal_environment (by simpa using same)
                    (meetContexts_environment bodyShape.breaks))
            | loop test body post =>
                simp only [checkStatement] at checked
                obtain ⟨tested,testChecked,checked⟩ := bind_checked checked
                have same := expression_environment test testChecked
                obtain ⟨_,_,checked⟩ := bind_checked checked
                obtain ⟨bodyFlow,bodyChecked,checked⟩ := bind_checked checked
                obtain ⟨_,_,checked⟩ := bind_checked checked
                obtain ⟨postFlow,_,checked⟩ := bind_checked checked
                obtain ⟨_,_,done⟩ := bind_checked checked
                have bodyShape := (ih fuel (by omega)).1 _ body _ _ _ _ _ bodyChecked
                rw [same] at bodyShape
                rw [← Except.ok.inj done]
                split
                · exact halt_shape_as same
                · exact loop_shape same (mergeNormal_environment (by simpa using same)
                    (meetContexts_environment bodyShape.breaks))
            | doWhile body test =>
                simp only [checkStatement] at checked
                obtain ⟨bodyFlow,bodyChecked,checked⟩ := bind_checked checked
                obtain ⟨_,_,checked⟩ := bind_checked checked
                obtain ⟨tested,testChecked,checked⟩ := bind_checked checked
                obtain ⟨_,_,done⟩ := bind_checked checked
                have bodyShape := (ih fuel (by omega)).1 _ body _ _ _ _ _ bodyChecked
                have incomingShape := mergeNormal_environment bodyShape.normal
                  (meetContexts_environment bodyShape.continues)
                have testedShape := (expression_environment test testChecked).trans
                  (getD_environment incomingShape (relax_environment context))
                rw [← Except.ok.inj done]
                apply loop_shape rfl
                apply mergeNormal_environment
                · split
                  · simpa using testedShape
                  · simp
                · exact meetContexts_environment bodyShape.breaks
            | for_ initializer tests post body =>
                rename_i init test postCode bodyCode
                simp only [checkStatement] at checked
                obtain ⟨initialized,initChecked,checked⟩ := bind_checked checked
                obtain ⟨_,_,checked⟩ := bind_checked checked
                obtain ⟨current,testChecked,checked⟩ := bind_checked checked
                obtain ⟨_,_,checked⟩ := bind_checked checked
                obtain ⟨bodyFlow,bodyChecked,checked⟩ := bind_checked checked
                obtain ⟨_,_,checked⟩ := bind_checked checked
                obtain ⟨postFlow,_,checked⟩ := bind_checked checked
                obtain ⟨_,_,done⟩ := bind_checked checked
                have initShape := (ih fuel (by omega)).2.2 _ initializer _ _ _ _ _ initChecked
                have currentShape := (optional_environment tests testChecked).trans
                  (getD_environment initShape.normal ((relax_environment initialized.dead).trans initShape.dead))
                have bodyShape := (ih fuel (by omega)).1 _ body _ _ _ _ _ bodyChecked
                rw [currentShape] at bodyShape
                have normalShape := mergeNormal_environment
                  (left := if test.any stops then none else some current) (right := meetContexts bodyFlow.breaks)
                  (by split <;> simp_all) (meetContexts_environment bodyShape.breaks)
                have beforeLeave := loop_shape currentShape
                  (normal := if initialized.normal.isSome then
                    mergeNormal (if test.any stops then none else some current) (meetContexts bodyFlow.breaks) else none)
                  (by split <;> simp_all)
                have left := leave_shape beforeLeave
                rw [initializerEnvironment_tail,enter_environment,List.tail_cons] at left
                rw [← Except.ok.inj done]
                exact left
            | break_ =>
                simp only [checkStatement] at checked
                obtain ⟨_,_,done⟩ := bind_checked checked
                rw [← Except.ok.inj done]
                exact ⟨rfl,by simp,by simp,by simp⟩
            | continue_ =>
                simp only [checkStatement] at checked
                obtain ⟨_,_,done⟩ := bind_checked checked
                rw [← Except.ok.inj done]
                exact ⟨rfl,by simp,by simp,by simp⟩
            | return_ values =>
                rename_i value
                cases value with
                | none =>
                    simp only [checkStatement] at checked
                    obtain ⟨_,_,done⟩ := bind_checked checked
                    rw [← Except.ok.inj done]
                    exact halt_shape context
                | some expression =>
                    simp only [checkStatement] at checked
                    obtain ⟨after,child,checked⟩ := bind_checked checked
                    obtain ⟨_,_,checked⟩ := bind_checked checked
                    obtain ⟨_,_,done⟩ := bind_checked checked
                    rw [← Except.ok.inj done]
                    exact halt_shape_as (expression_environment (values expression rfl) child)
            | arithmetic body =>
                simp only [checkStatement] at checked
                obtain ⟨_,_,checked⟩ := bind_checked checked
                exact (ih fuel (by omega)).1 _ body _ _ _ _ _ checked
            | revert =>
                rw [← Except.ok.inj checked]
                exact halt_shape context
          refine ⟨statementShape,?_,?_⟩
          · intro body form context returns loops unchecked flow checked
            cases form with
            | statement form =>
                rw [statement_prefix form]
                exact statementShape _ form _ _ _ _ _ checked
            | declaration declared rest =>
                simp only [checkStatement] at checked
                obtain ⟨a,firstChecked,checked⟩ := bind_checked checked
                obtain ⟨b,restChecked,done⟩ := bind_checked checked
                obtain ⟨binder,initializer,after,sourceEq,flowEqual,environment⟩ :=
                  declaration_environment declared firstChecked
                subst a
                have restShape := (ih fuel (by omega)).2.1 _ rest _ _ _ _ _ restChecked
                simp only [Flow.next,Option.getD_some] at restShape
                rw [environment] at restShape
                rw [sourceEq]
                change ShapeFlow (prefixEnvironment (Environment.declare (Env context) binder) _) flow
                have equal : b = flow := by simpa [Flow.next] using Except.ok.inj done
                rw [← equal]
                exact restShape
          · intro initializer form context returns loops unchecked flow checked
            cases form with
            | statement form =>
                rw [statement_initializer form]
                exact statementShape _ form _ _ _ _ _ checked
            | declaration form =>
                obtain ⟨binder,initial,after,sourceEq,flowEqual,environment⟩ := declaration_environment form checked
                rw [sourceEq,flowEqual]
                exact next_shape_as environment

theorem statement_scopes (form : Profile.Statement program statement)
    (checked : checkStatement registry fuel context returns loops unchecked statement = .ok flow) :
    ShapeFlow (Profile.scopesEnvironment context.scopes) flow :=
  (shapes program registry fuel).1 _ form _ _ _ _ _ checked

theorem body_scopes (form : Profile.Body program body)
    (checked : checkStatement registry fuel context returns loops unchecked body = .ok flow) :
    ShapeFlow (prefixEnvironment (Profile.scopesEnvironment context.scopes) body) flow :=
  (shapes program registry fuel).2.1 _ form _ _ _ _ _ checked

theorem initializer_scopes (form : Profile.Initializer program initializer)
    (checked : checkStatement registry fuel context returns loops unchecked initializer = .ok flow) :
    ShapeFlow (initializerEnvironment (Profile.scopesEnvironment context.scopes) initializer) flow :=
  (shapes program registry fuel).2.2 _ form _ _ _ _ _ checked

end Solidity.Execution.Safety.SourceControl
