/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.Profile
import Solidity.Core.Execution.Safety.TypedPackets

/-! Independent typing and representation of continuations. No field mentions
Machine.step, successful execution, reachability or an evaluator callback.
The source checker remains the typing authority for stored syntax. -/
namespace Solidity.Execution.Safety
open Static Aggregates

def prefixEnvironment (environment : Environment) : Stmt EmptyKey → Environment
  | .seq (.declare [some binder] _) rest => prefixEnvironment (Environment.declare environment binder) rest
  | _ => environment

def initializerEnvironment (environment : Environment) : Stmt EmptyKey → Environment
  | .declare [some binder] _ => Environment.declare environment binder
  | _ => environment

structure Control where
  returns : List Binder := []
  loop : Bool := false

def Control.inLoop (flowContext : Control) : Control := {flowContext with loop := true}
def Control.resultType (flowContext : Control) : SType :=
  match flowContext.returns.map Binder.type with
  | [type] => type
  | types => .tuple (Types.ofList types)

inductive Kind where
  | value : SType → Kind
  | target : SType → Kind
  | signal : Control → Kind
  | nextOnly

def TypeReady (registry : Registry) (type : SType) : Prop :=
  Supported type ∧ Static.wellFormed registry type = true

structure ExpressionCode (registry : Registry) (program : Program EmptyKey)
    (environment : Environment) (expression : Expr EmptyKey) : Prop where
  form : Profile.Expression program expression
  admitted : Profile.CheckedExpression registry environment expression

structure TargetCode (registry : Registry) (program : Program EmptyKey)
    (environment : Environment) (target : LValue EmptyKey) : Prop where
  form : Profile.Target program target
  admitted : ∃ fuel incoming after writable, Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment ∧
    Admission.checkLValue registry fuel incoming target writable = .ok after

structure StatementCode (registry : Registry) (program : Program EmptyKey)
    (environment : Environment) (flowContext : Control) (statement : Stmt EmptyKey) : Prop where
  form : Profile.Statement program statement
  admitted : Profile.CheckedStatement registry environment flowContext.returns (if flowContext.loop then 1 else 0) statement
  returnsReady : ∀ binder ∈ flowContext.returns, TypeReady registry binder.type

structure BodyCode (registry : Registry) (program : Program EmptyKey)
    (environment : Environment) (flowContext : Control) (body : Stmt EmptyKey) : Prop where
  form : Profile.Body program body
  admitted : Profile.CheckedStatement registry environment flowContext.returns (if flowContext.loop then 1 else 0) body
  returnsReady : ∀ binder ∈ flowContext.returns, TypeReady registry binder.type

structure DeclarationCode (registry : Registry) (program : Program EmptyKey)
    (environment : Environment) (declaration : Stmt EmptyKey) : Prop where
  form : Profile.Declaration program declaration
  admitted : ∃ fuel incoming after, Environment.Equivalent (Profile.scopesEnvironment incoming.scopes) environment ∧
    Admission.checkStatement registry fuel incoming [] 0 false declaration = .ok after

def TransferReady (registry : Registry) (source target : SType) : Prop :=
  TypeReady registry source ∧ TypeReady registry target ∧ ∃ kind, TransferRule true source target kind

inductive ArgumentsReady (registry : Registry) : List SType → List SType → Prop where
  | nil : ArgumentsReady registry [] []
  | cons : TransferReady registry source target → ArgumentsReady registry sources targets →
      ArgumentsReady registry (source :: sources) (target :: targets)

def ReturnReady (registry : Registry) (source : SType) (returns : List Binder) : Prop :=
  ArgumentsReady registry (Admission.resultComponents source) (returns.map Binder.type)

inductive HeapTargetRep (heap : Heap) (objects : List WordArena.Object) : Place → Prop where
  | persistent (owner : BitVec 160) (address : Contract.Interaction.Word) :
      HeapTargetRep heap objects ⟨.uint 31,{region := .storage owner,address}⟩
  | transient (owner : BitVec 160) (address : Contract.Interaction.Word) :
      HeapTargetRep heap objects ⟨.uint 31,{region := .transient owner,address}⟩
  | cell (object : WordArena.Object) (member : object ∈ objects) (index : Nat) (inside : index < object.length) :
      HeapTargetRep heap objects (object.cell heap index)

inductive TargetRep (registry : Registry) (heap : Heap) (objects : List WordArena.Object) (environment : Environment) :
    Execution.Target EmptyKey → SType → Prop where
  | local (bound : Environment.find environment localId = some type) (ready : TypeReady registry type) :
      TargetRep registry heap objects environment (.captured (.local localId type)) type
  | heap (represented : HeapTargetRep heap objects place) :
      TargetRep registry heap objects environment (.captured (.heap place)) (.uint 31)

inductive CompletionRep (registry : Registry) : Completion → List SType → Kind → Prop where
  | unary (supported : type.scalarSupported = true) (allowed : (checkUnary code type).isSome = true) :
      CompletionRep registry (.unary code) [type] (.value type)
  | binary (leftSupport : left.scalarSupported = true) (rightSupport : right.scalarSupported = true)
      (resultSupport : result.scalarSupported = true) (allowed : Admission.BinaryAllowed code left right result) :
      CompletionRep registry (.binary code result) [left,right] (.value result)
  | tuple (types : List SType) : CompletionRep registry .tuple types (.value (.tuple (Types.ofList types)))
  | cast (sourceSupport : source.scalarSupported = true) (targetSupport : target.scalarSupported = true)
      (allowed : Static.Allowed mode source target)
      (sourceFormed : Static.wellFormed registry source = true)
      (targetFormed : Static.wellFormed registry target = true) :
      CompletionRep registry (.cast mode target) [source] (.value target)
  | call (functionReady : TypeReady registry functionType)
      (functionAllowed : Static.Allowed .implicit functionType signature.type)
      (arguments : ArgumentsReady registry sourceTypes (typesList signature.parameters)) :
      CompletionRep registry (.call signature) (functionType :: sourceTypes) (.value signature.resultType)
  | namedCall (functionReady : TypeReady registry functionType)
      (functionAllowed : Static.Allowed .implicit functionType signature.type)
      (orderValid : ArgumentOrder.Valid order sourceTypes.length)
      (arguments : ∃ reordered, ArgumentOrder.select order sourceTypes = .ok reordered ∧
        ArgumentsReady registry reordered (typesList signature.parameters)) :
      CompletionRep registry (.namedCall signature order) (functionType :: sourceTypes) (.value signature.resultType)
  | length (pointer : Bool) :
      CompletionRep registry .length [WordArena.arrayType pointer] (.value (.uint 31))
  | index (pointer : Bool) (width : Core.Width) :
      CompletionRep registry (.index (.uint 31)) [WordArena.arrayType pointer,.uint width] (.target (.uint 31))
  | readIndex (pointer : Bool) (width : Core.Width) :
      CompletionRep registry (.readIndex (.uint 31)) [WordArena.arrayType pointer,.uint width] (.value (.uint 31))
  | newArray (width : Core.Width) :
      CompletionRep registry (.newArray (.uint 31)) [.uint width] (.value (WordArena.arrayType true))
  | assert_ : CompletionRep registry .assert_ [.bool] (.value (.tuple .nil))
  | require_ : CompletionRep registry (.require_ .empty) [.bool] (.value (.tuple .nil))
  | revertWith : CompletionRep registry (.revertWith .empty) [] (.value (.tuple .nil))

inductive SignalRep (registry : Registry) (program : Program EmptyKey) (heap : Heap)
    (objects : List WordArena.Object) (flowContext : Control) : Signal → Prop where
  | next : SignalRep registry program heap objects flowContext .next
  | break_ (allowed : flowContext.loop = true) : SignalRep registry program heap objects flowContext .break_
  | continue_ (allowed : flowContext.loop = true) : SignalRep registry program heap objects flowContext .continue_
  | return_ : SignalRep registry program heap objects flowContext (.return_ none)
  | values (represented : DatumRep program heap objects values type)
      (allowed : ReturnReady registry type flowContext.returns) :
      SignalRep registry program heap objects flowContext (.return_ (some values))

structure StateRep (program : Program EmptyKey) (objects : List WordArena.Object)
    (environment : Environment) (state : MachineState Unit) : Prop where
  heap : HeapRep state.heap objects
  cells : CellsRep program state.heap objects state.locals
  shape : Safety.Locals.environment state.locals = environment
  nonempty : state.locals ≠ []

def ExprRep (registry : Registry) (program : Program EmptyKey) (environment : Environment) :
    Expr EmptyKey → Prop := ExpressionCode registry program environment

inductive WritesRep (registry : Registry) (program : Program EmptyKey) (heap : Heap)
    (objects : List WordArena.Object) (environment : Environment) :
    List (Execution.Target EmptyKey × Value) → Prop where
  | nil : WritesRep registry program heap objects environment []
  | cons (targetRep : TargetRep registry heap objects environment target type)
      (valueRep : ValueRep program heap objects value) (transfer : TransferReady registry value.type type)
      (rest : WritesRep registry program heap objects environment writes) :
      WritesRep registry program heap objects environment ((target,value) :: writes)

inductive TaskRep (registry : Registry) (program : Program EmptyKey) (heap : Heap)
    (objects : List WordArena.Object) : Environment → Task EmptyKey → Environment → Kind → Prop where
  | eval (code : ExpressionCode registry program environment expression) :
      TaskRep registry program heap objects environment (.eval expression) environment (.value expression.type)
  | capture (code : TargetCode registry program environment target) :
      TaskRep registry program heap objects environment (.capture target) environment (.target target.type)
  | value (represented : DatumRep program heap objects value type) :
      TaskRep registry program heap objects environment (.value value) environment (.value type)
  | target (represented : TargetRep registry heap objects environment target type) :
      TaskRep registry program heap objects environment (.target target) environment (.target type)
  | collect (values : TypedPackets.CollectRep program heap objects (ExprRep registry program environment)
      types pending completed) (finish : CompletionRep registry completion types kind) :
      TaskRep registry program heap objects environment (.collect pending completed completion) environment kind
  | apply (packet : PacketRep program heap objects values (Types.ofList types))
      (finish : CompletionRep registry completion types kind) :
      TaskRep registry program heap objects environment (.apply completion values) environment kind
  | statement (code : StatementCode registry program environment flowContext statement) :
      TaskRep registry program heap objects environment (.exec statement) environment (.signal flowContext)
  | body (code : BodyCode registry program environment flowContext body) :
      TaskRep registry program heap objects environment (.exec body) (prefixEnvironment environment body) (.signal flowContext)
  | declaration (code : DeclarationCode registry program environment (.declare [some binder] initializer)) :
      TaskRep registry program heap objects environment (.exec (.declare [some binder] initializer))
        (Environment.declare environment binder) .nextOnly
  | resume (represented : SignalRep registry program heap objects flowContext signal) :
      TaskRep registry program heap objects environment (.resume signal) environment (.signal flowContext)
  | next : TaskRep registry program heap objects environment (.resume .next) environment .nextOnly
  | loop (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
      (bodyCode : StatementCode registry program environment flowContext.inLoop body)
      (postCode : StatementCode registry program environment flowContext post) :
      TaskRep registry program heap objects environment (.loopTest test body post) environment (.signal flowContext)
  | writes (represented : WritesRep registry program heap objects environment writes) :
      TaskRep registry program heap objects environment (.writes writes) environment (.value (.tuple .nil))

/-- Arithmetic modes wrap expression/control evaluation, never a captured
place. The actual target dispatch has no mode-restoration branch. -/
def ModeKind : Kind → Prop
  | .target _ => False
  | _ => True

inductive FrameRep (registry : Registry) (program : Program EmptyKey) (heap : Heap)
    (objects : List WordArena.Object) : Environment → Kind → Frame EmptyKey → Environment → Kind → Prop where
  | mode (permitted : ModeKind kind := by trivial) :
      FrameRep registry program heap objects environment kind (.mode mode) environment kind
  | scope (outerScope : outer ≠ []) :
      FrameRep registry program heap objects (inner :: outer) (.signal flowContext) .scope outer (.signal flowContext)
  | next (code : StatementCode registry program environment flowContext rest) :
      FrameRep registry program heap objects environment (.signal flowContext) (.next rest) environment (.signal flowContext)
  | prefix (code : BodyCode registry program environment flowContext rest) :
      FrameRep registry program heap objects environment .nextOnly (.next rest)
        (prefixEnvironment environment rest) (.signal flowContext)
  | discard : FrameRep registry program heap objects environment (.value type) .discard environment (.signal flowContext)
  | returnValue (allowed : ReturnReady registry type flowContext.returns) :
      FrameRep registry program heap objects environment (.value type) .returnValue environment (.signal flowContext)
  | readTarget : FrameRep registry program heap objects environment (.target type) .readTarget environment (.value type)
  | collect (values : TypedPackets.ActiveRep program heap objects (ExprRep registry program environment)
      types index type pending completed) (finish : CompletionRep registry completion types kind) :
      FrameRep registry program heap objects environment (.value type) (.collect index pending completed completion)
        environment kind
  | select (yesCode : ExpressionCode registry program environment yes)
      (noCode : ExpressionCode registry program environment no) (same : yes.type = no.type) :
      FrameRep registry program heap objects environment (.value .bool) (.select yes no) environment (.value yes.type)
  | branch (yesCode : StatementCode registry program environment flowContext yes)
      (noCode : StatementCode registry program environment flowContext no) :
      FrameRep registry program heap objects environment (.value .bool) (.branch yes no) environment (.signal flowContext)
  | lazy (rightCode : ExpressionCode registry program environment right) (boolean : right.type = .bool) :
      FrameRep registry program heap objects environment (.value .bool) (.lazy terminal right) environment (.value .bool)
  | assignRight (targetCode : TargetCode registry program environment target)
      (allowed : TransferReady registry source target.type) :
      FrameRep registry program heap objects environment (.value source) (.assignRight target none)
        environment (.value target.type)
  | assignLeft (rightCode : ExpressionCode registry program environment right)
      (allowed : TransferReady registry right.type targetType) :
      FrameRep registry program heap objects environment (.target targetType) (.assignLeft right none)
        environment (.value targetType)
  | commitValue (right : DatumRep program heap objects value source)
      (allowed : TransferReady registry source targetType) :
      FrameRep registry program heap objects environment (.target targetType) (.commitValue value none)
        environment (.value targetType)
  | commitTarget (targetRep : TargetRep registry heap objects environment target targetType)
      (allowed : TransferReady registry source targetType) :
      FrameRep registry program heap objects environment (.value source) (.commitTarget target none)
        environment (.value targetType)
  | compoundRight (targetCode : TargetCode registry program environment target)
      (leftSupport : target.type.scalarSupported = true) (rightSupport : source.scalarSupported = true)
      (token : Frontend.Inference.compoundToken code = true)
      (operation : Admission.BinaryAllowed code target.type source target.type) :
      FrameRep registry program heap objects environment (.value source) (.assignRight target (some code))
        environment (.value target.type)
  | compoundLeft (rightCode : ExpressionCode registry program environment right)
      (leftSupport : targetType.scalarSupported = true) (rightSupport : right.type.scalarSupported = true)
      (token : Frontend.Inference.compoundToken code = true)
      (operation : Admission.BinaryAllowed code targetType right.type targetType) :
      FrameRep registry program heap objects environment (.target targetType) (.assignLeft right (some code))
        environment (.value targetType)
  | compoundReadFirst (rightCode : ExpressionCode registry program environment right)
      (leftSupport : targetType.scalarSupported = true) (rightSupport : right.type.scalarSupported = true)
      (token : Frontend.Inference.compoundToken code = true)
      (operation : Admission.BinaryAllowed code targetType right.type targetType) :
      FrameRep registry program heap objects environment (.target targetType) (.compoundReadFirst right code)
        environment (.value targetType)
  | compoundValue (right : DatumRep program heap objects value source)
      (leftSupport : targetType.scalarSupported = true) (rightSupport : source.scalarSupported = true)
      (token : Frontend.Inference.compoundToken code = true)
      (operation : Admission.BinaryAllowed code targetType source targetType) :
      FrameRep registry program heap objects environment (.target targetType) (.commitValue value (some code))
        environment (.value targetType)
  | compoundTarget (targetRep : TargetRep registry heap objects environment target targetType)
      (leftSupport : targetType.scalarSupported = true) (rightSupport : source.scalarSupported = true)
      (token : Frontend.Inference.compoundToken code = true)
      (operation : Admission.BinaryAllowed code targetType source targetType) :
      FrameRep registry program heap objects environment (.value source) (.commitTarget target (some code))
        environment (.value targetType)
  | commitOld (targetRep : TargetRep registry heap objects environment target targetType)
      (old : ValueRep program heap objects oldValue) (oldType : oldValue.type = targetType)
      (leftSupport : targetType.scalarSupported = true) (rightSupport : source.scalarSupported = true)
      (token : Frontend.Inference.compoundToken code = true)
      (operation : Admission.BinaryAllowed code targetType source targetType) :
      FrameRep registry program heap objects environment (.value source) (.commitOld target code oldValue)
        environment (.value targetType)
  | update (nondelete : code ≠ .delete) (allowed : Static.UpdateAllowed code type true) :
      FrameRep registry program heap objects environment (.target type) (.update code) environment (.value type)
  | declare (supported : TypeReady registry binder.type)
      (allowed : ReturnReady registry source [binder])
      (fresh : Environment.find environment binder.id = none) :
      FrameRep registry program heap objects environment (.value source) (.declare [some binder])
        (Environment.declare environment binder) .nextOnly
  | loopCondition (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
      (bodyCode : StatementCode registry program environment flowContext.inLoop body)
      (postCode : StatementCode registry program environment flowContext post) :
      FrameRep registry program heap objects environment (.value .bool) (.loopCondition test body post)
        environment (.signal flowContext)
  | forInit (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
      (bodyCode : StatementCode registry program environment flowContext.inLoop body)
      (postCode : StatementCode registry program environment flowContext post) :
      FrameRep registry program heap objects environment (.signal flowContext) (.forInit test body post)
        environment (.signal flowContext)
  | forInitNext (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
      (bodyCode : StatementCode registry program environment flowContext.inLoop body)
      (postCode : StatementCode registry program environment flowContext post) :
      FrameRep registry program heap objects environment .nextOnly (.forInit test body post)
        environment (.signal flowContext)
  | loopBody (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
      (bodyCode : StatementCode registry program environment flowContext.inLoop body)
      (postCode : StatementCode registry program environment flowContext post) :
      FrameRep registry program heap objects environment (.signal flowContext.inLoop) (.loopBody test body post)
        environment (.signal flowContext)
  | loopPost (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool)
      (bodyCode : StatementCode registry program environment flowContext.inLoop body)
      (postCode : StatementCode registry program environment flowContext post) :
      FrameRep registry program heap objects environment (.signal flowContext) (.loopPost test body post)
        environment (.signal flowContext)
  | doBody (bodyCode : StatementCode registry program environment flowContext.inLoop body)
      (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool) :
      FrameRep registry program heap objects environment (.signal flowContext.inLoop) (.doBody body test)
        environment (.signal flowContext)
  | doCondition (bodyCode : StatementCode registry program environment flowContext.inLoop body)
      (testCode : ExpressionCode registry program environment test) (boolean : test.type = .bool) :
      FrameRep registry program heap objects environment (.value .bool) (.doCondition body test)
        environment (.signal flowContext)
  | call (caller : CellsRep program heap objects locals)
      (callerShape : Safety.Locals.environment locals = callerEnvironment) (callerNonempty : locals ≠ [])
      (returnCells : ∀ binder ∈ returns, Environment.find environment binder.id = some binder.type)
      (returnReady : ∀ binder ∈ returns, TypeReady registry binder.type) :
      FrameRep registry program heap objects environment (.signal ⟨returns,false⟩) (.call locals mode returns)
        callerEnvironment (.value (Control.resultType ⟨returns,false⟩))
  | resultTransfer (caller : CellsRep program heap objects locals)
      (callerShape : Safety.Locals.environment locals = callerEnvironment) (callerNonempty : locals ≠ [])
      (returnCells : ∀ binder ∈ returns, Environment.find environment binder.id = some binder.type)
      (returnReady : ∀ binder ∈ returns, TypeReady registry binder.type) :
      FrameRep registry program heap objects environment (.value (.tuple .nil)) (.resultTransfer locals mode returns)
        callerEnvironment (.value (Control.resultType ⟨returns,false⟩))

inductive StackRep (registry : Registry) (program : Program EmptyKey) (heap : Heap)
    (objects : List WordArena.Object) : Environment → Kind → List (Frame EmptyKey) → Prop where
  | value : StackRep registry program heap objects environment (.value type) []
  | signal : StackRep registry program heap objects environment (.signal ⟨[],false⟩) []
  | next : StackRep registry program heap objects environment .nextOnly []
  | cons : FrameRep registry program heap objects environment kind frame afterEnvironment afterKind →
      StackRep registry program heap objects afterEnvironment afterKind stack →
      StackRep registry program heap objects environment kind (frame :: stack)

structure ConfigurationWitness (registry : Registry) (program : Program EmptyKey)
    (config : Config Unit EmptyKey) where
  closed : Profile.ClosedProgram registry program
  objects : List WordArena.Object
  environment : Environment
  resultEnvironment : Environment
  kind : Kind
  state : StateRep program objects environment config.state
  task : TaskRep registry program config.state.heap objects environment config.task resultEnvironment kind
  stack : StackRep registry program config.state.heap objects resultEnvironment kind config.stack
  checkpoint : ∃ entryObjects entryEnvironment, StateRep program entryObjects entryEnvironment config.entry

def ConfigurationRep (registry : Registry) (program : Program EmptyKey) (config : Config Unit EmptyKey) : Prop :=
  Nonempty (ConfigurationWitness registry program config)

end Solidity.Execution.Safety
