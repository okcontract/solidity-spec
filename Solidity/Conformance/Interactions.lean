/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.SourceFacade
import Solidity.Target
import Lean.Data.Json.FromToJson

/-! A bounded interaction generator with two interpretations of each construction:
Solidity syntax and the actual shared continuation machine. A case descriptor
selects constructors and parameters; individual cases do not contain a second,
handwritten Solidity body or an operation-specific result evaluator. The small
generator's source interpretation is an unverified source/model correspondence boundary. Each
runtime body enters through resolved program admission and an ordinary call. -/
namespace Solidity.Conformance.Interactions
open Static Core Execution Aggregates Lean
open Contract.Interaction (Word wordBytes)

private def word : SType := .uint 31
private def arrayType (location : Location) : SType := .array word none location true
private def memoryArray := arrayType .memory
private def storageArray := arrayType .storage
private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := (· == 0),
  structFields := fun identity => if identity == 0 then
    some [("a", .array word none .memory false), ("ignored", word)] else none }

/-- Products of the two interpretations. Only the constructors below build the
generated bodies; the runtime component is ordinary resolved execution syntax. -/
private structure E where
  source : String
  model : Expr EmptyKey
private structure L where
  source : String
  model : LValue EmptyKey
private structure S where
  source : String
  model : Stmt EmptyKey
private structure B where
  id : Nat
  name : String
  type : SType

private def B.model (binder : B) : Binder := {id := binder.id, type := binder.type, name := some binder.name}
private def typeSource : SType → String
  | .uint 31 => "uint256"
  | .uint 0 => "uint8"
  | .array _ _ .memory _ => "uint256[] memory"
  | .array _ _ .storage _ => "uint256[] storage"
  | .structType _ .memory _ => "Holder memory"
  | _ => "INVALID_GENERATOR_TYPE"
private def B.source (binder : B) : String := typeSource binder.type ++ " " ++ binder.name
private def n (value : Nat) : E := ⟨toString value, .literal ⟨word, BitVec.ofNat 256 value⟩⟩
private def wordLiteral (value : Nat) : E := ⟨"uint256(" ++ toString value ++ ")", (n value).model⟩
private def truth (value : Bool) : E := ⟨if value then "true" else "false", .literal ⟨.bool, value⟩⟩
private def variableExpr (binder : B) : E := ⟨binder.name, .local binder.id binder.type⟩
private def target (binder : B) : L := ⟨binder.name, .local binder.id binder.type⟩
private def arrayPlace (slot : Nat) : Place :=
  ⟨.array word none .storage false, {region := .storage 0, address := BitVec.ofNat 256 slot}⟩
private def scalarPlace (slot : Nat) : Place :=
  ⟨word, {region := .storage 0, address := BitVec.ofNat 256 slot}⟩
private def stateArray (other : Bool := false) : E :=
  ⟨if other then "other" else "values", .read (.heap (arrayPlace (if other then 1 else 0)))⟩
private def stateWord (zero : Bool := false) : E :=
  ⟨if zero then "zero" else "marker", .read (.heap (scalarPlace (if zero then 3 else 2)))⟩
private def stateTarget : L := ⟨"marker", .heap (scalarPlace 2)⟩
private def index (array offset : E) : L :=
  ⟨array.source ++ "[" ++ offset.source ++ "]", .index word array.model offset.model⟩
private def read (place : L) : E := ⟨place.source, .read place.model⟩
private def binaryExpr (token : String) (code : BinaryCode) (result : SType) (left right : E) : E :=
  ⟨"(" ++ left.source ++ token ++ right.source ++ ")", .binary code result left.model right.model⟩
private def add := binaryExpr "+" (.arithmetic .add) word
private def mul := binaryExpr "*" (.arithmetic .mul) word
private def sub := binaryExpr "-" (.arithmetic .sub) word
private def equal := binaryExpr "==" (.compare .eq) .bool
private def assign (place : L) (value : E) : E :=
  ⟨"(" ++ place.source ++ "=" ++ value.source ++ ")", .assign place.model value.model⟩
private def compound (place : L) (value : E) : E :=
  ⟨"(" ++ place.source ++ "+=" ++ value.source ++ ")", .compound (.arithmetic .add) place.model value.model⟩
private def post (binder : B) : E := ⟨binder.name ++ "++", .update (.inc true) (target binder).model⟩
private def length (array : E) : E := ⟨array.source ++ ".length", .length array.model⟩
private def push (array value : E) : E :=
  ⟨array.source ++ ".push(" ++ value.source ++ ")", .push array.model value.model⟩
private def cast (type : SType) (value : E) : E := ⟨value.source, .cast .implicit type value.model⟩
private def tuple (values : List E) : E :=
  ⟨"(" ++ String.intercalate "," (values.map E.source) ++ ")", .tuple (values.map E.model)⟩
private def conditional (condition yes no : E) : E :=
  ⟨"(" ++ condition.source ++ "?" ++ yes.source ++ ":" ++ no.source ++ ")",
    .conditional condition.model yes.model no.model⟩
private def expr (value : E) : S := ⟨value.source ++ ";", .expr value.model⟩
private def seq (statements : List S) : S :=
  ⟨String.intercalate "\n" (statements.map S.source), (statements.map S.model).foldr Stmt.seq .skip⟩
private def ret (value : E) : S := ⟨"return " ++ value.source ++ ";", .return_ (some value.model)⟩
private def declare (binder : B) (value : E) : S :=
  ⟨binder.source ++ "=" ++ value.source ++ ";", .declare [some binder.model] (some value.model)⟩
private def declareTuple (binders : List B) (value : E) : S :=
  ⟨"(" ++ String.intercalate "," (binders.map B.source) ++ ")=" ++ value.source ++ ";",
    .declare (binders.map fun binder => some binder.model) (some value.model)⟩
private def branch (condition : E) (yes no : S) : S :=
  ⟨"if(" ++ condition.source ++ "){" ++ yes.source ++ "}else{" ++ no.source ++ "}",
    .if_ condition.model yes.model no.model⟩
private def newArray : E := ⟨"new uint256[](1)", .newArray word (n 1).model⟩
private def first (array : E) := read (index array (n 0))
private def packed (a b c : E) : E := add (mul a (n 1000000)) (add (mul b (n 1000)) c)

private structure F where
  name : String
  handle : Nat
  parameters : List B
  returns : List B
  body : S
  mutability : Mutability := .nonpayable
private def F.model (function : F) : FunctionDefinition EmptyKey := {
  parameters := function.parameters.map B.model, returns := function.returns.map B.model,
  body := function.body.model, mutability := function.mutability }
private def F.source (function : F) : String :=
  "function " ++ function.name ++ "(" ++ String.intercalate "," (function.parameters.map B.source) ++
  ") internal " ++ (if function.mutability == .pure then "pure " else "") ++
  "returns(" ++ String.intercalate "," (function.returns.map B.source) ++ "){" ++ function.body.source ++ "}\n"
private def call (function : F) (arguments : List E) : E :=
  let signature := function.model.signature
  ⟨function.name ++ "(" ++ String.intercalate "," (arguments.map E.source) ++ ")",
    .call signature (.literal ⟨signature.type, some function.handle⟩) (arguments.map E.model)⟩

private def appendFunction : F :=
  let value : B := ⟨0,"value",word⟩
  {name := "appendValue", handle := 1, parameters := [value], returns := [⟨1,"r",word⟩],
   body := seq [expr (push (stateArray) (variableExpr value)), ret (n 0)]}
private def observeFunction : F :=
  let array : B := ⟨0,"a",memoryArray⟩
  let ignored : B := ⟨1,"ignored",word⟩
  {name := "observeArray", handle := 2, parameters := [array,ignored], returns := [⟨2,"r",word⟩],
   mutability := .pure, body := ret (packed (length (variableExpr array)) (first (variableExpr array)) (variableExpr ignored))}
private def recursionFunction (memory : Bool) : F :=
  let type := if memory then memoryArray else storageArray
  let depth : B := ⟨0,"depth",word⟩
  let array : B := ⟨1,"a",type⟩
  let name := if memory then "descendMemory" else "descendStorage"
  let handle := if memory then 4 else 3
  let signature : FunctionSignature := ⟨if memory then .pure else .nonpayable,
    .cons word (.cons type .nil), .cons type .nil⟩
  let recur : E := ⟨name ++ "(depth-1,a)", .call signature
    (.literal ⟨signature.type,some handle⟩) [(sub (variableExpr depth) (n 1)).model,(variableExpr array).model]⟩
  {name,handle,parameters := [depth,array],returns := [⟨2,"r",type⟩],
   mutability := if memory then .pure else .nonpayable,
   body := branch (equal (variableExpr depth) (n 0)) (ret (variableExpr array))
     (seq [expr (compound (index (variableExpr array) (n 0)) (variableExpr depth)),ret recur])}

private def topic : Word := Access.hash ("Changed(uint256,uint256)".toUTF8.toList)
private def emitChanged (seed : E) : S :=
  ⟨"emit Changed(" ++ seed.source ++ ",marker);",
    .emit [.literal ⟨word,topic⟩,seed.model] [(stateWord).model]⟩
private def failure (kind : Nat) : S :=
  match kind with
  | 0 => ⟨"assert(false);", .expr (.assert_ (truth false).model)⟩
  | 1 => ⟨"require(false);", .expr (.require_ .empty (truth false).model [])⟩
  | _ => ret (binaryExpr "/" (.arithmetic .div) word (n 1) (stateWord true))
private def mutation (seed : E) : List S :=
  [expr (push (stateArray) seed), expr (assign stateTarget (mul seed (n 10))),emitChanged seed]
private def failFunction : F :=
  let kind : B := ⟨0,"kind",word⟩
  let seed : B := ⟨1,"seed",word⟩
  {name := "mutateAndFail", handle := 5, parameters := [kind,seed], returns := [⟨2,"r",word⟩],
   body := seq (mutation (variableExpr seed) ++ [branch (equal (variableExpr kind) (n 0)) (failure 0)
     (branch (equal (variableExpr kind) (n 1)) (failure 1) (failure 2)),ret (n 0)])}
private def functions : List F :=
  [appendFunction,observeFunction,recursionFunction false,recursionFunction true,failFunction]
private def program : Program EmptyKey := ⟨functions.map fun function => (function.handle,function.model)⟩

/-- The finite descriptor grammar. Natural parameters have small exhaustive
domains below, including reduction witnesses for discrepancy minimization. -/
inductive Descriptor where
  | aliasOrder (memory aliases : Bool) (seed delta : Nat)
  | conversionEffect (stage seed delta : Nat)
  | recursiveReturn (memory other : Bool) (depth : Nat)
  | mutationFailure (helper : Bool) (kind seed : Nat)
  deriving DecidableEq, Repr

private def Descriptor.family : Descriptor → String
  | .aliasOrder .. => "aliasing_effect_order"
  | .conversionEffect .. => "conversion_effects"
  | .recursiveReturn .. => "recursion_reference_returns"
  | .mutationFailure .. => "failure_storage_mutation"
private def Descriptor.parameters : Descriptor → List Nat
  | .aliasOrder memory aliases seed delta => [if memory then 1 else 0,if aliases then 1 else 0,seed,delta]
  | .conversionEffect stage seed delta => [stage,seed,delta]
  | .recursiveReturn memory other depth => [if memory then 1 else 0,if other then 1 else 0,depth]
  | .mutationFailure helper kind seed => [if helper then 1 else 0,kind,seed]
def Descriptor.name (descriptor : Descriptor) : String :=
  descriptor.family ++ "_" ++ String.intercalate "_" (descriptor.parameters.map toString)

private def initializeArrays (memory : Bool) (seed : Nat) : List S :=
  if memory then
    [declare ⟨1,"a",memoryArray⟩ newArray,declare ⟨3,"otherA",memoryArray⟩ newArray,
     expr (assign (index (variableExpr ⟨1,"a",memoryArray⟩) (n 0)) (n seed)),
     expr (assign (index (variableExpr ⟨3,"otherA",memoryArray⟩) (n 0)) (n (seed+1)))]
  else
    [expr (push (stateArray) (n seed)),expr (push (stateArray true) (n (seed+1))),
     declare ⟨1,"a",storageArray⟩ (stateArray),declare ⟨3,"otherA",storageArray⟩ (stateArray true)]
private def aliasBody (memory aliases : Bool) (seed delta : Nat) : S :=
  let type := if memory then memoryArray else storageArray
  let a : B := ⟨1,"a",type⟩
  let b : B := ⟨2,"b",type⟩
  let i : B := ⟨0,"i",word⟩
  seq (initializeArrays memory seed ++ [declare b (variableExpr (if aliases then a else ⟨3,"otherA",type⟩)),
    declare i (n 0),expr (compound (index (variableExpr a) (post i)) (compound (index (variableExpr b) (n 0)) (n delta))),
    ret (packed (first (variableExpr a)) (first (variableExpr b)) (variableExpr i))])
private def conversionBody (stage seed delta : Nat) : S :=
  let a : B := ⟨0,"a",memoryArray⟩
  let ignored : B := ⟨1,"ignored",word⟩
  let append := call appendFunction [n delta]
  let initialStatements := [expr (push (stateArray) (n seed))]
  if stage == 0 then
    let group := SType.tuple (.cons memoryArray (.cons word .nil))
    let choice := cast group (conditional (truth true) (tuple [stateArray,append])
      (tuple [stateArray true,wordLiteral 9]))
    seq (initialStatements ++ [declareTuple [a,ignored] choice,
      ret (packed (length (variableExpr a)) (first (variableExpr a)) (variableExpr ignored))])
  else if stage == 1 then
    let holder : B := ⟨0,"h",.structType 0 .memory true⟩
    let value : E := ⟨"Holder(" ++ (stateArray).source ++ "," ++ append.source ++ ")",
      .structConstructor 0 [(stateArray).model,append.model] [0,1]⟩
    let field : E := ⟨"h.a",.read (.field (.array word none .memory false) (variableExpr holder).model 0)⟩
    let ignoredField : E := ⟨"h.ignored",.read (.field word (variableExpr holder).model 1)⟩
    seq (initialStatements ++ [declare holder value,ret (packed (length field) (first field) ignoredField)])
  else seq (initialStatements ++ [ret (call observeFunction [stateArray,append])])
private def recursiveBody (memory other : Bool) (depth : Nat) : S :=
  let type := if memory then memoryArray else storageArray
  let selected : B := ⟨if other then 3 else 1,if other then "otherA" else "a",type⟩
  let result : B := ⟨2,"r",type⟩
  seq (initializeArrays memory 7 ++ [declare result (call (recursionFunction memory) [n depth,variableExpr selected]),
    expr (compound (index (variableExpr result) (n 0)) (n 3)),
    ret (packed (first (variableExpr selected)) (first (variableExpr result)) (length (variableExpr result)))])
private def failureBody (helper : Bool) (kind seed : Nat) : S :=
  if helper then ret (call failFunction [n kind,n seed])
  else seq (mutation (n seed) ++ [failure kind,ret (n 0)])
private def Descriptor.body : Descriptor → S
  | .aliasOrder memory aliases seed delta => aliasBody memory aliases seed delta
  | .conversionEffect stage seed delta => conversionBody stage seed delta
  | .recursiveReturn memory other depth => recursiveBody memory other depth
  | .mutationFailure helper kind seed => failureBody helper kind seed

def descriptors : List Descriptor :=
  ([false,true].flatMap fun memory => [false,true].flatMap fun aliases =>
    [1,7].flatMap fun seed => [1,3].map fun delta => .aliasOrder memory aliases seed delta) ++
  ([0,1,2].flatMap fun stage => [1,7].map fun seed => .conversionEffect stage seed 2) ++
  ([false,true].flatMap fun memory => [false,true].flatMap fun other =>
    [0,2].map fun depth => .recursiveReturn memory other depth) ++
  ([false,true].flatMap fun helper => [0,1,2].flatMap fun kind =>
    [1,7].map fun seed => .mutationFailure helper kind seed)

private def policyChoice (policy : Nat) (config : Config Unit EmptyKey) : Nat :=
  match config.task with
  | .eval (.compound _ (.index _ (.local 1 _) _) _) => policy % 3
  | .collect pending _ _ => if policy / 3 % 2 == 1 then pending.length-1 else 0
  | _ => 0
private def execute (descriptor : Descriptor) (policy : Nat) :=
  let state : MachineState Unit := {
    external := (),heap := MemoryOps.initialHeap,materializationRemaining := 100000 }
  let entry : FunctionDefinition EmptyKey := {
    parameters := [],returns := [⟨100,word,none⟩],body := descriptor.body.model }
  let resolved : Program EmptyKey := ⟨program.functions ++ [(6,entry)]⟩
  let expression : Expr EmptyKey := .call entry.signature (.literal ⟨entry.signature.type,some 6⟩) []
  do
    let config ← SourceFacade.prepareExpression registry {} resolved state expression
    return Execution.run (fun _ config => Machine.step physicalBackend registry {} resolved (policyChoice policy config) config)
      20000 [] config
private def logJson (event : Contract.Interaction.Event) : Json := Json.mkObj [
  ("emitter",toJson "self"),("topics",toJson (event.topics.map fun value => toString value.toNat)),
  ("data",toJson (event.data.map UInt8.toNat))]
private def observed : Aggregates.Result (Execution (Config Unit EmptyKey) (Observation Unit)) → Json
  | .error failure => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson ("admission: " ++ reprStr failure))]
  | .ok (.finished (.returned [.atom value] state)) => match encodeMemory value.type value.value with
    | .ok value => Json.mkObj [("status",toJson "returned"),("word",toJson (toString value.toNat)),
        ("logs",toJson (state.heap.execution.world.logs.map logJson))]
    | .error _ => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson "scalarEncoding")]
  | .ok (.finished (.failed (.panic code) state)) => Json.mkObj [("status",toJson "reverted"),
      ("bytes",toJson ((Contract.panic code).map UInt8.toNat)),
      ("logs",toJson (state.heap.execution.world.logs.map logJson))]
  | .ok (.finished (.failed (.revert bytes) state)) => Json.mkObj [("status",toJson "reverted"),
      ("bytes",toJson (bytes.map UInt8.toNat)),("logs",toJson (state.heap.execution.world.logs.map logJson))]
  | .ok (.finished (.inconclusive failure _)) => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson (reprStr failure))]
  | .ok (.exhausted _ _) => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson "exhausted")]
  | _ => Json.mkObj [("status",toJson "modelFailure"),("reason",toJson "unexpectedObservation")]
private def caseJson (descriptor : Descriptor) : Json :=
  let policies := match descriptor with | .aliasOrder .. => [0,1,2,3,4,5] | _ => [0,3]
  let probes : List Word := [0,1,2,3,Access.hash (wordBytes 0),Access.hash (wordBytes 1)]
  Json.mkObj [("name",toJson descriptor.name),("body",toJson descriptor.body.source),
    ("mutability",toJson "nonpayable"),("strategies",toJson policies),
    ("generation",Json.mkObj [("family",toJson descriptor.family),("parameters",toJson descriptor.parameters)]),
    ("observeLogs",toJson (match descriptor with | .mutationFailure .. => true | _ => false)),
    ("storageProbes",toJson (probes.map fun value => toString value.toNat)),
    ("outcomes",toJson (policies.map fun policy => observed (execute descriptor policy)))]

private def rejection : Json :=
  let bad : Stmt EmptyKey := .expr (.compound (.arithmetic .add) (.local 0 (.uint 0))
    (.literal ⟨.uint 1,1#16⟩))
  let state : MachineState Unit := {external := (),locals := [[(0,⟨.uint 0,some 1#8⟩)]]}
  let modelError := match SourceFacade.prepareStatement registry {} program state bad with
    | .error .rejected => toJson "staticRejected" | _ => Json.null
  Json.mkObj [("name",toJson "narrowing_control"),("body",toJson "uint8 a=1; a+=uint16(1); return a;"),
    ("modelError",modelError),("diagnostics",toJson [Json.mkObj [("type",toJson "TypeError"),
      ("errorCode",toJson "7366"),("message",toJson "Operator += not compatible with types uint8 and uint16.")]])]

def json : Json := Json.mkObj [
  ("solidityVersion",toJson Target.solidityVersion),("referenceCompilerVersion",toJson Target.referenceCompilerVersion),
  ("evmVersion",toJson Target.evmVersion),("sourceModelPairing",toJson "generatedInteractionConstructors;manualSourcePairing"),
  ("generatorSchema",toJson "solidity-interactions-v1"),
  ("declarations",toJson ("uint256[] values; uint256[] other; uint256 marker; uint256 zero;\n" ++
    "struct Holder {uint256[] a; uint256 ignored;} event Changed(uint256 indexed seed,uint256 value);\n" ++
    String.join (functions.map F.source))),
  ("cases",toJson (descriptors.map caseJson)),("rejections",toJson [rejection]),("modelChecks",toJson ([] : List Json))]

end Solidity.Conformance.Interactions

def main : IO Unit := IO.println Solidity.Conformance.Interactions.json.compress
