/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Execution.Safety.TypedPackets

namespace Solidity.Execution.Safety.TypedPackets.Tests
open Static Aggregates

private def program : Program EmptyKey := ⟨[]⟩
private def heap : Heap := MemoryOps.initialHeap
private def word : Datum := .atom ⟨.uint 31,7#256⟩
private def boolean : Datum := .atom ⟨.bool,true⟩
private def array : Datum := .atom ⟨WordArena.arrayType,Copy.memoryReference heap 96⟩
private def nested : Datum := .tuple [word,boolean]
private def types : List SType := [.uint 31,.bool,WordArena.arrayType,.tuple (.cons (.uint 31) (.cons .bool .nil))]
private def completed : List (Nat × Datum) := [(2,array),(0,word),(3,nested),(1,boolean)]

private theorem word_rep : DatumRep program heap [] word (.uint 31) := .atom (.word _ _ _ _)
private theorem boolean_rep : DatumRep program heap [] boolean .bool := .atom (.boolean _ _ _ _)
private theorem array_rep : DatumRep program heap [] array WordArena.arrayType := .atom (.emptyArray true)
private theorem nested_rep : DatumRep program heap [] nested (.tuple (.cons (.uint 31) (.cons .bool .nil))) :=
  .tuple (.cons word_rep (.cons boolean_rep .nil))

private theorem finished : CollectRep program heap [] (fun _ => True) types [] completed := by
  refine ⟨by simp,?_,?_⟩
  · intro index value member
    simp only [completed,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same <;> cases same
    · exact array_rep
    · exact word_rep
    · exact nested_rep
    · exact boolean_rep
  · decide +kernel

example : PacketRep program heap [] (Machine.ordered completed) (Types.ofList types) := finished.finish
example : (Machine.ordered completed).map Datum.type = types := finished.finished_types
example : Machine.ordered completed = [word,boolean,array,nested] := rfl
example : completed.length = types.length := by simpa using finished.length

-- Distinct source positions may contain the same reference. This is not a
-- fresh-tree or pairwise payload-separation hypothesis.
example : PacketRep program heap [] (Machine.ordered [(1,array),(0,array)])
    (.cons WordArena.arrayType (.cons WordArena.arrayType .nil)) := by
  apply CollectRep.finish (types := [WordArena.arrayType,WordArena.arrayType])
    (typing := fun _ : Expr EmptyKey => True)
  refine ⟨by simp,?_,?_⟩
  · intro index value member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same <;> cases same <;> exact array_rep
  · decide +kernel

-- Duplicate/dropped indexed occurrences cannot satisfy the invariant even
-- when both source operands happen to have the same scalar type.
example : ¬(completedTypes [(0,word),(0,word)]).Perm (indexed [.uint 31,.uint 31]) := by
  decide +kernel
example : ¬(completedTypes [(0,word)]).Perm (indexed [.uint 31,.bool]) := by decide +kernel

private def effectful : List (Expr EmptyKey) :=
  [.update (.inc true) (.local 0 (.uint 31)),.assign (.local 1 .bool) (.literal ⟨.bool,true⟩)]

example : CollectRep program heap [] (fun _ => True) (effectful.map Expr.type)
    (effectful.zipIdx.map fun (expression,index) => (index,expression)) [] :=
  CollectRep.initial _ (by simp)

example : ∃ rest, Machine.pick 1
    (effectful.zipIdx.map fun (expression,index) => (index,expression)) =
      some ((1,.assign (.local 1 .bool) (.literal ⟨.bool,true⟩)),rest) := by
  exact ⟨[(0,.update (.inc true) (.local 0 (.uint 31)))],rfl⟩

end Solidity.Execution.Safety.TypedPackets.Tests
