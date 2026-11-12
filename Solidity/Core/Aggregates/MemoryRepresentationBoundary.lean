/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Solidity.Core.Aggregates.Representation.Base

/-! Typed memory correspondence constrains headers, used bytes, pointer cells
and scalar packets. Byte padding and unallocated fringe are unconstrained.
The production storage-byte encoder can retain dirty padding, whereas the
canonical source constructor zeroes it. Both represent the same typed value;
they are not equal raw-memory states. Raw-memory observations require an
explicit typed/Yul representation relation and artifact-specific packet
correspondence. These witnesses establish typed-value correspondence only. -/
namespace Solidity.Aggregates.Copy
open Static
open Contract.Interaction (Word wordBytes)

theorem TreeRep.bytes_preserved
    (tree : TreeRep registry before lower type address (.bytes string values))
    (extent : after.allocated address.toNat (32+values.length) = true)
    (header : after.execution.memory.read address.toNat 32 = before.execution.memory.read address.toNat 32)
    (payload : after.execution.memory.read (address.toNat+32) values.length =
      before.execution.memory.read (address.toNat+32) values.length) :
    TreeRep registry after lower type address (.bytes string values) := by
  cases tree with
  | bytes string pointer address values base bounded _ oldHeader oldPayload =>
      exact .bytes string pointer address values base bounded extent
        (header.trans oldHeader) (payload.trans oldPayload)

/-- Writing only padding or fringe preserves the byte object's represented
value. Separation is from actual header and used-payload ranges, not from its
entire allocation; no promise is made about other objects at the written site. -/
theorem TreeRep.bytes_padding_write
    (tree : TreeRep registry heap lower type address (.bytes string values))
    (packet : List UInt8) (destination : Nat)
    (header : address.toNat+32 ≤ destination ∨ destination+packet.length ≤ address.toNat)
    (payload : address.toNat+32+values.length ≤ destination ∨
      destination+packet.length ≤ address.toNat+32) :
    TreeRep registry (MemoryOps.snapshotCopy heap destination packet)
      lower type address (.bytes string values) := by
  have extent : heap.allocated address.toNat (32+values.length) = true := by
    cases tree with | bytes _ _ _ _ _ _ allocated _ _ => exact allocated
  exact tree.bytes_preserved extent
    (MemoryOps.snapshotCopy_frame heap destination packet address.toNat 32 header)
    (MemoryOps.snapshotCopy_frame heap destination packet (address.toNat+32) values.length payload)

namespace MemoryRepresentationBoundary

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private def registry : Registry := {
  enumerations := fun _ => none, valueTypes := fun _ => none,
  contracts := fun _ => none, structures := fun _ => false }

private def canonical (values : List UInt8) : Heap :=
  let heap := MemoryOps.initializeBytes MemoryOps.initialHeap
    (32+MemoryOps.roundedSize values.length)
  let heap := MemoryOps.snapshotCopy heap 128 (wordBytes (BitVec.ofNat 256 values.length))
  MemoryOps.snapshotCopy heap 160 values

private theorem canonical_one_rep :
    TreeRep registry (canonical [0x11]) 128 (.bytes .memory true) 128 (.bytes false [0x11]) := by
  apply TreeRep.bytes false true 128 [0x11] <;> decide +kernel

private def nativeDirtySuffix : Heap := MemoryOps.snapshotCopy (canonical [0x11]) 161 [0xff]

theorem native_dirty_suffix_admissible :
    TreeRep registry nativeDirtySuffix 128 (.bytes .memory true) 128 (.bytes false [0x11]) :=
  canonical_one_rep.bytes_padding_write [0xff] 161 (by decide) (by decide)

/-- Deliberate negative boundary: typed correspondence does not entail exact
raw suffix equality, and must not be reported as such. -/
theorem canonical_source_differs_from_native_raw_suffix :
    (canonical [0x11]).execution.memory.read 160 32 ≠ nativeDirtySuffix.execution.memory.read 160 32 := by
  decide +kernel

private theorem canonical_empty_rep :
    TreeRep registry (canonical []) 128 (.bytes .memory true) 128 (.bytes false []) := by
  apply TreeRep.bytes false true 128 [] <;> decide +kernel

private def nativeEmptyFringe : Heap :=
  MemoryOps.snapshotCopy (canonical []) 160 (wordBytes (BitVec.ofNat 256 (0xaa*2^248)))

theorem native_empty_fringe_admissible :
    TreeRep registry nativeEmptyFringe 128 (.bytes .memory true) 128 (.bytes false []) :=
  canonical_empty_rep.bytes_padding_write _ 160 (by decide) (by decide)

theorem native_empty_fringe_unallocated : nativeEmptyFringe.allocated 160 32 = false := by decide +kernel

theorem canonical_source_differs_from_native_empty_fringe :
    (canonical []).execution.memory.read 160 32 ≠ nativeEmptyFringe.execution.memory.read 160 32 := by
  decide +kernel

end MemoryRepresentationBoundary
end Solidity.Aggregates.Copy
