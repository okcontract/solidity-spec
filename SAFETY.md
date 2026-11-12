# Admitted configurations and finite prefixes

Import `Solidity.Execution.Safety` for the first admitted-state safety profile.
The comprehensive `Solidity` umbrella also exports it. This connects actual
resolved admission to actual machine transitions; the earlier generic finite-run
soundness/completeness theorems remain separate.

## Independent invariant

[`Profile.lean`](Solidity/Core/Execution/Safety/Profile.lean) defines the supported
syntax independently of execution. Successful equations from the existing
`Admission` checker supply its operator, transfer, scope and signature evidence.
The profile includes:

- All executable scalar types, admitted unary/binary operations and scalar
  casts, and closed internal-function values, including mutability widening.
- Canonical `uint256[]` memory objects, shared empty references, aliases,
  allocation, length/index access and element writes. Eager siblings can mutate
  and read the same physical object in every permitted child order.
- Physical `uint256` persistent/transient storage places and their real
  read-only failure outcomes.
- Tuples, conditionals, lazy Boolean operators, assignments, compound assignments,
  increment/decrement, all loop forms, break/continue, arithmetic regions, empty
  `assert`/`require` payloads and explicit reverts.
- Closed recursive and named internal calls, scalar/memory-reference parameters
  and results, named defaults, and singleton declaration prefixes in blocks.
  A `for` post is an expression or skip.

This first profile excludes other aggregate families, storage/calldata reference
locals, tuple-pattern assignments, inline/struct construction, mutation of array
length, aggregate/event/error encoding, assembly and linked calls. Their existing
operational definitions are not promoted into this safety result. User-defined
value wrapping/unwrapping, external-function address/selector projections and
`delete` are also outside this profile.

[`Configuration.lean`](Solidity/Core/Execution/Safety/Configuration.lean) connects
admitted syntax to initialized typed local cells, closed handles, physical heap
packets, captured targets, operand partitions and every saved continuation.
Saved caller cells and the invocation checkpoint are represented too. The
environment relation preserves typed lookup after every lexical suffix drop,
including the checker's forward and runtime's reverse binder orders.
`ModeKind` excludes a mode frame applied to a target; the machine only handles
that frame for values and control signals. These are structural/representation
facts. No field assumes successful evaluation, reachability or a safe-step
callback.

Initial `configuration_expression` and `configuration_statement` derive this
invariant from actual successful entry admission, the structural profile, a
closed admitted function table and the independent initial state representation.
Admission alone cannot inspect physical packets or establish handle closure.

## Actual progress and resource adequacy

[`Progress.lean`](Solidity/Core/Execution/Safety/Progress.lean) proves
`configuration_progress` and `configuration_preservation` for the actual
`Machine.step`, using constructive primitive, call, scope and continuation
proofs. A step either preserves the invariant and checkpoint or produces a
represented source observation. Inconclusive observations and primitive
suspension do not satisfy that contract.

Aggregate fuel is `a + 2` for arbitrary natural `a`, and
`hostContinuationLimit = none`. Materialization uses a separate conservative
one-step bound:

```text
C = cost(2^256 - 1) = 66 * (2^256 - 1) + 96
prefixMaterializationBound(n) = (n + 1) * C
```

Progress/preservation require `C ≤ current.materializationRemaining`.
The finite-prefix theorem requires `(n + 1) * C ≤ initial.materializationRemaining`.

Only new word-array construction consumes this allowance in the profile.
Actual source allocation failures remain `Panic(0x41)`; host exhaustion is not
reclassified as a source failure. This uniform bound is intentionally large.
It is a logical host-work allowance, not EVM gas, physical host-memory
availability or a practical default budget.

[`FinitePrefixes.lean`](Solidity/Core/Execution/Safety/FinitePrefixes.lean)
proves `execute_prefix` by induction over the actual runner. The extra step in
the bound covers its inspection even at transition fuel zero. For every choice
sequence, a completed prefix has `ObservationRep`; an exhausted prefix retains
`ConfigurationRep`, the original checkpoint and at least `C` work allowance.
`checked_expression_prefix`/`checked_statement_prefix` and their finished
corollaries connect the result to the indexed checked-entry boundary.

`ObservationRep` permits represented return packets or actual source failures
with exact checkpoint rollback. Packet types are existential in this first
terminal predicate; it does not separately index the final packet by the
initial root's declared result type. The result is prefix safety for the stated
domain, not termination, full Solidity adequacy or compiler preservation.
