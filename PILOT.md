# Aliasing, evaluation order and rollback pilots

This pilot quantifies over input words, failure flags and related initial
states. Two initialized memory references alias one represented length-one
`uint256[]`. An ordinary entry call invokes an actual internal helper, which
writes the array payload and persistent slot zero. The caller reads through
the second alias, then returns the input word or reverts. The proofs execute
parameter binding, named-result initialization, helper invocation, result
transfer and caller restoration through the shared continuation machine.

[`AliasCallRollback.lean`](Solidity/Pilots/AliasCallRollback.lean) proves the
actual checked source run and its relation to a manually paired, hand-authored
23-byte Cancun fragment. Target memory has six active words, with bytes beyond
that extent zero. Actual metered target execution supplies the adequate-gas
observation and insufficient-gas rollback, including the complete target world
and transaction snapshot. Both exported refinements retain the exact equation
`gasRemaining = gas - used` whenever `needed ≤ gas`, with `used ≤ needed`.
Their source/target relation compares functional observations; this additional
equation characterizes target consumption without assigning EVM gas to the source.
Unrelated source slots, owners and disjoint memory
packets have explicit frame theorems. No successful execution or preservation
claim is supplied as an input premise.

[`AliasCallRollbackResources.lean`](Solidity/Pilots/AliasCallRollbackResources.lean)
connects the pilot to [the generic safety theorem](SAFETY.md). The exact source
trace completes within 160 transitions with choices `[]` for every
materialization allowance, including the default 4096. The generic theorem
composes with that same execution at `B ≥ 161*C`. Arbitrary-choice prefix safety
requires `B ≥ (steps+1)*C`, aggregate fuel 128 and no host continuation limit.
These allowances measure host work, separately from target gas. Generic final
packet typing is existential; the exact pilot additionally proves its returned
word. A nonemptiness theorem constructs related represented inputs for every
persistent world, owner, word and flag. A negative fixture confirms that the
default allowance does not meet the conservative uniform bound.

[`AliasCallRollbackGroupTests.lean`](Solidity/Pilots/AliasCallRollbackGroupTests.lean)
also applies actual prefix safety to `(a[0] = value) + b[0]` under every child
schedule. It permits different returned values and source overflow panic.

This is a supplied-entry memory relation and a fixed fragment proof. It does
not establish compiler emission, a deployment/allocation prefix, source-byte
correspondence or general lowering preservation.

With the pinned Lean toolchain, from the root of this package:

```sh
lake build Solidity.Pilots.AliasCallRollbackResourceTests Solidity.Pilots.AliasCallRollbackGroupTests
```

From the package root, check the pilot and foundation theorem contracts together:

```sh
python3 scripts/check_theorems.py \
  --lean-bin /path/to/lean-4.29.0/bin \
  --output /private/tmp/new-semantics-theorem-audit
```

Use the normal audit command; `--record-contracts` only records expectations for
review and cannot establish acceptance. Fresh imported kernel replay remains a
separate gate.

## Order-sensitive source/target refinement

[`OrderAliasRollbackRefinement.lean`](Solidity/Pilots/OrderAliasRollbackRefinement.lean)
connects two actual machine schedules to two fixed Cancun artifacts (25 and
111 bytes). A prepared function body writes storage, evaluates
`(a[0] = x) + b[0]` through two references to one initially zero array cell,
then returns the result or explicitly reverts.

Reading first returns `x`; writing first returns `x+x` when it fits and panics
with `0x11` otherwise. At `x = 2^255`, the schedules therefore disagree on
success versus rollback. The theorem quantifies over every word, failure flag,
related initial world, and host-work allowance, including zero. It derives the
actual source run with a transition allowance of 80 and its permitted-execution
witness. No source execution or desired target correspondence is assumed.

Both raw target traces determine adequate gas and exact consumption. The
refinement preserves status, return/revert bytes and related persistent state;
source failure restores the entry state, and target revert or insufficient gas
restores the complete world and transaction snapshot. Source admission is checked
for the prepared body with its expected return binder. Its entry relation is
inhabited for arbitrary persistent worlds. Negative controls reject a wrapping
zero result and a target that returns revert bytes while retaining its write.

These are hand-authored artifacts for a supplied entry relation. The theorem
covers neither source elaboration nor compiler emission. The new body has no
internal call or aggregate deep copy; internal-call composition is established
by the separate pilot above. External copying and call interactions are tested
by the independent [conformance corpus](CONFORMANCE.md).

```sh
lake build Solidity.Pilots.OrderAliasRollbackTests
```
