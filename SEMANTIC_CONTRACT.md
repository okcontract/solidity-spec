# Semantic contract: Solidity 0.8.36 / Cancun

`Solidity.Observation` defines the observation records and relations used by
this model's source/target interfaces. The target is pinned in `target.json`.

## Release domain and reference authority

The package contains resolved scalar and aggregate operations, an effectful
continuation machine, typed certificate interfaces and partial Cancun target
semantics. Inputs include explicit nominal registries, typed trees, function
tables and represented initial states. [SCALARS.md](SCALARS.md),
[SAFETY.md](SAFETY.md) and [PILOT.md](PILOT.md) state the corresponding input
contracts and proved conclusions.

The independently maintained language documentation, upstream type rules and
Cancun execution reference are pinned in [references/lock.json](references/lock.json).
Reference snapshots retain their upstream source identities and licenses.
The retained type/contract documentation indexes are labeled `indexOnly`;
their unbundled chapters are not part of the reference corpus. A content hash
establishes identity, not semantic adequacy.

The [paper](paper/solidity-semantics.pdf) states the kernel trust assumptions,
source/artifact-binding conditions and scope of the formalization. Source
syntax, model execution and exact artifact preservation are distinct contracts.

## Outcomes and observations

`Halt` distinguishes returned bytes, reverted bytes and EVM exceptional halt.
A Solidity panic is its ABI-encoded revert bytes; an observer cannot distinguish
it from an explicit revert producing the same bytes. Parse/type rejection,
unsupported modeling, invalid context, compiler failure and interpreter
exhaustion are not halts. `Attempt` and `Corresponds` prevent two exhausted or
unsupported runs from witnessing preservation. A separate progress/adequacy
proof must establish completion in the claimed domain.

`Record` observes the halt, balances/nonces/code, account existence, persistent
and transient storage, logs, account lifecycle and ordered call/creation/log
actions. `Lifecycle` records creation, touching and pending deletion; these are
needed for Cancun creation/deletion rules and are not inferred from an empty
code string or zero balance. `World.other` is not an escape hatch:
clients must show that no relevant effect is hidden in that projection.
Storage account keys in the observation are canonical 160-bit addresses.

`Rel functional` compares invocation state and ordered actions. `Rel metered`
also compares gas remaining, refunds, gas readings and access warmth.
`Rel representation` additionally compares the bound executing/creation bytes
and immutable values. `TraceRel` compares successive invocations; transaction
boundaries must be identified by the client. These relations are equivalences
on completed records and the stronger profiles imply weaker ones.

The functional profile requires a justified `Admissible` capability summary:
no gas-sensitive behavior, code introspection, raw representation observations
or unknown foreign context. Metered permits gas sensitivity but still excludes
unmodeled representation dependencies. Representation permits those features
only with an actual execution/representation theorem. `Admissible` is a
restriction on a proved summary, not a trusted Boolean analysis result. Internal
helper calls need not be external `Action.enterCall` events. Raw PC, memory,
stack or code observations in assembly require a bound target representation.

Exact gas and code equality are contracts for one bound compilation. Optimizer
variants need not have equal costs or byte strings. A source model with no
costed lowering cannot claim `Rel metered` by choosing arbitrary gas answers.
Out-of-gas is exceptional halt, never interpreter exhaustion. Functional
preservation requires resource adequacy for both completed executions; it does
not erase an actual target out-of-gas into successful source execution.

## Invocation and transaction boundaries

A callee failure restores its entry snapshot of storage, balances, account
creation/code, lifecycle, logs and transient storage. `failedInvocation`
records that snapshot; `failedInvocation_restores` is the projection theorem,
not a proof that every machine transition implements rollback. Consumed gas
is not restored. Refund/warmth rollback must follow the pinned EVM frame rules,
not a blanket copy of every field. A caught revert restores the callee boundary,
not its caller's earlier writes. A parent revert rolls back successful children.

The root boundary begins **after transaction admission and intrinsic-gas
accounting, before message execution**. The transaction sender nonce and gas
escrow already charged by admission are outside the invocation snapshot. Root
failure does not undo those admission effects. Fee settlement, refund caps,
base/blob fee burning and miner payments are outside this release profile;
their input/output interface is gas consumed, refund counter, effective prices
and final message outcome. Whole-transaction equivalence is outside this profile. Transient storage starts empty at root entry and is
cleared at transaction completion, including failure, never on a successful
nested return. `transaction_transient_cleared` states the clear operation.

## Environment contract

A theorem must quantify over the same explicit, valid context on both sides:
canonical caller/origin/recipient/coinbase addresses; call value and calldata;
static flag, depth, remaining gas; chain ID; block number, timestamp, gas limit,
base fee and `prevrandao`; effective transaction gas price; blob versioned hashes
and blob base fee; recent block hashes; pre-state accounts and storage; and the
initial access list. Word quantities have their specified 256-bit bounds,
nonces 64-bit bounds and addresses 160-bit bounds. Depth starts within the EVM
limit, gas is nonnegative and within the transaction/block allocation, and
value transfer must not invent balances or overflow them. Static propagation,
call ownership and creation collisions are execution rules, not caller wishes.

The chain supplies an authenticated header/history and an admitted transaction.
The header/transaction pair must satisfy Cancun's fork/admission rules in the
pinned execution specification (including blob version and count restrictions,
fee affordability, nonce, intrinsic gas and block limits). This project does
not prove consensus/header validity. BLOCKHASH's 256-block window, unavailable
hashes, BLOBHASH's out-of-range zero, and BLOBBASEFEE's fee calculation are
execution obligations; supplying arbitrary per-query answers is insufficient.
The environment remains fixed during an invocation except for explicitly
modeled world/resource transitions. Foreign code is executed in the same world
or satisfies a named, quantified context contract. An arbitrary callback is
conditional reasoning, not closed Solidity semantics.

## Refinement obligation

For an admitted source bundle/settings, exact bound creation/runtime artifact,
related initial representations and an admissible environment/profile, every
completed target trace must have a permitted source trace related by
`TraceRel`. The quantification is over target behavior, not one selected test
trace. Initialization, linking, constructor arguments and installed runtime
are included in the artifact relation. Source operand-order choices are the
permitted relation, independently of an interpreter's strategy.

Elaboration correctness, representation correctness, execution simulation,
resource adequacy, progress and context composition are separately discharged
premises. None may be named merely “Solidity behavior” or “compiler correctness.”
A finite test suite cannot discharge a universal premise. Infinite execution
requires a separate divergence-sensitive relation; finite `TraceRel` makes no
termination or infinite-trace claim. Full transaction settlement, consensus,
networking and cryptographic security are outside this profile. Cryptographic
functions still require concrete functional meanings; Keccak injectivity is
not assumed.
