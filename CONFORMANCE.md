# External conformance checks

The compatibility profile is Solidity `0.8.36+commit.8a079791`, Cancun,
`viaIR: true`, with optimization disabled and enabled at 200 runs.

From this package, run:

```sh
python3 scripts/check_conformance.py \
  --solc /path/to/solc-0.8.36 \
  --lean-bin /path/to/lean-4.29.0/bin \
  --output /tmp/new-solidity-conformance-run
```

The output directory must be new. Anvil must be on `PATH`, or supplied with
`--anvil`. The runner starts a temporary local Cancun node; it does not access
a remote chain. Python's standard library is sufficient.

Fourteen manually paired cases exercise aliased operand ordering, aggregate
copy timing, compound destination capture, overlapping tuple assignments,
internal calls, checked overflow, and rollback. The runner executes the actual
Lean machine and checks admission before compiling Solidity. Target outcomes
must belong to the finite set of exported permitted schedule witnesses. That
set need not enumerate every possible schedule: a mismatch requires examining
the pairing and schedule coverage before concluding that the semantics differ.

Three static rejection controls compare compiler diagnostics with direct
`Admission.checkFunction` rejections and retain runtime model rejection separately.
Each control also checks admission with the invalid body in an unreachable branch;
raw execution of that variant must return zero, demonstrating why execution alone
cannot establish static rejection. Two model resource controls distinguish host
exhaustion from source revert. Unsupported execution, failed admission, compiler
rejection, RPC errors, host exhaustion, target-resource failure, and runtime revert
remain separate outcomes. Target-resource failures have their own
`targetResourceFailures` counter and fail the check; the current `Machine.step`
corpus does not produce them.

Each runtime probe uses `eth_call` against unchanged initial contract storage.
Reverting probes additionally run as transactions: their receipt must report
failure with no logs, and the selected storage slots must remain unchanged.
This is a bounded rollback observation, not complete-world equivalence.

The three aggregate-copy probes are also compiled with `viaIR: false`, with
both optimizer settings. These are explicit boundary controls: legacy returns
length one for construction and internal calls, and panics with `0x32` for the
indexed struct fixture. IR returns lengths two and the encoded result 514.
Legacy observations must disagree with the IR witness set; they are not counted
as supported-profile conformance successes.

The run retains source, exact Standard JSON requests and compiler responses,
tool identities and hashes, RPC observations, process exit codes, and a report
bound to the package inputs. Successful execution establishes evidence for this
corpus and configuration. It does not prove the manual source/model pairing,
general compiler correctness, or generic safety for every operational feature.
