# Theorem contracts

[`theorems.json`](theorems.json) records selected theorem roots, their expected
elaborated statements, complete kernel-statement hashes and permitted transitive
axioms. Its `sourceClosure` binds the imported project definitions, build inputs
and audit implementation by package-relative path and SHA-256. These contracts
specify a selected interface with explicit premises.

From this package, with the pinned Lean toolchain:

```sh
make replay
```

The release command builds the package, runs the audit's negative controls,
compares the compiled declarations and source closure with the manifest, then
uses `leanchecker --fresh` to replay the comprehensive library and pilot/scalar
fixture roots. A changed statement, definition source, axiom allowance, missing
root or changed import closure fails the manifest gate. Source identity includes
comments; it is intentionally stricter than logical equivalence.

The gate also runs independently:

```sh
python3 scripts/check_theorems.py --output /tmp/new-theorem-audit
```

An optional `--lean-bin /path/to/lean-4.29.0/bin` selects installed binaries.
The output directory must be new; omitting it creates a temporary directory.
Raw audit/build output, process exit codes and input identities are retained.
Each root must be a theorem. Its complete logical dependency closure must be
safe and total, and its transitive axioms must fit that root's allowance.
Imported inputs and the manifest must stay unchanged during checking.

`--record-contracts` explicitly records changed statements, hashes, axioms and
source closure for review. `--record-source-closure` updates only source identity
and requires compiled statements and axiom allowances to match already.
Neither recording mode is an acceptance run: inspect the diff, then run the
ordinary gate. The release command never records or repairs its own expectations.

The statement hash alone does not bind the bodies of named predicates. The
source closure supplies that additional binding; fresh kernel replay checks
proof terms independently of elaboration. Together they still rely on the
pinned Lean toolchain and build/load path. They do not establish Solidity
conformance, source elaboration, or correctness of arbitrary compiler output.
