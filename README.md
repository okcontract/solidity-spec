# Solidity Spec

Solidity Spec is an executable formal model of Solidity in Lean.
It follows our work on [oksolc](https://github.com/okcontract/oksolc)'s compiler verification.

This standalone Lean 4.29.0 package targets **Solidity 0.8.36**, reference
compiler **0.8.36+commit.8a079791**, and **Cancun**. `target.json` and
`Solidity/Target.lean` record the pin; an accepted pragma does not select a
different semantics. Compiler compatibility is scoped to **`viaIR: true`**,
with optimization disabled or enabled at 200 runs. Legacy code generation is
outside this profile: it can perform implicit aggregate argument copies before
later argument effects, whereas the documented IR policy gathers raw arguments
before conversion. This scope is not a proof of general compiler conformance.

The package contains certificate models and a shared typed core with
correspondence proofs for its statement and certificate interfaces.
It is an **incomplete, standalone Solidity formalization**.

Read the [paper](paper/solidity-semantics.pdf)
([LaTeX source](paper/solidity-semantics.tex)) for the semantics and trust boundary.
The [external conformance checks](CONFORMANCE.md) compare selected machine
executions with the pinned compiler and a local Cancun EVM, including explicit
legacy-pipeline boundary controls.

| Layer | Authoritative sources | Role |
| --- | --- | --- |
| Unified scalar, aggregate and effect core | `Solidity/Core`, `Solidity/Core/Aggregates`, `Solidity/Core/Execution` | Width-indexed values, physical aggregate references, permitted effect orders, scopes, loops and internal function frames |
| Correspondence proofs | `Solidity/Proofs`, `Solidity/Compatibility/Execution` | Word, typed-expression, condition and stateful evaluators agree with the core; complete call certificates imply core trace preservation |
| Checked frontend stages | `Solidity/Frontend` | Typed name resolution, rational constants, exact integer conversion, structural elaboration and evaluation preservation; unannotated scalar inference and nominal types |
| Words and typed contract language | `Contract/Language`, `Contract/Semantics` | Typed finite statements, explicit arithmetic modes, rollback, helpers, logs |
| Admitted Solidity | `Solidity/Word.lean`, `Checked.lean`, `Function.lean`, `ABI.lean`, `StorageSource.lean` | Expression evaluation, call admission, stateful statements |
| Layout and initialization | `Solidity/StorageLayout.lean`, `StorageInitialization.lean`, `StorageConstructor.lean` | Packed Boolean fields, word fields, declaration order and constructor execution |
| Target machine | `Contract/Evm` | Partial Cancun bytecode semantics, gas, storage and deployment frames |
| Supporting models | `Contract/Yul`, `Contract/Interaction`, `Contract/Export` | Word expressions, world/memory operations and Keccak |
| Certificate interfaces | `Solidity/Call.lean`, `Contract.lean`, `Storage.lean`, `StorageCreation.lean` | Precise predicates and composition theorems for accepted artifacts |
| Proof audit | `Contract/Check` | Dependency/axiom inspection for selected theorem contracts |

Paths following the first entry in a cell are relative to the same directory.
The resolved machine and certificate interfaces have different input domains.
Consult the paper for their source-admission assumptions and proof scope.

## Build and check

From the root of this package, with the toolchain in `lean-toolchain` installed:

```sh
make replay
```

`make check` builds both libraries and their regression modules with four Lean
workers. `make replay` also checks selected theorem statements, transitive axioms
and definition-source identities, then freshly rechecks the foundation, pilot
and scalar machine proof closures, one at a time. Set `JOBS` to change build
parallelism. For an explicit installation, prepend the Lean 4.29.0 `bin`
directory to `PATH` so Lake and the kernel checker share the same toolchain. The package uses Lean's bundled `Std` and has no external Lean
package dependencies. The manifest checks require Python 3's standard library;
no Zig compiler is required.

To rebuild the paper with [Tectonic](https://tectonic-typesetting.github.io/):

```sh
make paper
```

The result is `paper/solidity-semantics.pdf`; intermediate files stay in
`paper/build/`. Tectonic may download its TeX bundle on the first build.

## Use the model

Use `import Solidity.Execution` for lightweight checked execution. Additional
laws are in `Solidity.Execution.Proofs`, and admitted-state safety is in
`Solidity.Execution.Safety`. Compiler-model bridge clients use
`Solidity.Compatibility.Execution`. The `Solidity` umbrella exports all of
these interfaces. Certificate clients also use the exported
`Compiler.Validation` namespaces.

The execution machine consumes resolved, typed trees and explicit program
tables. It models effect-order choices, physical aliases, scopes, loops,
internal calls and rollback. Source return, revert and fault remain distinct
from unsupported behavior and interpreter exhaustion. Host-work bounds are
separate from EVM gas.

A successful proof checks a statement about this model under its stated
assumptions. The [safety contract](SAFETY.md) describes the supported
configuration profile; the paper explains the scope of the executable model
and the interpretation of its certificate interfaces.

## Documentation

- [Semantic contract](SEMANTIC_CONTRACT.md): observations, environmental
  assumptions, rollback and refinement obligations.
- [Scalar expressions](SCALARS.md): types, conversion rules and checked input
  interfaces.
- [Execution modules](Solidity/Core/Execution) and
  [aggregate modules](Solidity/Core/Aggregates): executable definitions and proofs.
- [Safety](SAFETY.md) and [source/target pilots](PILOT.md): theorem statements,
  premises and the manually paired Cancun fragments.
- [Theorem contracts](THEOREMS.md): selected roots, expected statements and
  permitted axioms.
- [Reference corpus](references/README.md): pinned language and execution
  references, source identities and licenses.
- [Release checks](RELEASE.md): build, proof replay and paper reproduction.

Source licensing is [GPL-3.0](LICENSE.txt). Vendored reference snapshots retain
their upstream notices and licenses.
