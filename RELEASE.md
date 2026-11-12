# Release checks

Solidity Spec is a standalone Lean package targeting Solidity 0.8.36, its IR pipeline and Cancun.
`target.json` fixes both optimizer configurations (off and on with 200 runs).
The toolchain is pinned to Lean 4.29.0 in `lean-toolchain`.

From the repository root:

```sh
make replay JOBS=4
make paper
```

`make replay` builds the two libraries and their regression modules with four
Lean workers, runs the Python negative controls, and enforces the theorem
manifest (statements, transitive axioms and definition-source identities). It
then freshly rechecks these proof closures sequentially with
`leanchecker --fresh`:

- `Solidity`
- `Solidity.Pilots.AliasCallRollbackResourceTests`
- `Solidity.Pilots.AliasCallRollbackGroupTests`
- `Solidity.Pilots.OrderAliasRollbackTests`
- `Solidity.Conformance.ScalarMachineTests`

For an explicit installation, prepend the Lean 4.29.0 `bin` directory to
`PATH` so Lake and the fresh kernel checker use the same toolchain.
`make check` runs only the build. The package uses Lean's bundled `Std` and
requires no external Lean packages. Manifest checks require Python 3's standard
library; proof checking does not require a Solidity compiler.

Run the separate [external conformance checks](CONFORMANCE.md) with the exact
pinned Solidity compiler and Anvil. They compare 14 selected effect cases under
both IR optimizer settings and exercise legacy copy-timing boundary controls.
Compiler/EVM checks retain their input identities and observations in a new
local output directory. They are not part of the proof-only CI gate.

`make paper` requires Tectonic and writes `paper/solidity-semantics.pdf`.
Intermediate TeX files stay in `paper/build/`.

The [CI workflow](.github/workflows/lean.yml) runs the build and fresh kernel
replay on pushes and pull requests and retains its logs. These checks validate
proofs about the released model; they do not establish complete Solidity
conformance or certify arbitrary compiler output. [THEOREMS.md](THEOREMS.md)
describes the selected theorem contracts.

Release source archives contain the tracked package files and their licenses.
Build caches, intermediate TeX files and local evidence directories are excluded.
The [paper](paper/solidity-semantics.pdf) states the model's scope, proof
assumptions and research context.
