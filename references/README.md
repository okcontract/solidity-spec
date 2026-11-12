# Pinned reference corpus

`lock.json` records selected Solidity documentation/type-analysis sources and
the complete Cancun fork directory from execution-specs by immutable upstream
revision and SHA-256. Its `snapshot` paths are relative to the repository root.
The snapshots retain their upstream license notices; the corresponding license
files are included.

These files are reference material, not imported Lean code or an executable
Python distribution. Shared and cross-fork execution-specs dependencies are
not bundled. A file hash records identity; it does not prove agreement between
the reference and the Lean definitions.

The retained Solidity `docs/types.rst` and `docs/contracts.rst` files are upstream
indexes. The lock labels them `indexOnly` and lists their unbundled includes.
They are not substitutes for those chapters. Substantive snapshots include the
storage and memory layout documentation, control structures and upstream type
and constant evaluation rules.

`policies.json` describes the fixed compiler-specific choices implemented in
`Solidity.Policy`, their source references and model fixtures. Language
permissions and fixed execution choices have separate entries.

The execution-spec-tests Cancun manifest records upstream Git blob identities
for an external test corpus. It is a reference inventory, not a record that
those tests were executed by this package.
