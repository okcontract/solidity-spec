# Static types and scalar expressions

The resolved scalar-expression interface targets Solidity
**0.8.36+commit.8a079791 / Cancun**. It supplies an unannotated expression
checker, executable evaluator and conformance generators.

## Inputs, values and failure boundaries

`Static.SType` retains signedness and width, fixed-byte width, payable addresses,
enum identity/cardinality, user-defined value-type identity/underlying type,
contract identity/payability/ancestry and function visibility, mutability and
parameter/result types. It also represents aggregate, reference, tuple,
metatype and fixed-point forms for explicit type classification.
[Aggregate operations](Solidity/Core/Aggregates) use physical reference values
and checked locations. Unsupported execution types have an empty value family,
rather than a fabricated zero or successful result. Scalar integers and bytes use the core's
width-indexed `BitVec` values.

`Static.WellFormed` checks resolved nominal metadata against a registry and
recursively checks structural types. The executable checker is equivalent to
that independent judgment. Registry construction, inheritance linearization and declaration scope are
input assumptions. The aggregate checker validates legal type locations separately.
`inferResolved` checks all supplied names and types against the registry,
including unused branches, and validates the inferred result type.
`inferResolved_iff` characterizes its successful results by resolved-input,
elaboration and well-formed-result judgments. The conformance generators consume
this checked entry point. Clients still supply the registry; it is not proof of
source admission.

An internal function value is an optional abstract handle. Representation may
identify compiler-equivalent functions after optimization, so handle/declaration
injectivity is not assumed. External functions carry address and selector.
The uninitialized internal handle is representable; the execution machine implements its call and
panic 0x51 through the shared effectful machine. Function equality here is
equality of the supplied handles.

The interfaces distinguish these failures:

| Class | Meaning |
| --- | --- |
| `StaticError.rejected`, lexical/literal errors, unknown name | Rejection by a modeled source rule |
| `StaticError.unsupported` | A type or operation outside the implemented execution profile |
| `ConversionFailure.panic bytes` | Runtime Solidity panic, including arithmetic 0x11, divisor 0x12 and enum range 0x21 |
| Interpreter fuel exhaustion | Separate control-machine result; never a scalar panic or successful execution |

`SourceExpr.eval_runtime` and `SourceExpr.failure_is_panic` prove that an
accepted typed pure expression produces a value or panic, never a static
rejection or unsupported marker during execution. This is not a theorem about
EVM gas adequacy or arbitrary source-program termination.

## Rules and checked interfaces

| Interface | Meaning and principal proof |
| --- | --- |
| `Implicit`, `SourceCast`, `ExplicitRule` | Source conversions, payable syntax and scalar coercion permissions; `implicit_iff`, `sourceCast_iff`, `explicitRule_iff` |
| `coerce`, `convert` | Machine conversion separated from source permission; `allowed_coercible`, `convert_supported`, widening exactness and narrowing modulo laws |
| `ScalarBinary`, `ScalarUnary` | Independent indexed operator rules; `checkBinary_iff`, `checkUnary_iff` |
| `wordPow`, `boundedPow` | Executable binary exponentiation and saturated checked arithmetic; mathematical specifications and signed/unsigned checked/unchecked laws |
| `Digits`, `NumberConverts`, `IntegerMobile`, `StringConverts` | Positional digits, literal representability, smallest integer mobile type and string conversion; checker equivalence theorems |
| `Materializes`, `Elaborates`, node typing judgments | Literal/runtime conversion and structural expression elaboration; `materialize_iff`, `infer_iff`, `binary_iff`, `runtimeChoice_iff`, `runtimeBinary_iff`, `unary_iff`, `conditional_iff` |
| `AssignmentTyping`, `UpdateAllowed` | Plain/compound assignment plans and scalar increment/decrement/delete; `assignment_iff`, `updateAllowed_iff`, lvalue requirements |
| `OperatorSignature`, `UnaryOperatorSignature` | Pure free-function signatures for user-defined operators; checker equivalence and binary binding construction |

`Frontend.Inference.Source` has names, literal spellings, Boolean values,
unary/binary operators, conditionals, source casts and value-type wrap/unwrap.
Binary operands need no supplied operator/type annotations. For example,
`uint8 x; x + 1` remains `uint8`, while `x + 256` becomes `uint16`.
Shifts and powers type their operands asymmetrically. Literal-only arithmetic
keeps exact rationals and the pinned precision policy; runtime arithmetic uses
the chosen checked/unchecked mode. Width-changing and sign-changing runtime
casts cannot be combined in one source cast. Literal conversions check
representability instead of applying runtime truncation.

Checking visits both logical operands and both conditional arms. Invalid casts
therefore reject even in unreachable expressions. Evaluation subsequently uses
short circuiting. `SourceExpr.Evaluates` independently permits operand orders
at each ordinary binary node, and `eval_permitted` relates the executable
strategy to it. Expressions in this profile are pure. Aggregate reference access
uses the aggregate heap interface. The [execution machine](Solidity/Core/Execution)
handles effectful expressions and internal calls.

Scalar update primitives return the next value and the prefix/postfix expression
result; delete has an empty-tuple result. Assignment plans require implicit
conversion back to the left type. These primitives do not resolve or write an
lvalue. Global `using` lookup, overload uniqueness and user-defined operator
resolution are input assumptions; the continuation machine executes resolved
internal calls. The scalar expression
checker handles builtin operators and explicit wrap/unwrap. Signature checking
supplies no function-result oracle.

## Literal policy and provenance

`Frontend.Lexical` models numeric token spellings, decimal/scientific rationals,
denominations, hex numbers and address-shaped literals. String tokens preserve
quote/kind/raw escapes. ASCII, Unicode and hex decoding, adjacency, UTF-8 checks,
fixed-byte padding and reference-type conversion permissions are explicit.
Unicode UTF-8 validation follows concatenation of adjacent tokens, while raw
direction markers are checked within each token. The aggregate heap supplies allocation and
copying of finite dynamic string/byte packets; the pure scalar inference tree
does not allocate reference values.

The pinned reference has observable admission quirks. They are compatibility
rules for this exact version, not general mathematical conventions:

- `.5` is a valid literal. Scientific precision checks use its reduced rational
  mantissa. Positive/negative boundary witnesses are `0.5e1233` and `5.0e-1233`.
- A nonzero mantissa with a plus-signed exponent (`1e+2`) rejects. A zero
  mantissa bypasses exponent value parsing (`0e+2` and `0e08` are zero).
- Leading-zero exponent digits are parsed as octal: `1e010` is 10^8; `1e08`
  rejects. This follows upstream bigint parsing, not decimal exponent notation.
- The pinned underscore exclusions distinguish lower-case `e` from upper-case
  `E`: `1e_2` rejects, while `1E_2` and `1_E2` are admitted.

The decimal precision precheck reifies the stored binary64 `log2(10)` value
and its rounded product using exact integers. It does not call a floating-point
oracle. The equivalence of this reification to all host library computations
is a model-adequacy obligation; boundary conformance is evidence, not that proof.
Address checksum evaluation uses the existing concrete Keccak implementation;
this work does not prove its full functional correctness or cryptographic security.

`references/lock.json` pins the retained upstream documentation, `Types.cpp`
and `ConstantEvaluator.cpp`. The retained upstream `types.rst` is an index:
its included chapters are not bundled. The lock records this distinction and
enumerates the unbundled includes.

## Proof scope and executable examples

Checker equivalence relates executable checks to the declared resolved
expression/type judgments. The registry, token spellings and correspondence to
source bytes are explicit input assumptions. Literal recognition is executable,
with separate digit and representability proofs. Fixed-point types are
recognized, while fixed-point execution is unsupported and distinguished from
a source type error.

`Solidity.Conformance.Inference` generates Solidity expressions and Lean
expectations from the same unannotated trees. `Solidity.Conformance.StaticMatrix`
generates combinations of scalar types, function types and operators. These
are model-based fixtures; their rendering is not a verified parser or a proof
of arbitrary compiler behavior.

The package build checks the scalar and inference regression modules.
`make replay` also freshly rechecks the scalar machine regression proof closure.
