# RELEASE-NOTES — Residua 0.3

English | [中文](RELEASE-NOTES.zh-CN.md)

Release 0.3 keeps the self-bootstrap closure — verifiable-provenance
compilation, rebuilt byte-identically from the committed wasm seed with
only a C compiler — and adds the `rsd` build tool, `UInt64` in the
language, the first typed `ExecModel` instances at the execution
boundary, and the MST-NF composition theorems. MST-NF is Residua's
foundational theory: it lives in the public repository
[github.com/residua-labs/MST-NF](https://github.com/residua-labs/MST-NF)
at pinned commit `4432a34`, which holds the proofs.

## New in 0.3

- **The `rsd` build tool.** `rsd build` compiles a program through the
  content-addressed store and recompiles only what changed; `rsd test`
  runs the end-to-end suite; `rsd run` executes; `rsd cache` is the
  store itself. Dispatcher `rsd/`, store and graph `lib/rsd/`,
  `lib/Rsd.rsd`; user document `docs/BUILD.md`; note
  `release/notes/rsd-tool.md`.
- **`UInt64` in the language.** The compiler sources now use it.
- **Suites restored.** The benchmark and test suites 0.1.1/0.1.2
  shipped and 0.2 dropped are back at their current bytes:
  `benchmarks/`, `instruments/lrc-host/`, `perf/`,
  `ACKNOWLEDGEMENTS.md`, and the TESTING guide. A new gate check
  refuses a later release that drops a path an earlier release shipped
  without a changelog line saying so.
- **Typed `ExecModel` instances at the execution boundary**
  (`semantics/Effect/AdmissionNF.lean`): `monitorModel` and
  `exec9AdmissionModel`, with the four Tier-1 laws proved — quotient
  factorization, admissibility soundness, residue totality and
  representative precision. Repository-side receipt:
  `reports/effect-sem/ADMISSION-NF.md` (11 theorems checked, axioms
  within `propext`/`Quot.sound`, refusal control 1/1).
- **Three surface spellings.** `examples/surfaces/` ships five
  programs each printed in the `.rsd`, `.rsj` and `.rsm` spellings;
  `docs/surfaces/` documents the profiles and records the round-trip
  check that all three parse to the same tree.
- **New seed cut; the wasm route defaults to `narrow`.** The committed
  seed is re-cut at the pinned head; from this cut the wasm route
  compiles with the `narrow` layer as its default, while the native
  route stays 64-bit.
- **The MST-NF composition theorems** (`lean/nf-compose/`): how a
  step's necessity composes over products, sums, sequences and
  dispatch, on the pinned necessity-execution model vendored in the
  directory. Independent audit passed (`reports/nf-compose/REPORT.md`,
  Lean 4.14, axioms `propext` only).
- **Public documents for outside readers.** `README.md` in the usual
  open-source order with a copy-paste quick start; `docs/` by the
  Diátaxis split with an index; `docs/GLOSSARY.md`; `CONTRIBUTING.md`;
  `CODE_OF_CONDUCT.md` (Contributor Covenant 2.1); `SECURITY.md`;
  issue and pull-request templates. The build tool's sources ship under
  their public names (`rsd/`, `lib/rsd/`, `lib/Rsd.rsd`). Comments in
  pinned source bytes still name internal work items and reports; they
  carry no personal data and change with the next seed cut.

## MST-NF status at 0.3

Each shipped component is either bound to the pinned `ExecModel`
(`lean/nf-compose/pinned/MSTNecessityExecModelMWE.lean`) with the four
Tier-1 laws proved, or recorded as a gap.

| shipped component | status |
|---|---|
| compiler chain (`rsdc`, `rsc`) | gap — no `ExecModel` instance yet |
| execution layer (`semantics/Effect/`) | instance shipped: `monitorModel`, `exec9AdmissionModel`; Tier-1 laws proved (`AdmissionNF.lean`) |
| syntax engine (`rsdc/profiles/`, `semantics/Syntax/`) | gap — no `ExecModel` instance yet |
| QFormat (`docs/QFORMAT.md`, `release/checks/qformat/`) | gap — no `ExecModel` instance yet |
| `rsd` build tool (`rsd/`, `lib/rsd/`) | gap — no `ExecModel` instance yet |
| NF composition (`lean/nf-compose/`) | framework shipped: composition theorems over the pinned model, independently audited |

0.1 and 0.2 shipped without any such instances: their `Monitor.lean`
cited the three-form encoding, which is not the `ExecModel` definition.
0.3 ships the first typed instances; the gaps above are recorded, not
release-blocking.

Admission-audit status: the admission audit of the wasm0 instance is
signed on the development main line, after this release — the
instance's decider runs by type-variable unification against an
independent wasm-validate oracle over two seeds, with no
counter-signature. The QFormat, rsx and scm instances passed the
vacuity check at an earlier revision; the lambda-RC admission stays
open, being rebuilt under a corrected criterion.

## In this archive

- the committed `rsdc`/`rsc` wasm seeds and their source closure under
  `bootstrap/seed/`, with the recipe that rebuilds them
- the rsd chain `rsd -> rscm -> wasm` invoked as the stage host's file
  contract (`docs/RSD-COMMAND.md`)
- the `rsd` build tool (`rsd/`, `lib/rsd/`, `lib/Rsd.rsd`)
- frozen formal semantics per layer (scm, lambda-RC, wasm0) pinned by
  content digest, as specification texts; `semantics/Syntax/` and
  `semantics/Effect/` including the typed `ExecModel` instances
- the syntax engine's grammar profiles (`rsdc/profiles/`) and
  specification (`semantics/Syntax/`); the engine itself is inside
  the shipped compiler sources
- the MST-NF composition package (`lean/nf-compose/`, pinned model
  included) and its audit report (`reports/nf-compose/REPORT.md`)
- the benchmark, differential and performance suites (`benchmarks/`,
  `instruments/lrc-host/`, `perf/`)
- the language conformance corpus the bootstrap grammar was measured
  against (`docs/LANGUAGE.md` rows)
- the performance record (`docs/PERF-RECORD.tsv`, form in
  `docs/PERF-RECORD.md`)
- the stranger documents in English, with `README` and the `docs/`
  mirrors in Chinese `.zh-CN.md`
- the per-goal release notes (`release/notes/`), the runnable
  conformance checks (`release/checks/`) and the vendored licence texts
  (`release/licenses/`)

## Verification

`docs/VERIFY-RELEASE.md` is the protocol: seed digests, the archive
digest, then the full seed recipe on a clean Linux x86-64 or macOS
arm64
account — the recipe's rebuilt compiler images must compare
byte-identical to the committed seeds (`seed_roundtrip=2/2`). Host
receipts for the archive ship under `release/`.

## Stated limits of 0.3

Single-module programs (no `import`); no I/O execution layer (the
effect-boundary semantics specifies the host contract; the language has
no effects); no proof checking (the R-CIC kernel is not in this
release); a 4 GiB address space; no publish/query entry for results; no
importable standard library. The bootstrap `.rsd` grammar refuses
`theorem`, `axiom`, `class`, `abbrev`, `variable`, `opaque`, `by` and
`import` as source constructs.

## Order after 0.3

1. R-CIC kernel + the agent entry's publish/query entry — the first
   point a stranger can find, check and reuse another's result.
2. Programming completeness: modules, real programs, an execution
   layer, 64-bit addressing, application suites.
3. Cheap confirmation of execution: wasm0 -> AIR -> zk.
4. Generic connectors to external semantics (K/KORE, Lean/Rocq import).
