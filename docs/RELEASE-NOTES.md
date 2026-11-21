# RELEASE-NOTES — Residua 0.2

English | [中文](RELEASE-NOTES.zh-CN.md)

Release 0.2 keeps the 0.1 self-bootstrap closure — verifiable-provenance
compilation, rebuilt byte-identically from the committed wasm seed with
only a C compiler — and adds the goals closed since: the final typed
content identity, the syntax engine closed over its grammar class, and
the formal semantics of the execution boundary.

## New in 0.2

- **Typed content identity `q` (format v1).** The kind of the addressed
  content is inside the hashed bytes:
  `q(kind, c) = SHA-256("<kind> <len>\0" ++ c)`, printed `sha256:<hex>`;
  raw SHA-256 remains as `digest` for file integrity and interop only.
  Cross-kind address collisions can no longer occur. Specification:
  `docs/QFORMAT.md`; conformance vectors:
  `release/checks/qformat/`; note: `release/notes/qformat-1.md`.
- **Syntax engine closed over its grammar class.** One function —
  (a grammar of the class given as data, an input) -> a tree or a named
  refusal — whose verdicts and trees equal the class's mechanically
  checked reference decider on grammars generated from the class, with
  planted mutants as controls. Sources `rsdc/syntax/`; class
  `semantics/Syntax/`; surface profiles shipped as data
  `rsdc/profiles/*.syn`; note: `release/notes/syntax-engine.md`.
- **Execution-boundary semantics E0–E4.** The wire format, admission
  and seal judgments of the effect boundary, the conformance classifier
  and the recorded transport sessions, as Lean 4.14 statements
  (`semantics/Effect/`); acceptance evidence
  `reports/effect-sem/` (repository-side); note:
  `release/notes/effect-sem.md`.

## In this archive

- the committed `rsdc`/`rsc` wasm seeds and their source closure
  (`bootstrap/seed/stage-14274/`)
- the seed recipe (`bootstrap/seed/stage-14274/README.md`) and the C
  host bridges it needs
- the rsd chain `rsd -> rscm -> wasm` invoked as the stage host's file
  contract (`docs/RSD-COMMAND.md`)
- frozen formal semantics per layer (scm, lambda-RC, wasm0) pinned by
  content digest, as specification texts; the 0.2 additions
  `semantics/Syntax/` and `semantics/Effect/`
- the syntax engine and its grammar profiles (`rsdc/syntax/`,
  `rsdc/profiles/`)
- the language conformance corpus the bootstrap grammar was measured
  against (`docs/LANGUAGE.md` rows)
- the performance record (`docs/PERF-RECORD.tsv`, form in
  `docs/PERF-RECORD.md`)
- the stranger documents: INSTALL, QUICKSTART, VERIFY-RELEASE, OVERVIEW,
  LANGUAGE, STDLIB, RSD-COMMAND, SPECS, QFORMAT, PERF-RECORD —
  in English; README and ten `docs/` texts (OVERVIEW, ARCHITECTURE,
  TRUST, GLOSSARY, STABILITY, FAQ, RELATED-WORK, CONTRIBUTING-SECURITY,
  QFORMAT, RELEASE-NOTES, this file included) also ship in Chinese
  `.zh-CN.md` mirrors
- the per-goal release notes (`release/notes/`), the runnable
  conformance checks (`release/checks/`) and the vendored licence texts
  (`release/licenses/`)

## Verification

`docs/VERIFY-RELEASE.md` is the protocol: seed digests, the
archive digest, then the full seed recipe on a clean Linux x86-64
or macOS arm64 account — the recipe's rebuilt compiler images must compare
byte-identical to the committed seeds (`seed_roundtrip=2/2`). The macOS arm64
host (Apple clang, `PATH=/usr/bin:/bin`, no Lean) was reproduced
byte-identically on two Darwin hosts.

## Stated limits of 0.2

Single-module programs (no `import`); no I/O execution layer (the
effect-boundary semantics specifies the host contract; the language has
no effects); no proof checking (the R-CIC checker is not in this
release); no UInt64; a 4 GiB address space; no publish/query entry for
results; no importable standard library. The bootstrap `.rsd` grammar
refuses `theorem`, `axiom`, `class`, `abbrev`, `variable`, `opaque`,
`by` and `import` as source constructs.

## Order after 0.2

1. The `rsd` build tool (`build`/`test`/`run`/`cache`) together with the
   recut bootstrap seed its sources require — held back from 0.2
   (repository-side at `rsd/`, `lib/rsd/`).
2. R-CIC kernel + the agent entry's publish/query entry — the first
   point a stranger can find, check and reuse another's result.
3. Programming completeness: modules, real programs, UInt64, an
   execution layer, 64-bit addressing, application suites.
4. Cheap confirmation of execution: wasm0 -> AIR -> zk.
5. Generic connectors to external semantics (K/KORE, Lean/Rocq import).

`closure_claim=0` (`release/MANIFEST.md`).
