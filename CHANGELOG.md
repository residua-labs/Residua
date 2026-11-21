# Changelog

English | [中文](CHANGELOG.zh-CN.md)

**Versioning.** A feature release is numbered 0.2, 0.3, …, in the order in which goals are completed. A patch release of
a published version (documents, attribution, packaging, shipped test suites; the inputs of the bootstrap recipe
unchanged) is numbered 0.1.1, 0.1.2, …. A published tag is never moved. Each release lists the SHA-256 of its source
archive; the repository tree at the tag equals the archive.

## [0.2] — 2026-11-20

Feature release: the 0.1 self-bootstrap closure plus three goals closed since.

- **Typed content address (q format v1).** Every content identity carries its kind inside the hashed bytes:
  `q(kind, c) = SHA-256("<kind> <len>\0" ++ c)`, printed `sha256:<hex>`; raw SHA-256 remains as `digest` for
  file integrity and interop only. Cross-kind address collisions can no longer occur. Specification and kind
  registry: [`docs/QFORMAT.md`](docs/QFORMAT.md); conformance check:
  [`release/checks/qformat/`](release/checks/qformat/); release note: [`release/notes/qformat-1.md`](release/notes/qformat-1.md).
- **Syntax engine closed over its grammar class.** The parser is one function over grammar data; on grammars
  generated from the class its verdicts and trees equal the mechanically checked reference decider
  (`semantics/Syntax/`), with planted mutants as controls. Engine sources `rsdc/syntax/`; the surface
  profiles ship as data (`rsdc/profiles/*.syn`); release note: [`release/notes/syntax-engine.md`](release/notes/syntax-engine.md).
- **Execution-boundary semantics E0–E4.** Wire format, admission and seal judgments, the conformance
  classifier and recorded transport sessions, as Lean 4.14 statements (`semantics/Effect/`); acceptance
  evidence `reports/effect-sem/` (repository-side); release note: [`release/notes/effect-sem.md`](release/notes/effect-sem.md).
- **Documents.** User documents moved from `release/` to `docs/` as Markdown (`.zh-CN.md` for Chinese).
- The seed members stay at their 0.1 bytes (no recut); five declared 0.2 increments are exempt —
  the seed README recipe, `ASSEMBLY.tsv`, `CUT.tsv`, the macOS WABT pin and `bootstrap/Wasm2CHost.c`;
  q format v1 does not change emitted bytes.
- The bootstrap recipe gains a macOS arm64 host (Apple clang, `PATH=/usr/bin:/bin`, no Lean),
  reproduced byte-identically on two Darwin hosts.

## [0.1] — 2026-11-19

First public release: the minimal self-bootstrapping closure of the rsd compiler.

- Compiler chain `rsd → rscm → wasm` (`rsdc`, `rsc`) with its 54 source files, and a committed WebAssembly seed that rebuilds
  both compilers byte for byte from source with only a C compiler.
- Frozen formal semantics of each layer (scm, λRC, wasm0), pinned by content digest.
- Performance record against Koka on GCP t2d-standard-4; reference columns for C++, OCaml, Haskell, Java, Swift and Lean 4.14
  were added to `perf/` (repository-side) the same day.
- Evidence: the fixed point was reproduced from the documentation alone by an independent agent on a fresh Linux
  virtual machine; the release was reviewed by two independent model families.
- Archive: `rsd-src.tar`, SHA-256 `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`, 201 files.
- Release: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1
