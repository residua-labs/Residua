# Changelog

English | [中文](CHANGELOG.zh-CN.md)

**Versioning.** A feature release is numbered 0.2, 0.3, …, in the order in which goals are completed. A patch release of
a published version (documents, attribution, packaging, shipped test suites; the inputs of the bootstrap recipe
unchanged) is numbered 0.1.1, 0.1.2, …. A published tag is never moved. Each release lists the SHA-256 of its source
archive; the repository tree at the tag equals the archive.

## [0.1.2] — 2026-11-20

Patch release of 0.1.1: the test and benchmark suites ship; the bootstrap recipe's inputs are byte-identical to 0.1.

- `benchmarks/` (186 files): the benchmark programs and their emitted `.rscm` modules, `expected/` outputs, the Rust
  reference implementations, the Koka comparison harness, and `benchmarks/langs/` with the vendored Koka `test/bench`
  and Lean `4.14` `test/bench` sources the ports derive from (Koka Apache-2.0, Lean 4 Apache-2.0, Benchmarks Game
  BSD-3-Clause, Bend Apache-2.0).
- `instruments/lrc-host/` (101 files): the differential test suite — `Diff.rsd`, the Sides/Mutants tables,
  `Images.tsv`, `Peaks.tsv` and the pinned `img/` images.
- `release/docs/TESTING` (+`.zh-CN`): how to run each suite and how the performance record was produced; the
  `lean --run` runners are a test tool, not part of the bootstrap recipe.
- The public documents now follow the publication register of the 0.1.1 documents; the release gate checks the
  ship set mechanically against a table of internal identifiers.
- Archive: `rsd-src.tar`, SHA-256 see the release page, 437 files.
- Release: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2

## [0.1.1] — 2026-11-20

Patch release of 0.1: documents, attribution and packaging; the bootstrap recipe's inputs are byte-identical to 0.1.

- The ship set drops the application tree (`web/`, the 52 application files
  now repository-side and cited by path and digest in `release/docs/LANGUAGE`) and adds the performance record
  (`perf/`): the ship set is now 148 files.
- Attribution completed: the notices carry per-file verbatim upstream headers for the Lean 4 ports, and the `web/h5i`
  design gained 6 repository-side provenance rows at upstream
  `9774f28a2a` (Apache-2.0).
- `ACKNOWLEDGEMENTS.md` and `ACKNOWLEDGEMENTS.zh-CN.md` added; both READMEs rewritten in the publication register.
- Internal publisher identifiers removed from shipped notices and provenance; the release gate rejects them
  mechanically, together with stale version strings and internal tool names.
- Version scheme corrected: feature releases are 0.2, 0.3, … (0.11 would sort after 0.10); patch releases are
  0.1.1, 0.1.2, …. The published 0.1 archive is unchanged.
- Archive: `rsd-src.tar`, SHA-256 `165690af75bebf7841cbd3f14459d66b7d295aa65f2676b935eee5ee3a9b030b`; the archive holds 148 files.
- Release: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.1

## [0.1] — 2026-11-19

First public release: the minimal self-bootstrapping closure of the rsd compiler.

- Compiler chain `rsd → rscm → wasm` (`rsdc`, `rsc`) with its 54 source files, and a committed WebAssembly seed that rebuilds
  both compilers byte for byte from source with only a C compiler.
- Frozen formal semantics of each layer (scm, λRC, wasm0), pinned by content digest.
- Performance record against Koka on GCP t2d-standard-4; reference columns for C++, OCaml, Haskell, Java, Swift and Lean 4.14
  were added to [`perf/`](perf/README.md) the same day.
- Evidence: the fixed point was reproduced from the documentation alone by an independent agent on a fresh Linux
  virtual machine; the release was reviewed by 2 independent model families.
- Archive: `rsd-src.tar`, SHA-256 `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`; the archive holds 201 files.
- Release: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1
