# Changelog

English | [中文](CHANGELOG.zh-CN.md)

Versions: a feature release is 0.2, 0.3, …; a small iteration of a published release (documents, attribution, packaging,
shipped test suites, with the bootstrap recipe's inputs unchanged) is 0.1.1, 0.1.2, …. A published tag is never moved.
Each release lists its source archive's SHA-256; the repository tree at the tag equals the archive.

## [0.1] — 2026-11-19

First public release: the minimal self-bootstrapping closure of the rsd compiler.

- Compiler chain `rsd → rscm → wasm` (`rsdc`, `rsc`) with its 54 source files, and a committed WebAssembly seed that rebuilds
  both compilers byte for byte from source with only a C compiler.
- Frozen formal semantics of each layer (scm, λRC, wasm0), pinned by content digest.
- Performance record against Koka on GCP t2d-standard-4; reference columns for C++, OCaml, Haskell, Java, Swift and Lean 4.14
  were added to [`perf/`](perf/README.md) the same day.
- Verification: fixed point reproduced from the documents by an independent agent on a fresh Linux VM; reviews by two
  independent model families.
- Archive: `rsd-src.tar`, SHA-256 `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`, 201 files.
- Release: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1
