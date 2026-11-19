# Acknowledgements and references

English | [中文](ACKNOWLEDGEMENTS.zh-CN.md)

Residua is a research project. It builds on the work of many other projects. This file lists every project whose code
we ported, whose tools or data we used as a test oracle, and whose design we studied, as far as our records show.
The per-file record for each release is `release/NOTICES.md` and `release/PROVENANCE.tsv` in that release.

**If you find code or an idea taken from your work without credit here, please tell us**, by opening an issue or by
private vulnerability reporting on this repository. We will add the credit, and fix the release, as a matter of course.

## Code ported into Residua (licence as published upstream)
- Lean 4 — leanprover/lean4 (Apache-2.0): the compiler IR passes (RC, borrow, reset/reuse, dead-code, case simplification,
  emission) ported as `lib/lrc/`; basic data representations; parts of the kernel algorithms used as reference.
- Koka — koka-lang/koka (Apache-2.0): benchmark programs; the Perceus reference-counting model (Reinking, Xie, de Moura,
  Leijen, PLDI 2021).
- Bend / HVM2 — bendlang/bend (Apache-2.0): benchmark programs; papers by Taelin et al.
- The Computer Language Benchmarks Game — benchmarksgame-team (BSD-3-Clause): benchmark programs.
- earley-lean — Daniel1854/earley-lean (Apache-2.0): Earley parser.
- elaboration-zoo and smalltt — AndrasKovacs (BSD-3-Clause, MIT): elaboration algorithms.
- Cedar — cedar-policy/cedar-spec (Apache-2.0, proofs rechecked) and cedar-integration-tests (test oracle).
- lean-regex — pandaman64/lean-regex (Apache-2.0, proofs rechecked).
- matching-logic-lean — eveil-labs (Apache-2.0).
- CosmWasm cw-plus (Apache-2.0): contract code and test oracle.
- libuv (ISC): address representation, in an application tree.

## Tools and data used as test oracles (not shipped as code)
- Lean 4 kernel and toolchain, Lean4Lean (digama0/lean4lean), Mathlib, Batteries, Aesop, quote4, ProofWidgets4, plausible,
  import-graph, LeanSearchClient, lean4-cli, LNSym.
- WebAssembly Binary Toolkit (WABT, Apache-2.0): the seed recipe fetches a pinned release to build the executors.
- K framework, KEVM, KWasm, kevm-plugin, proof-generation (Runtime Verification); Metamath (metamath-exe and databases).
- HTTP: llhttp (via httptools), h11, hyper, hyper-util, http-body-util, tokio, bytes, oha.
- z3, verina, serde_json, schemars, anyhow.

## Designs and papers we studied
- Lean Kernel Arena (leanprover/lean-kernel-arena) and nanoda, as kernel-checker references.
- Perceus and FBIP (Koka papers); Lean 4's compiler (lambda-RC IR).
- h5i (h5i-dev/h5i, Apache-2.0): verified HTTP kernels; our web experiments modelled its request policy.
- Ninja-go and ABFS (Google): two-phase content-addressed action caching.
- Bazel, Buck2, Nix: action keys and input addressing. Salsa: incremental computation.
- Datomic and DataScript (tonsky/datascript); Prolly trees (Dolt/Noms); Merkle Search Trees (Auvolat and Taïani, 2019);
  DBSP (Budiu et al., VLDB 2023).
- CakeML (verified bootstrapping); Zig (self-hosting from a committed seed).
- Benchmark collections: plb2, Programming-Language-Benchmarks, kostya/benchmarks, are-we-fast-yet.
- Others cited in the design notes: CPython grammar, XNU Mach-O headers, Berkeley SoftFloat and IEEE 754, Knuth TAOCP 4.3.1,
  ring (Clojure), rust-lang/regex, OOPSLA'23 artifact by Chen et al.
