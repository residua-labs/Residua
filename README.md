# Residua

**Verifiable computation and proof, identified by content.**

English | [中文](README.zh-CN.md)

## Abstract

Residua is a research project on the reuse of computational and deductive results between parties that do not trust one
another. A result is identified by a content address (*q*: a SHA-256 digest of the result's content) rather than by its
producer or by the version of the toolchain that built it, and it is admitted only after mechanical checking against
formally defined semantics.

The project's language, **rsd**, is designed so that a program and a proof are terms of one dependent type theory: the
same term is compiled to native or WebAssembly code and is checked by a proof kernel. Releases 0.1–0.2 contribute the
compilation half of this design, a self-bootstrapping compiler chain whose provenance any third party can verify from a
committed seed, together with the toolchain's content-identity format, its syntax engine and the formal semantics of
its execution boundary. The proof-checking half (the R-CIC kernel) is the subject of
later releases.

> **Status.** Research release **0.2** (2026-11-20): the self-bootstrapping closure of the rsd compiler plus typed
> content identity, the closed syntax engine and execution-boundary semantics.
> Not yet a general-purpose language; see [Limitations](#limitations).

## Motivation

1. **Maintenance dominates the cost of formal results.** In a formal development, re-checking after upstream changes,
   repair, coordination and review cost far more than the kernel check itself.
2. **Producers are increasingly automated.** Most future results will come from automated agents, whose output cannot be
   accepted on the producer's word. Only mechanical checking and content identity scale to that setting.
3. **Semantics are siloed.** Results live in separate systems (Lean, Rocq, K, WebAssembly, the EVM) and do not carry
   across them.
4. **Results are bound to toolchain versions.** In current proof assistants a compiled library is tied to the toolchain
   version that built it (Lean's `.olean` files, for example), so a version change rebuilds and re-checks everything
   downstream. A result identified by its content remains the same result across versions.

## Approach

- **Identity by content.** An artifact or a result is identified by a content address *q*. Equality of *q* is the
  criterion for reuse; names, locations and producers are not.
- **Admission by checking.** A result enters the system only through a mechanical check against formal semantics. The
  producer, whether a person, a compiler or an automated agent, is outside the trusted base (the de Bruijn
  criterion [9]).
- **One language for programs and proofs.** By design, an rsd term is both compiled and checked by one kernel, so a
  statement about a program is a statement about the term that runs.
- **A verifiable toolchain.** The compiler that produces every other artifact is itself reproducible from a committed
  seed, so its provenance is checked rather than assumed.

## Release 0.2

### Contribution

**Compilation with verifiable provenance.** Given a source and an artifact, any party can rebuild the compiler from a
committed WebAssembly seed using only a C compiler, and check byte for byte that the artifact derives from that source,
trusting neither the publisher nor a large binary toolchain.

| Component | Contents |
|---|---|
| Compiler chain | `rsd → rscm → wasm`: front end `rsdc` and back end `rsc`, with their complete sources (53 files, pinned by SHA-256) |
| Seed | `bootstrap/seed/stage-14274/`: the two compilers as WebAssembly, the recipe, and every digest it checks |
| Formal semantics | Frozen specifications of each layer (scm, λRC, wasm0), pinned by content digest (`semantics/`, `gates/semalign/`, `lean/rsd-cert/`) |
| Performance record | Measured against Koka and six other languages on fixed hardware (`docs/PERF-RECORD.md`, `docs/PERF-RECORD.tsv`) |
| Content identity | Typed address `q` (format v1): specification and registry [`docs/QFORMAT.md`](docs/QFORMAT.md), vectors [`release/checks/qformat/`](release/checks/qformat/) |
| Syntax engine | Data-driven engine closed over its grammar class: sources `rsdc/syntax/`, class `semantics/Syntax/`, profiles `rsdc/profiles/*.syn` |
| Effect semantics | Execution-boundary semantics E0–E4 (`semantics/Effect/`); acceptance evidence `reports/effect-sem/` |
| Documentation | Installation, verification protocol, architecture, trust model, glossary, stability policy, FAQ (`docs/`, English and Chinese) |

### Evidence

- **Independent reproduction.** The seed recipe was reproduced from the documentation alone, by an independent agent with
  no prior knowledge of the project, on a fresh Linux virtual machine: both compilers were rebuilt byte-identical to the
  seed.
- **Independent review.** The release was reviewed by two independent model families.
- **Archive identity.** The repository tree at tag `rsd-0.2` is byte-identical to the published source archive.
- **Per-goal audit.** Each goal new in 0.2 carries an independent signed audit; transcripts are collected in
  `reports/release-02/evidence/`.

## Reproducing the bootstrap

Requirements: Linux x86-64 (GCC, GNU binutils, coreutils, Bash, curl, tar) or macOS arm64 (Apple clang, base system). No Lean, Node or OCaml.

```sh
# 1. Download and verify the archive (from the rsd-0.2 release page)
sha256sum -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src

# 2. Rebuild both compilers from the seed in a clean environment (20-45 minutes)
env -i PATH=/usr/bin:/bin bash --noprofile --norc
#    then run the commands of bootstrap/seed/stage-14274/README.md
```

The recipe fetches a pinned WABT release, translates the two seed executors to C, builds them, recompiles both compilers
from source, and exits 0 only if the rebuilt compilers are byte-identical to the committed seed.

Further reading:

- [`docs/QUICKSTART.md`](docs/QUICKSTART.md): the first run, step by step, and how to compile a source
- [`docs/VERIFY-RELEASE.md`](docs/VERIFY-RELEASE.md): every digest check of the release
- [`docs/OVERVIEW.md`](docs/OVERVIEW.md) and [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md): what 0.2 is
  and how the layers fit together

## Evaluation

<!-- generated-from-perf -->
**Method.** GCP t2d-standard-4. Koka columns: two fresh virtual machines, each value the mean of the two machines'
medians of 5 runs on a pinned core. Other-language columns: three fresh virtual machines, median of 5 on a
pinned core. A ratio is Residua's wall time divided by the reference's; below 1, Residua is faster. The programs
are taken unmodified from Koka's benchmark suite (the suite of the Perceus paper [5]) and from Lean 4's
benchmarks.

| Geometric mean, Residua 0.1 / … | Koka (native) | Koka (wasm) | C++ | OCaml | Haskell | Java | Swift | Lean 4.14 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| ratio | 0.973 | 1.047 | 0.822 | 0.586 | 0.281 | 0.451 | 0.164 | 0.570 |
<!-- end-generated-from-perf -->

Self-bootstrap from the seed takes 1162 s (peak 3.6 GiB).

**Scope.** These figures describe one small suite on one machine type. They characterise this release and are not a
general ranking of the languages compared. Per-program tables, empty cells and their causes, toolchain pins and the
history of every version are in `docs/PERF-RECORD.tsv`.

## Limitations

Release 0.2 is for reproducible, auditable compilation and for research on verified, bootstrappable compilers.

- Single-module programs only (no `import`).
- No I/O execution layer: the effect-boundary semantics specifies the host contract; the language itself has no effects.
- No proof checking: the R-CIC kernel is not in this release, and shipped `theorem` texts are specifications, not checked claims.
- No `UInt64`; a 4 GiB address space.
- The 0.2 surface language is a strict bootstrap subset; `theorem`, `axiom`, `class`, `abbrev` and `by` are refused
  ([`docs/LANGUAGE.md`](docs/LANGUAGE.md)).

## Research agenda

Feature releases are numbered 0.2, 0.3, … in the order in which their goals are completed. No goal is tied to a number
in advance, and no dates are promised. The goals:

- **Checking another party's result.** The R-CIC proof kernel, whose verdicts agree with Lean4Lean [7] and which accepts
  no invalid input of the Lean Kernel Arena; the final q format; a publish-and-query entry for results.
- **Programming completeness.** Modules, `UInt64`, 64-bit addressing, an I/O execution layer, real application suites.
- **Inexpensive confirmation of execution.** wasm0 → AIR → zero-knowledge proofs.
- **Connections to external semantics.** K/KORE, Lean and Rocq import.

## Related work

The seed-based bootstrap addresses the trusting-trust problem [1]; related approaches are diverse double-compiling [2]
and bootstrappable builds [3], and verified bootstrapping of a compiler was established by CakeML [4]. The back end
manages memory by reference counting with reuse, after "Counting Immutable Beans" [6] and Perceus [5]; its passes are
ported from the compiler of Lean 4 [11], and its target is WebAssembly [12]. Accepting results from untrusted producers
on checkable evidence is in the tradition of proof-carrying code [8]; the per-layer translation checks are in the
tradition of translation validation [10]. The planned proof kernel is compared against Lean4Lean [7].
`release/NOTICES.md` and `release/PROVENANCE.tsv` list the code this project ported, the tools it used as test oracles, and
the designs it studied.

## Releases

| Version | Date | Archive SHA-256 | Notes |
|---|---|---|---|
| [0.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1) | 2026-11-19 | `59d0956e…` | First public release: minimal self-bootstrapping closure |
| [0.1.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.1) | 2026-11-19 | see the release page | Patch release: the performance record ships in the archive, attribution completed, internal identifiers removed |
| [0.1.2](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2) | 2026-11-19 | see the release page | Patch release: benchmark and differential test suites shipped |
| [0.2](https://github.com/residua-labs/Residua/releases/tag/rsd-0.2) | 2026-11-20 | see the release page | Feature release: q format v1, syntax engine, effect semantics; [CHANGELOG](CHANGELOG.md) |

Full history: [CHANGELOG.md](CHANGELOG.md).

## Repository layout

| Path | Contents |
|---|---|
| `bootstrap/` | The committed seed, its recipe and the C host bridges |
| `rsdc/`, `rsc/`, `lib/` | Compiler sources (front end, back end, shared library and runtime); `rsdc/syntax/`, `rsdc/profiles/` the syntax engine and grammar profiles |
| `semantics/`, `gates/`, `lean/` | Frozen formal semantics and the per-layer translation checks; `semantics/Syntax/`, `semantics/Effect/` the 0.2 statements |
| `docs/` | The stranger documents (English and Chinese) |
| `release/` | Release manifest, provenance, notices, licences, checks and per-goal notes |
| `perf/` | Performance record of every version |

## Citing this work

Please cite the release you used, with the digest of its source archive:

```bibtex
@software{residua_0_2,
  title   = {Residua: Verifiable Computation and Proof, Identified by Content},
  author  = {{Residua Labs contributors}},
  year    = {2026},
  version = {0.2},
  url     = {https://github.com/residua-labs/Residua/releases/tag/rsd-0.2}
}
```

## Contributing and security

Issues are welcome. Report security problems through GitHub's private vulnerability reporting on this repository; see
[`docs/CONTRIBUTING-SECURITY.md`](docs/CONTRIBUTING-SECURITY.md).

## Acknowledgements

Residua builds on many other projects. `release/NOTICES.md` and `release/PROVENANCE.tsv` list the code we ported, the tools we
used as test oracles, and the designs we studied; per-file attribution is in `release/NOTICES.md` and
`release/PROVENANCE.tsv`. If you find your work used without credit, please open an issue or use private vulnerability
reporting, and we will correct it.

## References

1. K. Thompson. Reflections on trusting trust. *Communications of the ACM* 27(8), 1984.
2. D. A. Wheeler. Countering trusting trust through diverse double-compiling. *ACSAC*, 2005.
3. Bootstrappable Builds. https://bootstrappable.org
4. R. Kumar, M. O. Myreen, M. Norrish, S. Owens. CakeML: a verified implementation of ML. *POPL*, 2014.
5. A. Reinking, N. Xie, L. de Moura, D. Leijen. Perceus: garbage free reference counting with reuse. *PLDI*, 2021.
6. S. Ullrich, L. de Moura. Counting immutable beans: reference counting optimized for purely functional programming.
   *IFL*, 2019.
7. M. Carneiro. Lean4Lean: verifying a typechecker for Lean, in Lean. arXiv:2403.14064, 2024.
8. G. C. Necula. Proof-carrying code. *POPL*, 1997.
9. H. Barendregt, F. Wiedijk. The challenge of computer mathematics. *Philosophical Transactions of the Royal Society A*
   363, 2005.
10. A. Pnueli, M. Siegel, E. Singerman. Translation validation. *TACAS*, 1998.
11. L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming language. *CADE*, 2021.
12. A. Haas et al. Bringing the web up to speed with WebAssembly. *PLDI*, 2017.

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
