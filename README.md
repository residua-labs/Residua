# Residua

**Verifiable computation and proof, identified by content.**

English | [中文](README.zh-CN.md)

Residua is a research project building infrastructure for using another party's computation or proof without
trusting that party. Every result is identified by a content address (*q*, a SHA-256 digest of what the result is) rather than
by who produced it or which toolchain version built it, and a result is admitted only after mechanical checking against
formally defined semantics.

The language, **rsd**, is designed so that a program and a proof are terms of one dependent type theory: the same term is
compiled to native or WebAssembly code and checked by a proof kernel. Release 0.1 delivers the compilation half of that
design. The proof-checking half (the R-CIC kernel) is the subject of the next release.

> **Status:** research release **0.1** — the minimal self-bootstrapping closure of the rsd compiler.
> Not a general-purpose language yet. See [Limitations](#limitations).

## Why

- **Checking is not the expensive part.** For formal results, re-checking after upstream changes, repair, coordination and
  review cost far more than the kernel check itself.
- **Producers will be machines.** Most future results will come from automated agents that cannot be trusted. Only
  mechanical checking and content identity scale to that.
- **Semantics do not compose.** Results live in separate systems (Lean, Rocq, K, WebAssembly, the EVM) and do not carry
  across them.

## What 0.1 provides

**Verifiable-provenance compilation.** Given a source and an artifact, anyone can rebuild the compiler from a committed
WebAssembly seed using only a C compiler, and check byte for byte that the artifact comes from that source — trusting neither
the publisher nor a large binary toolchain.

| Component | Contents |
|---|---|
| Compiler chain | `rsd → rscm → wasm`: front end `rsdc` and back end `rsc`, with their complete sources (54 files, pinned by SHA-256) |
| Seed | `bootstrap/seed/stage-14274/`: the two compilers as WebAssembly, the recipe, and every digest it checks |
| Formal semantics | Frozen specifications of each layer (scm, λRC, wasm0), pinned by content digest (`semantics/`, `gates/semalign/`, `lean/rsd-cert/`) |
| Performance record | Measured against Koka and six other languages on fixed hardware ([`perf/`](perf/README.md)) |
| Documentation | Installation, verification protocol, architecture, trust model, glossary, stability policy, FAQ (`release/docs/`, English and Chinese) |

### Verification of this release

- The seed recipe was reproduced, from the documentation alone, by an independent agent with no prior knowledge of the
  project, on a fresh Linux virtual machine: both compilers rebuilt byte-identical to the seed.
- The release was reviewed by two independent model families.
- The repository tree at tag `rsd-0.1` is byte-identical to the published source archive.

## Quick start

Requirements: Linux x86-64, GCC, GNU binutils, coreutils, Bash, curl and tar. No Lean, Node or OCaml.

```sh
# 1. Download and verify the archive (from the rsd-0.1 release page)
sha256sum -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src

# 2. Rebuild both compilers from the seed in a clean environment (20-45 minutes)
env -i PATH=/usr/bin:/bin bash --noprofile --norc
#    then run the commands of bootstrap/seed/stage-14274/README.md
```

The recipe fetches a pinned WABT release, translates the two seed executors to C, builds them, recompiles both compilers
from source, and exits 0 only if the rebuilt compilers are byte-identical to the committed seed.

Then:

- [`release/docs/QUICKSTART`](release/docs/QUICKSTART) — the first run, step by step, and how to compile a source
- [`release/docs/VERIFY-RELEASE`](release/docs/VERIFY-RELEASE) — every digest check of the release
- [`release/docs/OVERVIEW`](release/docs/OVERVIEW) and [`release/docs/ARCHITECTURE`](release/docs/ARCHITECTURE) — what 0.1 is
  and how the layers fit together

## Performance

Measured on GCP t2d-standard-4 (two fresh VMs, median of five runs, pinned core). Ratio = Residua time / other time; below 1
means Residua is faster. Programs are taken unmodified from Koka's benchmark suite (the Perceus paper, PLDI 2021) and Lean 4's
benchmarks.

| Geometric mean, Residua 0.1 / … | Koka (native) | Koka (wasm) | C++ | OCaml | Haskell | Java | Lean 4.14 |
|---|---:|---:|---:|---:|---:|---:|---:|
| ratio | 0.973 | 1.047 | 0.822 | 0.586 | 0.281 | 0.451 | 0.570 |

Self-bootstrap from the seed takes 1162 s (peak 3.6 GiB). Per-program tables, empty cells and their causes, and the history
of every version are in [`perf/`](perf/README.md).

## Limitations

Release 0.1 is for reproducible, auditable compilation and for research on verified, bootstrappable compilers.

- Single-module programs only (no `import`).
- No I/O execution layer.
- No proof checking: the R-CIC kernel is not in this release, and shipped `theorem` texts are specifications, not checked claims.
- No `UInt64`; a 4 GiB address space.
- The content-identity (q) format is not final.
- The 0.1 surface language is a strict bootstrap subset; `theorem`, `axiom`, `class`, `abbrev` and `by` are refused
  ([`release/docs/LANGUAGE`](release/docs/LANGUAGE)).

## Roadmap

Releases are numbered 0.11, 0.12, … in the order their goals close. No dates are promised.

1. **Checking another party's result.** The R-CIC proof kernel, verdict-equal with Lean4Lean on its checked corpus and
   accepting no invalid input of the Lean Kernel Arena; the final q format; a publish and query entry for results.
2. **Programming completeness.** Modules, `UInt64`, 64-bit addressing, an I/O execution layer, real application suites.
3. **Cheap confirmation of execution.** wasm0 → AIR → zero-knowledge proofs.
4. **Connectors to external semantics.** K/KORE, Lean and Rocq import.

## Repository layout

| Path | Contents |
|---|---|
| `bootstrap/` | The committed seed, its recipe and the C host bridges |
| `rsdc/`, `rsc/`, `lib/` | Compiler sources (front end, back end, shared library and runtime) |
| `semantics/`, `gates/`, `lean/` | Frozen formal semantics and the per-layer translation checks |
| `release/` | Release manifest, provenance, notices, licences and documentation |
| `perf/` | Performance record of every version |

## Contributing and security

Issues are welcome. Report security problems through GitHub's private vulnerability reporting on this repository; see
[`release/docs/CONTRIBUTING-SECURITY`](release/docs/CONTRIBUTING-SECURITY).

## Acknowledgements

Residua builds on many other projects. [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md) lists the code we ported, the tools we used as
test oracles, and the designs we studied; per-file attribution is in `release/NOTICES.md` and `release/PROVENANCE.tsv`. If you
find your work used without credit, please open an issue or use private vulnerability reporting, and we will correct it.

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
