# OVERVIEW — what Residua is, what release 0.3 offers, its limits

English | [中文](OVERVIEW.zh-CN.md)

This is the long-form document: the design, the motivation, the evidence,
the limits, and the references. For the short version, read
[`README.md`](../README.md).

## What it is

Residua is a research project on reusing computational and deductive
results between parties that do not trust one another. A result is
identified by a content address ([q](GLOSSARY.md): a typed SHA-256 of the
result's bytes) rather than by its producer or by the version of the
toolchain that built it, and it is admitted only after mechanical
checking against formally defined semantics.

The project's language, [rsd](GLOSSARY.md), is designed so that a
program and a proof are terms of one dependent type theory: the same
term is compiled to native or WebAssembly code and checked by a proof
kernel. Releases so far contribute the compilation half of this design:
a self-bootstrapping compiler chain whose provenance any third party can
verify from a committed [seed](GLOSSARY.md), together with the toolchain's
content-identity format, its syntax engine, and the formal semantics of
its execution boundary. The proof-checking half (the [R-CIC](GLOSSARY.md) kernel) is
the subject of later releases.

## Why — four facts

1. **Maintenance dominates the cost of formal results.** Re-checking
   after upstream changes, repair, coordination and review cost far
   more than the kernel check itself.
2. **Producers are increasingly automated.** Output from automated
   agents cannot be accepted on the producer's word; only mechanical
   checking and content identity scale to that setting.
3. **Semantics are siloed.** Results live in separate systems (Lean,
   Rocq, K, WebAssembly, the EVM) and do not carry across them.
4. **Results are bound to toolchain versions.** A compiled library is
   tied to the toolchain version that built it (Lean's `.olean` files,
   for example), so a version change rebuilds and re-checks everything
   downstream. A result identified by its content remains the same
   result across versions.

## Approach

- **Identity by content.** An artifact or result is identified by its
  content address q. Equality of q is the criterion for reuse; names,
  locations and producers are not.
- **Admission by checking.** A result enters the system only through a
  mechanical check against formal semantics. The producer — a person, a
  compiler or an automated agent — is outside the trusted base (the
  de Bruijn criterion [9]).
- **One language for programs and proofs.** By design, an rsd term is
  both compiled and checked by one kernel, so a statement about a
  program is a statement about the term that runs.
- **A verifiable toolchain.** The compiler that produces every other
  artifact is itself reproducible from a committed seed, so its
  provenance is checked rather than assumed.

## What 0.3 offers — and only this

**Compilation with verifiable provenance.** Given a source and an
artifact, anyone can rebuild the compiler from the committed
WebAssembly seed with a C compiler and the pinned wasm runtime
(wasmtime v50.0.1 plus binaryen version_133 `wasm-opt`, both
user-downloaded), and check
byte for byte that the artifact derives from that source — trusting
neither the publisher nor a large binary toolchain. The recipe runs on
Linux x86-64 and macOS arm64.

Carried by this release:

- The rsd compiler chain `rsd → `[rscm](GLOSSARY.md)` → wasm` (front end `rsdc`, back end
  `rsc`), self-hosted: both compilers ship as committed seeds under
  `bootstrap/seed/` together with their pinned source membership and
  the recipe that rebuilds them.
- The `rsd` build tool (`rsd/` and `lib/rsd/`): `rsd build` compiles a
  program through the content-addressed store, recompiling only what
  changed; `rsd test` runs the end-to-end suite; `rsd run` executes;
  `rsd cache` is the content store itself. See `docs/BUILD.md`.
- The typed content address `q` (format v1): the kind of the addressed
  content lives inside the hashed bytes, so addresses of different
  kinds cannot collide (`docs/QFORMAT.md`, checks
  `release/checks/qformat/`).
- The syntax engine, closed over its grammar class: one function over
  grammar data, checked against a mechanically verified reference
  decider (`semantics/Syntax/`; profiles `rsdc/profiles/*.syn`).
- The bootstrap surface check: the compiler's six source files, `import`
  lines stripped and joined in member order into a 1,325,136-byte bundle,
  parse cleanly under the OCaml reference front end (corpus verdicts in
  `docs/LANGUAGE.md`).
- The execution-boundary semantics: wire format, admission and seal
  judgments, the conformance classifier and recorded transport
  sessions, as Lean 4.14 statements (`semantics/Effect/`).
- `UInt64` in the language.
- Frozen formal semantics of each compiler layer (scm, [lambda-RC](GLOSSARY.md),
  [wasm0](GLOSSARY.md)), pinned by content digest; their `.lean`/`.rsd` texts ship
  as the pinned specification. `theorem` declarations in these texts are
  pinned specification, not proof checking; `semantics/Effect/AdmissionNF.lean`
  ships for audit and its imports (`Lib.Exec9Core`, `Lib.Receipt`) are
  repository-side — checking it needs the development repository.
- The benchmark and differential test suites (`benchmarks/`,
  `instruments/lrc-host/`) and the per-version performance record
  (`perf/`, `docs/PERF-RECORD.md` + `.tsv`).
- The seed is recut at this release's sources (it carries `UInt64` and
  the current compiler membership); a fresh `bootstrap/seed/stage-*`
  directory replaces the 0.1-era one.

## How the chain fits together

- `rsdc` compiles `.rsd` source to `.rscm`, the binary interface of the
  scm layer (`docs/EMITTER.md`).
- `rsc` lowers `.rscm` to `.wasm` at the seed's pinned construction
  word.
- The C seed host `bootstrap/seed/stage-14274/seed-host.c` embeds the
  seed modules on the pinned wasmtime engine;
  `bootstrap/seed/stage-14274/` carries the host, the pins and the
  recipe.
- Invocation is the executor file contract documented in
  `docs/RSD-COMMAND.md`.

## Stated limits

- Single-module programs only: `import` is refused by the front edge.
- No I/O execution layer: program input/output is the host's file
  contract, not a language effect.
- No proof checking: the R-CIC kernel and certificates are not in this
  release; shipped `theorem` texts are pinned specification.
- No publish/query entry for results.
- No importable standard library (`docs/STDLIB.md`).
- The `.rsd` surface accepted by the front edge is the bootstrap subset
  of `docs/LANGUAGE.md`, which refuses `theorem`, `axiom`, `class`,
  `abbrev`, `variable`, `opaque`, `by` and `import`.

Who 0.3 is for: reproducible, auditable compilation — supply chain and
research on verified, bootstrappable compilers. It is not a
general-purpose language.

## Evidence

- **Independent reproduction.** The seed recipe was reproduced from the
  documentation alone, by an independent agent with no prior knowledge
  of the project, on a fresh Linux virtual machine: both compilers were
  rebuilt byte-identical to the seed.
- **Independent review.** The release was reviewed by two independent
  model families.
- **Archive identity.** The repository tree at the release tag is
  byte-identical to the published source archive.
- **Per-goal audit.** Each feature new in this release carries an
  independent signed audit; transcripts are collected repository-side.

## Research agenda

Feature releases are numbered 0.3, 0.4, … in the order in which their
goals are completed. No goal is tied to a number in advance, and no
dates are promised:

- **Checking another party's result.** The R-CIC proof kernel, the
  final q format and a publish-and-query entry for results.
- **Programming completeness.** Modules, 64-bit addressing, an I/O
  execution layer, real application suites.
- **Inexpensive confirmation of execution.** wasm0 → AIR →
  zero-knowledge proofs.
- **Connections to external semantics.** K/KORE, Lean and Rocq import.

## Related work

The seed-based bootstrap addresses the trusting-trust problem [1];
related approaches are diverse double-compiling [2] and bootstrappable
builds [3], and verified bootstrapping of a compiler was established by
CakeML [4]. The back end manages memory by reference counting with
reuse, after "Counting Immutable Beans" [6] and Perceus [5]; its passes
are ported from the compiler of Lean 4 [11], and its target is
WebAssembly [12]. Accepting results from untrusted producers on
checkable evidence is in the tradition of proof-carrying code [8]; the
per-layer translation checks are in the tradition of translation
validation [10]. The planned proof kernel is compared against
Lean4Lean [7]. `release/NOTICES.md` and `release/PROVENANCE.tsv` list
the code this project ported, the tools it used as test oracles, and
the designs it studied.

## References

1. K. Thompson. Reflections on trusting trust. *Communications of the
   ACM* 27(8), 1984.
2. D. A. Wheeler. Countering trusting trust through diverse
   double-compiling. *ACSAC*, 2005.
3. Bootstrappable Builds. https://bootstrappable.org
4. R. Kumar, M. O. Myreen, M. Norrish, S. Owens. CakeML: a verified
   implementation of ML. *POPL*, 2014.
5. A. Reinking, N. Xie, L. de Moura, D. Leijen. Perceus: garbage free
   reference counting with reuse. *PLDI*, 2021.
6. S. Ullrich, L. de Moura. Counting immutable beans: reference
   counting optimized for purely functional programming. *IFL*, 2019.
7. M. Carneiro. Lean4Lean: verifying a typechecker for Lean, in Lean.
   arXiv:2403.14064, 2024.
8. G. C. Necula. Proof-carrying code. *POPL*, 1997.
9. H. Barendregt, F. Wiedijk. The challenge of computer mathematics.
   *Philosophical Transactions of the Royal Society A* 363, 2005.
10. A. Pnueli, M. Siegel, E. Singerman. Translation validation.
    *TACAS*, 1998.
11. L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming
    language. *CADE*, 2021.
12. A. Haas et al. Bringing the web up to speed with WebAssembly.
    *PLDI*, 2017.
