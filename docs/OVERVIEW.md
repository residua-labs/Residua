# OVERVIEW — what Residua is, what release 0.4 offers, its limits

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
a self-bootstrapping compiler chain whose provenance any party can
verify from a committed [seed](GLOSSARY.md), together with the toolchain's
content-identity format, its syntax engine, its `Proc` execution host,
and the formal semantics of its execution boundary. The proof-checking
half (the [R-CIC](GLOSSARY.md) kernel) is the subject of later releases.

## Why — key facts

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
  de Bruijn criterion [^9]).
- **One language for programs and proofs.** By design, an rsd term is
  compiled and checked by one kernel, so a statement about a program is
  a statement about the term that runs.
- **A verifiable toolchain.** The compiler that produces every other
  artifact is itself reproducible from a committed seed, so its
  provenance is checked rather than assumed.

## What 0.4 offers — and only this

**Compilation and CLI/file execution with verifiable provenance.** Given
multi-module `.rsd` sources and an artifact, anyone can rebuild the
compiler from the committed WebAssembly seed with a C compiler and the
pinned wasm runtime (wasmtime v50.0.1 plus binaryen version_133
`wasm-opt`, user-downloaded), verify byte for byte that the compiler
reproduces its seed, compile a multi-module `Proc` program to
WebAssembly, and run it on the C11 `procwt` host — trusting neither the
publisher nor a large binary toolchain. The recipe runs on Linux x86-64
and macOS arm64.

Carried by this release:

- The rsd compiler chain `rsd → `[rscm](GLOSSARY.md)` → wasm` (front end `rsdc`, back end
  `rsc`), self-hosted: the compilers ship as committed seeds under
  `bootstrap/seed/stage-14274/` (`rsdc.wasm` `12,519,278` bytes,
  `rsc.wasm` `14,275,644` bytes) together with their pinned `54`-member
  source closure and the recipe that rebuilds them in `105 s` on Linux
  x86-64 and `191 s` on macOS arm64.
- Multi-module `.rsd` programs (`import`), IEEE-754 `Float` (`binary64`),
  `do`-notation over `Proc`, the standard `Proc` library
  (`lib/ProcBytes.rsd`, `lib/Proc9.rsd`, `glue/std/`), the C11
  WebAssembly and wasm2c `Proc` execution hosts (`glue/host/procwt.c`,
  `glue/host/proc9core.h`, `glue/host/proc9.c`), and the multi-module
  CLI example (`examples/app04/`).
- The `rsd` build tool (`rsd/`, `glue/rsd/`, `lib/rsd/`, `lib/Rsd.rsd`):
  `rsd build` compiles a program through the content-addressed store,
  recompiling only what changed; `rsd test` runs the end-to-end suite;
  `rsd run` executes `Proc` programs on `procwt`; `rsd cache` is the
  content store itself. See `docs/BUILD.md`.
- An Apache-2.0 balanced map (`lib/AvlMap.rsd`), ported from Lean
  v4.36.0 (`Std.DTreeMap`), replacing the 0.3 OCaml `stdlib/map.ml` port.
- The typed content address `q` (format v1): the kind of the addressed
  content lives inside the hashed bytes, so addresses of different
  kinds cannot collide (`docs/QFORMAT.md`, checks
  `release/checks/qformat/`).
- The syntax engine, closed over its grammar class: a single function over
  grammar data, checked against a mechanically verified reference
  decider (`semantics/Syntax/`; profiles `rsdc/profiles/*.syn`).
- The bootstrap surface check: the compiler's source bundle (`import`
  lines stripped and joined in member order into a 1,447,122-byte bundle)
  parses cleanly under the OCaml reference front end (corpus verdicts in
  `docs/LANGUAGE.md`).
- The execution-boundary semantics (`semantics/Effect/`) and the
  MST-NF composition package (`lean/nf-compose/`, extended in 0.4 with
  multi-hop compiler composition in `HopCompose.lean` and recursion
  composition in `Rec.lean` and `NfRec/CheckedStatus.lean`).
- Frozen formal semantics of each compiler layer (scm, [lambda-RC](GLOSSARY.md),
  [wasm0](GLOSSARY.md)), pinned by content digest; their `.lean`/`.rsd` texts ship
  as the pinned specification. `theorem` declarations in these texts are
  pinned specification, not proof checking; `semantics/Effect/AdmissionNF.lean`
  ships for audit and its imports (`Lib.Exec9Core`, `Lib.Receipt`) are
  repository-side — checking it needs the development repository.
- The benchmark and differential test suites (`benchmarks/`,
  `instruments/lrc-host/`, including `Float` differential and mutation
  checks) and the per-version performance record (`perf/`,
  `docs/PERF-RECORD.md` + `.tsv`).

## How the chain fits together

- `rsdc` compiles `.rsd` source to `.rscm`, the binary interface of the
  scm layer (`docs/EMITTER.md`), and prints export indices when given the
  `\0RSDC-ENTRIES\n` header.
- `rsc` lowers `.rscm` to `.wasm` at the seed's pinned construction
  word (`14274`).
- `seed-host.c` embeds the seed modules on the pinned wasmtime engine
  and reads each module's exported `__heap_base` global so heap
  allocation begins above static data segments; `glue/host/procwt.c`
  hosts compiled `Proc` WebAssembly modules over an in-process 9P2000
  responder.
- Compiler invocation follows the file contract in `docs/RSD-COMMAND.md`.

## Stated limits

- Separate `.rmod` module compilation omits `Float` (`type code 13`) and
  per-module `Proc` `do`-desugaring (`release/GAPS.tsv`); multi-module
  programs assemble modules in topological order before `rsdc`.
- `glue/host/procwt.c` serves CLI arguments, clocks and local file
  reads/writes over an in-process 9P2000 responder (`release/GAPS.tsv`);
  networking and subprocess spawning are not included.
- No proof checking: the R-CIC kernel and certificates are not in this
  release; shipped `theorem` texts are pinned specification.
- No publish/query entry for results.
- The `.rsd` surface accepted by the front edge is the bootstrap subset
  of `docs/LANGUAGE.md`, which refuses `theorem`, `axiom`, `class`,
  `abbrev`, `variable`, `opaque` and `by`.

Who 0.4 is for: reproducible, auditable compilation and self-contained
CLI/file programs — supply chain and research on verified,
bootstrappable compilers.

## Evidence

- **Independent reproduction.** The seed recipe was reproduced on clean
  Linux x86-64 and macOS arm64 environments: the compilers rebuilt
  byte-identical to the committed seed, and `examples/app04` matched the
  stock Lean 4.14.0 oracle across all `16` differential test cases.
- **Independent review.** Each release line is reviewed across
  independent model families.
- **Archive identity.** The repository tree at the release tag is
  byte-identical to the published source archive.
- **Per-goal audit.** Each feature in this release carries an
  independent audit; transcripts are collected repository-side.

## Research agenda

Feature releases are numbered 0.3, 0.4, … in the order in which their
goals are completed. No goal is tied to a number in advance, and no
dates are promised:

- **Checking another party's result.** The R-CIC proof kernel, the
  final q format and a publish-and-query entry for results.
- **Programming completeness.** Separate `.rmod` compilation across the
  full language, 64-bit WebAssembly addressing, broader host services,
  and larger application suites (such as Cedar and mathlib4 imports).
- **Inexpensive confirmation of execution.** wasm0 → AIR →
  zero-knowledge proofs.
- **Connections to external semantics.** K/KORE, Lean and Rocq import.

## Related work

The seed-based bootstrap addresses the trusting-trust problem [^1];
related approaches are diverse double-compiling [^2] and bootstrappable
builds [^3], and verified bootstrapping of a compiler was established by
CakeML [^4]. The back end manages memory by reference counting with
reuse, after "Counting Immutable Beans" [^6] and Perceus [^5]; its passes
are ported from the compiler of Lean 4 [^11], and its target is
WebAssembly [^12]. Accepting results from untrusted producers on
checkable evidence is in the tradition of proof-carrying code [^8]; the
per-layer translation checks are in the tradition of translation
validation [^10]. The planned proof kernel is compared against
Lean4Lean [^7]. `release/NOTICES.md` and `release/PROVENANCE.tsv` list
the code this project ported, the tools it used as test oracles, and
the designs it studied.

## References

[^1]: K. Thompson. Reflections on trusting trust. *Communications of the
   ACM* 27(8), 1984.
[^2]: D. A. Wheeler. Countering trusting trust through diverse
   double-compiling. *ACSAC*, 2005.
[^3]: Bootstrappable Builds. https://bootstrappable.org
[^4]: R. Kumar, M. O. Myreen, M. Norrish, S. Owens. CakeML: a verified
   implementation of ML. *POPL*, 2014.
[^5]: A. Reinking, N. Xie, L. de Moura, D. Leijen. Perceus: garbage free
   reference counting with reuse. *PLDI*, 2021.
[^6]: S. Ullrich, L. de Moura. Counting immutable beans: reference
   counting optimized for purely functional programming. *IFL*, 2019.
[^7]: M. Carneiro. Lean4Lean: verifying a typechecker for Lean, in Lean.
   arXiv:2403.14064, 2024.
[^8]: G. C. Necula. Proof-carrying code. *POPL*, 1997.
[^9]: H. Barendregt, F. Wiedijk. The challenge of computer mathematics.
   *Philosophical Transactions of the Royal Society A* 363, 2005.
[^10]: A. Pnueli, M. Siegel, E. Singerman. Translation validation.
    *TACAS*, 1998.
[^11]: L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming
    language. *CADE*, 2021.
[^12]: A. Haas et al. Bringing the web up to speed with WebAssembly.
    *PLDI*, 2017.
