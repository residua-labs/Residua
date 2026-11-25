# RELEASE-NOTES — Residua 0.4

English | [中文](RELEASE-NOTES.zh-CN.md)

Release 0.4 keeps the self-bootstrap closure — verifiable-provenance
compilation rebuilt byte-identically from the committed WebAssembly
[seed](GLOSSARY.md) with only a C compiler — and adds multi-module `.rsd`
programs, IEEE-754 `Float` (`binary64`), `Proc` `do`-notation and the
C11 + Wasmtime `procwt` execution host, the standard `Proc` library
(`glue/std/`), the multi-module `examples/app04` CLI, a smaller and
faster recut seed, an Apache-2.0 balanced map (`lib/AvlMap.rsd`), and
multi-hop plus recursion composition theorems in `lean/nf-compose/`.
MST-NF is Residua's foundational theory: it lives in the public
repository
[github.com/residua-labs/MST-NF](https://github.com/residua-labs/MST-NF)
at pinned commit `4432a34`, which holds the proofs.

## New in 0.4

- **Modules, `Proc` `do`-notation, and the `procwt` execution host.**
  Multi-module `.rsd` programs use `import` across `lib/`, `glue/std/`
  and application modules, sequence effects with `do { let x <- … }`,
  and run as WebAssembly on the C11 + Wasmtime host `glue/host/procwt.c`
  (`glue/host/proc9core.h`; wasm2c counterpart `glue/host/proc9.c`).
  `glue/std/` ships `Args`, `Files`, `Graph`, `Json`, `Map`, `Proc` and
  `Str`; `lib/ProcBytes.rsd` and `lib/Proc9.rsd` ship the byte-slice and
  9P2000 codecs; `glue/rsd/main.rsd` and `glue/rsd/build.rsd` wire
  `rsd run` to `procwt`.
- **IEEE-754 `Float` (`binary64`).** Supported end-to-end across `rsdc`,
  the `.rscm` wire format (`docs/EMITTER.md`), `lambda-RC`, and
  WebAssembly emission, preserving `NaN`, `±Infinity` and `-0.0`, with
  differential oracle and mutation suites under `instruments/lrc-host/`.
- **Three-module CLI example (`examples/app04/`).** `Stats.rsd`,
  `Table.rsd` and `Main.rsd` read a line-delimited file of floating-point
  numbers, compute `count`, `min`, `max`, `mean` and population
  `variance`, format an aligned ASCII table with `String`, write an
  output file, and exit nonzero on malformed input or I/O errors —
  matching stock Lean `4.14.0` across all `16` differential inputs.
- **Smaller, faster recut seed (`bootstrap/seed/stage-14274/`).**
  `rsdc.wasm` drops from `19.9 MB` in 0.3 to `12,519,278` B
  (`845b99ef…`, entry `f896`, `__heap_base` `765288`) and `rsc.wasm`
  drops from `20.5 MB` to `14,275,644` B (`b52b07d1…`, entry `f2615`,
  word `14274`, `__heap_base` `603704`). `seed-host.c` reads each
  module's exported `__heap_base` global and supports `\0RSDC-ENTRIES\n`.
  Clean-environment compiler rebuild runs in `105 s` (`193 s` total
  recipe) on Linux x86-64 and `191 s` (`337 s` total recipe) on macOS
  arm64.
- **Apache-2.0 balanced map (`lib/AvlMap.rsd`).** Re-ported from Lean
  `v4.36.0` (`Std/Data/DTreeMap/Internal/Def.lean` and `Balancing.lean`),
  replacing 0.3's OCaml `stdlib/map.ml` port so every shipped compiler
  and library file carries a permissive licence.
- **Multi-hop and recursion MST-NF composition (`lean/nf-compose/`).**
  `NfCompose/HopCompose.lean` proves composition across compiler hops,
  and `NfCompose/Rec.lean` plus `NfRec/CheckedStatus.lean` prove bounded
  and well-founded recursion composition over the pinned `ExecModel`.

## MST-NF status at 0.4

Each shipped component is either bound to the pinned `ExecModel`
(`lean/nf-compose/pinned/MSTNecessityExecModelMWE.lean`) with the Tier-1
laws proved, or recorded as a gap.

| shipped component | status |
|---|---|
| compiler chain (`rsdc`, `rsc`) | gap — per-hop `ExecModel` instances repository-side; hop composition proved (`HopCompose.lean`) |
| execution layer (`semantics/Effect/`, `glue/host/`) | instance shipped: `monitorModel`, `exec9AdmissionModel`; Tier-1 laws proved (`AdmissionNF.lean`) |
| syntax engine (`rsdc/profiles/`, `semantics/Syntax/`) | gap — no `ExecModel` instance shipped yet |
| QFormat (`docs/QFORMAT.md`, `release/checks/qformat/`) | gap — no `ExecModel` instance shipped yet |
| `rsd` build tool (`rsd/`, `glue/rsd/`, `lib/rsd/`) | gap — no `ExecModel` instance shipped yet |
| NF composition (`lean/nf-compose/`) | framework shipped: product/sum/seq/dispatch, multi-hop (`HopCompose.lean`) and recursion (`Rec.lean`) composition proved |

## In this archive

- the committed `rsdc`/`rsc` wasm seeds and their `54`-member source
  closure under `bootstrap/seed/stage-14274/`, with the recipe that
  rebuilds them
- the rsd chain `rsd -> rscm -> wasm` (`docs/RSD-COMMAND.md`)
- the `Proc` execution hosts (`glue/host/`), standard `Proc` modules
  (`lib/ProcBytes.rsd`, `lib/Proc9.rsd`, `glue/std/`), and the
  `examples/app04/` multi-module CLI program
- the `rsd` build tool (`rsd/`, `glue/rsd/`, `lib/rsd/`, `lib/Rsd.rsd`)
- frozen formal semantics per layer (scm, lambda-RC, wasm0) pinned by
  content digest, plus `semantics/Syntax/` and `semantics/Effect/`
- the MST-NF composition package (`lean/nf-compose/`, including
  `HopCompose.lean`, `Rec.lean` and `NfRec/CheckedStatus.lean`) and its
  audit report (`reports/nf-compose/REPORT.md`)
- the benchmark, differential and performance suites (`benchmarks/`,
  `instruments/lrc-host/`, `perf/`)
- the language conformance corpus (`docs/LANGUAGE.md`) and performance
  record (`docs/PERF-RECORD.tsv`, `docs/PERF-RECORD.md`)
- English documentation with Chinese `.zh-CN.md` mirrors for `README`,
  `CHANGELOG` and paired `docs/` pages
- release notes (`release/notes/`), runnable conformance checks
  (`release/checks/`), reader-facing `release/GAPS.tsv`, provenance
  (`release/PROVENANCE.tsv`), notices (`release/NOTICES.md`, `NOTICE`)
  and vendored licence texts (`release/licenses/`)

## Verification

`docs/VERIFY-RELEASE.md` is the protocol: seed digests, archive digest,
clean-environment seed rebuild on Linux x86-64 or macOS arm64 verifying
byte-identical compiler output (`cmp` against `rsdc.wasm` and `rsc.wasm`
plus `REBUILT-SHA256SUMS`), and building and running `examples/app04` on
`procwt`.

## Stated limits of 0.4

Separate `.rmod` compilation omits `Float` and per-module `Proc`
`do`-desugaring (`release/GAPS.tsv`; multi-module builds assemble source
modules in topological order); `procwt` serves CLI arguments, clocks and
local file I/O over an in-process 9P2000 responder (`release/GAPS.tsv`
`G01`), without networking or subprocess spawning; part of `rsd`'s
native compiler-worker closure stays repository-side (`release/GAPS.tsv`
`G06`); no proof checking (the R-CIC kernel is not in this release); a
`4 GiB` WebAssembly linear-memory address space; no publish/query entry
for results. The bootstrap `.rsd` grammar refuses `theorem`, `axiom`,
`class`, `abbrev`, `variable`, `opaque` and `by`.

## Order after 0.4

1. R-CIC kernel and a publish/query entry for checking and reusing
   another party's result.
2. Separate `.rmod` compilation across the full language, 64-bit
   addressing, broader host capabilities, and application suites.
3. Inexpensive confirmation of execution: wasm0 -> AIR -> zk.
4. Connectors to external semantics (K/KORE, Lean/Rocq import).
