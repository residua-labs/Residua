# Changelog

English | [中文](CHANGELOG.zh-CN.md)

All notable changes to this project are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). A feature release is
numbered 0.2, 0.3, …, in the order in which goals are completed; a patch
release of a published version (documents, attribution, packaging, shipped
test suites; the inputs of the bootstrap recipe unchanged) is numbered
0.x.y. A published tag is never moved. Each release lists the SHA-256 of its
source archive; the repository tree at the tag equals the archive.

## [0.4] — 2026-11-25

### Added

- `examples/app04/` (`examples/app04/Stats.rsd`, `examples/app04/Table.rsd`,
  `examples/app04/Main.rsd`): multi-module CLI program reading a
  line-delimited file of floating-point numbers, computing `count`, `min`,
  `max`, `mean` and population `variance` with `Float` (`binary64`),
  formatting an aligned ASCII table with `String`, writing an output file,
  and exiting nonzero with diagnostics on malformed lines or I/O errors.
- `glue/host/` (`glue/host/procwt.c`, `glue/host/proc9core.h`,
  `glue/host/proc9.c`): C11 `Proc` execution hosts for WebAssembly
  (Wasmtime C API v50.0.1, reading exported `__heap_base` and probing
  `driveS` automatically) and wasm2c, backed by an in-process 9P2000
  responder serving `/env/args`, `/dev/time`, `/dev/mono` and host file
  reads/writes.
- `glue/std/` (`glue/std/Args.rsd`, `glue/std/Files.rsd`,
  `glue/std/Graph.rsd`, `glue/std/Json.rsd`, `glue/std/Map.rsd`,
  `glue/std/Proc.rsd`, `glue/std/Str.rsd`) and `lib/ProcBytes.rsd`,
  `lib/Proc9.rsd`: standard `Proc` modules for CLI arguments, chunked file
  I/O, strings, JSON, maps, graphs, byte slices and 9P2000 frames.
- `glue/rsd/` (`glue/rsd/main.rsd`, `glue/rsd/build.rsd`): `rsd run`
  front-door entry and build script connecting `import`-using `Proc`
  programs to `procwt` and `wasm-opt --translate-to-exnref`.
- `lean/nf-compose/NfCompose/HopCompose.lean`,
  `lean/nf-compose/NfCompose/Rec.lean` and
  `lean/nf-compose/NfRec/CheckedStatus.lean`: multi-hop compiler
  composition and bounded/well-founded recursion composition theorems over
  the pinned `ExecModel`.
- `instruments/lrc-host/CheckFloat64.rsd`,
  `instruments/lrc-host/Float64Oracle.rsd`,
  `instruments/lrc-host/Wasm2CHost.c`,
  `instruments/lrc-host/MutantsBound.tsv`,
  `instruments/lrc-host/MutantsExcl.tsv`,
  `instruments/lrc-host/MutantsF64.tsv`,
  `instruments/lrc-host/MutantsFlow.tsv`,
  `instruments/lrc-host/MutantsKBox.tsv`,
  `instruments/lrc-host/MutantsLit.tsv`,
  `instruments/lrc-host/MutantsLoops.tsv`,
  `instruments/lrc-host/ProgArrFlow.rsd`,
  `instruments/lrc-host/ProgBound.rsd`,
  `instruments/lrc-host/ProgKBox.rsd`,
  `instruments/lrc-host/ProgLitCall.rsd`,
  `instruments/lrc-host/ProgLitWord.rsd`,
  `instruments/lrc-host/ProgNumTail.rsd` and
  `instruments/lrc-host/ProgPad.rsd`: IEEE-754 `Float` (`binary64`)
  differential oracle, wasm2c host and compiler mutation/regression inputs.

### Changed

- Recut seed under `bootstrap/seed/stage-14274/` and updated
  `bootstrap/README.md`: `rsdc.wasm` (`12,519,278` B, `845b99ef…`, entry
  `f896`, `__heap_base` `765288`) and `rsc.wasm` (`14,275,644` B,
  `b52b07d1…`, entry `f2615`, word `14274`, `__heap_base` `603704`) replace
  the 0.3 seed blobs (`19.9 MB` / `20.5 MB`); `seed-host.c` reads the
  loaded module's exported `__heap_base` global and supports the
  `\0RSDC-ENTRIES\n` query header; clean-environment rebuild runs in
  `105 s` on Linux x86-64 and `191 s` on macOS arm64.
- `rsdc/`, `rsc/`, `lib/`, `lib/lrc/`, `docs/EMITTER.md`, `semantics/`,
  `lean/rsd-cert/Residua/Bootstrap/R2/` and `instruments/lrc-host/`: added
  IEEE-754 `Float` (`binary64`), multi-module `import` support, `Proc`
  `do`-notation, `\0RSDC-ENTRIES\n` entry inspection, and updated array,
  constructor-layout and reference-counting passes.
- `lib/AvlMap.rsd`: replaced the 0.3 OCaml `stdlib/map.ml` port with an
  Apache-2.0 port of Lean `v4.36.0`'s weight-balanced tree
  (`Std/Data/DTreeMap/Internal/Def.lean` and `Balancing.lean`).
- `rsd/`, `lib/rsd/` and `benchmarks/MANIFEST.tsv`: updated build-tool
  modules and benchmark manifest metadata for the 0.4 tree.
- `lean/nf-compose/NfCompose/Hop.lean` and
  `lean/nf-compose/lakefile.lean`: a hop is admitted only if the translated
  program is itself admissible on the target side; the package builds the
  new modules.
- `gates/semalign/METHOD.md`, `reports/nf-compose/REPORT.md`,
  `benchmarks/koka/README.md` and `benchmarks/koka/README.zh-CN.md`:
  corrections of code spans and of one command line; no change of meaning.
- `README.md`, `README.zh-CN.md`, `CHANGELOG.md`, `CHANGELOG.zh-CN.md`,
  `docs/`, `NOTICE` and `release/`:
  updated quick start (`examples/app04` built and run from the seed),
  `docs/BUILD.md` + `.zh-CN.md`, `docs/VERIFY-RELEASE.md`, `docs/SPECS.md`,
  `docs/LANGUAGE.md`, `docs/STDLIB.md`, `docs/OVERVIEW.md` + `.zh-CN.md`,
  `docs/RELEASE-NOTES.md` + `.zh-CN.md`, `release/GAPS.tsv`,
  `release/SHIP-RULES.tsv`, `release/PROVENANCE.tsv`, `release/NOTICES.md`,
  `release/BUILD-INPUTS.tsv`, `release/MANIFEST.md` and
  `release/PRIOR-SHIP-SETS.tsv`.

### Removed

- None (every path shipped in 0.3 remains in 0.4).

## [0.3] — 2026-11-24

### Added

- The `rsd` build tool: `rsd build`, `rsd test`, `rsd run`, `rsd cache`
  (dispatcher and compiler worker `rsd/`; store, dependency graph and
  session layer `lib/rsd/`, `lib/Rsd.rsd`; user document `docs/BUILD.md`;
  planted-row conformance check `release/checks/rsd-tool/`). The sources
  ship; `lib/laws/RsdScheduleLaws.rsd` ships the schedule laws for
  `lib/rsd/schedule.rsd`. Building the tool itself needs the
  development repository — the runnable compiler in this archive is the
  seed recipe.
- `UInt64` support in the language (the compiler sources now use it).
- The benchmark and test suites the 0.1.1/0.1.2 archives shipped and 0.2
  dropped, restored: `benchmarks/`, `instruments/lrc-host/`, `perf/`,
  `ACKNOWLEDGEMENTS.md` + `.zh-CN.md`, `lib/lrc/Closures.rsd`, and the
  TESTING guide as `TESTING.md` + `.zh-CN.md`.
- `benchmarks/koka/entries.tsv`, `benchmarks/koka/images.tsv` and
  `benchmarks/koka/modules.tsv`: the narrow-table inputs and the
  per-module/per-image digests measured on the 0.3 seed.
- `instruments/lrc-host/ProgWrap.rsd` (its emitted
  `instruments/lrc-host/img/progwrap.rscm` image stays repository-side
  like the other generated images).
- `examples/surfaces/` and `docs/surfaces/`: five programs each printed
  in the `.rsd`, `.rsj` and `.rsm` surface spellings, with a round-trip
  check that all three parse to the same tree.
- The MST-NF composition theorems in Lean 4.14 (`lean/nf-compose/`):
  composition rules for the pinned necessity-execution model, built and
  checked on the release toolchain with an independent audit passed
  (`reports/nf-compose/REPORT.md` ships as the audit report). MST-NF is
  Residua's foundational theory: it lives in the public repository
  [github.com/residua-labs/MST-NF](https://github.com/residua-labs/MST-NF)
  at pinned commit `4432a34`, which holds the proofs.
- `semantics/Effect/AdmissionNF.lean`: the execution layer's typed
  `ExecModel` instances (`monitorModel`, `exec9AdmissionModel`) with
  the four Tier-1 laws proved — the first typed instances shipped
  (0.1 and 0.2 had none; their `Monitor.lean` cited the three-form
  encoding, which is not the definition). Receipt:
  `reports/effect-sem/ADMISSION-NF.md`.
- `release/TERMS.tsv`: the word policy for public prose (which internal
  words leave, which real terms get a glossary entry), checked by the gate.
- Community files: `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md` (Contributor
  Covenant 2.1), `SECURITY.md`, issue and pull-request templates under
  `.github/`.
- Per-feature notes under `release/notes/`, English and Chinese.
- A gate check that the ship set never drops a path an earlier published
  release shipped without a CHANGELOG line saying so
  (`release/PRIOR-SHIP-SETS.tsv`).

### Changed

- Public documents rewritten for outside readers: `README.md` in the
  usual open-source order, `docs/` arranged by the Diátaxis split with an
  index, the release notes in plain words, academic text moved to
  `docs/OVERVIEW.md`.
- `docs/GLOSSARY.md` + `.zh-CN.md`: expanded for the new 0.3 terms.
- `semantics/Rsx/Lower.rsd`: the adequacy statements `AdeqApp`,
  `AdeqLetE`, `AdeqConst`, `AdeqConstDelta` and `adequacyClosed` gained an
  `EnvClosed` hypothesis, and refutations of the unguarded forms were
  added (`not_adeqApp`, `not_adeqLetE`, `not_adeqConstDelta`).
- `rsdc/profiles/rsd.syn`, `rsj.syn`, `rsm.syn` and `rsv.syn`: the
  grammars gained the `syntax_124_max`/`imax`, `syntax_162_tactic`,
  `syntax_217`, `syntax_327`, `syntax_415`, `syntax_518` and
  `syntax_565_*` production family (`rsm.syn` in surface notation,
  `rsd.syn` the corresponding tokens and rules).
- New seed cut: the committed seed is rebuilt at this head and carries
  the current compiler sources (including `UInt64`); from this cut the
  wasm route compiles with the `narrow` layer as its default and the
  native route stays 64-bit.
- The bootstrap recipe now runs the seed in its own Wasm form on a
  pinned wasmtime C API (v50.0.1) through the C host
  `bootstrap/seed/stage-14274/seed-host.c`, with
  `wasm-opt --translate-to-exnref` (binaryen version_133) recoding the
  seeds' legacy exception-handling instructions; the wasm2c translation
  and the C optimizer over the seed are gone, and the recipe runs on
  Linux x86-64 and macOS arm64.
- `CHANGELOG.md` reformatted to Keep a Changelog.

### Removed

- `bootstrap/seed/stage-14274/ASSEMBLY.tsv` — the recut does
  not emit it; member binding is verified on the
  `RscSourceModule_<sha256>` section markers inside `sources/rsdc.rsd`
  and `sources/rsc.rsd` instead.
- `release/FINDINGS.tsv` — a table derived by the release gate; it stays in the
  development repository.
- `bootstrap/seed/stage-14274/WABT-MACOS-ARM64-SHA256SUMS` — superseded;
  the new wasm-runtime recipe runs on Linux x86-64 and macOS arm64 and
  needs no WABT toolchain.
- The generated and binary files leave the source archive (the
  release ships the recut seed pair only; everything else
  is built or generated by the user). Each path below was shipped
  by the named earlier release:
  - `benchmarks/bfs.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/bfs.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/binarytrees.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/binarytrees.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/cfold.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/cfold.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/deriv.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/deriv.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/editdist.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/editdist.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/fannkuch.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/fannkuch.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/gameoflife.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/gameoflife.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/hashmap.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/hashmap.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/histogram.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/histogram.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/lexer.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/lexer.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/merkle.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/merkle.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/nqueens.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/nqueens.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/pidigits.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/pidigits.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/queens.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/queens.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/rbtree.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/rbtree.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/rbtreeck.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/rbtreeck.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/symreg.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/symreg.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/terrain.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/terrain.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/treebitonic.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/treebitonic.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/treematmul.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/treematmul.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `benchmarks/treeradix.rscm` (0.1.2) — emitted module (generated); the `.rsd` source ships.
  - `benchmarks/treeradix.rscm.meta` (0.1.2) — generated sidecar of an emitted module.
  - `bootstrap/ProcWasm2CHost.c` (0.1/0.1.1/0.1.2/0.2) — wasm2c C host; the seed runs on pinned wasmtime via stage-14274/seed-host.c.
  - `bootstrap/seed/manifest.json` (0.1/0.1.1/0.1.2/0.2) — superseded seed manifest; stage-14274/CUT.tsv is the cut record.
  - `bootstrap/seed/rsc.rscm` (0.1/0.1.1/0.1.2/0.2) — emitted module (generated); the `.rsd` source ships.
  - `bootstrap/seed/rsc.wasm` (0.1/0.1.1/0.1.2/0.2) — superseded pinned seed blob; the recut pair is the one seed.
  - `bootstrap/seed/rsdc.wasm` (0.1/0.1.1/0.1.2/0.2) — superseded pinned seed blob; the recut pair is the one seed.
  - `bootstrap/seed/stage-14274/EXECUTOR-SHA256SUMS` (0.1/0.1.1/0.1.2/0.2) — wasm2c-route pin; kept repository-side for the internal check tool.
  - `bootstrap/seed/stage-14274/WABT-RUNTIME-SHA256SUMS` (0.1/0.1.1/0.1.2/0.2) — wasm2c-route pin; kept repository-side for the internal check tool.
  - `bootstrap/seed/stage-14274/WABT-SHA256SUMS` (0.1/0.1.1/0.1.2/0.2) — wasm2c-route pin; kept repository-side for the internal check tool.
  - `bootstrap/sources.json` (0.1/0.1.1/0.1.2/0.2) — superseded seed metadata.
  - `bootstrap/Wasm2CHost.c` (0.1/0.1.1/0.1.2/0.2) — wasm2c C host; the seed runs on pinned wasmtime via stage-14274/seed-host.c.
  - `instruments/lrc-host/img/binarytrees.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/binarytreeskk.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/cfold.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/deriv.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/litlong.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/nqueens.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/nqueenskk.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progarr.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progbtkoka.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progclosed.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progconv.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progeq.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progeq2.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progeq2x.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/proghead.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/proginl.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progkinds.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progloops.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progmag.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progmap.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progmap2.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/prognarrow.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/prognum.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/prognumeral.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/prognumind.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/prognumxlen.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/prognumxnum.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/prognumxtag.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progorder.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progpack.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progtest.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/progwidth.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/rbtree.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/rbtreeck.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/treebitonic.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `instruments/lrc-host/img/treematmul.rscm` (0.1.2) — pinned image (generated); re-emit by compiling its Prog source — TESTING.
  - `release/checks/qformat/vectors/crafted.bin` (0.2) — generated conformance vector; the check README gives the command that makes it.
  - `release/checks/qformat/vectors/hello.bin` (0.2) — generated conformance vector; the check README gives the command that makes it.
  - `release/checks/qformat/vectors/nf1.bin` (0.2) — generated conformance vector; the check README gives the command that makes it.
  - `release/checks/qformat/vectors/one.bin` (0.2) — generated conformance vector; the check README gives the command that makes it.
  - `reports/codex4-assign5-stage-word/Wasm2CHost.c` (0.1/0.1.1/0.1.2/0.2) — wasm2c C host; the seed runs on pinned wasmtime via stage-14274/seed-host.c.


### Fixed

- The 0.2 archive silently dropped suites 0.1.1/0.1.2 shipped; 0.3
  restores them (see Added) and the new gate check keeps a later release
  from doing the same.

#### MST-NF status at 0.3

Each shipped component is either bound to the pinned `ExecModel` with
the four Tier-1 laws proved, or recorded as a gap.

| shipped component | status |
|---|---|
| compiler chain (`rsdc`, `rsc`) | gap — no `ExecModel` instance yet |
| execution layer (`semantics/Effect/`) | instance shipped: `monitorModel`, `exec9AdmissionModel`; Tier-1 laws proved (`AdmissionNF.lean`) |
| syntax engine | gap — no `ExecModel` instance yet |
| QFormat | gap — no `ExecModel` instance yet |
| `rsd` build tool | gap — no `ExecModel` instance yet |
| NF composition (`lean/nf-compose/`) | framework shipped: composition theorems over the pinned model, independently audited |

## [0.2] — 2026-11-20

### Added

- Typed content address (q format v1): `q(kind, c) =
  SHA-256("<kind> <len>\0" ++ c)`, printed `sha256:<hex>`; raw SHA-256
  remains as `digest` for file integrity and interop only.
  ([`docs/QFORMAT.md`](docs/QFORMAT.md), checks
  [`release/checks/qformat/`](release/checks/qformat/)).
- A syntax engine closed over its grammar class: one function over
  grammar data, checked against a mechanically verified reference decider
  (`semantics/Syntax/`; sources `rsdc/syntax/`; profiles
  `rsdc/profiles/*.syn`).
- Execution-boundary semantics: wire format, admission and seal
  judgments, the conformance classifier and recorded transport sessions,
  as Lean 4.14 statements (`semantics/Effect/`).
- The bootstrap recipe gained a macOS arm64 host (Apple clang,
  `PATH=/usr/bin:/bin`, no Lean), reproduced byte-identically on two
  Darwin hosts.
- User documents moved from `release/docs/` to `docs/` as Markdown,
  English and Chinese.
- Archive: `rsd-src.tar`, SHA-256
  `151bfd4f6a910e9c4232e84b6cf6cfd7618a1009e5c32d41acd995b9b0d5b8fb`,
  212 files.

### Changed

- The seed members stayed at their 0.1 bytes (no recut); five declared
  increments were exempt — the seed README recipe, `ASSEMBLY.tsv`,
  `CUT.tsv`, the macOS WABT pin and `bootstrap/Wasm2CHost.c`.

## [0.1.2] — 2026-11-19

### Added

- `benchmarks/` (186 files): the benchmark programs and their emitted
  `.rscm` modules, `expected/` outputs, the Rust reference
  implementations, the Koka comparison harness, and `benchmarks/langs/`
  with the vendored Koka `test/bench` and Lean `4.14` `test/bench`
  sources the ports derive from (Koka Apache-2.0, Lean 4 Apache-2.0,
  Benchmarks Game BSD-3-Clause, Bend Apache-2.0).
- `instruments/lrc-host/` (101 files): the differential test suite —
  `Diff.rsd`, the Sides/Mutants tables, `Images.tsv`, `Peaks.tsv` and the
  pinned `img/` images.
- The TESTING guide (`TESTING.md` and `TESTING.zh-CN.md` at the root).

### Changed

- The public documents followed the publication register of the 0.1.1
  documents; the release gate checked the ship set mechanically against
  a table of internal identifiers.
- Archive: `rsd-src.tar`, SHA-256
  `a3185221854ccbf61642d65e88cc37102235ed06474dbd542a83a3eae0577a47`,
  437 files.

## [0.1.1] — 2026-11-19

### Added

- `ACKNOWLEDGEMENTS.md` and `ACKNOWLEDGEMENTS.zh-CN.md`; both READMEs
  rewritten in the publication register.
- `perf/`: the per-version performance record moved into the archive.

### Changed

- Attribution completed: per-file verbatim upstream headers for the
  Lean 4 ports, and 6 repository-side provenance rows for the `web/h5i`
  design at upstream `9774f28a2a` (Apache-2.0).
- Internal publisher identifiers removed from shipped notices and
  provenance; the release gate rejects them mechanically.
- Archive: `rsd-src.tar`, SHA-256
  `165690af75bebf7841cbd3f14459d66b7d295aa65f2676b935eee5ee3a9b030b`,
  148 files.

### Removed

- The `web/` application tree (52 files): repository-side now, cited by
  path and digest in `docs/LANGUAGE.md`. Ship set became 148 files.

### Fixed

- Version scheme corrected: feature releases are 0.2, 0.3, … (0.11 would
  sort after 0.10); patch releases are 0.1.1, 0.1.2, ….

## [0.1] — 2026-11-19

### Added

- First public release: the minimal self-bootstrapping closure of the
  rsd compiler — `rsd → rscm → wasm` (`rsdc`, `rsc`) with its 54 source
  files, and a committed WebAssembly seed that rebuilds both compilers
  byte for byte with only a C compiler.
- Frozen formal semantics of each layer (scm, λRC, wasm0), pinned by
  content digest.
- Performance record against Koka on GCP t2d-standard-4; reference
  columns for C++, OCaml, Haskell, Java, Swift and Lean 4.14.
- Evidence: the [fixed point](docs/GLOSSARY.md) was reproduced from the documentation alone
  by an independent agent on a fresh Linux virtual machine; the release
  was reviewed by two independent model families.
- Archive: `rsd-src.tar`, SHA-256
  `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`,
  201 files.

[0.4]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.4
[0.3]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.3
[0.2]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.2
[0.1.2]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2
[0.1.1]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.1
[0.1]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1
