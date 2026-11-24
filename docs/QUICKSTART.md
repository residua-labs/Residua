# QUICKSTART — first run against the 0.3 release

Release 0.3 carries the self-bootstrap closure: the committed wasm
[seed](GLOSSARY.md), the `rsdc`/`rsc` source closure, the runtime and these documents,
plus the `rsd` build tool as sources (`docs/BUILD.md` — it cannot be
compiled from the archive alone) and the `examples/surfaces/` programs.
The first run is the seed recipe itself. Every claim names its source.
This document will change in later versions.

## 20 to 45 minutes: rebuild the compilers from the seed

On a clean Linux x86-64 checkout — or macOS arm64; or the source
archive extracted
into a fresh directory (`mkdir rsd-src && tar -xf rsd-src.tar -C
rsd-src`; the archive's members sit at its top level) — with GCC,
GNU binutils, coreutils, Bash, curl and tar (clang on macOS), and no
Lean, elan, lake,
Node or OCaml on PATH, run the pinned recipe:

```sh
env -i PATH=/usr/bin:/bin bash --noprofile --norc
# then the commands of bootstrap/seed/stage-14274/README.md
```

(The measured spread is 1154.8 s on the recorded perf host to 2043 s
on a 4-vCPU Debian 12 guest — `docs/PERF-RECORD.tsv`.)

The recipe fetches a pinned wasmtime C API and a pinned binaryen
(digests in `bootstrap/seed/stage-14274/{WASMTIME,BINARYEN}-SHA256SUMS`),
recodes the seeds' legacy exception-handling instructions with
`wasm-opt`, compiles the C host `stage-14274/seed-host.c`, and runs
all four compiler calls inside the seed's own Wasm form. It rebuilds
both RSCM files and both Wasm
files byte-identical to the committed seeds and exits 0 — the recipe's
wall and peak are recorded per version in `docs/PERF-RECORD.tsv`.

## What just happened

`bootstrap/seed/stage-14274/rsdc.wasm` (sha256 `1aeacfb6b097…dbc6be75`)
read the whole-module input `sources/rsdc.rsd` and emitted an RSCM file
matching the fixpoint digest; `stage-14274/rsc.wasm` (sha256
`b7db967608fe…0b2e90`) lowered both RSCM files to Wasm matching the
committed seeds (`stage-14274/README.md`, `REBUILT-SHA256SUMS`,
`SHA256SUMS`). The 54 source members the seeds were cut from are pinned
by sha256 in `stage-14274/SOURCE-MEMBERS-SHA256SUMS` — `sha256sum -c`
verifies them against the checkout.

## Compiling a source

The rebuilt runtime host is the compiler's executor:
`$out/run rsdc <entry> <rsdc.wasm> <source.rsd> <out.rscm> 0 cons`
compiles, and
`$out/run rsc <entry> <rsc.wasm> <file.rscm> <out.wasm> 14274 cons`
lowers
(`stage-14274/README.md`, the `rebuild_root` command lines; the
entries are read from `stage-14274/CUT.tsv`). The
inputs the recipe demonstrates are the two whole-module sources
`sources/{rsdc,rsc}.rsd` — "the exact RSD byte streams" of the
seed cut, including generated runtime definitions
(`stage-14274/README.md`); the grammar those sources are written in
is `docs/LANGUAGE.md`, whose probe table refuses `import`,
`theorem`, `axiom`, `class`, `abbrev`, `variable`, `opaque`, `by`
(all err=1). `rsd/examples/answer.rsd` is a small compilable input;
`docs/RSD-COMMAND.md` documents the executor file contract, and
`docs/BUILD.md` documents the `rsd` verbs the tool adds on top.

## Not in 0.3

Modules (`import`), compiled dispatcher binaries, the 9P execution
layer's device servers, theorem checking, the elaborator and the
application suites are named future work (`release/GAPS.tsv`,
`docs/OVERVIEW.md`). The `.rsm`/`.rsj` surfaces and the RSX entry do
ship in 0.3: see `docs/surfaces/` and `examples/surfaces/`.
