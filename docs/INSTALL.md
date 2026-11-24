# INSTALL — the 0.3 minimal bootstrap, from the source archive

This document covers reproducing release 0.3 — the committed wasm [seed](GLOSSARY.md),
the `rsdc`/`rsc` source closure, the runtime and these documents —
with no Lean, elan, lake, Node or OCaml anywhere on PATH. Every claim
names its source path. The steps will change in later versions.

## What the release gives you

- `rsd-src.tar` — the 0.3 source archive: `bootstrap/seed/stage-14274/`
  (the committed seed pair, its whole-module sources, the recipe and
  its digest manifests), the 54 compiler
  source members, `bootstrap/seed/stage-14274/seed-host.c` (the C host
  bridge) and `docs/`, `LICENSE`,
  `NOTICE`, `lean-toolchain`. Its path inventory is
  `release/BUILD-INPUTS.tsv` (shipped); its sha256 is the
  `release-source-archive` pin published with the release.
- `bootstrap/seed/stage-14274/` — the 0.3 committed seed:
  `rsdc.wasm` (sha256 `1aeacfb6b097…dbc6be75`), `rsc.wasm` (sha256
  `b7db967608fe…0b2e90`), the two whole-module `sources/*.rsd`, the
  digest manifests and `README.md` (`stage-14274/SHA256SUMS`).

## Host requirements

- Linux x86-64 with GCC, GNU binutils and coreutils, or macOS arm64
  with clang — plus Bash, curl and tar (the recipe's host table in
  `stage-14274/README.md`).
- Network access for the two pinned fetches, unless their payloads
  are cached and checked against the same sums:
  - **wasmtime v50.0.1 C API** — `wasmtime-v50.0.1-{x86_64-linux,
    aarch64-macos}-c-api.tar.xz`, sha256 pinned in
    `stage-14274/WASMTIME-SHA256SUMS`, licence Apache-2.0 WITH
    LLVM-exception (`github.com/bytecodealliance/wasmtime`).
  - **binaryen version_133** — `binaryen-version_133-{x86_64-linux,
    arm64-macos}.tar.gz`, sha256 pinned in
    `stage-14274/BINARYEN-SHA256SUMS`, licence Apache-2.0
    (`github.com/WebAssembly/binaryen`). `wasm-opt` recodes the seed's
    legacy exception-handling instructions to the `exnref` encoding
    wasmtime implements.
  Neither tool is shipped; the recipe downloads and verifies them.
- Nothing else: the recipe refuses if `lean`, `elan`, `lake`, `node`
  or `ocaml` resolves on PATH (`stage-14274/README.md`, the
  `command -v` guard). That refusal is the point — 0.3 is a seed,
  not a toolchain install.

## Steps

```sh
# verify the released archive against the digest file published beside it
sha256sum -c rsd-src.tar.sha256    # expect: rsd-src.tar: OK
# (macOS: shasum -a 256 -c rsd-src.tar.sha256)

# the archive's members sit at the top level — extract into a fresh
# directory, then work at the extraction root
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src

env -i PATH=/usr/bin:/bin bash --noprofile --norc
# then run the commands of bootstrap/seed/stage-14274/README.md
```

Expected: exit 0, two zero-status emissions, two zero-status
lowerings, four rebuilt hashes matching `REBUILT-SHA256SUMS`, and the
two seed byte comparisons — the altered-Wasm control must compare
nonzero (`stage-14274/README.md`). The recipe's wall and peak are
recorded per version in `docs/PERF-RECORD.tsv`.

## After the rebuild

`$out/run` is the runtime host: `run rsdc <entry> <module.wasm>
<source.rsd> <out.rscm> 0 cons` compiles, `run rsc <entry>
<module.wasm> <file.rscm> <out.wasm> 14274 cons` lowers — with the
entries and translated modules of `stage-14274/README.md`
(`rebuild_root`; the wasmtime host is `stage-14274/seed-host.c`). The
grammar the front end accepts is `docs/LANGUAGE.md`.

## Not in 0.3

compiled dispatcher binaries (the `rsd` tool ships as sources — see
`docs/BUILD.md` for its scope), modules (`import` refuses err=1), the
9P device servers, theorem checking and the application suites — see
`docs/OVERVIEW.md` and `release/GAPS.tsv`.
