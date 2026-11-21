# INSTALL — the 0.2 minimal bootstrap, from the source archive

This document covers reproducing release 0.2 — the committed wasm seed,
the `rsdc`/`rsc` source closure, the runtime and these documents —
with no Lean, elan, lake, Node or OCaml anywhere on PATH. Every claim
names its source path. The steps will change in later versions (0.2+).

## What the release gives you

- `rsd-src.tar` — the 0.2 source archive: `bootstrap/seed/` (the
  stage-14274 seed pair, its whole-module sources and digest
  manifests, plus the older pinned seed pair and `manifest.json`),
  `bootstrap/sources.json` and `bootstrap/README.md`, the 53 compiler
  source members, the C host bridges and `docs/`, `LICENSE`,
  `NOTICE`, `lean-toolchain`. Its path inventory is
  `release/BUILD-INPUTS.tsv` (shipped); its sha256 is the
  `release-source-archive` pin published with the release.
- `bootstrap/seed/stage-14274/` — the 0.2 committed seed:
  `rsdc.wasm` (sha256 `dcd40993dcda…49a32ec`), `rsc.wasm` (sha256
  `ce2cff5b42fd…e139a2`), the two whole-module `sources/*.rsd`, the
  digest manifests and `README.md` (`stage-14274/SHA256SUMS`).

## Host requirements

- Linux x86-64 or macOS arm64 (the recipe's host table in
  `stage-14274/README.md`).
- On Linux: GCC, GNU binutils and coreutils, Bash, curl and tar.
  On macOS: Apple clang and the base system (shasum, bsdtar), Bash,
  curl and tar. Network access for the pinned WABT fetch unless the
  `WABT-*-SHA256SUMS` payloads are cached.
- Nothing else: the recipe refuses if `lean`, `elan`, `lake`, `node`
  or `ocaml` resolves on PATH (`stage-14274/README.md`, the
  `command -v` guard). That refusal is the point — 0.2 is a seed,
  not a toolchain install.

## Steps

```sh
# verify the released archive against the digest file published beside it
sha256sum -c rsd-src.tar.sha256    # expect: rsd-src.tar: OK

# the archive's members sit at the top level — extract into a fresh
# directory, then work at the extraction root
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src

env -i PATH=/usr/bin:/bin bash --noprofile --norc
# then run the commands of bootstrap/seed/stage-14274/README.md
```

Expected: exit 0, two zero-status emissions, two zero-status
lowerings, four rebuilt hashes matching `REBUILT-SHA256SUMS`, and the
two seed byte comparisons — the altered-Wasm control must compare
exit 1 (`stage-14274/README.md`). The recipe's wall and peak are
recorded per version in `docs/PERF-RECORD.tsv`; first-run wall
is dominated by the `-O0` first split.

## After the rebuild

`$out/rsdc/run` and `$out/rsc/run` are the compiler: `run rsdc
<source.rsd> <out.rscm> 0 cons`, `run rsc <file.rscm> <out.wasm>
14274 cons` (`stage-14274/README.md`, `rebuild_root`). The grammar the
front end accepts is `docs/LANGUAGE.md`.

## Not in 0.2

the internal dispatcher binaries and example programs, modules
(`import` refuses err=1), the 9P device servers, theorem checking and
the application suites — see `docs/OVERVIEW.md` and
`release/MANIFEST.md`.

closure_claim = 0
