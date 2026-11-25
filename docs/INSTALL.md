# INSTALL — host requirements and 0.4 minimal bootstrap

This document covers reproducing release 0.4 — rebuilding `rsdc` and
`rsc` byte-for-byte from the committed WebAssembly [seed](GLOSSARY.md)
and compiling and running `Proc` programs through `glue/host/procwt.c`
— with no Lean, elan, Lake, Node, OCaml or Rust on `PATH`.

## What the archive provides

- `bootstrap/seed/stage-14274/` — the 0.4 committed seed pair:
  `rsdc.wasm` (`845b99ef…`, entry `f896`) and `rsc.wasm` (`b52b07d1…`,
  entry `f2615` at construction word `14274`), the whole-module sources
  `sources/{rsdc,rsc}.rsd`, the C11 seed host `seed-host.c`
  (`ea7a4e2e…`), the SHA-256 sum files, and `README.md`.
- The 54 compiler source members pinned in
  `bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS`.
- `glue/host/{procwt.c,proc9core.h,proc9.c}` — the C11 `Proc` execution
  hosts (`procwt.c` links against the same pinned `wasmtime` v50.0.1 C
  API as `seed-host.c` and includes an in-process POSIX responder for
  `env`, `fs` and `clock`).
- `lib/Proc{,Bytes,9}.rsd`, `glue/std/*.rsd`, and
  `examples/app04/{Stats,Table,Main}.rsd` — the `Proc` runtime, standard
  library modules and three-module `Float` + `String` CLI example.

## Host requirements

- **Linux x86-64** with GCC, GNU binutils and coreutils, or **macOS
  arm64** with Apple clang — plus `sh`/`bash`, `curl`, `tar`, `awk`,
  `grep`, `cmp`, and `sha256sum` (`shasum -a 256` on macOS), and about
  8 GiB of available RAM (peak RSS during the 0.4 acceptance rebuild was
  `5.70 GiB` on Linux x86-64 and `5.78 GiB` on macOS arm64).
- Network access (or pre-fetched tarballs verified against the same
  sums) for the two pinned user downloads:
  - **wasmtime v50.0.1 C API** — `wasmtime-v50.0.1-{x86_64-linux,aarch64-macos}-c-api.tar.xz`,
    pinned in `bootstrap/seed/stage-14274/WASMTIME-SHA256SUMS`
    (Apache-2.0 WITH LLVM-exception).
  - **binaryen version_133** — `binaryen-version_133-{x86_64-linux,arm64-macos}.tar.gz`,
    pinned in `bootstrap/seed/stage-14274/BINARYEN-SHA256SUMS`
    (Apache-2.0). `wasm-opt --translate-to-exnref` recodes legacy Wasm
    `try`/`catch` instructions to `exnref`.
- Clean `PATH`: the recipe refuses if `lean`, `elan`, `lake`, `node` or
  `ocaml` resolves on `PATH`.

## Steps

```sh
sha256sum -c rsd-src.tar.sha256    # macOS: shasum -a 256 -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src
env -i PATH=/usr/bin:/bin bash --noprofile --norc
# run the recipe in bootstrap/seed/stage-14274/README.md (seed rebuild only)
# or the Quick start in README.md (seed rebuild + procwt + examples/app04)
```

Measured 0.4 clean-archive timings: compiler rebuild `105 s` (`193 s`
end-to-end with `examples/app04` and 16 test cases) on Linux x86-64;
`191 s` (`337 s` end-to-end) on macOS arm64.

## Open limits in 0.4

See `docs/BUILD.md`, `docs/OVERVIEW.md` and `release/GAPS.tsv` for what
remains repository-side or slated for later releases.
