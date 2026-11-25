# Wasm seed bootstrap

Use the [committed seed and wasm-runtime bootstrap](seed/stage-14274/README.md)
to rebuild both current compilers. That recipe is self-contained: it
compiles `seed/stage-14274/seed-host.c` with a C compiler and runs
the shipped seed modules on a pinned wasmtime (v50.0.1) after recoding
legacy exception instructions with a pinned binaryen `wasm-opt`
(`version_133`).

## What is here

- `seed/stage-14274/` — the 0.4 committed seed modules (`rsdc.wasm`
  entry `f896`, `rsc.wasm` entry `f2615` at construction word `14274`),
  their SHA-256 sums, the whole-module sources they were cut from (55
  section references across 54 source members), `seed-host.c`, the
  pinned runtime manifests, and the reproduction recipe (`README.md`).

## What changed in 0.4

- **Static ground objects and `__heap_base`.** Modules lowered with
  closed static objects export an immutable `__heap_base` global above
  the data segment (`765288` in `rsdc.wasm`, `603704` in `rsc.wasm`,
  where `[65536, __heap_base)` holds static ground objects).
  `seed/stage-14274/seed-host.c` (SHA-256
  `ea7a4e2e11727712abd538489e09dcf6f4852e9c0e76250e4742bfce5935fd8e`)
  reads and validates `__heap_base` before writing host input, then uses
  that address for capacity, the initial allocation cursor and live-byte
  counters; modules without `__heap_base` retain base `65536`.
- **Dynamic entry discovery.** `rsdc` supports a `\0RSDC-ENTRIES\n`
  header query that emits `entry\t<ordinal>\t<name>` rows for a module's
  exported definitions.
- **Measured 0.4 timings.** From the packed archive in a clean
  `PATH=/usr/bin:/bin` environment, rebuilding both compilers from the
  0.4 seed took `105 s` on Linux x86-64 (`193 s` end-to-end including
  tool setup, `examples/app04` compilation and 16 verification cases;
  peak RSS `5,978,144 KiB`) and `191 s` on macOS arm64 (`337 s`
  end-to-end; peak RSS `6,058,592 KiB`).

## Repository-side material

The earlier wasm2c route's files — `Wasm2CHost.c`,
`ProcWasm2CHost.c`, `sources.json`, `seed/manifest.json`, the WABT and
executor sum files under `seed/stage-14274/`, and the older pinned seed
pair `seed/{rsdc,rsc}.wasm` — stay in the development repository and do
not ship in the archive.

The bootstrap driver used during development (`bootstrap/Bootstrap.cjs`,
`bootstrap/CollectStaged.cjs`, `bootstrap/CollectSeedLink.cjs`,
`bootstrap/seed/Check.rsd`, `bootstrap/seed/Cut.rsd`) is repository-side
as well.
