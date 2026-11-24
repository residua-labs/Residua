# Wasm seed bootstrap

Use the [committed seed and wasm-runtime bootstrap](seed/stage-14274/README.md)
to rebuild both current compilers. That recipe is self-contained: it
compiles `seed/stage-14274/seed-host.c` with a C compiler and runs
the shipped seed modules on a pinned wasmtime.

## What is here

- `seed/stage-14274/` — the committed seed modules, their SHA-256 sums,
  the whole-module sources they were cut from, the pinned host and
  runtime manifests, and the reproduction
  recipe (`README.md`).

## Repository-side material

The earlier wasm2c route's files — `Wasm2CHost.c`,
`ProcWasm2CHost.c`, `sources.json`, `seed/manifest.json` and the older
pinned seed pair `seed/{rsdc,rsc}.wasm` — stay in the development
repository and do not ship in the archive.

The bootstrap driver used during development (`bootstrap/Bootstrap.cjs`,
`bootstrap/CollectStaged.cjs`, `bootstrap/CollectSeedLink.cjs`) is
repository-side as well. It orchestrates the same stage
chain the seed recipe spells out by hand, records receipts for each
stage, and checks the stage-2/stage-3 byte equality the recipe also
checks.
