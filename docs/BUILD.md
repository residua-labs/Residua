# The rsd build tool

English | [中文](BUILD.zh-CN.md)

`rsd` is the build and run tool of the release. Its sources are `rsd/`
(the dispatcher and compiler worker), `glue/rsd/` (the `rsd run` entry
and build script), `glue/host/` (the C11 WebAssembly and wasm2c `Proc`
execution hosts), and `lib/rsd/` plus `lib/Rsd.rsd` (the content store,
dependency graph and session layer).

Scope: the C11 `Proc` execution host (`glue/host/procwt.c`) compiles
directly from this archive with a C compiler and the pinned Wasmtime C
API, and the `rsd` front-door binary (`glue/rsd/build.rsd`) compiles
when stock Lean `4.14.0` is also installed. Part of `rsd/rsdc.rsd`'s
native compiler-worker closure and the `rsd test` corpus manifest stay
repository-side (`release/GAPS.tsv`); the standalone compiler chain in
this archive is the [seed](GLOSSARY.md) recipe under
`bootstrap/seed/stage-14274/`.

## Building from this archive

With `$capi` pointing to the unpacked Wasmtime `v50.0.1` C API directory
(downloaded and SHA-256-verified in `README.md` or
`bootstrap/seed/stage-14274/README.md`) and `LDL=-ldl` on Linux x86-64
or empty on macOS arm64, compile the standalone `Proc` WebAssembly host
without Lean:

```sh
mkdir -p out/rsd-build
cc -O2 -std=c11 -Wall -Wextra -Werror -I "$capi/include" \
    glue/host/procwt.c "$capi/lib/libwasmtime.a" -lpthread -lm $LDL \
    -o out/rsd-build/procwt
```

`procwt` loads a translated `.wasm` module, reads its exported
`__heap_base` global so linear-memory allocation starts above static
data segments, discovers `driveS` automatically when the step slot is
`auto`, and serves CLI arguments, clocks and host file reads/writes over
an in-process 9P2000 responder (`-` in the server slot).

If stock Lean `4.14.0` (`lean` and `leanc` on `PATH`) is installed as
well, build the `rsd` dispatcher front door alongside `procwt`:

```sh
mkdir -p out/rsd-oleans/rsd out/rsd-build
lean --root=. -o out/rsd-oleans/rsd/BuildAssembly.olean rsd/BuildAssembly.rsd
LEAN_PATH="$PWD/out/rsd-oleans" WASMTIME_INC="$capi/include" WASMTIME_LIB="$capi/lib" \
    RSD_BUILD="$PWD/out/rsd-build" lean --run glue/rsd/build.rsd -- --home .
```

## Verbs

- `rsd build <source.rsd>` compiles a program: it computes the import
  closure of the named file, compiles each declaration once, and writes
  the artifact under the store. Rebuilding after an edit recompiles only
  the declarations whose inputs changed.
- `rsd test` runs the end-to-end suite (`rsd/suite.rsd`): the corpus
  manifest through every stage — source, closure, compile, lower, wasm,
  run — with the outcome, the refusing stage, wall time and peak memory
  recorded per row.
- `rsd run <source.rsd> -- <args>` builds if needed, sets up a library
  view over `lib/`, `glue/` and sibling `.rsd` modules when `import`
  headers are present, translates legacy-exception WebAssembly to
  `exnref` once via `wasm-opt`, and executes `Proc` programs on
  `procwt`.
- `rsd cache` is the content store: `cache key <inputs...>` prints the
  key a recipe is stored under; `cache get <key> <dest>` restores a
  recorded result (`hit`) or exits `1` (`miss`); `cache put <key> <dir>
  --rc 0` publishes a result atomically — a result whose run failed is
  never stored.

## Trust assumptions

Every object in the store is addressed by the sha256 of the bytes that
produced it; a `cache get` refuses a payload whose recorded inputs no
longer match the worktree, and a stored run is served only after
reproducing runs agree. These guarantees were exercised by the
planted-row suite (`release/checks/rsd-tool/`), whose independent audit
is `reports/release-02/evidence/AUDIT-RSD-TOOL.e0c2404440.md`
(repository-side).

## References

- Sources: `rsd/`, `glue/rsd/`, `glue/host/`, `lib/rsd/`, `lib/Rsd.rsd`.
- Release note: `release/notes/rsd-tool.md`.
- Examples: `examples/app04/`, `rsd/examples/`.
