# QUICKSTART — first run from the 0.4 source archive

Release 0.4 carries the self-bootstrapping compiler closure (`bootstrap/seed/stage-14274/`),
the C11 `wasmtime` execution host (`glue/host/procwt.c`), the `Proc` and
`glue/std/` standard modules, the three-module CLI example
`examples/app04/{Stats,Table,Main}.rsd`, and the `rsd` build tool
sources (`docs/BUILD.md`). Every command below runs on Linux x86-64 or
macOS arm64 in a clean `PATH=/usr/bin:/bin` shell with a C11 compiler,
`curl`, `tar`, `awk` and `grep` — no Lean, Node, OCaml or Rust.

## 1. Verify and extract the archive

```sh
sha256sum -c rsd-src.tar.sha256    # macOS: shasum -a 256 -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src
```

Extract into a directory outside any `.git` working tree so the clean
environment checks evaluate the archive alone.

## 2. Rebuild both compilers from the [seed](GLOSSARY.md) and run `examples/app04`

Run the Quick start script in [`README.md`](../README.md) (or the
standalone bootstrap recipe in `bootstrap/seed/stage-14274/README.md`)
inside `env -i PATH=/usr/bin:/bin /bin/sh -eu`:

1. **Verify seed pins** (`SHA256SUMS`, `SOURCE-MEMBERS-SHA256SUMS`,
   `SEED-HOST-SHA256SUMS`) and download pinned `wasmtime` v50.0.1 C API
   and `binaryen` `version_133` (`wasm-opt`), checking both against
   `WASMTIME-SHA256SUMS` and `BINARYEN-SHA256SUMS`.
2. **Translate and build hosts**: `wasm-opt --all-features --translate-to-exnref`
   recodes the seed modules' legacy `try`/`catch` instructions to
   `exnref`; `cc` compiles `seed-host.c` (`$out/run`) and
   `glue/host/procwt.c` (`$out/procwt`).
3. **Rebuild `rsdc` and `rsc`**: `$out/run` executes `rsdc` (`f896`) and
   `rsc` (`f2615`, word `14274`) on `sources/{rsdc,rsc}.rsd`, checks
   byte-equality with the committed seeds and `REBUILT-SHA256SUMS`
   (`105 s` on Linux x86-64, `191 s` on macOS arm64), and translates the
   rebuilt modules for `wasmtime`.
4. **Compile and run `examples/app04`**: strip `^import ` lines across
   `lib/Proc{Bytes,,9}.rsd`, `glue/std/{Str,Proc,Args,Files}.rsd`, and
   `examples/app04/{Stats,Table,Main}.rsd` in dependency order; query
   `\0RSDC-ENTRIES\n` for `main`'s export ordinal (`f151`); compile to
   `app04.rscm` and `app04.wasm`; and run `$out/procwt` on a file of
   floating-point numbers to write the formatted summary table.

## Open limits in 0.4

Building the standalone native `rsd` compiler worker without
repository-side `.lean` glue, separate `RMOD1` compilation of
cross-module `Proc`/`Float` files without `import` stripping, and proof
checking (`R-CIC`) are recorded in `release/GAPS.tsv` and
`docs/OVERVIEW.md`.
