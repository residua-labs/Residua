# Residua

English | [中文](README.zh-CN.md)

Residua is a compiler whose own build you can check byte for byte: a committed WebAssembly [seed](docs/GLOSSARY.md) rebuilds the toolchain from source with nothing but a C compiler, and every artifact is addressed by the hash of its content rather than by who produced it.

It exists because the expensive part of verified software is not the checking — it is trusting the toolchain. A result that names its producer or its compiler version cannot be compared or reused safely across parties that do not trust each other. Content addressing plus a seed-verified toolchain removes those assumptions.

The longer-term design is a language where a program and a proof are terms of a single dependent type theory; this release ships the compilation and CLI/file execution half of that design.

## What is new in 0.4 compared with 0.3

| Area | 0.3 | 0.4 |
|---|---|---|
| Modules & I/O | single-module only; no `Proc` host | `import` across modules, `Proc` `do`-notation, `glue/std/`, and the C11 + Wasmtime `procwt` host (`glue/host/procwt.c`) |
| Language | `UInt64`, integers, arrays, inductives | + IEEE-754 `Float` (`binary64`) end-to-end (`rsdc`, `.rscm`, `lambda-RC`, WebAssembly) |
| Example | single-line `rsd/examples/answer.rsd` | multi-module `examples/app04/{Stats,Table,Main}.rsd` (`Float` stats + `String` table + file I/O) |
| Seed & compiler | `19.9 MB` / `20.5 MB` wasm; `20–45 min` rebuild | `12.5 MB` / `14.3 MB` wasm (`845b99ef…` / `b52b07d1…`); `__heap_base` in `seed-host.c`; rebuild in `105 s` Linux / `191 s` macOS |
| Map licence | `lib/AvlMap.rsd` ported from OCaml `stdlib/map.ml` (LGPL-2.1) | `lib/AvlMap.rsd` ported from Lean `v4.36.0` `Std.DTreeMap` (Apache-2.0) |
| Specifications | product/sum/seq/dispatch composition | + multi-hop (`HopCompose.lean`) and recursion (`Rec.lean`, `NfRec/CheckedStatus.lean`) composition in `lean/nf-compose/` |

## Status

Research release **0.4**. Working today: rebuilding the compiler byte-for-byte from the committed seed on Linux x86-64 and macOS arm64; compiling multi-module `.rsd` programs with `Float` (`binary64`), `String`, `Proc` `do`-notation and `glue/std/` to WebAssembly and running them on `glue/host/procwt.c`; the `rsd` build tool's verbs (`docs/BUILD.md`); the typed content-address format; the syntax engine; the formal semantics of the execution boundary and MST-NF composition (`lean/nf-compose/`, proved over the pinned model from [residua-labs/MST-NF](https://github.com/residua-labs/MST-NF), commit `4432a34`).

Not yet: proof checking (the R-CIC kernel), separate `.rmod` compilation for `Float` and `Proc` (`release/GAPS.tsv`), networking/subprocess host services, 64-bit WebAssembly addressing, and a publish/query entry for results. See [docs/OVERVIEW.md](docs/OVERVIEW.md) for the full picture and its limits.

## Evaluation

<!-- generated-from-perf -->
**Method.** GCP t2d-standard-4. Koka columns: two fresh virtual machines, each value the mean of the two machines'
medians of 5 runs on a pinned core. Other-language columns: three fresh virtual machines, median of 5 on a
pinned core. A ratio is Residua's wall time divided by the reference's; below 1, Residua is faster. The programs
are taken unmodified from Koka's benchmark suite (the suite of the Perceus paper; see the reference list in `docs/OVERVIEW.md`) and from Lean 4's
benchmarks.

| Geometric mean, Residua 0.1 / … | Koka (native) | Koka (wasm) | C++ | OCaml | Haskell | Java | Swift | Lean 4.14 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| ratio | 0.973 | 1.047 | 0.822 | 0.586 | 0.281 | 0.451 | 0.164 | 0.570 |
<!-- end-generated-from-perf -->

## Quick start

You need a C11 compiler (`cc`), POSIX `sh`, `awk`, `curl`, `tar` (with `xz`), and `sha256sum` (`shasum -a 256` on macOS). No Lean, Node, Python or OCaml. Expect `3–6` minutes (`~193 s` on Linux x86-64, `~337 s` on macOS arm64).

Unpack and verify the source archive (outside any `.git` checkout):

```sh
sha256sum -c rsd-src.tar.sha256       # macOS: shasum -a 256 -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src
```

Then run in a clean environment (`env -i PATH=/usr/bin:/bin /bin/sh -eu`) from the unpacked archive root to rebuild `rsdc` and `rsc` from the seed, verify byte-for-byte seed reproduction, and compile and run `examples/app04`:

```sh
set -eu
export LC_ALL=C
seed=$PWD/bootstrap/seed/stage-14274
out=$PWD/out/app04-run
platform=$(uname -s)-$(uname -m)
case "$platform" in
    Linux-x86_64)
        SHASUM=sha256sum
        binaryen_tar=binaryen-version_133-x86_64-linux.tar.gz
        wasmtime_tar=wasmtime-v50.0.1-x86_64-linux-c-api.tar.xz
        LDL=-ldl ;;
    Darwin-arm64)
        SHASUM="shasum -a 256"
        binaryen_tar=binaryen-version_133-arm64-macos.tar.gz
        wasmtime_tar=wasmtime-v50.0.1-aarch64-macos-c-api.tar.xz
        LDL= ;;
    *) printf 'unsupported host: %s\n' "$platform" >&2; exit 1 ;;
esac

mkdir -p "$out/tools" "$out/translated" "$out/rebuilt" "$out/app"
( cd "$seed" && $SHASUM -c SHA256SUMS )
$SHASUM -c "$seed/SOURCE-MEMBERS-SHA256SUMS"
$SHASUM -c "$seed/SEED-HOST-SHA256SUMS"

[ -f "$out/tools/$binaryen_tar" ] || curl -fsSL --retry 3 -o "$out/tools/$binaryen_tar" \
    "https://github.com/WebAssembly/binaryen/releases/download/version_133/$binaryen_tar"
[ -f "$out/tools/$wasmtime_tar" ] || curl -fsSL --retry 3 -o "$out/tools/$wasmtime_tar" \
    "https://github.com/bytecodealliance/wasmtime/releases/download/v50.0.1/$wasmtime_tar"
grep " $binaryen_tar\$" "$seed/BINARYEN-SHA256SUMS" > "$out/tools/pins"
grep " $wasmtime_tar\$" "$seed/WASMTIME-SHA256SUMS" >> "$out/tools/pins"
( cd "$out/tools" && $SHASUM -c pins && tar -xf "$binaryen_tar" && tar -xf "$wasmtime_tar" )

wasmopt=$out/tools/binaryen-version_133/bin/wasm-opt
capi=""
for d in "$out/tools"/wasmtime-v50.0.1-*-c-api; do
    if [ -d "$d" ]; then capi=$d; fi
done

# 1. Translate seed Wasm modules to exnref and build the C11 seed host + procwt host
"$wasmopt" --all-features "$seed/rsdc.wasm" --translate-to-exnref -o "$out/translated/rsdc.wasm" &
p1=$!
"$wasmopt" --all-features "$seed/rsc.wasm" --translate-to-exnref -o "$out/translated/rsc.wasm" &
p2=$!
wait "$p1" "$p2"

cc -O2 -std=c11 -Wall -Wextra -Werror -I "$capi/include" -c "$seed/seed-host.c" -o "$out/seed-host.o"
cc "$out/seed-host.o" "$capi/lib/libwasmtime.a" -lpthread -lm $LDL -o "$out/run"
cc -O2 -std=c11 -Wall -Wextra -Werror -I "$capi/include" \
    glue/host/procwt.c "$capi/lib/libwasmtime.a" -lpthread -lm $LDL -o "$out/procwt"

rsdc_entry=$(awk -F'\t' '$1=="rsdc_entry"{print $2}' "$seed/CUT.tsv")
rsc_entry=$(awk -F'\t' '$1=="rsc_entry"{print $2}' "$seed/CUT.tsv")

# 2. Rebuild rsdc and rsc from source with the seed and verify the byte-for-byte fixed point
"$out/run" rsdc "$rsdc_entry" "$out/translated/rsdc.wasm" \
    "$seed/sources/rsdc.rsd" "$out/rebuilt/rsdc.rscm" 0 cons
"$out/run" rsc "$rsc_entry" "$out/translated/rsc.wasm" \
    "$out/rebuilt/rsdc.rscm" "$out/rebuilt/rsdc.raw.wasm" 14274 cons
cmp -s "$seed/rsdc.wasm" "$out/rebuilt/rsdc.raw.wasm"
"$wasmopt" --all-features "$out/rebuilt/rsdc.raw.wasm" --translate-to-exnref -o "$out/rebuilt/rsdc.wasm"

"$out/run" rsdc "$rsdc_entry" "$out/translated/rsdc.wasm" \
    "$seed/sources/rsc.rsd" "$out/rebuilt/rsc.rscm" 0 cons
"$out/run" rsc "$rsc_entry" "$out/translated/rsc.wasm" \
    "$out/rebuilt/rsc.rscm" "$out/rebuilt/rsc.raw.wasm" 14274 cons
cmp -s "$seed/rsc.wasm" "$out/rebuilt/rsc.raw.wasm"
( cd "$out/rebuilt" && grep "\.rscm\$" "$seed/REBUILT-SHA256SUMS" | $SHASUM -c - )
"$wasmopt" --all-features "$out/rebuilt/rsc.raw.wasm" --translate-to-exnref -o "$out/rebuilt/rsc.wasm"

# 3. Compile and run the multi-module app04 CLI with the rebuilt compiler and procwt
awk '/^import / {next} {print}' \
    lib/ProcBytes.rsd lib/Proc.rsd lib/Proc9.rsd \
    glue/std/Str.rsd glue/std/Proc.rsd glue/std/Args.rsd glue/std/Files.rsd \
    examples/app04/Stats.rsd examples/app04/Table.rsd examples/app04/Main.rsd \
    > "$out/app/app04.rsd"

printf '\000RSDC-ENTRIES\n' | cat - "$out/app/app04.rsd" > "$out/app/app04.ent.in"
"$out/run" rsdc "$rsdc_entry" "$out/rebuilt/rsdc.wasm" \
    "$out/app/app04.ent.in" "$out/app/app04.entries" 0 cons
app_entry=$(awk -F'\t' '$1=="entry" && $3=="main" {print "f"$2}' "$out/app/app04.entries")

"$out/run" rsdc "$rsdc_entry" "$out/rebuilt/rsdc.wasm" \
    "$out/app/app04.rsd" "$out/app/app04.rscm" 0 cons
"$out/run" rsc "$rsc_entry" "$out/rebuilt/rsc.wasm" \
    "$out/app/app04.rscm" "$out/app/app04.raw.wasm" 14274 cons
"$wasmopt" --all-features "$out/app/app04.raw.wasm" --translate-to-exnref -o "$out/app/app04.wasm"

printf -- '-2.5\n0.0\n1.25\n2.75\n10.25\n' > "$out/app/numbers.txt"
"$out/procwt" "$out/app/app04.wasm" "$app_entry" auto 4000000000000000 "" "" - \
    "$out/app/numbers.txt" "$out/app/summary.txt"
cat "$out/app/summary.txt"
```

See [docs/BUILD.md](docs/BUILD.md) for the higher-level `rsd` build and run verbs.

## Example

```rust
enum Tree<T> { leaf, node(Tree<T>, T, Tree<T>) }

fn sum(t: Tree<Nat>) -> Nat {
  match t {
    Tree::leaf => 0,
    Tree::node(l, x, r) => sum(l) + x + sum(r)
  }
}

fn mirror<T>(t: Tree<T>) -> Tree<T> {
  match t {
    Tree::leaf => Tree::leaf,
    Tree::node(l, x, r) => Tree::node(mirror(r), x, mirror(l))
  }
}

theorem sum_mirror(t: Tree<Nat>): sum(mirror(t)) = sum(t) by {
  induction t with
  | leaf => rfl
  | node l x r hl hr => simp [sum, mirror, hl, hr]; omega
}
```

A program and a theorem about it, in the same language: `sum_mirror` holds for every tree, and its proof is checked by the kernel. The spelling is Rust's; the meaning is the type theory's. Values do not change, every `match` covers all cases, and every function terminates.

A Rust form that would mean something else here is refused by name, with the form to write:

| Written | Refused as | Write instead |
|---|---|---|
| `let mut x = 1;` | `closed_mut` | `let x = 1;` |
| `f(&x)` | `closed_borrow` | `f(x)` |
| `return x` | `closed_return` | `x`, as the last expression of the block |
| `for y in xs { … }` | `closed_loop` | recursion or a fold |
| `if b { 1 }` | `if_without_else` | `if b { 1 } else { 0 }` |
| `a - b` on `Nat` | `nat_subtraction` | `Nat::sub(a, b)`, which stops at 0 |
| `a / b` on `Int` | `int_division` | `Int::tdiv(a, b)` (truncating) or `Int::ediv(a, b)` (Euclidean) |

**Status.** This Rust-spelled proof surface is in development and not in the 0.4 archive. Today it is a syntax extension of Lean 4.14: stock Lean elaborates it, and the example above has the same kernel terms as its Lean spelling. The compiler in 0.4 reads the bootstrap surface, a subset of Lean 4.14 ([docs/LANGUAGE.md](docs/LANGUAGE.md)); its own sources and the multi-module `examples/app04/` CLI of the quick start are written in it:

```lean
-- examples/app04/Main.rsd (entry excerpt)
def main : Proc := do {
  let rawArgs <- argvP 0;
  let out <- appDispatchArgs rawArgs;
  out
}
```

## Documentation

Start at [docs/INDEX.md](docs/INDEX.md): first build, verifying a release, running the test suites, the language subset, the glossary, and the architecture notes — in English, with a Chinese mirror for most documents.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). Development happens in the project's private workspace; the public repository takes issues and proposals through GitHub.

## Releases

| Version | Date | Archive SHA-256 | Notes |
|---|---|---|---|
| [0.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1) | 2026-11-19 | `59d0956e…` | first public release: minimal self-bootstrapping closure |
| [0.1.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.1) | 2026-11-19 | `165690af…` | patch: performance record ships, attribution completed |
| [0.1.2](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2) | 2026-11-19 | `a3185221…` | patch: benchmark and differential test suites shipped |
| [0.2](https://github.com/residua-labs/Residua/releases/tag/rsd-0.2) | 2026-11-20 | `151bfd4f…` | q format v1, syntax engine, effect semantics |
| [0.3](https://github.com/residua-labs/Residua/releases/tag/rsd-0.3) | 2026-11-24 | `b07ae731…` | rsd build tool, UInt64, recut seed, restored suites, open-source docs |
| [0.4](https://github.com/residua-labs/Residua/releases/tag/rsd-0.4) | 2026-11-25 | `d25d1c17…` | modules, Proc file/CLI I/O, Float (binary64), app04 example, smaller/faster seed, Apache-2.0 map |

Full history: [CHANGELOG.md](CHANGELOG.md).

## Security

Report vulnerabilities privately through GitHub; see [SECURITY.md](SECURITY.md).

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
