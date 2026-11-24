# Residua

English | [中文](README.zh-CN.md)

Residua is a compiler whose own build you can check byte for byte: a committed WebAssembly [seed](docs/GLOSSARY.md) rebuilds the toolchain from source with nothing but a C compiler, and every artifact is addressed by the hash of its content rather than by who produced it.

It exists because the expensive part of verified software is not the checking — it is trusting the toolchain. A result that names its producer or its compiler version cannot be compared or reused safely across parties that do not trust each other. Content addressing plus a seed-verified toolchain removes both assumptions.

The longer-term design is a language where a program and a proof are terms of one dependent type theory; this release ships the compilation half of that design.

## What is new in 0.3 compared with 0.2

| Area | 0.2 | 0.3 |
|---|---|---|
| Build tool | not shipped | `rsd build` / `rsd test` / `rsd run` / `rsd cache` (`rsd/`, `lib/rsd/`) |
| Language | no `UInt64` | `UInt64` supported |
| Seed | 0.1-era bytes | recut at this release's sources |
| Test suites | benchmarks/, instruments/lrc-host/, perf/ missing | restored (0.2 regression, fixed) |
| Documents | academic register | rewritten for outside readers; glossary, community files |
| Specifications | layered semantic spec only | + MST-NF composition theorems in Lean 4.14 (`lean/nf-compose/`; the theory lives at [github.com/residua-labs/MST-NF](https://github.com/residua-labs/MST-NF), pinned commit `4432a34`, which holds the proofs) |

## Status

Research release **0.3**. Working today: rebuilding the compiler from the committed seed on Linux x86-64 and macOS arm64; compiling single-module `.rsd` sources to WebAssembly; the `rsd` build tool's four verbs; the typed content-address format; the syntax engine; the formal semantics of the execution boundary. The foundational theory behind the execution-boundary work is MST-NF, held with its proofs in its own repository: [residua-labs/MST-NF](https://github.com/residua-labs/MST-NF), commit `4432a34`.

Not yet: modules, proof checking, an I/O execution layer, real application suites. See [docs/OVERVIEW.md](docs/OVERVIEW.md) for the full picture and its limits.

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

You need a C toolchain, Bash, curl, tar, and about 20–45 minutes. No Lean, Node or OCaml.

```sh
# 1. Download and verify the source archive (from the release page)
sha256sum -c rsd-src.tar.sha256       # macOS: shasum -a 256 -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src

# 2. Rebuild both compilers from the seed in a clean environment
env -i PATH=/usr/bin:/bin bash --noprofile --norc
#    then run the commands in the seed recipe README under bootstrap/seed/
```

The recipe fetches a pinned wasmtime and a pinned binaryen, recodes the seeds' legacy exception-handling instructions, compiles one small C host, runs all four compiler calls inside the seed's own Wasm form, and exits only when the rebuilt compilers are byte-identical to the committed seed.

Then compile a program to WebAssembly (paths as the recipe leaves them):

```sh
"$out/run" rsdc f832  "$out/translated/rsdc.wasm" rsd/examples/answer.rsd answer.rscm 0 cons
"$out/run" rsc  f2268 "$out/translated/rsc.wasm"  answer.rscm answer.wasm 14274 cons
```

`answer.wasm` runs on any WebAssembly runtime. `docs/BUILD.md` documents the higher-level `rsd build`/`rsd run` verbs.

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

A program and a theorem about it, in one language: `sum_mirror` holds for every tree, and its proof is checked by the kernel. The spelling is Rust's; the meaning is the type theory's. Values do not change, every `match` covers all cases, and every function terminates.

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

**Status.** This surface is in development and not in the 0.3 archive. Today it is a syntax extension of Lean 4.14: stock Lean elaborates it, and the example above has the same kernel terms as its Lean spelling. The compiler in 0.3 reads the bootstrap surface, a subset of Lean 4.14 ([docs/LANGUAGE.md](docs/LANGUAGE.md)); its own sources are written in it, and so is the program of the quick start:

```lean
-- rsd/examples/answer.rsd
def main : Int := 42
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

Full history: [CHANGELOG.md](CHANGELOG.md).

## Security

Report vulnerabilities privately through GitHub; see [SECURITY.md](SECURITY.md).

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
