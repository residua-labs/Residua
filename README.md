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

```lean
-- rsd/examples/answer.rsd
def main : Int := 42
```

One program, three surface spellings — the round-trip check in
`docs/surfaces/` parses each to the same tree:

```lean
-- examples/surfaces/do.rsd  (the .rsd surface)
def sumList (xs : List Nat) : Nat := Id.run do
  let mut total := 0
  for x in xs do
    total := total + x
  return total
```

```js
// examples/surfaces/do.rsj  (the .rsj surface)
let sumList = (xs: List(Nat), ): Nat => Id.run(do: {
  syntax_225(syntax_134(tree_name(total), tree_none, tree_num(0)))
  syntax_206(tree_12(syntax_207(tree_none, tree_name(x), tree_name(xs)), tree_none), tree_46_general(syntax_223(tree_name(total), tree_none, binary_1(tree_name(total), tree_name(x))), ))
  return total;
});
```

```racket
;; examples/surfaces/do.rsm  (the .rsm surface)
#lang rsd
(define (sumList [xs : (List Nat)] ) : Nat (Id.run (do:
  (#:syntax225 (#:syntax134 (#:tree-name total) #:none (#:tree-num 0)))
  (#:syntax206 (#:tree12 (#:syntax207 #:none (#:tree-name x) (#:tree-name xs)) #:none) (#:tree46-general (#:syntax223 (#:tree-name total) #:none (#:binary1 (#:tree-name total) (#:tree-name x))) ))
  (return total)
)))
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
| [0.3](https://github.com/residua-labs/Residua/releases/tag/rsd-0.3) | 2026-11-24 | see the release page | rsd build tool, UInt64, recut seed, restored suites, open-source docs |

Full history: [CHANGELOG.md](CHANGELOG.md).

## Security

Report vulnerabilities privately through GitHub; see [SECURITY.md](SECURITY.md).

## License

Apache License 2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
