# Performance record

English | [中文](README.zh-CN.md)

There is one record per version, measured by one fixed method so that versions can be compared. Every row of every
version is in [HISTORY.tsv](HISTORY.tsv) (machine-readable; a new version appends its rows). The full form and rules of
a record are in `release/docs/PERF-RECORD` of that version's source.

## Method

**Machine.** GCP t2d-standard-4 (AMD EPYC 7B13, 4 vCPUs), Linux x86_64; two fresh virtual machines per version. Each value
is the mean of the two machines' medians of 5 runs on a pinned core. **Reference.** Koka 3.2.9 on the same machine and
the same benchmark suite. **Metric.** A ratio is Residua's wall time divided by Koka's; below 1, Residua is faster.

**Scope and limitations.** The suite is small; its programs are allocation-heavy functional workloads, each run on one
pinned core; and one machine type is measured. The ratios characterise a release on this suite; they are not a general ranking of
the languages compared. Rows that are not like-for-like ports are recorded and excluded from the geometric means, as
marked below.

## Summary

| version | native geomean vs Koka | wasm geomean vs Koka | self-bootstrap | rsdc self-compile | rsc self-compile |
|---|---:|---:|---:|---:|---:|
| 0.1 | 0.973 (6 rows) | 1.047 (4 rows) | 1161.7 s, 3.6 GiB | 119.0 s, 0.67 GiB | 301.2 s, 2.0 GiB |

Geomeans are over the rows marked "in geomean" below: the like-for-like ports of Koka's own programs. Rows marked "no" are
our own variants of a benchmark (different source), recorded but not compared.

## 0.1 (compiler at 4a639b7b0, seed f640f43df; 2026-11-19)

Wall-time ratios, residua / Koka:

| benchmark | route | size | ratio | in geomean |
|---|---|---:|---:|---|
| binarytrees-kk | native | 21 | 0.969 | no |
| binarytrees-kk-qbe | native | 21 | 0.953 | yes |
| binarytrees | native | 21 | 0.573 | no |
| binarytrees-qbe | native | 21 | 1.580 | no |
| cfold | native | 20 | 1.006 | yes |
| cfold | wasm | 20 | 1.121 | yes |
| deriv | native | 10 | 0.990 | yes |
| deriv | wasm | 10 | 0.940 | yes |
| nqueens-kk | native | 13 | 1.031 | yes |
| nqueens-kk | wasm | 13 | 1.114 | yes |
| nqueens | native | 13 | 1.795 | no |
| nqueens | wasm | 13 | 2.707 | no |
| rbtree-ck | native | 4200000 | 0.984 | yes |
| rbtree-kk | native | 4200000 | 0.880 | yes |
| rbtree-kk | wasm | 4200000 | 1.024 | yes |
| rbtree | native | 4200000 | 1.315 | no |
| rbtree | wasm | 4200000 | 1.506 | no |

Compiler's own cost (Linux, CPU executables built from the seed): self-bootstrap from the seed 1161.7 s (peak 3.6 GiB);
rsdc compiling itself 118.96 s (0.67 GiB); rsc compiling itself 301.23 s (2.0 GiB); the largest test source: emit 0.06 s,
lower 2.76 s; deriv: emit 0.15 s, lower 4.69 s.

## Other languages (0.1)

The same six programs, taken unmodified from Koka's `test/bench` (the suite of the Perceus paper, PLDI 2021; tag v3.2.9) and
from Lean 4.14.0's `tests/bench`, measured on the same machine type (three fresh t2d-standard-4 VMs, median of 5, pinned core,
every cited VM pair within 10 percent, every cell's output checked before timing). The residua column is the like-for-like
row of each program. Ratio = residua wall / language wall (below 1 = residua faster).

| ratio | cpp | rust | ocaml | haskell | java | swift | lean |
|---|---|---|---|---|---|---|---|
| rbtree | 0.926 | 0.245 | 0.712 | 0.406 | 0.456 | 0.082 | 0.358 |
| rbtree-ck | - | 0.116 | 0.532 | 0.079 | 0.225 | 0.166 | 0.421 |
| nqueens | 0.790 | 0.320 | 0.601 | 0.087 | 0.572 | 0.189 | - |
| cfold | 0.436 | 0.205 | 0.379 | 0.422 | - | 0.168 | 0.696 |
| deriv | 0.543 | 0.203 | 0.623 | 0.335 | 0.234 | 0.284 | 0.649 |
| binarytrees | 2.168 | 0.408 | 0.751 | 1.240 | 1.362 | 0.161 | 0.881 |

| geomean residua/lang | C++ | OCaml | Haskell | Java | Swift | Lean 4.14 |
|---|---:|---:|---:|---:|---:|---:|
| 0.1 | 0.822 | 0.586 | 0.281 | 0.451 | 0.164 | 0.570 |

The Rust column (geomean 0.232) is residua's own straightforward ports (Box/Rc, not tuned), not from the published suite,
and is not comparable with the suite columns. Empty cells: rbtree-ck/C++ is killed at the 12.5 GiB cap (the upstream
program deep-copies the map per checkpoint); cfold/Java overflows the default thread stack; Lean's suite has no nqueens.
Toolchains: cpp = g++ 13.3.0 -O3 -pthread; rust = rustc 1.100.0 (0ef1bc386) -C opt-level=3 -C codegen-units=1; ocaml = ocamlopt 4.14.2 flambda=true -O3 (vm5+vm6; vm3 ran 4.14.1 flambda=false and its ocaml cells are kept as third-run evidence only); haskell = GHC 9.4.7 -O2; java = OpenJDK 21.0.13.1 default GC; lean = Lean 4.14.0 (commit 410fab728470) lean -c + leanc -O3; swift = swiftc 6.0.3 RELEASE -O. Reference columns depend only on the machine type and these pins; they are measured once per pin and
reused by later versions.
