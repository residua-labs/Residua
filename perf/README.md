# Performance record

English | [中文](README.zh-CN.md)

One record per version, measured the same way so that versions can be compared. Every row of every version is in
[HISTORY.tsv](HISTORY.tsv) (machine-readable; a new version appends its rows). The full form and rules of a record are in
`release/docs/PERF-RECORD` of that version's source.

**Machine:** GCP t2d-standard-4 (AMD EPYC 7B13, 4 vCPUs), Linux x86_64; two fresh VMs per version; each value is the mean of
the two VMs' medians of 5 runs on a pinned core. **Reference:** Koka 3.2.9 on the same machine and the same benchmark suite.
A ratio is residua wall time / Koka wall time (below 1 = faster than Koka).

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
