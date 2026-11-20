# benchmarks/koka — the 2-route Koka table

Produces the measured Koka comparison table: residua vs Koka v3.2.9 on
2 routes — native (residua wasm2c `-O2` C executable vs `koka -O2`
executable) and wasm (both modules under one node engine) — at the fixed
sizes, on 1 GCP t2d-standard-4 VM, with CPU seconds beside wall, peak
RSS, code sizes, and 2 page columns (portable and each side's host
best; the Koka column is read in the host rule). See the driver's header
comment for the full rule list.

## Layout

- `KokaBase.rsd` — the driver; `lean --run` with 3 commands
  (`images`, `table`, `report`).
- `timecell.c` — 1-process measurement cell: fork/exec + wait4,
  CLOCK_MONOTONIC wall, `ru_maxrss` peak RSS, `ru_utime+ru_stime` CPU,
  wall kill. Output: `wall_ns \t maxrss_kb \t cpu_us \t status`.
- `src/test/bench/koka/*.kk` — Koka sources vendored verbatim from release
  `v3.2.9` (binarytrees, cfold, deriv, nqueens, rbtree, rbtree-ck).
- `images/`, `modules/`, `refusals/`, `state/` — generated, untracked:
  RSCM images, compiled modules, front-end refusal texts, per-run cells
  and tables. Never committed.

## Run

```sh
# 1. image+module step (minutes; the only step that builds residua
#    artifacts): today's images by the twin, modules by the compiler
#    built by the import closure under --store
lean --run benchmarks/koka/KokaBase.rsd images [14274] \
  [out/kbstore/build/rsc-native compile]
#    env: KB_VARIANT_cfold / KB_VARIANT_deriv — a second source for a
#    refused program (rows labelled `variant, not the source`)
#         KB_STORE (default out/kbstore), KB_TWIN (default out/lrc/twin),
#         KB_NATIVE_COMPILER (default: a previously built `rsc-native`
#         binary on PATH) — a run on a separate machine points these
#         under a state directory (`$KB_STATE`) so the store and twin
#         ship with the worktree, e.g.:
#    KB_STORE=$KB_STATE/kbstore \
#    KB_TWIN=$KB_STATE/bin/twin \
#    KB_NATIVE_COMPILER=$KB_STATE/bin/rsc-native \
#    lean --run benchmarks/koka/KokaBase.rsd images 14274 \
#      $KB_STATE/kbstore/build/rsc-native compile
#    Whatever MODCMD the images step records in modules.tsv is the exact
#    argv the table command repeats — it is provenance, not executed on
#    the host.

# 2. on `1` GCP t2d-standard-4 VM; run all rows in one job:
lean --run benchmarks/koka/KokaBase.rsd table 14274 <runtag> <the same MODCMD>

# 3. locally, after copying run state back:
lean --run benchmarks/koka/KokaBase.rsd report reports/koka-table
```

The host step resumes: every finished cell and artifact is a file under
`$KB_STATE/<runtag>/`; a re-run continues where it stopped.
`MODCMD` in the table command must equal the module compile command the
images step recorded in `$KB_STATE/modules.tsv` — module provenance
is checked, not rebuilt, on the host.

Table rules: sizes binarytrees 21, nqueens 13, rbtree 4,200,000,
rbtree-ck (5, 4,200,000), cfold 20, deriv 10; 1 pinned core
(`taskset -c`); wall = whole-process timecell median of 5; equality
before timing (printed text, with the declared binarytrees `trees`-line
exception); binarytrees twice — with equal-call sharing (labelled, out of
the geomean) and at the `qbe` layer (in the geomean); refused sources are
named rows per route; a module-swap control row must report not equal.
Limits: wall 600 s, heap cap 4 GiB, fuel 10^12, stacks raised and
recorded. Env overrides: `KB_REPS`, `KB_WALL`, `KB_FUEL`, `KB_CAP`,
`KB_STACK`, `KB_NODE_STACK`, `KB_CORE`, `KB_KOKA_TAG`, `KB_WABT_TAG`,
`KB_EMSDK_TAG`, `KB_BT_WASM_WALL`, `KB_COUNTER_DIR`. Each completed run
appends one counter line under `KB_COUNTER_DIR` (default
`$KB_STATE/counter`, file name `local` unless `KB_COUNTER_NAME` overrides it).

closure_claim = 0.
