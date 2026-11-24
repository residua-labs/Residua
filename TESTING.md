# TESTING — the shipped test and benchmark suites

English | [中文](TESTING.zh-CN.md)

3 suites ship in this archive: `benchmarks/` (the programs behind the
performance record of the release and the correctness corpus),
`instruments/lrc-host/` (the differential test suite the ported compiler
passes are checked with), and `examples/surfaces/` (the three-surface
round-trip check). None is part of the bootstrap recipe: the
recipe is the [seed](docs/GLOSSARY.md) directory and its C bridges only (`docs/INSTALL.md`,
`docs/VERIFY-RELEASE.md`).

## benchmarks/ — performance and correctness corpus

Contents: the `.rsd` benchmark programs (their emitted `.rscm`
modules are repository-side — re-emit one with `rsdc
<program>.rsd` under the chain below), `benchmarks/MANIFEST.tsv`
(per-program provenance and recheck
statement), `benchmarks/expected/` (byte-exact expected outputs),
`benchmarks/rust/` (the Rust reference ports the comparisons cite),
`benchmarks/koka/` (the Koka comparison harness, including `timecell.c`),
and `benchmarks/langs/` (vendored upstream suites the ports derive from:
Koka `test/bench` and the Lean 4.14 test/bench programs).

To run one program through the shipped chain: compile its `.rsd` with
`rsdc`, lower the `.rscm` with `rsc`, and run the result on a wasm
runtime — the same surface
`docs/RSD-COMMAND.md` documents for the seed's own programs. Compare
the output byte for byte against `benchmarks/expected/<name>.txt`; the
MANIFEST row gives the input each program was checked at and the status
vocabulary (`rsd:equal`, `rscm:compiled_equal`, named refusals).

Toolchain: the rsd chain needs only a C compiler and the committed seed
(as in QUICKSTART). The comparison columns are optional and external:
Rust references need `rustc` (1.99.1 was used), the Koka harness needs a
C compiler for `timecell.c` and a Koka toolchain to rebuild the `.kk`
side. The vendored files under `benchmarks/langs/` are source snapshots
kept for provenance; rebuilding them needs their own toolchains and is
not part of any check here.

## instruments/lrc-host/ — differential test suite

Contents: `Diff.rsd` (the check driver), `Images.tsv` (pinned front-end
images and their values), `Sides.rsd`/`SidesMutants.tsv` and the
`Mutants*.tsv` tables (mutation rows), `Peaks.tsv`, `img/` (pinned image
files), and the `Prog*`/support `.rsd` programs the images come from.

Run it with `lean --run` — the Lean 4.14.0 toolchain pinned by
`lean-toolchain`. `lean --run` is a test tool here: nothing in the
release recipe needs Lean.

- `lean --run instruments/lrc-host/Diff.rsd` — every check: each ported
  pass in `lib/lrc/` is diffed against the pinned Lean 4.14.0 pass it
  cites (the oracle); exit 0 means no mismatch.
- `lean --run instruments/lrc-host/Diff.rsd quick` — the same with the
  image check in short form.
- `lean --run instruments/lrc-host/Diff.rsd mutants [TAG]` — every row
  of the `Mutants*.tsv` tables (or one table): each mutation must change
  the pass's output or be refused.
- `lean --run instruments/lrc-host/Diff.rsd plants` — every mutation row
  plants: its FROM text occurs exactly once in its FILE.
- `lean --run instruments/lrc-host/Diff.rsd ir` / `cite` / `mag` —
  write image IR dumps, check the Lean line citations of the ported
  modules, or the front-end integer-operation table.

Two subcommands need repository-side inputs: `rsdc` runs the OCaml
reference front end `instruments/rsdc-ml/rsdc.ml` (an OCaml instrument,
not shipped), and the image check reads ten `img/*.rscm` images named in
`Images.tsv` that are repository-side (generated artifacts, not shipped).
Every other subcommand works on shipped files plus the Lean toolchain.

## examples/surfaces/ — three-surface round-trip check

Contents: five small programs written three times — once each in the
`.rsd`, `.rsj` and `.rsm` surfaces — plus `docs/surfaces/` (the surface
documentation and `check.tsv`, the table behind this section).

The check reparses each surface text and compares the resulting tree
against the other surfaces' trees for the same program; every row must
reprint to itself. Its driver (`tools/surface-docs/X3.rsd`, run under the
same Lean 4.14.0 toolchain with `LEAN_PATH=build/syntax/rsd/lib:build/syntax`)
is repository-side — it imports compiled syntax libraries, not shipped
sources; the shipped `docs/surfaces/check.tsv` records each row's result
of the `fast` tier.

## How the performance record was produced

`docs/PERF-RECORD.tsv` is the measured record (its form and
vocabulary are in `docs/PERF-RECORD.md`). The procedure — the
record's run commands — is kept repository-side at
`reports/perf-record/` under the version `0.1/README.md`: a fresh GCP t2d-standard-4 job per
VM, a `git archive` of the seed commit committed into a fresh
repository, the `bootstrap/seed/stage-14274/README.md` bash block run
under `env -i PATH=/usr/bin:/bin`, then 3 serial runs of each
self-compile and compile-speed step on 2 VMs; the `wall_s` column is
the two-VM mean and `vm_spread_pct` the per-row spread. The benchmark
images came from the shipped `benchmarks/` programs; the Koka column was
measured with `benchmarks/koka/` on the same VMs.
