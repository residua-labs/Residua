# METHOD — sem_aligned gate (GATE-HARNESS-0 r2, item g6)

One page. Mechanical sources only; no semantics is designed or redesigned here.

## The hole (plan/PHASE1-BOUNDARY.md §6)

> IN: as tasks/SEM-ALIGN latest revision states: rscm's meaning is scm's
> (evalLF) with the core ops frozen, checked by differential on the chain's
> corpus.
> COUNTER: corpus programs with equal results out of the corpus.
> GATE: 0 differences.

## The two sides (mechanical sources, all committed)

- **rscm's meaning** = `Residua.Bootstrap.SCM.evalSCM` —
  `lean/rsd-cert/Residua/Bootstrap/SCM.lean` (the chain's own evaluator over
  the decoded wire program; evalLF's arm-for-arm bootstrap copy, per
  interfaces/SEM-ALIGN-0.md).
- **scm's evalLF** = `Residua.Bootstrap.Semantics.eval lawsA`
  (= `evalBoot`) — `lean/rsd-cert/Residua/Bootstrap/Semantics.lean`, the
  evalLF core parameterized by `ArithLaws`, operating on the intrinsically
  typed `BootExpr`/`Programs` of `Residua.Bootstrap.IR`. The identical file
  ships in `oracle/scm/Residua/Bootstrap/Semantics.lean` — `Semantics.lean`
  and `IR.lean` are byte-identical across the two trees (sha256
  `4ffcb7d990e8c77fa5dce42bcb4e1ae798e3cddd04803ac7c1fcbd2cb7fa46d2` and
  `83d89f0c309d45c96f8e1e0472f1c5048995cdb90168f616337b947aa4a8bb8a`).
  There is no `scm/Residua` at the repo root: `test -d scm/Residua` exits 1,
  `git ls-files scm/Residua` is empty, and `diff -rq lean/rsd-cert/Residua
  scm/Residua` exits 2 (`diff: scm/Residua: No such file or directory`);
  the oracle tree is `oracle/scm/Residua`. The trees are not identical end
  to end — `diff -rq lean/rsd-cert/Residua oracle/scm/Residua` exits 1 with
  16 lines: the lean tree alone has `BootTypeWire.lean`, `Bundle.lean`,
  `BundleRed.lean`, `SCM.lean`, `SCMAuditCached.lean`, `SCMSourceWire.lean`,
  `EvalLean`, `Rsdc` and `Runtime`; the oracle tree alone has
  `EncodeWasm0.lean`, `Wasm0`, `Wasm0.lean`, `Wasm0Machine.lean` and
  `SlotSemanticsCore.lean`; `EvalBootSeparators.lean` differs at 12 theorem
  tactics (`decide` on the lean tree, `native_decide` on the oracle tree;
  the theorem equations are the same text) and `SHA256.lean` differs.
  `gates/semalign/TreeId.rsd` reproduces every clause of this paragraph
  (Rerun below).

Both evaluators consume the same decoded corpus program. Wire decode is the
existing typed decoder: `rscmDAny` in `emitter/evallean/RscmAny.lean`
(`SCMSourceWire` tag-first framing, EVAL-LEAN-0). Arguments/results use the
one value text encoding, `emitter/evallean/ValText.lean` (`valParse`,
`valShow`).

## The bridge (codec, not semantics)

`SCMExpr`/`SCMPrograms` (SCM.lean) and `BootExpr`/`Programs` (IR.lean) are
ctor-for-ctor isomorphic; only three constructor names differ
(`let1→letE`, `boundedFold→foldE`, `boundedFix→fixE`). The driver maps them
mechanically (`bridgeExpr`/`bridgeArgs`/`bridgeBranches`/`bridgePrograms` in
`SemAlign.rsd`).

Result correspondence (`valToSCM` in `SemAlign.rsd`): scm-side `Val` is
normalized into the chain's `SCMVal` encoding before comparison —
`.pair a b → .list [a,b]`, `.inj i v → .record [("tag",.int i),("val",v)]`,
`.bytes bs → .list` of byte ints — exactly `evalSCM`'s own encodings
(SCM.lean `pairE`/`inj`/`packBytes` arms, `bytesToSCM`). Equality is the
chain's own `scmValEq`; `none = none` counts equal (shared fuel rule:
nonzero checked at every node, decremented only at `call`, N6c).

## Corpus

`rsc/rows/manifest.txt` — the chain's rows corpus, cross-pinned by q in
`e2e/manifest.tsv` (`eval=self` section). `CORPUS.tsv` normalizes its two
accepted field orders (`class arg...` and `arg class`) into fixed columns:
`name, rscm, program_q(e2e), entry-index, fuel, class, args`.

Classes decidable by source semantics alone: `value`, `value:<v>`,
`residue:<d>`, `sourceFuelExhausted`, `sourceStuck:<r>`. Host-layer classes
(`capacity:*`, `machineClock`, `pin`, `v1:*`) cannot be decided by evalSCM /
evalLF — they are emitted as named gap rows (`gap=host_class`) and excluded
from the counter denominator, as task refusals require.

## Planted wrong core op

`Residua.Bootstrap.Semantics.lawsMutant` — the committed mutant bundle
(`mutantAdd`/`mutantMod`/`mutantDiv` wrapping/truncating, plus int-valued
comparisons) — driven through `eval` as a third side (`eval lawsMutant`).
Additionally `SemAlign.rsd` defines `lawsPlanted` (law A with `addF`
replaced by truncating wrap) as a gate-local injection. The gate requires
the differential to catch ≥1 divergence on the corpus for each.

## The counter

For every decidable corpus row: `semalign run` prints `A=<valShow|none>
B=<valShow|none> equal=0|1`. `equal=1` iff `scmValEq` holds on normalized
values (or both `none`). COUNTER = `equal`-rows out of decidable rows.
Gate = `0 differences`, plus mutant caught. Decode/entry/arg failures are
named gap rows, never silent passes.

## Row notes

- `tally-deep` (fuel 200000, arg 2000) recurses deeper than an 8 MiB
  main-thread rlimit allows. On Linux the runtime's stack guard aborted
  it (`gap=run_rc134`); Check.rsd now execs every row under
  `sh -c 'ulimit -s unlimited || ulimit -s 524288'` so the row is
  measured on any host. Darwin already raises the exe's stack at link
  time (`-stack_size 0x20000000`), and the same shell line runs there
  as a no-op fallback.
- `rbtree-100` records `oracle_bad=1` (COMPARE `oracle=0`). Its class
  `value:10` is the e2e expectation, where `hostSourceArgs`
  (`rsc/rows-rsd/RscHost.rsd`) rewrites arg `16` to `[]` for the
  `(list (record 8))` second parameter of entry 14. This gate passes the
  argument text literally (`16`), so both sides return `none`
  (`A=none B=none equal=1`) and the `value:10` class cannot be
  discharged. Probes at fuel 100, 100000 and 4e15 all print the same
  `none`/`none`/`equal=1`; the divergence is the host arg rewrite, not
  the fuel model — the earlier fuel sentence was wrong.

## Rerun

    <lean> gates/semalign/Check.rsd          # builds, runs, writes compare table
    # artifacts: gates/semalign/out/         # oleans, exes, per-row observations, COMPARE.tsv

    lean --run gates/semalign/TreeId.rsd     # reproduces the tree paragraph above:
    # scm/Residua absent (test -d, git ls-files, diff rc 2), the real
    # lean/rsd-cert/Residua vs oracle/scm/Residua diff -rq (rc 1, 16 lines,
    # 9/5/2), and the byte-identical Semantics.lean/IR.lean pair.

    lean -o gates/semalign/out/NF.olean lib/NF.rsd
    LEAN_PATH=gates/semalign/out lean --run gates/semalign/StepScope.rsd
    # step-scope probes for lib/NF.rsd's def step rule: column-0, indented,
    # namespace- and section-nested placements refuse nf_step_role; non-step
    # controls admit; stock-lean subprocesses pin the scoped names.
