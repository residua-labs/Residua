# RSD-COMMAND — the 0.2 executor command surface

0.2 ships no dispatcher binary: the command surface is the two CPU
executors the seed recipe builds (`$out/rsdc/run`, `$out/rsc/run`).
Every claim names its source. This document will change in later
versions (0.2+).

## Invocation (verbatim from `bootstrap/seed/stage-14274/README.md`)

```sh
"$out/rsdc/run" rsdc <input.rsd>  <output.rscm> 0     cons
"$out/rsc/run"  rsc  <input.rscm> <output.wasm> 14274 cons
```

- argv[1] names the compiler role (`rsdc`, `rsc`).
- argv[2]/argv[3] are the input and output paths (`.rsd` -> `.rscm`,
  `.rscm` -> `.wasm`).
- argv[4] is the word: `0` for the rsdc front call (public entry
  `f779`), `14274` for the rsc construction call (entry `f1971`)
  (`stage-14274/README.md` header).
- argv[5] is the heap layout (`cons`).

## Output and verdict

Each call prints a JSON record on stdout; success is
`"tag":"0","status":"0","detail":"0"` — the recipe greps exactly that
string (`stage-14274/README.md`, the `grep -qF` lines). The recipe's
whole run ends `bootstrap complete … seed_roundtrip=2/2 images=2/2`.

## Refusals

A source outside the bootstrap grammar is a named refusal, not a
crash: the grammar's accept/refuse table is `docs/LANGUAGE.md`
(`import`, `theorem`, `axiom`, `class`, `abbrev`, `variable`,
`opaque`, `by` all err=1); the residue names the sources declare are
catalogued repository-side (`docs/RESIDUES.md` is not in the archive).

## Not in 0.2

The internal dispatcher binaries, their `--lib/--store/
--home/--fuel/--print/--watch` flags, the q-keyed
module cache, `Proc`/`topen`/`tread`/`twrite` argv handling and the
`main_args`/`main_arity`/exit-63/64/70 verdicts belong to the
earlier plan's command — none ship in 0.2 (`release/MANIFEST.md`).

closure_claim = 0
