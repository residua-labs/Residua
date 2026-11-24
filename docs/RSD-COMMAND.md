# RSD-COMMAND — the 0.3 executor command surface

0.3 ships no compiled dispatcher binary: the direct command surface is
the wasmtime host the [seed](GLOSSARY.md) recipe builds (`$out/run`,
compiled from `bootstrap/seed/stage-14274/seed-host.c`). The `rsd`
tool's verbs sit on top and ship as sources
(`docs/BUILD.md`). Every claim names its source. This document will
change in later versions.

## Invocation (verbatim from `bootstrap/seed/stage-14274/README.md`)

```sh
"$out/run" rsdc <rsdc-entry> <rsdc.wasm> <input.rsd>  <output.rscm> 0     cons
"$out/run" rsc  <rsc-entry>  <rsc.wasm>  <input.rscm> <output.wasm> 14274 cons
```

- argv[1] names the compiler role (`rsdc`, `rsc`).
- argv[2] is the module's public entry export (`f832` for rsdc, `f2268`
  for rsc; the recipe reads both from `stage-14274/CUT.tsv`).
- argv[3] is the seed module — after the recipe's
  `wasm-opt --translate-to-exnref` recoding (`stage-14274/README.md`).
- argv[4]/argv[5] are the input and output paths (`.rsd` -> `.rscm`,
  `.rscm` -> `.wasm`).
- argv[6] is the word: `0` for the rsdc front call, `14274` for the rsc
  construction call.
- argv[7] is the heap layout (`cons`).

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

## Not in 0.3

A compiled dispatcher binary, its `--lib/--store/
--home/--fuel/--print/--watch` flags, the q-keyed
module cache, `Proc`/`topen`/`tread`/`twrite` argv handling and the
`main_args`/`main_arity`/exit-63/64/70 verdicts belong to the
earlier plan's command — none ship in 0.3 (`release/GAPS.tsv`).
