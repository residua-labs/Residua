# Release note — execution-boundary semantics (E0–E4)

English | [中文](effect-sem.zh-CN.md)

Status: **shipped in release 0.2**; the summary also appears in
`docs/RELEASE-NOTES.md`. `closure_claim = 0`.

## What it provides

`semantics/Effect/` is the Lean 4.14 formal semantics of the execution
layer's boundary — the host contract programs meet when the runtime
serves files and sessions, stated against the `EFFECT-ABI-0` interface:

- **E0** trace semantics: replay of executions, and observations
  determining full traces and frontiers.
- **E1** the wire format and judgments: the full T/R frame inventory,
  send/receive/seal transitions, first-residue ordering, receipt
  replay and checkpoint reconstruction.
- **E2** the conformance classifier: canonical state and event,
  projection through `sigma`, ordered tests with refusal or admitted
  outcome.
- **E3** the seed catalogue: 40 named cases (6 C, 15 T, 10 R, 3 F,
  6 S) each paired with an admitted neighbor, reachability and exact
  state checked, against an independent oracle.
- **E4** recorded transport evidence: the 83-row fixture map joined
  1:1, live socket sessions and their controls, and the repaired
  `lib/exec/Exec9.rsd` corpus.

## Acceptance evidence

- Source revision: `3ed96aec8109cf10f0a2b3433eb5693e7c9ac1ff` (on the
  development `main` branch); statement set revision 3, Lean 4.14.
- Independent audit: verdict **SIGN** at that sha; transcript
  `reports/release-02/evidence/AUDIT-EFFECT-CLOSE.r1.md` (copied into
  the packet from the development contracts repository). All audit
  checks ran on clean worktrees of the subject sha.
- E3 conformance: 40/40 seeds, 258/258 obligations (boundary 103,
  format 7, grammar 27, mutant 6, precedence 17, prewire 33, receipt
  21, transition 44); differential oracle 2/2 session kinds with
  4/4 negative controls refused.
- E4: 83/83 fixture-map rows joined; 29/29 executable witnesses;
  live corpus 9/9 sessions adjudicated with 15/15 controls; Exec9
  corpus 12/12 sessions (48 T, 45 R, 2 sealed) with 13/13 controls.
- Carried invariants: E1 witnesses 7/7 + authorities 6/6, E2 monitor
  rows 14/14, admission 20/20 with the unordered-input refusal armed;
  mutants M6 (transport) and M7 (canonical hash) caught.

## Limits

- The statements specify the host boundary; the language has no effect
  constructs, and no execution-layer binary ships.
- Because the wasm lowering of `Exec9` exhausts its fuel bound, the
  E4 Exec9 corpus closes over the compiled native boundary; the
  shipped wasm executor is unaffected (repository-side note
  `reports/effect-sem/E4-exec9.md`).
