# RELATED WORK — what Residua takes, and how it differs

English | [中文](RELATED-WORK.zh-CN.md)

- **Lean 4** — kernel rules, parser, IR design (lambda-RC) and basic
  data representation are taken from it. Residua differs in identity by
  content across versions and in the self-reproducing seed.
- **CakeML and CompCert** — verified compilation is the model for the
  layer-by-layer hops; Residua does not yet have an end-to-end
  correctness proof.
- **Zig** — the committed wasm seed that rebuilds the compiler is Zig's
  approach.
- **Bootstrappable builds** (stage0, GNU Mes, Guix full-source
  bootstrap) — they reduce the binary seed to a few hundred bytes
  small enough to audit directly; Residua's seed is larger and its
  trust rests on the fixpoint and reproduction instead.
- **Koka and Perceus** — reference counting with reuse; Koka is the
  performance reference in the record (`docs/PERF-RECORD.md`).
- **lean4lean, nanoda** — independent Lean kernels, used as
  cross-checks for R-CIC.
