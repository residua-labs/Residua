# Release note — the three surface spellings

English | [中文](surfaces.zh-CN.md)

Status: **new in release 0.3**; the summary also appears in
`docs/RELEASE-NOTES.md`.

## What it provides

The same program can be written in three surface spellings:

- `.rsd` — the Lean-like spelling the compiler front edge reads.
- `.rsj` — a JavaScript-like spelling of the same tree.
- `.rsm` — a Racket-like spelling (`#lang rsd`).

`examples/surfaces/` ships five programs — `do`, `inductive`, `match`,
`module`, `structure` — each printed in all three spellings.
`docs/surfaces/` documents each spelling's profile (name line, comment
forms) and records the round-trip check in `check.tsv`: every program's
three spellings parse to the same tree q, and the `.rsd` spelling is
accepted by stock Lean 4.14.

## Where it lives

- `examples/surfaces/*.rsd`, `*.rsj`, `*.rsm` — the five programs.
- `docs/surfaces/rsd.md`, `rsj.md`, `rsm.md` — one document per
  spelling, in English and Chinese.
- `docs/surfaces/check.tsv` — the measured round-trip table.
