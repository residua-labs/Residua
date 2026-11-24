# Release note — the rsd build tool

English | [中文](rsd-tool.zh-CN.md)

Status: **new in release 0.3**; the summary also appears in
`docs/RELEASE-NOTES.md`.

## What it provides

`rsd` is the build and run tool of the release:

- `rsd build <source.rsd>` computes the import closure of the named
  file, compiles each declaration once, and writes artifacts to the
  content-addressed store; rebuilding after an edit recompiles only the
  declarations whose inputs changed.
- `rsd test` runs the end-to-end suite (`rsd/suite.rsd`) — source,
  closure, compile, lower, wasm, run — recording outcome, refusing
  stage, wall time and peak memory per row.
- `rsd run <source.rsd> -- <args>` builds if needed, then executes.
- `rsd cache` is the content store: `key`, `get`, `put`; a result whose
  run failed is never stored.

Sources: the dispatcher and compiler worker `rsd/`; the store,
dependency graph and session layer `lib/rsd/` plus `lib/Rsd.rsd`.
User document: `docs/BUILD.md`; conformance check:
`release/checks/rsd-tool/` (planted rows).

## Acceptance evidence

- The build tool closed with an independent audit passed on the
  development main line; its evidence transcript is collected
  repository-side.
- The tool's sources ship and are covered by the same archive digest
  as the rest of the tree.

## Limits

- The store's guarantees were exercised by the planted-row suite
  (`release/checks/rsd-tool/`); it is not yet exercised at the scale
  of the compiler's own build in a public recipe.
- `rsd` runs against the committed seed pair; a seed update changes the
  executor action's inputs and re-derives it rather than reusing a
  stale artifact.
- The tool cannot be compiled from this archive alone: part of its
  build closure is repository-side (`release/GAPS.tsv`); the runnable
  compiler here is the seed recipe.
