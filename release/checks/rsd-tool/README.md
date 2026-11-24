# release/checks/rsd-tool — conformance fixtures for the rsd build tool

What a stranger can check about the `rsd` build tool (`rsd build`,
`rsd test`, `rsd run`, `rsd cache`) using the fixtures in this
directory. The specification is `docs/BUILD.md` (English) /
`docs/BUILD.zh-CN.md` (中文); the tool's sources are `rsd/` and
`lib/rsd/` of the archive.

## Fixtures

- `answer42.rsd` — a planted program whose evaluated result is
  `value:42` (`manifest.tsv`, row `ex-answer`; expected digest of the
  row's input bytes is recorded in the same table).
- `R4Main.rsd`, `R4Dep.rsd`, `R4Indep.rsd` — a planted dependency
  graph: `R4Main` imports `R4Dep`; `R4Indep` shares no declaration.
- `r4-merkle.tsv` — the per-file digest table of that graph.
- `manifest.tsv` — the row manifest: row id, scope, input path, the
  sha256 of the input bytes, the expected exit code and the expected
  output marker.

## What to verify

1. `rsd build answer42.rsd` produces a runnable artifact; running it
   through `rsd run` prints `value:42`.
2. `rsd build` on `R4Main.rsd` compiles only the declarations in its
   import closure: a change to `R4Indep.rsd` does not change the
   build's outputs; a change to `R4Dep.rsd` does (the digests in
   `r4-merkle.tsv` are the identity each row's result is keyed by).
3. `rsd cache key` of a fixed recipe prints the same 32-hex key on
   every call; a `cache put` of a payload stores it under that key and
   a `cache get` reports `hit` and restores the recorded outputs.

Expected exits and markers are the columns of `manifest.tsv`.
