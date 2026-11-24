# The rsd build tool

English | [中文](BUILD.zh-CN.md)

`rsd` is the build and run tool of the release. Its sources are `rsd/`
(the dispatcher and the compiler worker) and `lib/rsd/` (the store,
the dependency graph and the session layer).

Scope: the tool's sources ship, but part of its build closure is
repository-side, so `rsd` cannot be compiled from this archive alone —
the runnable compiler here is the [seed](GLOSSARY.md) recipe. `rsd test` also reads
an end-to-end manifest that is repository-side. Both are named in
`release/GAPS.tsv`.

## Verbs

- `rsd build <source.rsd>` compiles a program: it computes the import
  closure of the named file, compiles each declaration once, and
  writes the artifact under the store. Rebuilding after an edit
  recompiles only the declarations whose inputs changed.
- `rsd test` runs the end-to-end suite (`rsd/suite.rsd`): the corpus
  manifest through every stage — source, closure, compile, lower,
  wasm, run — with the outcome, the refusing stage, wall time and peak
  memory recorded per row.
- `rsd run <source.rsd> -- <args>` builds if needed, then executes.
- `rsd cache` is the content store: `cache key <inputs...>` prints the
  key a recipe is stored under; `cache get <key> <dest>` restores a
  recorded result (`hit`) or exits 1 (`miss`); `cache put <key> <dir>
  --rc 0` publishes a result atomically — a result whose run failed is
  never stored.

## Trust assumptions

Every object in the store is addressed by the sha256 of the bytes that
produced it; a `cache get` refuses a payload whose recorded inputs no
longer match the worktree, and a stored run is served only after two
reproducing runs agree. These guarantees were exercised by the
planted-row suite (`release/checks/rsd-tool/`), whose independent
audit is `reports/release-02/evidence/AUDIT-RSD-TOOL.e0c2404440.md`
(repository-side).

## References

- Sources: `rsd/`, `lib/rsd/`, `lib/Rsd.rsd`.
- Release note: `release/notes/rsd-tool.md`.
- Examples: `rsd/examples/`.
