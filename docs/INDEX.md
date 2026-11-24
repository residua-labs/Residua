# Documentation index

English | [中文](INDEX.zh-CN.md)

The documents follow the [Diátaxis](https://diataxis.fr) split:
tutorials to learn by, how-to guides for a task, reference for facts,
explanation for understanding. Documents are written in English;
entries linking a `.zh-CN.md` file have a Chinese mirror, the rest are
English only.

## Tutorials — learn by doing

- [QUICKSTART.md](QUICKSTART.md) — rebuild the compilers from the seed
  and run your first compile.
- [BUILD.md](BUILD.md) — the `rsd` build tool: `rsd build`, `rsd test`,
  `rsd run`, `rsd cache`.

## How-to guides — do a task

- [VERIFY-RELEASE.md](VERIFY-RELEASE.md) — check every digest of the
  release archive.
- [TESTING.md](../TESTING.md) — run the benchmark and differential test
  suites (repository root).
- [RSD-COMMAND.md](RSD-COMMAND.md) — invoke the rebuilt compilers
  directly (the executor file contract).
- [INSTALL.md](INSTALL.md) — host requirements for the recipe.

## Reference — facts to look up

- [LANGUAGE.md](LANGUAGE.md) — the `.rsd` surface the front edge
  accepts (the bootstrap subset, with its accept/refuse table).
- [surfaces/](surfaces/README.md) — the `.rsd`/`.rsj`/`.rsm` surface
  spellings and the example programs' round-trip check.
- [STDLIB.md](STDLIB.md) — the library sources that ship.
- [QFORMAT.md](QFORMAT.md) — the typed content-address format `q`.
- [GLOSSARY.md](GLOSSARY.md) — every technical term, defined once.
- [PERF-RECORD.md](PERF-RECORD.md) + `.tsv` — the performance record
  and how to read its rows.
- [SPECS.md](SPECS.md) — which texts are pinned specification.
- [STABILITY.md](STABILITY.md) — what the project promises to keep.
- [FAQ.md](FAQ.md) — frequent questions.
- [EMITTER.md](EMITTER.md) — the `.rscm` file format.
- [TRUST.md](TRUST.md) — what you trust (and do not) when you run the
  recipe.

- [CONTRIBUTING-SECURITY.md](CONTRIBUTING-SECURITY.md) — contributing and security reporting.

## Explanation — understand the design

- [OVERVIEW.md](OVERVIEW.md) — what Residua is, the motivation, the
  evidence, the limits, the references.
- [ARCHITECTURE.md](ARCHITECTURE.md) — the layer-by-layer design of the
  semantic chain.
- [RELATED-WORK.md](RELATED-WORK.md) — how this relates to other work.
- [RELEASE-NOTES.md](RELEASE-NOTES.md) — what each release changed,
  expanded per goal.

Repository layout and release bookkeeping (`release/MANIFEST.md`,
`release/NOTICES.md`, `release/PROVENANCE.tsv`) live under `release/`.
