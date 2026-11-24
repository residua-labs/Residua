# Surfaces

Three spellings, one program. rsd follows Lean 4.14. rsj follows Reason. rsm follows Racket. The syntax engine reads a profile as data and can print a tree in any of the three profiles.

## Read and write

Write rsd the way you write a small Lean 4.14 file. The files in `examples/surfaces/*.rsd` are accepted by stock Lean 4.14. How to read each spelling, and the keywords, operators, comments, and layout, are in [rsd.md](rsd.md), [rsj.md](rsj.md), and [rsm.md](rsm.md). Chinese pages sit beside them.

rsj uses `let`, `type`, and `switch`. Comments are `//` and `/* */`.

rsm uses parenthesized forms. The first line is `#lang rsd`. Comments are `;` and `#| |#`. The profile file is `rsdc/profiles/rsm.syn` and its name line is `rsl`.

The five examples are one construct family each: a function with `match`, a structure, a recursive inductive, a `do` block with a loop, and a module with an import. Each `.rsd` file is the source that was written. Each `.rsj` file and each `.rsm` file is bytes the engine printer emitted from that tree. Do not edit the printed files by hand. The shipped rsj and rsm profiles spell the `for` loop and `let mut` with their `syntax_206` and `syntax_225` forms.

## Add a profile

A new profile is data. Add a text file `rsdc/profiles/<name>.syn`. The engine reads that file. Adding a profile does not require a change to the engine. `rsdc/profiles/rsv.syn` was added that way. The engine's own note is `rsdc/syntax/README.md`: profiles are data.

After a profile changes, regenerate the grammar section of its page with the command below.

## Regenerate and check

Grammar pages, from the profile text:

```
lean --run tools/surface-docs/Gen.rsd
```

The check parses each example with each profile, prints the rsj and rsm bytes, parses those bytes again, and requires the three tree q values to be equal. It also asks stock Lean 4.14 to accept each `.rsd` file. The engine objects have to be built first, by the syntax build (`OracleSource.rsd`, then `oracle` for the modules on the plan, then `BridgeMain.rsd` with `LEAN_PATH=build/syntax/rsd/lib:build/syntax`, `generate`, and `oracle` for `Engine` and `PrattTier`). The do loop is ambiguous on the general reader, so the check installs the fast reader. That is the reader whose tree the printer used.

```
LEAN_PATH=build/syntax/rsd/lib:build/syntax lean --run tools/surface-docs/X3.rsd fast
```

That command writes `examples/surfaces/*.rsj`, `examples/surfaces/*.rsm`, and `docs/surfaces/check.tsv` when those files are absent. A second run has to reproduce the same bytes. `docs/surfaces/check.tsv` records each tree q, the Lean exit code, and the refusal controls. Run `Gen.rsd` again afterwards so the side-by-side section shows the printed spellings.

<!-- surface-docs:profiles -->
| file | name line | header | line comment | block comment |
| --- | --- | --- | --- | --- |
| `rsdc/profiles/rsd.syn` | `rsd` | (none) | `--` | `/-` … `-/` |
| `rsdc/profiles/rsj.syn` | `rsj` | (none) | `//` | `/*` … `*/` |
| `rsdc/profiles/rsm.syn` | `rsl` | `#lang rsd` | `;` | `#|` … `|#` |

<!-- /surface-docs:profiles -->
