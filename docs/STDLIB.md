# STDLIB — what a 0.4 source can use, measured

Release 0.4 ships builtin primitive types in the compiler substrate
(`rsdc/Compile.rsd`) together with the user-facing `Proc` and `glue/std/`
source modules used by multi-module CLI programs such as
`examples/app04/`. Every claim names its source path.

## Builtins (no import needed)

The front end resolves these names against the substrate
(`rsdc/Compile.rsd`, the `dataKnownBytes` table at ~line 6303,
sha256 `f9da627e…` at this head):

- Types: `Int`, `Nat`, `Bool`, `Float`, `String`, `Char`, `Unit`,
  `UInt8`, `UInt16`, `UInt32`, `UInt64`, `USize`,
  `List`, `Array`, `Option`, `Prod`
- Constructors and values: `true`, `false`, `some`, `none`,
  `List.nil`, `List.cons`, `Nat.zero`, `Nat.succ`
- `Float` (`binary64`) operations: `+`, `-`, `*`, `/`, comparisons,
  `Float.abs`, `Float.neg`, `Float.sqrt`, `Float.floor`, `Float.ceil`,
  `Float.round`, `Float.isNaN`, `Float.toUInt64`, `Float.ofInt`,
  `Float.ofNat`, and `UInt64.toFloat` (`toString` on `Float` is not yet
  wired; format explicitly as in `examples/app04/Table.rsd`,
  `release/GAPS.tsv`).
- `String` operations: `++`, `String.length`, `String.drop`,
  `String.startsWith`, `String.toList`, `String.mk`,
  `String.singleton`, and `toString` on `Int` and `Nat`.

## Shipped user-program modules (`lib/Proc*` and `glue/std/`)

0.4 ships the `Proc` effect representation and standard library modules
used by programs executed on `glue/host/procwt.c`:

- `lib/Proc.rsd` — the `Proc` state/step datatype, `do`-notation `bind`
  and `pure`, and the resident-memory `driveS` step entry
- `lib/ProcBytes.rsd` — byte-list (`List Int`) equality, length, slice
  and append helpers
- `lib/Proc9.rsd` — 9P2000 message encoders, R-message validators and
  device session helpers
- `glue/std/Str.rsd` — `Bs` (`List Int` UTF-8 bytes) splitting, trimming,
  number parsing and formatting helpers
- `glue/std/Args.rsd` — command-line argument reader (`argvP`) over the
  `env` device
- `glue/std/Files.rsd` — file read/write (`fRead`, `fReadTry`, `fWrite`,
  `fWriteTry`) over the `fs` device, including a packed binary-tree
  reader for multi-chunk files
- `glue/std/Proc.rsd` — command execution (`shP`) when a `cmd` device
  responder is attached
- `glue/std/Map.rsd`, `glue/std/Json.rsd`, `glue/std/Graph.rsd` —
  monomorphic byte-key maps, zero-copy JSON slice readers/writers, and
  directed graph traversals

In a C-only archive environment without Lean, multi-module `Proc`
programs concatenate their module closure in dependency order with
`^import ` lines stripped before calling `rsdc` (`README.md` Quick
start; `release/GAPS.tsv`).

## Toolchain-internal `lib/` members

The 54 source members listed in
`bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS` (`lib/lrc/*`,
`lib/rt/*`, `lib/Runtime*`, `lib/RscBase.rsd`, `lib/AvlMap.rsd`,
`lib/Tarjan.rsd`, …) and the build-tool modules under `lib/rsd/` and
`lib/Rsd.rsd` remain compiler and build-tool internals rather than user
APIs.
