# STDLIB — what a 0.3 source can use, measured

Version 0.3 ships no separate standard-library binary and no
user-facing module library: "basic data" is substrate-level (wired
into the front edge and the lowerer), `import` refuses err=1, and the
shipped `lib/` members are toolchain internals of the `rsdc`/`rsc`
closure, not an importable API. Every claim names its source; this
doc will change in later versions.

## Builtins (no import needed)

The front edge resolves these names against the substrate
(`rsdc/Compile.rsd`, the `dataKnownBytes` table at ~line 5671,
sha256 `cba87a06…` at this head):

- Types: `Int`, `Nat`, `Bool`, `String`, `Char`, `Unit`,
  `UInt8`, `UInt16`, `UInt32`, `UInt64`, `USize`,
  `List`, `Array`, `Option`, `Prod`
- Constructors/values: `true`, `false`, `some`, `none`,
  `List.nil`, `List.cons`, `Nat.zero`, `Nat.succ`

Literals and forms are in `docs/LANGUAGE.md`: numerals,
`"strings"`, `'c'` chars, `[a, b]` lists, `#[...]` arrays,
`⟨...⟩` anonymous constructors, `{ ty with f := v, .. }` instance
literals, the 14 binary operators and `!`/`-` unary.

`Option` constructors are builtin identities (`rsdc/Compile.rsd`
~line 6536): `some`/`none` work without imports.

## No modules in 0.3

`import` is a named refusal of the bootstrap grammar (err=1;
`docs/LANGUAGE.md` probe table). The 54 shipped source members
(`bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS`) are the
compiler's own closure — the `lib/lrc/*` lowering passes, the
`lib/rt/*` and `lib/Runtime*` runtime definitions, `lib/RscBase.rsd`,
`lib/ShortCutFusion.rsd`, `lib/TypeFacts.rsd`, `lib/Tarjan.rsd`,
`lib/ArrayWireNF.rsd`, `lib/AvlMap.rsd`, `lib/Fuel.rsd`,
`lib/Object{Layout,Storage}.rsd`, `lib/StaticGround.rsd`,
`lib/WasmDecode.rsd`, `lib/ownership/Borrow.rsd` — toolchain
internals, not an importable user API (the import machinery is
the modules milestone; `release/GAPS.tsv`). 0.3 adds `lib/rsd/` and
`lib/Rsd.rsd` — the `rsd` build tool's store, graph and session
sources, toolchain internals in the same sense.

## Not in 0.3

The user-facing `lib/` module tree of the earlier plan (the Proc,
Session, Receipt, Gate, Word and Arena modules, and the example
programs), richer data modules (`Num`, `Vec`, `Coll`, `OrderedMap`,
`Sha256`, `Float`, `Word32`, `Word64`, `Proc9`), the 9P device host
tree and any `import` path — repository-only or refused in 0.3
(`release/GAPS.tsv`).

