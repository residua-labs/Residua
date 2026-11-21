# Emitter: Lean 4.14 to typed `SCMPrograms` (design, revision 0, section 6 corrected)

Scope: how an ordinary first-order program written in Lean 4.14 (the P1′ source language) becomes a
`Residua.Bootstrap.SCM.SCMPrograms S S` of the chain, and whether the emitted R-CIC certificate checker lies
inside the chain's source domain. Pins: chain `17586d3d4c` (`IR.lean`, `SCM.lean`, `LowerSCM.lean`, wire
`docs/BOOTSTRAP_SCM_SOURCE_WIRE.md`); consumer contract `26147cfc16`; owner's domain review `e74a63bf9b`;
untyped emitter `lean/algorithms/ResiduaRCCLeanToScm.lean` (blob `254bd184`, sha256 `27e19c49…`) at
`8820fe64d8`, not on main. Every number below was measured by the prototype unless marked READ or INFERRED.
The prototype is a 440-line change to that emitter (sha256 `04775a89…`); it is the emitter's new identity and
the old pin stays.

## 1. The emitter and the printer as NF instances (four roles; everything else is transport)

| Role | Emitter | Printer (`SCMPrograms` to `.rsn`) |
|---|---|---|
| q | source module closure content + emitter q + profile q (the BootTy table of §3, the fuel profile of §6) → the output program's identity, which is `SourceTask` (signature table + ordered bodies) | the `SCMPrograms` q |
| a | accept, or a named refusal; the chain's source admission re-judges the output, so the emitter stays untrusted | `parse(print(a)) = a` through the front end |
| σ | the canonical `SCMPrograms` plus its index table (module, table index, Lean declaration) | the one rendering |
| ρ | closed: §8 | closed: the printer's own |

Transport, not roles: file writing, module file names, the order of a hash map's iteration, the driver's `run_cmd`,
progress text. Module names are presentation and live in the manifest; table indices are significant.

## 2. Route: print `BootExpr`, obtain `SCMPrograms` by `lowerToSCM`

`lowerExpr : BootExpr S G t → SCMExpr S G t` is constructor for constructor (`letE`→`let1`, `foldE`→`boundedFold`,
`fixE`→`boundedFix`, every other arm the same name). So printing `SCMExpr` directly and printing `BootExpr` then
lowering give the same `SCMPrograms`; the difference is which theorem the printed program inherits.
* Printing `SCMExpr` leaves, per program, a refinement "Lean definition ↔ `evalSCM`" with no general theorem
  behind it; a run-by-run check is translation validation.
* Printing `BootExpr` inherits `lowerToSCM_correct_evalBoot` (axioms `propext`, `Quot.sound`): the SCM evaluation
  of the lowered program equals the Boot evaluation, erased. What remains per definition is the same statement
  the fusion line already proves for `instantiate`, against `evalBoot`, where values are typed (`ValB`).
* Measured on the sample: the Boot-printed `catalog_canon` program satisfies
  `lowerToSCM bootProg = directlyPrintedSCMProg := rfl`, and the chain theorem instantiates at its first entry.
The print route printed `BootExpr` `Programs`, and the compilation input was `lowerToSCM` of it. Each leg after
that (LOW-2 onward, success-only today) applies to the result like to any `SCMPrograms`. The theorem left per
program on that route: `evalBoot p fuel env body = some (toVal (f x))` for the Lean definition `f`, by kernel
reduction for finite rows and by induction for a general statement; the emitter proved neither.

EMITTER-4 gives the per-program inheritance of `lowerToSCM_correct_evalBoot` up. The emitter encodes the
structured `Sc` term to RSCM bytes; `rscmD` checks those bytes back to a `SCMPrograms`. That theorem applies
to a `BootExpr`, and this route never builds one. A checked `Sc → BootExpr` — the same static types the
encoder already uses, one constructor per `Sc` node, the same refusal names — could recover the inheritance
later, because `lowerToSCM` of that `BootExpr` is the `SCMExpr` `rscmD` already checks. It is not built here.

## 3. Lean type to BootTy

| Lean | BootTy |
|---|---|
| `Nat Int Char UIntN Fin` | `i64` (checked: overflow is `none`, see §5) |
| `Bool` `String` | `bool` `str` |
| `Unit`, an erased family | `record []` |
| `Option α` `List α` `Array α` | `option` `list` (`ByteArray` = `list i64`: the core has no bytes eliminator) |
| structure / one-constructor inductive | `record` of its relevant fields, positional keys `f0 f1 …` (Lean field names are presentation; a rename must not move q) |
| several constructors | `sum` of payloads, summand `k` = constructor `k`; a constructor with exactly one relevant field is unboxed (`Sum Int String` = `sum [i64, str]`, the carrier of the fusion line); no field = `record []` |
| `Prod α β` | `record [f0, f1]` (not `pair`; fields are accessed through the same `field`) |
| recursive, indexed or nested inductive | none: `bad`, a use is `[typed_unrepresentable]` (§6) |
| function types | none; function arguments are removed by specialisation (§4) |

## 4. Lean form to constructor, specialisation, refusals

| Lean form after the kernel unfolding equation | Constructors |
|---|---|
| literals, variables, `let`, `if`/`ite`/`dite`/`cond`/`decide` | `litI litB litS var let1 ifE` |
| `+ - *`, comparisons, `==`/`=`/`≠` | `add sub mul`, `lt gt`, `eqE` (+ `notE`); `<=` as `notE (lt b a)` |
| `&&` `||` (Lean short-circuits) | `ifE` (never `andE`/`orE`, which evaluate both sides) |
| constructor of a sum / `casesOn` | `inj k payload` / `matchE` (branches in constructor order; fields read by `field`); this replaces every `(= (field m tag) k)` chain of today's code |
| structure literal / projection | `recCons … recNil` / `field r i` |
| `List`/`Option` constructors and eliminators | `emptyList listSingleton listAppend listFirst listDrop listLen`, `someE noneE isSomeE unwrapSome` |
| `Nat` truncated `a - b`, `max a b`, `min`, `Int.natAbs` | compositions through `let1`/`ifE`/`lt` (no constructor needed) |
| `Int.fmod a b` | `modE` (floor modulus, agrees with the chain wherever it returns) |
| `/` on `Int`, `Int.ediv` | `divE` (exact division only: differs only where the chain refuses) |
| absurd arm (`False.elim`, `noConfusion`) | `unwrapSome noneE` (stuck, any type) |
| structural recursion, mutual blocks | `call` by table index; fuel is §5 |

Specialisation: Lean is polymorphic and BootTy is monomorphic, so a call with a type argument or a function
argument is compiled to one specialised module per distinct (callee, static arguments) pair. The untyped emitter
already specialised function arguments; the typed emitter adds type arguments, so `List.find?` at two row types
is two modules. A static argument that captures a `let`-bound variable is abstracted as an extra parameter; the
untyped emitter turns the let into a `let` head and refuses (`application of non-constant head letE`); the
prototype binds the variable as a local instead and the refusal disappears (§9).

Not in the 53, named: string concatenation (`String.append`/`++`), number to string, code point at an index
(`str-code-at`), `String.toNat?`: refused as `[typed_gap_<op>]`. The owner confirmed concatenation as a gap
(review R1) and the final position is to exclude it from the core; text building is library code over `list i64`.
Stock `%` on `Int` is refused as `[typed_refused_int_mod]`; write `Int.fmod`.

## 5. Numbers and fuel

* `Nat` and `Int` are `i64`. `add sub mul` are range-checked: where Lean computes a value outside
  `[-2^63, 2^63-1]` the chain returns `none` (row `9223372036854775807 + 1` of the sample). Named residue
  `[typed_i64_overflow]`; a program claims agreement with Lean only inside the range.
* Truncating `Nat` subtraction is not inherited as an operator: Lean's `a - b` is emitted as the composition
  `let d = a - b in if d < 0 then 0 else d` (42 sites in the checker closure).
* Two fuels, never one. (1) Chain fuel: a `Nat` supplied with the entry (`evalSCM`), decremented at `call` only;
  the requirement is the call nesting depth, not the number of calls. Measured: list recursion by `call` needs
  length + 21 (4154 for 4133 rows); tree recursion needs the tree height. It belongs in the manifest. (2) Program
  fuel: a source parameter such as `exprFuel`; type `i64`, range `0 ≤ f ≤ 2^63-1`, decrement only under the guard
  `0 < f`; source `Nat.succ` patterns on it lower to `eqE f 0` and `f - 1` with no truncation case reachable.
* Unreachable arms and fuel exhaustion are both `none` (SEM-1 is the chain's open row); programs that must tell
  them apart return a `residue` value on the reachable paths.

## 6. Recursive data: typed emission joined to the arena (EMITTER-2 r4: plain allocation)

Revision 4 ships the **plain-allocation form**: an arena-allocated constructor
lowers to `alloc` (append without search, same `Node`, same sequential
handles), and `intern` (find-or-add) is the later revision for compared types.
The emitter selects per type by one rule, S0.2 rule 4: `alloc` unless the
program compares the type with `=`/`≠` — comparison needs canonical handles,
so only the intern form can carry it. On an alloc'd type structural `=` is
**refused by name** (`[typed_arena_eq_unsupported]`), never emitted as handle
equality — handle equality is wrong when distinct handles hold equal nodes.

Boundary: the emitter knows `Node`'s fields and the `intern`/`alloc`/`read`
signatures, nothing else — the library's bodies are ordinary modules emitted
like any program's; the switch only chooses between two known names.

Cost note: `intern` is O(|arena|) per construction (the find loop), and
`alloc`'s `ar ++ [n]` is O(|arena|) under the chain's functional lists — the
plain form trades the find for a copy; both are quadratic in total nodes for
a program that materialises every node (binarytrees at depth d does; measured
in the EMITTER-2 report).

The paragraphs below keep the r3 interning design, the later revision; the
threading, representation and closure rules are shared by both forms.

Which type goes to the arena: exactly what `bootTy` used to refuse as
`recursive_or_indexed` — a Lean inductive that is recursive (`isRec`) or
indexed. It lowers to the interned-arena representation this tree already
adopted from the Fu1Bridge line (§ withdrawn paragraph below): an `i64`
handle into `Arena = List Node`, canonical find-or-add interning, sequential
handles, structural `=` collapsed to handle `=`. Indexed inductives ride the
same lowering with flat (i64-class) indices as leading scalar slots; a
non-flat index is the named refusal `[typed_arena_index_nonflat]`. Every
other type is unchanged: first-order programs keep records and sums, and
their RSCM bytes do not move (EMITTER-1 hashes are an acceptance row).

Representation differences from Fu1Bridge, each with its reason (its
choices are otherwise adopted: `{r, a}` record threading, trailing arena
parameter on every signature that mentions a recursive type, alloc'ing
functions return `{r, a}`):

* The universal node is `Node := { tag : Int, kids : List Int, i0..i2 : Int,
  b0 b1 : Bool, t0 : Str }` — an explicit `kids` list of child handles plus
  class slots — instead of Fu1Bridge's dense per-class union schema built by
  fam inference. Reason: the library's walks must address child slots
  uniformly for any type with no inference in the emitter; the type map
  Lean→slot is computed from Lean's own constructor types. Cost: one list
  per node. `tag` is the constructor's index; a field is a kid when its type
  lowers to the arena, else it fills the next slot of its class (i64-class:
  Int/Nat/Char/UIntN/Fin; Bool; Str).
* The library arena is the flat v1 list, not Fu1Bridge's v3 digit trie.
  Semantics are the same (find-or-add, sequential handles); the trie is a
  certified replacement for later (OPT line), measured in the report.

Threading: the arena is an expression, not state — the chain has no state.
Within a body the emitter carries a current arena term (side register in the
emitter state); every allocation binds `let1 ra := intern node ar` and
re-binds value/arena from its fields; every call to an arena-signature
function passes the current arena and, when the callee allocs, rebinds the
same way. The result packet carries the arena only when the source's result
type is arena-typed — neither benchmark does, so packets stay small (the
21.8 MB figure was the untyped arena route returning the whole arena).

Sharing and interning (the intern form, later revision): every construction path
goes through `intern` (find-or-add), so structurally equal nodes share a handle and `=` on
handles is exact structural equality — Fu1Bridge's canonicality invariant,
now by construction (no construction path exists outside the library). For
programs whose source relies on node identity (no sharing), interning is
still observationally equal for check-style folds: the observable counts do
not distinguish identity; where a program does observe sharing, that is a
departure to state per program (binarytrees: documented, output-equal).

Closures: the library's walks take their step as an ordinary function
argument, as Lean writes it; `.rsd` and the library may have closures, the
chain may not. The emitter removes them before SCM by one rule: if the
function is known at the call site, specialize — emit one content-named
instance per (walk, step) pair, shared across programs by content name; if
it is not known, defunctionalize — a closure value is a record `{ctag,
fields}` over the program's closed set of closure tags, apply is a match
over that set, and captured recursive values ride the arena as handles. A
function value that is stored rather than applied, or flows somewhere both
rules miss, is the named refusal `[typed_closure_unresolved]`. The library
definitions themselves (`Node`, `intern`, `read`, tag/slot helpers, the
walks) are singletons pinned as a fixed sig-table prefix, so every program
calls the same q for intern and read.

`decide`-free elaboration at scale: the emitter's recursion stays
fuel-bounded structural walking of Lean terms (`bootTy`, pattern lowering);
no `decide` on runtime types appears, and the arena lowering adds no new
elaboration obligations — slot maps come from constructor telescopes. The
two benchmark programs elaborate in minutes on stock Lean 4.14 (measured in
the report).

History (superseded by this section): an interned arena exists and carries
the checker through the chain's candidate compiler (Fu1Bridge line,
DESIGN.md §"One route"; the withdrawn text below kept for the record).

Lean's own types do not map: of the 211 modules of the typed closure, 200 have a recursive or indexed type in
their signature (first offender: `Expr` 102, `Level` 56, derivations `TyConvT` 18, `HasTyT` 12, `ConvT` 12).
* Tokens (prior art, read first): `Tokens := List (sum [i64, str])`, prefix order, with binder markers where
  needed. At the pin the fusion line's flat codec, dynamic lift and dynamic instantiate elaborate unchanged against
  both its original R-CIC copy and main's, including `dynamic_instantiate_contract`
  (`propext`, `Quot.sound`). Gaps measured: `Expr.lit` is excluded (a `lit` row is refused; the checker uses
  literals), constants carry a `String` where the checker has `Nat` refs (decimal text was used), there is no
  conversion, whnf or memo on it, and its cost on small terms is high (§9).
* Arena: nodes in a list of records indexed by `i64`; hash-consing and memo by index pairs need constant-time
  subterm access, which a flat prefix does not give and which `listDrop`+`listFirst` gives only in O(index). The
  precedent (a radix trie of nested lists of fixed depth `d`) costs O(d·B) per access and needs no new
  constructor; BootTy has no dependent depth, so `d` is fixed per instance.
* Recommendation by provability and fit: tokens as the boundary and for one-shot substitution; an arena as the
  working form for conversion and memo; derivation values (`ConvT`, `HasTyT`, `TyConvT`, built inside and dropped
  from the returned summary) erased, with a refinement showing the summary does not depend on them.
* Flat-to-arena is expressible as a data refinement: encode/decode functions and, per function, a simulation
  lemma `decode (f_arena (encode t)) = f_flat t`; the fusion line's `execInstantiate_refines_instantiate` is the
  same shape for tree against flat. It is not a compiler pass over one program (LOW-1/LOW-2 keep types), so it is
  a certified replacement of one program by another with a different interface, at Boot level, before lowering.
  Sharing must also be unobservable (a second lemma). Not measured.

## 7. Identity and order

Table index and call index are significant for q; module names are not. The untyped emitter names
specialisations `_s<k>` by queue order and sorts by name, so one new specialisation renumbers the others. The
typed emitter must name a specialisation by the content of (callee, static arguments) and order the table
callee-first by Lean name. The driver must fail when the work queue is not empty after the job cap (the untyped
`compileClosure` stops silently at 100000 jobs; none was hit: the queue drains at 210 modules).

## 8. Closed refusal set (emitter)

`[chain_scm_not_emitted]` with a reason (inherited family: no unfolding equation, partial application, a
function-carrying structure in data position, non-definition callee, unsupported expression kind), plus
`[typed_unrepresentable] <type>`, `[typed_gap_<op>]`, `[typed_refused_int_mod]`, `[typed_unbound_variable]`,
`[typed_unknown_callee]`, `[typed_untyped_injection]`, `[typed_no_field]`, `[typed_field_of_non_record]`,
`[typed_match_of_non_sum]`, `[typed_match_arity]`, `[queue_not_drained]`. The terminal case is the first.
A refusal never writes a stand-in.

## 9. What the prototype shows (rows are real; commands in the report)

* `catalog_canon` (7 entries, 11 modules, 0 refusals): the printed file elaborates against the pinned `SCMExpr`
  (2.3 s); two planted type mutants are rejected by Lean; 49/49 request rows give the expected values under the
  value map "drop the constant `tag` field"; node counts against today's code on 36 small rows: 0.5 to 1.04,
  median 0.89.
* Grammar examples P1 and P2 (1 and 8 modules): both elaborate; 6 of 6 and 6 of 6 rows agree with stock Lean, plus
  one P1 row that overflows i64, which the chain refuses (Lean computes a value). Today's emitter emits P1 (same
  values on all 7 rows, the overflow row `null` there) and refuses P2.
* Certificate closure (route A, emitter blob `254bd184`, commit `8820fe64d8`): regenerates to 210 modules,
  byte-identical to the committed tree. At main `b0db4a6344` the same emitter completes 216 modules and refuses
  `Rcic.Declarative.sortPiConv?` (`unknown free variable`), so the checker on main has no complete emission.
* Operators of the 210 modules: 21 heads, all with a form in §4; 995 sum-tag reads become `matchE`, 1164 record
  constructions with a leading tag become `inj`.

## 10. Open, for cc

1. Literal tokens (tag 7) and `Nat` const refs in the flat codec. Correction: conversion on the interned arena runs, and a memo exists; both on a branch.
2. `sortPiConv?` refusal on main: cause not found (the let-capture fix does not remove it).
3. Specialisation naming and ordering (§7) before any q is minted.
4. A `residue` mapping from `R.Residue`-like Lean types to BootTy `residue` (a sum of `ok`/`res` was emitted).
5. Whether `unwrapSome noneE` as the unreachable arm is acceptable to the chain's SEM-1 plan.

## RSCM type table, revision WIRE-SEQ-0: a sequence says what it was written as

Type tags of the image stream (inline `54 leb(k)` references are unchanged): 0 i64, 1 bool, 2 str, 3 bytes,
4 list(T), 5 pair(A,B), 6 sum, 7 record, 8 option(T), 9 residue(T), and, new, **10 seq(kind, width, T)**:
the bytes `10 kind width <T>`. `kind` is the source kind of the sequence, the code of `lib/ArrayWireNF.rsd`
`basicKind`: 2 ByteArray, 4 Array (a List is still written as tag 4, kind 0 by convention). `width` is the
element width in bits: 8, 16 or 32 for UInt8, UInt16 and UInt32 elements (a ByteArray is 8), 0 for every other
element (a full word, a magnitude, an object). `T` is the element type as before.

The meaning is unchanged: scm has one sequence, and `seq(kind, width, T)` means `list(T)` exactly as an Array has
always been the list of its elements; no operator is added and `evalLF` is untouched. Readers read tag 10 as tag 4:
canonical type identity, digests and sizes are those of `list(T)` (lib/RscBase.rsd `readTyIter`, `tyNeedGo`,
`tyNode`, `typeDigest`, `sizeGoWithLayers`, `listTysGo`; rsc/fuse.rsd `readTyGo`; the Lean decoders
`RscmDecode*.bootTyD`), so an old image (no tag 10) reads as before and a new image reads as the old image of
the same program. The stage may later keep the kind and width (Fable's P3); nothing reads them yet.
Written by rsdc/Compile.rsd `tyW` and instruments/rsdc-ml/rsdc.ml `tyW` (Array of a non-Char element, ByteArray).

### WIRE-SEQ-0 revision 2: a fixed-width scalar says its width; who reads what

New, in the same image revision: **tag 11 width**, the bytes `11 w`, a fixed-width scalar of `w` bits (8, 16, 32: the
front end's UInt8, UInt16 and UInt32; UInt64 and USize: width 64, see the row UINT64-0 below). It stands wherever the type of such a
value is written: a parameter, a result, a constructor field, a sequence element. It means exactly the word type
`0` (i64): the readers read `11 w` as `0`, so identity, digests, sizes and `evalLF` are those of the word.
Written by `tyW` of both front ends. The sequence rows above and this row are the whole revision; no operator.

## RSCM revision UINT64-0 (W row): a 64-bit word has its own operators

(sonnet-lrc2 for cc, 2026-11-19; owner "那就做"; the rows of this section are the whole revision. closure_claim = 0.)

Lean's `UInt64` (and `USize`, the same type on the 64-bit targets) is `Fin (2^64)` with primitive operations
(`lean_uint64_*`). A value does not fit the wire's checked i64 (`litI` is 8 bytes of two's complement, `add sub mul`
refuse outside `[-2^63, 2^63-1]`), so the width-64 word gets its own literal and operators, the way `Nat` got a magnitude
and unlike UInt8/16/32, which stay i64 with explicit reductions (rows above).

**Type.** The type table row `11 64` of WIRE-SEQ-0 revision 2 names the type `w64`: a value is a `Val.int n` with
`0 <= n < 2^64`. Readers still read `11 w` as the word type `0` for identity, digests and sizes, so an old reader meets
the new type without trouble and refuses only at the first new operator (below). `USize` is `w64` (one code in both front
ends). The stage keeps a `w64` as one full 64-bit word in both layouts (narrow packs only 8, 16 and 32).

**Literal and operators.** Expression tags below 100 (the stage's own forms start at 100; a stage primitive's code is the
wire constructor's tag). Operand and result type `w64` unless written otherwise; "operand in domain" means `0 <= n < 2^64`,
outside it the value is `none` (the checker of every other operator does the same for an i64 outside its range).

| tag | name | operands | meaning in evalLF (Nat mod 2^64; Lean's `UInt64` function) | Lean |
|---|---|---|---|---|
| 64 | `litW` | 8 bytes, little endian, unsigned | `n` as written, `0 <= n < 2^64` (a leaf, like tag 0 without its sign byte: 9 bytes) | `UInt64.ofNat n`, a literal |
| 65 | `wAdd` | a b | `(a + b) % 2^64` | `a + b` |
| 66 | `wSub` | a b | `(a + 2^64 - b) % 2^64` | `a - b` |
| 67 | `wMul` | a b | `(a * b) % 2^64` | `a * b` |
| 68 | `wDiv` | a b | `if b = 0 then 0 else a / b` | `a / b` (`UInt64.div`) |
| 69 | `wMod` | a b | `if b = 0 then a else a % b` | `a % b` (`UInt64.mod`) |
| 70 | `wLt` | a b | the Bool `a < b` on the unsigned values | `decide (a < b)` |
| 71 | `wLe` | a b | the Bool `a <= b` on the unsigned values | `decide (a <= b)` |
| 72 | `wAnd` | a b | bitwise and of the 64-bit patterns | `a &&& b` |
| 73 | `wOr` | a b | bitwise or | `a ||| b` |
| 74 | `wXor` | a b | bitwise xor | `a ^^^ b` |
| 75 | `wNot` | a | `2^64 - 1 - a` | `~~~a` |
| 76 | `wShl` | a n | `(a * 2^(n % 64)) % 2^64` (`n` is a `w64`) | `a <<< n` |
| 77 | `wShr` | a n | `a / 2^(n % 64)` | `a >>> n` |

Equality of two `w64` values is the existing `eqE` (tag 14, structural on the integers); `>` and `>=` are `wLt` and `wLe`
with the operands swapped. Everything else a front end needs is written with these and the existing operators:
`toNat` of a `w64` is `hi * 2^32 + lo` with `hi = wShr a 32` and `lo = wAnd a 0xFFFFFFFF` read as ordinary words (both
below 2^32, so they are i64 values) in the library's `Nat` arithmetic; `UInt64.ofNat n` is `lo + hi * 2^32` of the low 64
bits of the magnitude (`wAdd (wShl hi 32) lo`); `toUInt8/16/32` is `wAnd` with the mask followed by the width's own word
(i64 below 2^32, so no reduction is lost); `UInt32.toUInt64` and the like are the identity on the integer. No dedicated
conversion operator is added.

**Where Lean and the machine differ (the edge rows test exactly these).**
1. Division and modulus by zero: Lean's `x / 0 = 0` and `x % 0 = x`; wasm's `i64.div_u` and `rem_u` trap. evalLF has
   Lean's value; the stage guards the divisor.
2. The shift count: Lean uses `n % 64`, the same as masking by 63; wasm's shifts mask by 63 for an i64 as well, so the
   stage may use them directly, and a count at or above 64 must still give `a <<< (n % 64)`.
3. Comparisons return the wire's Bool word 0/1 like tags 12 to 14 (not a trap, not a flag).
4. A `w64` at or above 2^63 is a negative i64 in a machine word: compare, divide, modulus and every conversion to a wider
   or Nat value must be unsigned in the stage (`wLt` and `wLe` exist so the wire says so; the generic `lt` and `gt` stay signed).
5. `wAdd`, `wSub` and `wMul` wrap; they never refuse (the i64 operators of the word types 8/16/32 refuse on overflow).

**Readers.** A reader that does not know a tag below refuses by name at it (RscBase `skipEGo`: `rdFail (cUnsup + tag)`, the
tag in the code). An image with neither an expression tag 64 to 77 nor the type `11 64` compiles to the same bytes as before
under each existing layer set. A declared `UInt64` field occupies eight bytes under every layer set, including in images that
have the type `11 64` without a `w64` operator.
The stage (lib/lrc/FromWire, Prim, Emit) refuses an image with a tag 64 to 77 by the named code until it implements the
operators (Fable, item 2 of UINT64-0); it never miscompiles one. The stage's existing words `primAddW/SubW/MulW` (103 to 105),
`primDivU/RemU` and the constant shift cover tags 65 to 69 and 77 with a constant count; it lacks unsigned less-than and
less-or-equal, the variable shifts and `and/or/xor/not`, about six primitives. The scm layer gains the fourteen arms in S4 revision 2 (a sibling, never an edit of the frozen files): lean/rsd-cert/Residua/Bootstrap/R2/{SCM,SCMAuditCached,SCMSourceWire}.lean and Residua/EvalLean/R2/RscmDecode.lean, q's and rows in reports/uint64/S4-R2.md; this
row is its specification. Written by `rsdc/Compile.rsd` and `instruments/rsdc-ml/rsdc.ml` (`tyW` writes `11 64`; the
operator lowering writes the tags above); both hosts byte-equal on every row.

**Evidence the row asks for.** Rows at and around 2^63 and 2^64 (comparison, division, modulus, wraparound add and mul,
shifts by 0, 63 and 64, bitwise operations, conversions), each value equal to stock Lean's; planted rows (a signed compare
on a value at or above 2^63, a missing reduction after `wMul`, a shift count not reduced mod 64, `x / 0` not 0) caught.

Metadata, unchecked: the `kind` byte of tag 10 and the `width` bytes of tags 10 and 11 are advisory. The readers
skip them without validating them (a `10 7 99 T` reads as `list(T)`, an `11 99` as a word); nothing reads them yet
(the stage's use is Fable's P2/P3). A later reader that uses them must validate them first.

Edited bytes: a new image differs from the old one of the same program only at type positions, in the signature
type table and in the inline type payloads of bodies (let, equality, list-length nodes carry their types): each
old `04` (or `00`) becomes `0a kk ww` (or `0b ww`); the size grows by exactly 2 bytes per sequence type and 1 per
fixed-width scalar type.

Who reads which image (seed recipe, bootstrap/seed/stage-14274): the committed seed's `rsdc` writes old-format
images only (it has no tag 10 or 11 writer); the seed's `rsc` reads old-format images only and refuses a tag 10
or 11 by name. In stage 1 the seed's rsdc compiles the head's sources into old-format images and the seed's rsc
lowers them, so the seed never meets a new image. The rsdc built in stage 1 writes the new format and the rsc built
in stage 1 (the head's `RscBase`) reads it. Stage 2 and stage 3 are new-format end to end.

Image readers of the chain that refuse tags 10 and 11 by name, never misreading (frozen or not in the goal): the
IFACE-2 template checker `lean/iface2/BaseWire.lean` (readTyIter, tyNeedGo); the v1 to v2 converter
`emitter/evallean/RscmNF.lean` `encTy` (`[rscm_bad_type]`, used by e2e/PerfCensus and emitter/port/evallean
NFMain); `lib/RscmV2.rsd` `v2Ex` (type-node code 9; no v2 writer emits tags 10 or 11 today); the frozen copies
(`rsdc/laws/defs/FuelReuseBase.rsd`, `rsdc/laws/r3/WholeBoundaryValues.rsd`,
`proofs/rsd-proofs/sources/FuelReuseBase.rsd`, `bootstrap/seed/stage-14274/sources`) read pinned old images only.
The readers that accept them: `lib/RscBase.rsd` (readTyIter, tyNeedGo, tyNode, typeDigest, sizeGoWithLayers,
listTysGo), `rsc/fuse.rsd` (readTyGo), the Lean decoders `lean/rsd-cert/Residua/EvalLean/RscmDecode.lean` and
`RscmDecodeArr.lean` (bootTyD), and through them `lib/lrc/FromWire.rsd` and `rsc/rsc.rsd`.
