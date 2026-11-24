# The rsj surface

rsj follows the Reason and OCaml family. Bindings are written with `let`, types with `type`, and matches with `switch`. A line comment starts with `//`. A block comment runs from `/*` to `*/`. A file has no required header line.

It spells the same trees as rsd. The keywords and the layout are Reason's. The program is not a different language underneath.

## One program, three spellings

<!-- surface-docs:example -->
One function, three spellings. The rsj and rsm texts were printed by the engine from the rsd tree.

### rsd

```
def classify (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | _ => 1
```

### rsj

```
let classify = (n: Nat, ): Nat => switch (n) {
  | 0 => 0;
  | _ => 1;
};
```

### rsm

```
#lang rsd
(define (classify [n : Nat] ) : Nat (match n
  [0 0]
  [_ 1]
))
```

<!-- /surface-docs:example -->

## Grammar

<!-- surface-docs:grammar -->
This section is generated from `rsdc/profiles/rsj.syn`. Regenerate it with `lean --run tools/surface-docs/Gen.rsd`.

### Whitespace, comments, and delimiters

- The profile name line is `rsj`.
- A file has no required header line.
- Whitespace: space, tab, line feed, carriage return.
- A line comment starts with `//` and runs to the end of the line.
- A block comment runs from `/*` to `*/`.
- Grouping openers: `(`, `[`, `{`.
- Grouping closers: `)`, `]`, `}`.

### Keywords

Count: 421, in alphabetical order.

```
_
alias
arrow
binary_1
binary_10
binary_11
binary_12
binary_13
binary_14
binary_15
binary_16
binary_17
binary_18
binary_19
binary_2
binary_20
binary_21
binary_22
binary_23
binary_24
binary_25
binary_26
binary_27
binary_28
binary_29
binary_3
binary_30
binary_31
binary_32
binary_33
binary_34
binary_35
binary_36
binary_37
binary_38
binary_4
binary_5
binary_6
binary_7
binary_8
binary_9
char
chunk_closed
chunk_end
chunk_middle
chunk_open
constructor
deriving
do
do:
do_43
do_44
do_45
else
expr_type
fun
function
global
hiding
if
implicit
import
in
let
method
module
name
open
partial
pattern
prelude
product
prop_and
prop_not
prop_or
quoted_name
rec
return
return_44
runtime
scope
structural
switch
syntax_100
syntax_101
syntax_102
syntax_103
syntax_105
syntax_106
syntax_107
syntax_108
syntax_109
syntax_110
syntax_111
syntax_112
syntax_113
syntax_114
syntax_115
syntax_116
syntax_117
syntax_118
syntax_119
syntax_121
syntax_122
syntax_123
syntax_124
syntax_124_imax
syntax_124_max
syntax_125
syntax_126
syntax_127
syntax_128
syntax_129
syntax_134
syntax_135
syntax_136
syntax_137
syntax_138
syntax_139
syntax_140
syntax_141
syntax_142
syntax_143
syntax_144
syntax_145
syntax_146
syntax_147
syntax_154
syntax_155
syntax_156
syntax_157
syntax_158
syntax_159
syntax_160
syntax_161
syntax_162
syntax_162_tactic
syntax_164
syntax_165
syntax_166
syntax_167
syntax_168
syntax_169
syntax_200
syntax_201
syntax_202
syntax_203
syntax_204
syntax_205
syntax_206
syntax_207
syntax_208
syntax_209
syntax_210
syntax_211
syntax_212
syntax_213
syntax_214
syntax_215
syntax_216
syntax_217
syntax_218
syntax_219
syntax_220
syntax_221
syntax_222
syntax_223
syntax_224
syntax_225
syntax_229
syntax_232
syntax_234
syntax_235
syntax_236
syntax_237
syntax_300
syntax_301
syntax_302
syntax_303
syntax_304
syntax_305
syntax_306
syntax_307
syntax_308
syntax_309
syntax_310
syntax_311
syntax_312
syntax_313
syntax_314
syntax_315
syntax_316
syntax_317
syntax_318
syntax_319
syntax_320
syntax_321
syntax_322
syntax_323
syntax_324
syntax_325
syntax_326
syntax_327
syntax_328
syntax_329
syntax_330
syntax_331
syntax_332
syntax_333
syntax_334
syntax_335
syntax_336
syntax_337
syntax_338
syntax_339
syntax_340
syntax_341
syntax_342
syntax_343
syntax_344
syntax_345
syntax_346
syntax_347
syntax_348
syntax_349
syntax_350
syntax_351
syntax_352
syntax_353
syntax_354
syntax_355
syntax_356
syntax_357
syntax_358
syntax_359
syntax_360
syntax_361
syntax_362
syntax_363
syntax_364
syntax_368
syntax_369
syntax_370
syntax_371
syntax_372
syntax_373
syntax_374
syntax_375
syntax_376
syntax_377
syntax_378
syntax_400
syntax_401
syntax_402
syntax_403
syntax_404
syntax_405
syntax_406
syntax_407
syntax_408
syntax_409
syntax_410
syntax_411
syntax_412
syntax_413
syntax_414
syntax_415
syntax_500
syntax_501
syntax_502
syntax_503
syntax_504
syntax_505
syntax_506
syntax_507
syntax_508
syntax_509
syntax_510
syntax_511
syntax_512
syntax_513
syntax_514
syntax_515
syntax_516
syntax_517
syntax_518
syntax_518_match
syntax_519
syntax_520
syntax_521
syntax_522
syntax_523
syntax_524
syntax_525
syntax_526
syntax_527
syntax_528
syntax_529
syntax_530
syntax_531
syntax_532
syntax_533
syntax_534
syntax_535
syntax_536
syntax_537
syntax_538
syntax_539
syntax_540
syntax_541
syntax_542
syntax_543
syntax_544
syntax_545
syntax_546
syntax_547
syntax_548
syntax_549
syntax_550
syntax_551
syntax_552
syntax_553
syntax_554
syntax_555
syntax_556
syntax_557
syntax_558
syntax_559
syntax_560
syntax_561
syntax_562
syntax_563
syntax_564
syntax_565
syntax_565_assumption
syntax_565_conv
syntax_565_funext
syntax_565_intros
syntax_565_let
syntax_565_lhs
syntax_565_match
syntax_565_refine
syntax_565_show
syntax_566
syntax_567
syntax_568
syntax_569
syntax_570
syntax_571
syntax_599
termination_by
theorem
tree_10
tree_11_array
tree_11_list
tree_12
tree_13
tree_14
tree_14_wild
tree_15
tree_16
tree_17
tree_18
tree_19
tree_20
tree_21_def
tree_21_partial
tree_21_theorem
tree_22
tree_23
tree_24
tree_25
tree_26
tree_27
tree_28
tree_29
tree_30
tree_31
tree_32
tree_33
tree_34
tree_35
tree_36
tree_37
tree_38
tree_39
tree_4
tree_40
tree_41
tree_42
tree_43
tree_44
tree_45
tree_45_structural
tree_46_general
tree_46_legacy
tree_47
tree_48
tree_5
tree_55_typed
tree_55_untyped
tree_56
tree_56_runtime
tree_57
tree_58
tree_59
tree_60
tree_8
tree_9
tree_char
tree_derived
tree_global
tree_name
tree_none
tree_num
tree_str
type
unary_1
unary_2
unary_3
unary_4
```

### Operators

One row is one symbol, precedence, and associativity. Count: 27.

| symbol | precedence | associativity | occurrences |
| --- | --- | --- | --- |
| `~~~` | 100 | unary | 1 |
| `-` | 75 | unary | 1 |
| `<<<` | 75 | left | 1 |
| `>>>` | 75 | left | 1 |
| `%` | 70 | left | 1 |
| `*` | 70 | left | 1 |
| `/` | 70 | left | 1 |
| `::` | 67 | right | 1 |
| `+` | 65 | left | 1 |
| `++` | 65 | left | 1 |
| `-` | 65 | left | 1 |
| `&&&` | 60 | left | 1 |
| `^^^` | 58 | left | 1 |
| `|||` | 55 | left | 1 |
| `!=` | 50 | nonassociative | 1 |
| `<=` | 50 | nonassociative | 1 |
| `=` | 50 | nonassociative | 1 |
| `==` | 50 | nonassociative | 1 |
| `>` | 50 | nonassociative | 1 |
| `>=` | 50 | nonassociative | 1 |
| `≠` | 50 | nonassociative | 1 |
| `≤` | 50 | nonassociative | 1 |
| `≥` | 50 | nonassociative | 1 |
| `!` | 40 | unary | 1 |
| `&&` | 35 | left | 1 |
| `||` | 30 | left | 1 |
| `<=>` | 20 | nonassociative | 1 |

### Layout

Each entry is one constraint token from the profile, with how many productions carry it.

- `@forbid-clear` × 15 — A following token may not be written as if this indentation had already ended.
- `@layout=1:adjacent` × 1 — An indentation constraint, written `@layout=1:adjacent`.

<!-- /surface-docs:grammar -->
