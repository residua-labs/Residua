# The rsm surface

rsm follows the Racket family. The profile file is `rsdc/profiles/rsm.syn`. Its name line says `rsl`. These pages and the example files use the name rsm.

A file starts with the line `#lang rsd`. Forms are parenthesized lists. A line comment starts with `;`. A block comment runs from `#|` to `|#`.

It spells the same trees as rsd and rsj.

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
This section is generated from `rsdc/profiles/rsm.syn`. Regenerate it with `lean --run tools/surface-docs/Gen.rsd`.

### Whitespace, comments, and delimiters

- The profile name line is `rsl`.
- A file starts with this header line: `#lang rsd`.
- Whitespace: space, tab, line feed, carriage return.
- A line comment starts with `;` and runs to the end of the line.
- A block comment runs from `#|` to `|#`.
- Grouping openers: `(`, `[`.
- Grouping closers: `)`, `]`.

### Keywords

Count: 40, in alphabetical order.

```
Type
_
abbrev
and-prop
angle
ann
cases
character-code
define
do
do:
field
fun
global
hiding
if
import
in
index?
inductive
inst
let
list
match
method
mutual
name
namespace
not-prop
open
or-prop
paren
prelude
prod
return
section
struct
theorem
tuple
values
```

### Operators

One row is one symbol, precedence, and associativity. Count: 31.

| symbol | precedence | associativity | occurrences |
| --- | --- | --- | --- |
| `!` | — | prefix unary | 2 |
| `!=` | — | prefix | 2 |
| `%` | — | prefix | 2 |
| `&&` | — | prefix | 2 |
| `&&&` | — | prefix | 2 |
| `*` | — | prefix | 2 |
| `+` | — | prefix | 2 |
| `++` | — | prefix | 2 |
| `-` | — | prefix | 2 |
| `-` | — | prefix unary | 2 |
| `/` | — | prefix | 2 |
| `::` | — | prefix | 2 |
| `<` | — | prefix | 2 |
| `<->` | — | prefix | 2 |
| `<<<` | — | prefix | 2 |
| `<=` | — | prefix | 2 |
| `=` | — | prefix | 2 |
| `==` | — | prefix | 2 |
| `>` | — | prefix | 2 |
| `>=` | — | prefix | 2 |
| `>>>` | — | prefix | 2 |
| `^^^` | — | prefix | 2 |
| `and-prop` | — | prefix | 2 |
| `not-prop` | — | prefix unary | 2 |
| `or-prop` | — | prefix | 2 |
| `||` | — | prefix | 2 |
| `|||` | — | prefix | 2 |
| `~~~` | — | prefix unary | 2 |
| `≠` | — | prefix | 2 |
| `≤` | — | prefix | 2 |
| `≥` | — | prefix | 2 |

### Layout

Each entry is one constraint token from the profile, with how many productions carry it.

- `@layout=1:adjacent` × 1 — An indentation constraint, written `@layout=1:adjacent`.

<!-- /surface-docs:grammar -->
