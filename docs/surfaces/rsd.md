# The rsd surface

rsd follows the Lean 4.14 family. A file is ordinary Lean text: `def`, `structure`, `inductive`, `namespace`, `import`, and `do`. Stock Lean 4.14 accepts the programs in `examples/surfaces/*.rsd`.

The same program can be printed in the other two surfaces. The spellings differ. The tree the engine builds from each spelling is the same.

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
This section is generated from `rsdc/profiles/rsd.syn`. Regenerate it with `lean --run tools/surface-docs/Gen.rsd`.

### Whitespace, comments, and delimiters

- The profile name line is `rsd`.
- A file has no required header line.
- Whitespace: space, tab, line feed, carriage return.
- A line comment starts with `--` and runs to the end of the line.
- A block comment runs from `/-` to `-/`.
- Grouping openers: `(`, `[`, `{`.
- Grouping closers: `)`, `]`, `}`.

### Keywords

Count: 132, in alphabetical order.

```
Prop
Sort
Type
_
abbrev
all_goals
apply
assert!
assumption
at
attribute
axioms
break
builtin_initialize
by
by_cases
cases
catch
change
class
config
congr
constructor
continue
contradiction
decide
decreasing_by
decreasing_tactic
def
deriving
disch
discharger
do
elab
else
end
exact
example
extends
false
finally
first
for
forall
from
fun
funext
generalize
generalizing
have
hiding
if
import
in
induction
inductive
infix
infixl
infixr
initialize
instance
intro
kind
let
local
m!
macro_rules
match
motive
mut
mutual
name
namespace
next
nomatch
noncomputable
nonrec
obtain
omega
only
opaque
open
panic!
partial
postfix
prefix
prelude
priority
private
protected
rcases
rec
refine
rename_i
repeat
return
rfl
run_cmd
run_elab
runtime
rw
s!
scoped
section
set_option
show
simp
simp_all
simp_arith
simpa
split
structural
structure
subst
syntax
termination_by
then
theorem
throwError
trivial
true
try
unfold
universe
unless
unreachable!
unsafe
using
variable
where
while
with
```

### Operators

One row is one symbol, precedence, and associativity. Count: 51.

| symbol | precedence | associativity | occurrences |
| --- | --- | --- | --- |
| `=>` | 110 | nonassociative | 1 |
| `<$>` | 100 | right | 4 |
| `~~~` | 100 | unary | 6 |
| `∘` | 90 | right | 4 |
| `^` | 80 | right | 4 |
| `-` | 75 | unary | 6 |
| `<<<` | 75 | left | 3 |
| `>>>` | 75 | left | 3 |
| `▸` | 75 | nonassociative | 6 |
| `%` | 70 | left | 3 |
| `*` | 70 | left | 3 |
| `/` | 70 | left | 3 |
| `::` | 67 | right | 4 |
| `+` | 65 | left | 3 |
| `++` | 65 | left | 2 |
| `-` | 65 | left | 3 |
| `&&&` | 60 | left | 3 |
| `*>` | 60 | left | 2 |
| `>>` | 60 | right | 4 |
| `^^^` | 58 | left | 3 |
| `>>=` | 55 | left | 2 |
| `|||` | 55 | left | 3 |
| `!=` | 50 | nonassociative | 6 |
| `<` | 50 | nonassociative | 6 |
| `<=` | 50 | nonassociative | 4 |
| `=` | 50 | nonassociative | 6 |
| `==` | 50 | nonassociative | 6 |
| `>` | 50 | nonassociative | 6 |
| `>=` | 50 | nonassociative | 4 |
| `∈` | 50 | right | 4 |
| `≠` | 50 | nonassociative | 4 |
| `≤` | 50 | nonassociative | 6 |
| `≥` | 50 | nonassociative | 6 |
| `!` | 40 | right | 4 |
| `!` | 40 | unary | 6 |
| `¬` | 40 | right | 4 |
| `¬` | 40 | unary | 4 |
| `&&` | 35 | left | 2 |
| `/\` | 35 | right | 4 |
| `×` | 35 | right | 8 |
| `∧` | 35 | right | 4 |
| `||` | 30 | left | 2 |
| `∨` | 30 | right | 4 |
| `->` | 25 | right | 6 |
| `→` | 25 | right | 6 |
| `<|>` | 22 | right | 4 |
| `<->` | 20 | nonassociative | 4 |
| `↔` | 20 | nonassociative | 4 |
| `|>.` | 10 | left | 4 |
| `|>` | 1 | left | 2 |
| `<|` | 0 | right | 4 |

### Layout

Each entry is one constraint token from the profile, with how many productions carry it.

- `@boundary=0:col-eq,0:linebreak` × 2 — A column or line-break constraint, written `@boundary=0:col-eq,0:linebreak`.
- `@boundary=0:col-ge` × 12 — A column or line-break constraint, written `@boundary=0:col-ge`.
- `@boundary=0:col-ge,1:col-eq,1:linebreak` × 1 — A column or line-break constraint, written `@boundary=0:col-ge,1:col-eq,1:linebreak`.
- `@boundary=0:col-ge,1:linebreak` × 1 — A column or line-break constraint, written `@boundary=0:col-ge,1:linebreak`.
- `@boundary=0:col-ge,3:col-eq,3:linebreak` × 3 — A column or line-break constraint, written `@boundary=0:col-ge,3:col-eq,3:linebreak`.
- `@boundary=0:col-gt` × 16 — A column or line-break constraint, written `@boundary=0:col-gt`.
- `@boundary=0:line-eq` × 1 — A column or line-break constraint, written `@boundary=0:line-eq`.
- `@boundary=0:linebreak,0:col-eq` × 2 — A column or line-break constraint, written `@boundary=0:linebreak,0:col-eq`.
- `@boundary=0:no-ws` × 2 — A column or line-break constraint, written `@boundary=0:no-ws`.
- `@boundary=0:no-ws,1:no-ws,2:no-ws` × 1 — A column or line-break constraint, written `@boundary=0:no-ws,1:no-ws,2:no-ws`.
- `@boundary=0:ws` × 3 — A column or line-break constraint, written `@boundary=0:ws`.
- `@boundary=1:col-gt` × 3 — A column or line-break constraint, written `@boundary=1:col-gt`.
- `@boundary=1:line-eq` × 2 — A column or line-break constraint, written `@boundary=1:line-eq`.
- `@boundary=1:linebreak` × 4 — A column or line-break constraint, written `@boundary=1:linebreak`.
- `@boundary=1:no-ws` × 22 — A column or line-break constraint, written `@boundary=1:no-ws`.
- `@boundary=1:no-ws,2:no-ws` × 18 — A column or line-break constraint, written `@boundary=1:no-ws,2:no-ws`.
- `@boundary=1:no-ws,4:no-ws` × 3 — A column or line-break constraint, written `@boundary=1:no-ws,4:no-ws`.
- `@boundary=1:ws` × 14 — A column or line-break constraint, written `@boundary=1:ws`.
- `@boundary=2:col-gt` × 1 — A column or line-break constraint, written `@boundary=2:col-gt`.
- `@boundary=2:no-ws` × 6 — A column or line-break constraint, written `@boundary=2:no-ws`.
- `@boundary=3:col-ge` × 2 — A column or line-break constraint, written `@boundary=3:col-ge`.
- `@boundary=4:col-gt` × 1 — A column or line-break constraint, written `@boundary=4:col-gt`.
- `@boundary=5:col-gt` × 1 — A column or line-break constraint, written `@boundary=5:col-gt`.
- `@forbid-clear` × 21 — A following token may not be written as if this indentation had already ended.
- `@layout-clear` × 80 — Indentation from outside is cleared. The inside is not held to the outer column.
- `@layout-root` × 33 — This production opens an indented block. Later lines of the block line up under it.
- `@layout=1:adjacent` × 11 — An indentation constraint, written `@layout=1:adjacent`.
- `@layout=1:continuation` × 14 — This piece continues the previous line.
- `@scoped-layout=0:argument` × 3 — A local indentation constraint, written `@scoped-layout=0:argument`.
- `@scoped-layout=0:not-outdented` × 9 — The next line stays at least as indented as this line.
- `@scoped-layout=0:not-outdented,3:not-outdented` × 1 — A local indentation constraint, written `@scoped-layout=0:not-outdented,3:not-outdented`.
- `@scoped-layout=0:not-outdented,5:not-outdented` × 1 — A local indentation constraint, written `@scoped-layout=0:not-outdented,5:not-outdented`.
- `@scoped-layout=1:argument` × 6 — A local indentation constraint, written `@scoped-layout=1:argument`.

<!-- /surface-docs:grammar -->
