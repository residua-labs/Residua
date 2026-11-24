# rsd 表面

rsd 遵循 Lean 4.14 这一族。文件就是普通的 Lean 文本：`def`、`structure`、`inductive`、`namespace`、`import` 和 `do`。Lean 4.14 接受 `examples/surfaces/*.rsd` 里的程序。

同一个程序可以印成另外两种表面。拼写不同。引擎从每种拼写建出的树相同。

## 一个程序，三种拼写

<!-- surface-docs:example -->
同一个函数，三种拼写。rsj 与 rsm 由引擎的打印机从 rsd 的树写出。

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

## 文法

<!-- surface-docs:grammar -->
这一节由 `rsdc/profiles/rsd.syn` 生成。重新生成的命令是 `lean --run tools/surface-docs/Gen.rsd`。

### 空白、注释与分隔

- profile 的名字行是 `rsd`.
- 文件没有必须放在开头的 header 行。
- 空白：空格, 制表符, 换行, 回车.
- 行注释以 `--` 开头，直到行尾。
- 块注释由 `/-` 到 `-/`.
- 分组开括号：`(`, `[`, `{`.
- 分组闭括号：`)`, `]`, `}`.

### 关键字

共 132 个，按字母序。

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

### 运算符

同一个符号、优先级和结合性算一行。共 51 行。

| 符号 | 优先级 | 结合性 | 出现次数 |
| --- | --- | --- | --- |
| `=>` | 110 | 无结合 | 1 |
| `<$>` | 100 | 右结合 | 4 |
| `~~~` | 100 | 一元 | 6 |
| `∘` | 90 | 右结合 | 4 |
| `^` | 80 | 右结合 | 4 |
| `-` | 75 | 一元 | 6 |
| `<<<` | 75 | 左结合 | 3 |
| `>>>` | 75 | 左结合 | 3 |
| `▸` | 75 | 无结合 | 6 |
| `%` | 70 | 左结合 | 3 |
| `*` | 70 | 左结合 | 3 |
| `/` | 70 | 左结合 | 3 |
| `::` | 67 | 右结合 | 4 |
| `+` | 65 | 左结合 | 3 |
| `++` | 65 | 左结合 | 2 |
| `-` | 65 | 左结合 | 3 |
| `&&&` | 60 | 左结合 | 3 |
| `*>` | 60 | 左结合 | 2 |
| `>>` | 60 | 右结合 | 4 |
| `^^^` | 58 | 左结合 | 3 |
| `>>=` | 55 | 左结合 | 2 |
| `|||` | 55 | 左结合 | 3 |
| `!=` | 50 | 无结合 | 6 |
| `<` | 50 | 无结合 | 6 |
| `<=` | 50 | 无结合 | 4 |
| `=` | 50 | 无结合 | 6 |
| `==` | 50 | 无结合 | 6 |
| `>` | 50 | 无结合 | 6 |
| `>=` | 50 | 无结合 | 4 |
| `∈` | 50 | 右结合 | 4 |
| `≠` | 50 | 无结合 | 4 |
| `≤` | 50 | 无结合 | 6 |
| `≥` | 50 | 无结合 | 6 |
| `!` | 40 | 右结合 | 4 |
| `!` | 40 | 一元 | 6 |
| `¬` | 40 | 右结合 | 4 |
| `¬` | 40 | 一元 | 4 |
| `&&` | 35 | 左结合 | 2 |
| `/\` | 35 | 右结合 | 4 |
| `×` | 35 | 右结合 | 8 |
| `∧` | 35 | 右结合 | 4 |
| `||` | 30 | 左结合 | 2 |
| `∨` | 30 | 右结合 | 4 |
| `->` | 25 | 右结合 | 6 |
| `→` | 25 | 右结合 | 6 |
| `<|>` | 22 | 右结合 | 4 |
| `<->` | 20 | 无结合 | 4 |
| `↔` | 20 | 无结合 | 4 |
| `|>.` | 10 | 左结合 | 4 |
| `|>` | 1 | 左结合 | 2 |
| `<|` | 0 | 右结合 | 4 |

### 缩进与换行

每条是 profile 里的一个约束记号，以及它出现的次数。

- `@boundary=0:col-eq,0:linebreak` × 2 — 列与换行约束，原文是 `@boundary=0:col-eq,0:linebreak`。
- `@boundary=0:col-ge` × 12 — 列与换行约束，原文是 `@boundary=0:col-ge`。
- `@boundary=0:col-ge,1:col-eq,1:linebreak` × 1 — 列与换行约束，原文是 `@boundary=0:col-ge,1:col-eq,1:linebreak`。
- `@boundary=0:col-ge,1:linebreak` × 1 — 列与换行约束，原文是 `@boundary=0:col-ge,1:linebreak`。
- `@boundary=0:col-ge,3:col-eq,3:linebreak` × 3 — 列与换行约束，原文是 `@boundary=0:col-ge,3:col-eq,3:linebreak`。
- `@boundary=0:col-gt` × 16 — 列与换行约束，原文是 `@boundary=0:col-gt`。
- `@boundary=0:line-eq` × 1 — 列与换行约束，原文是 `@boundary=0:line-eq`。
- `@boundary=0:linebreak,0:col-eq` × 2 — 列与换行约束，原文是 `@boundary=0:linebreak,0:col-eq`。
- `@boundary=0:no-ws` × 2 — 列与换行约束，原文是 `@boundary=0:no-ws`。
- `@boundary=0:no-ws,1:no-ws,2:no-ws` × 1 — 列与换行约束，原文是 `@boundary=0:no-ws,1:no-ws,2:no-ws`。
- `@boundary=0:ws` × 3 — 列与换行约束，原文是 `@boundary=0:ws`。
- `@boundary=1:col-gt` × 3 — 列与换行约束，原文是 `@boundary=1:col-gt`。
- `@boundary=1:line-eq` × 2 — 列与换行约束，原文是 `@boundary=1:line-eq`。
- `@boundary=1:linebreak` × 4 — 列与换行约束，原文是 `@boundary=1:linebreak`。
- `@boundary=1:no-ws` × 22 — 列与换行约束，原文是 `@boundary=1:no-ws`。
- `@boundary=1:no-ws,2:no-ws` × 18 — 列与换行约束，原文是 `@boundary=1:no-ws,2:no-ws`。
- `@boundary=1:no-ws,4:no-ws` × 3 — 列与换行约束，原文是 `@boundary=1:no-ws,4:no-ws`。
- `@boundary=1:ws` × 14 — 列与换行约束，原文是 `@boundary=1:ws`。
- `@boundary=2:col-gt` × 1 — 列与换行约束，原文是 `@boundary=2:col-gt`。
- `@boundary=2:no-ws` × 6 — 列与换行约束，原文是 `@boundary=2:no-ws`。
- `@boundary=3:col-ge` × 2 — 列与换行约束，原文是 `@boundary=3:col-ge`。
- `@boundary=4:col-gt` × 1 — 列与换行约束，原文是 `@boundary=4:col-gt`。
- `@boundary=5:col-gt` × 1 — 列与换行约束，原文是 `@boundary=5:col-gt`。
- `@forbid-clear` × 21 — 后面的记号不能写成仿佛这块缩进已经结束。
- `@layout-clear` × 80 — 进入这里时清掉外层缩进，里面的内容不受外面的列约束。
- `@layout-root` × 33 — 这条产生式打开一块缩进区域，后面的行对齐在它下面。
- `@layout=1:adjacent` × 11 — 缩进约束，原文是 `@layout=1:adjacent`。
- `@layout=1:continuation` × 14 — 这一截是上一行的续行。
- `@scoped-layout=0:argument` × 3 — 局部缩进约束，原文是 `@scoped-layout=0:argument`。
- `@scoped-layout=0:not-outdented` × 9 — 下一行的缩进不能少于这一行。
- `@scoped-layout=0:not-outdented,3:not-outdented` × 1 — 局部缩进约束，原文是 `@scoped-layout=0:not-outdented,3:not-outdented`。
- `@scoped-layout=0:not-outdented,5:not-outdented` × 1 — 局部缩进约束，原文是 `@scoped-layout=0:not-outdented,5:not-outdented`。
- `@scoped-layout=1:argument` × 6 — 局部缩进约束，原文是 `@scoped-layout=1:argument`。

<!-- /surface-docs:grammar -->
