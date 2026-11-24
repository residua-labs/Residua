# rsm 表面

rsm 遵循 Racket 这一族。profile 文件是 `rsdc/profiles/rsm.syn`。它的名字行写的是 `rsl`。这些页面和例子文件用的名字是 rsm。

文件以 `#lang rsd` 这一行开头。形式是带括号的列表。行注释以 `;` 开头。块注释从 `#|` 到 `|#`。

它拼的是和 rsd、rsj 相同的树。

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
这一节由 `rsdc/profiles/rsm.syn` 生成。重新生成的命令是 `lean --run tools/surface-docs/Gen.rsd`。

### 空白、注释与分隔

- profile 的名字行是 `rsl`.
- 文件以这一行开头：`#lang rsd`.
- 空白：空格, 制表符, 换行, 回车.
- 行注释以 `;` 开头，直到行尾。
- 块注释由 `#|` 到 `|#`.
- 分组开括号：`(`, `[`.
- 分组闭括号：`)`, `]`.

### 关键字

共 40 个，按字母序。

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

### 运算符

同一个符号、优先级和结合性算一行。共 31 行。

| 符号 | 优先级 | 结合性 | 出现次数 |
| --- | --- | --- | --- |
| `!` | — | 前缀一元 | 2 |
| `!=` | — | 前缀 | 2 |
| `%` | — | 前缀 | 2 |
| `&&` | — | 前缀 | 2 |
| `&&&` | — | 前缀 | 2 |
| `*` | — | 前缀 | 2 |
| `+` | — | 前缀 | 2 |
| `++` | — | 前缀 | 2 |
| `-` | — | 前缀 | 2 |
| `-` | — | 前缀一元 | 2 |
| `/` | — | 前缀 | 2 |
| `::` | — | 前缀 | 2 |
| `<` | — | 前缀 | 2 |
| `<->` | — | 前缀 | 2 |
| `<<<` | — | 前缀 | 2 |
| `<=` | — | 前缀 | 2 |
| `=` | — | 前缀 | 2 |
| `==` | — | 前缀 | 2 |
| `>` | — | 前缀 | 2 |
| `>=` | — | 前缀 | 2 |
| `>>>` | — | 前缀 | 2 |
| `^^^` | — | 前缀 | 2 |
| `and-prop` | — | 前缀 | 2 |
| `not-prop` | — | 前缀一元 | 2 |
| `or-prop` | — | 前缀 | 2 |
| `||` | — | 前缀 | 2 |
| `|||` | — | 前缀 | 2 |
| `~~~` | — | 前缀一元 | 2 |
| `≠` | — | 前缀 | 2 |
| `≤` | — | 前缀 | 2 |
| `≥` | — | 前缀 | 2 |

### 缩进与换行

每条是 profile 里的一个约束记号，以及它出现的次数。

- `@layout=1:adjacent` × 1 — 缩进约束，原文是 `@layout=1:adjacent`。

<!-- /surface-docs:grammar -->
