# 发布说明——三种表面写法

[English](surfaces.md) | 中文

状态：**0.3 新增**；摘要同时见 `docs/RELEASE-NOTES.zh-CN.md`。

## 内容

同一个程序可以用三种表面写法书写：

- `.rsd`——编译器前端读取的类 Lean 写法。
- `.rsj`——同一棵树的类 JavaScript 写法。
- `.rsm`——类 Racket 写法（`#lang rsd`）。

`examples/surfaces/` 随附五个程序——`do`、`inductive`、`match`、
`module`、`structure`——每个都以三种写法打印。
`docs/surfaces/` 记录每种写法的剖面（名称行、注释形式）及
`check.tsv` 中的往返检查：每个程序的三种写法解析到同一个树 q，
且 `.rsd` 写法被原版 Lean 4.14 接受。

## 位置

- `examples/surfaces/*.rsd`、`*.rsj`、`*.rsm`——五个程序。
- `docs/surfaces/rsd.md`、`rsj.md`、`rsm.md`——每种写法一份文档，
  中英双语。
- `docs/surfaces/check.tsv`——实测的往返检查表。
