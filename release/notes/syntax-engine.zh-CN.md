# 版本说明 — 在其文法类上闭合的语法引擎

[English](syntax-engine.md) | 中文

状态：**随 0.3 版发货**；摘要另见 `docs/RELEASE-NOTES.zh-CN.md`。

## 提供的内容

解析器是一个函数：（以数据给出的类内文法，一个输入）-> 一棵树
或一个带位置的命名拒绝。类在 `semantics/Syntax/Class.rsd`：
`SynSpec.Grammar`、`Parses` 关系与参照判定器 `refParses` 及其
正确性证明（公理 `propext`、`Quot.sound`）。引擎实现源码位于开发仓库的
`rsdc/syntax/`；本归档中它们随 seed 的整模块源包
（`bootstrap/seed/stage-14274/sources/`）发货，而一种表面是
`rsdc/profiles/*.syn` 中的数据——新增一个 profile 不需要改动
`rsdc/syntax/`。所发编译器接受的
表面不变（`docs/LANGUAGE.md` 的 `.rsd` 引导子集）。

## 验收证据

- 源码修订：`28b9ff89f10514b93de92b8c0f60a109660ffa49`（在开发
  `main` 分支上）。
- 独立审核：在该 sha 上判定 an independent audit passed；记录
  `reports/release-02/evidence/AUDIT-SYNTAX-ENGINE.28b9ff89f1.md`
  （仓库侧保存，不在本归档）。
- 与类一致（E2）：`rsdc/syntax/ClassGate.rsd`（仓库侧）在 240 个生成文法
  与 4,334 个生成输入上——`disagreements=0`；每个文法带一个会
  改变 `refParses` 判定的变异体（240/240 已武装），并检查覆盖：
  右部长度 0..3、优先级 −1..2、结合性 0..3、消歧 0..3、选择组
  大小 1..3、布局操作 12/12、作用域操作 12/12、边界操作 7/7。
- 层间相等（E3）：在快速层的子类上，Earley 与 Pratt 两层给出
  同一棵树或同时拒绝——224 个文法、5,679 项检查、
  `disagreements=0`；武装对照 `mkA1 16` 可分开两层
  （`err=72` 对 `err=90`）。
- 引擎性（E4）：`rse.syn` profile 的加入在 `rsdc/syntax/` 下
  没有 diff。
- 全性与确定性（E5）：1,122 项规则翻转压力检查；相等的
  （文法 q，输入）在两台主机上给出相等的树 q。
- 代价界（E6）：在生成输入上测增长——输入加倍时 Earley 的
  adds 比 ≈2.00、Pratt 的 steps 比 ≈2.00；受保护的列缓存比
  1.999，其未缓存对照为 3.97（已武装），符合公开界（Earley
  层用 Leo 1991）。

## 局限

- 类之外的 profile 记于 `reports/synspec/OUTSIDE-CLASS.tsv`
  （仓库侧）；需要类外构造的语言是一次类修订，不是引擎改动。
- 每种语言的语料验收属于各 profile 自身，不属于引擎。
