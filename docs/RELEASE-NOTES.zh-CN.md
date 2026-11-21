# RELEASE-NOTES — Residua 0.2

[English](RELEASE-NOTES.md) | 中文

0.2 版本保留 0.1 的自举闭合——可验证来源的编译，只用 C 编译器
从提交的 wasm 种子逐字节重建——并加入此后闭合的各项目标：最终
的带类型内容标识、在其文法类上闭合的语法引擎，以及执行边界的
形式语义。

## 0.2 新增

- **带类型的内容标识 `q`（格式 v1）。** 被寻址内容的种类进入
  哈希字节内部：`q(kind, c) = SHA-256("<kind> <len>\0" ++ c)`，
  打印为 `sha256:<hex>`；裸 SHA-256 保留为 `digest`，仅用于文件
  完整性与互操作。跨种类的地址冲突不再可能。规范：
  `docs/QFORMAT.zh-CN.md`；一致性向量：
  `release/checks/qformat/`；说明：`release/notes/qformat-1.zh-CN.md`。
- **在其文法类上闭合的语法引擎。** 一个函数——（以数据给出的
  类内文法，一个输入）-> 一棵树或一个命名拒绝——其判定与树
  在自类生成的文法上与该类经机器检查的参照判定器相等，并以
  埋入的变异体作对照。源 `rsdc/syntax/`；类 `semantics/Syntax/`；
  作为数据发货的表面 profile `rsdc/profiles/*.syn`；说明：
  `release/notes/syntax-engine.zh-CN.md`。
- **执行边界语义 E0–E4。** 线格式、准入与封签判断、一致性
  分类器以及录制的传输会话，以 Lean 4.14 陈述书写
  （`semantics/Effect/`）；验收证据 `reports/effect-sem/`
  （仓库侧）；说明：`release/notes/effect-sem.zh-CN.md`。

## 本归档内容

- 提交的 `rsdc`/`rsc` wasm 种子及其源码闭包
  （`bootstrap/seed/stage-14274/`）
- 种子配方（`bootstrap/seed/stage-14274/README.md`）及其所需的
  C 宿主桥
- 以阶段宿主文件契约调用的 rsd 链 `rsd -> rscm -> wasm`
  （`docs/RSD-COMMAND.md`）
- 逐层冻结的形式语义（scm、lambda-RC、wasm0），以内容摘要钉住，
  作为规范文本；0.2 新增 `semantics/Syntax/` 与 `semantics/Effect/`
- 语法引擎及其文法 profile（`rsdc/syntax/`、`rsdc/profiles/`）
- 引导文法对照测量的语言一致性语料（`docs/LANGUAGE.md` 各表）
- 性能记录（`docs/PERF-RECORD.tsv`，形式见
  `docs/PERF-RECORD.md`）
- 外来者文档：INSTALL、QUICKSTART、VERIFY-RELEASE、OVERVIEW、
  LANGUAGE、STDLIB、RSD-COMMAND、SPECS、QFORMAT、
  PERF-RECORD——均为英文；README 与十个 `docs/` 文本（OVERVIEW、
  ARCHITECTURE、TRUST、GLOSSARY、STABILITY、FAQ、RELATED-WORK、
  CONTRIBUTING-SECURITY、QFORMAT、RELEASE-NOTES，含本文件）另有
  `.zh-CN.md` 中文版
- 逐目标发布说明（`release/notes/`）、可运行的一致性检查
  （`release/checks/`）与 vendored 许可证文本（`release/licenses/`）

## 核验

`docs/VERIFY-RELEASE.md` 即核验规程：种子摘要、归档摘要，然后
在一台干净的 Linux x86-64 或 macOS arm64 账户上完整执行种子配方——
配方重建出的编译器映像必须与提交的种子逐字节一致（`seed_roundtrip=2/2`）。
macOS arm64 宿主（Apple clang、`PATH=/usr/bin:/bin`、无 Lean）已在
两台 Darwin 宿主上逐字节复现。

## 0.2 的版本局限

单模块程序（没有 `import`）；没有 I/O 执行层（效果边界语义规定
的是宿主机契约，语言本身没有效果）；没有证明检查（R-CIC 检查器
不在本版本）；没有 UInt64；4 GiB 地址空间；没有结果的发布/查询
入口；没有可导入的标准库。引导 `.rsd` 文法拒绝 `theorem`、
`axiom`、`class`、`abbrev`、`variable`、`opaque`、`by` 与
`import` 作为源构造。

## 0.2 之后的顺序

1. `rsd` 构建工具（`build`/`test`/`run`/`cache`）连同其源码所需的
   重切引导种子——本版本未含（仓库侧在 `rsd/`、`lib/rsd/`）。
2. R-CIC 内核 + agent 入口的发布/查询入口——陌生人第一次能找到、
   检查并复用他人结果的点。
3. 编程完备性：模块、真实程序、UInt64、执行层、64 位寻址、应用
   套件。
4. 廉价的执行确认：wasm0 -> AIR -> zk。
5. 通往外部语义的通用连接器（K/KORE、Lean/Rocq 导入）。

`closure_claim=0`（`release/MANIFEST.md`）。
