# Residua

[English](README.md) | 中文

性能：[perf/](perf/README.zh-CN.md) 保存每个版本的性能记录，测量方法相同，版本之间可以比较。

Residua 是一套基础设施，让人无需信任对方，就能使用对方的计算或证明。一个结果按其内容的地址（q）来识别，
而不是按谁产出了它、或用哪个版本的工具链构建了它；结果只凭机械检查准入，建立在一张形式化定义的语义网络之上。
Residua 的设计是计算和证明一体：在它的语言 rsd 中，程序和证明是同一个依赖类型论中的项，同一个项既被编译成
原生代码或 WebAssembly，又由内核检查。这一点尚未端到端证实；0.1 版本交付的是编译这一半——证明检查那一半
（R-CIC 内核）在后续版本，见下文的版本局限。

## 为什么

- 形式化结果的成本主要花在重复检查、上游变化后的修补、协调和审查上；内核检查本身只占一小部分。
- 将来的结果大多由不可信的机器产出。能扩展到这种规模的，只有机械检查和按内容识别。
- 形式语义彼此割裂（Lean、Rocq、K、wasm、EVM），结果无法跨越它们组合。

## 0.1 提供什么

可验证来源的编译。给定一份源码和一份产物，任何人都可以从提交在仓库中的 wasm 种子出发——只用 C 编译器，
不需要别的工具链——逐字节重建，核验这份产物确实来自这份源码：既不必信任发布者，也不必信任一个庞大的
二进制工具链。

支撑它的：

- rsd 编译器链 `rsd -> rscm -> wasm`（`rsdc`、`rsc`），其自身源码就在本归档中
- 逐层冻结的形式语义（scm、lambda-RC、wasm0），按内容地址钉住，以规范文本形式随
  `semantics/`、`gates/semalign/` 与 `lean/rsd-cert/` 发货
- 每版本一份的性能记录（`release/docs/PERF-RECORD.tsv`；固定的 PERF-RECORD-0 形式
  见 `release/docs/PERF-RECORD`）
- 两个不同模型族的封签，以及种子配方的第三方复现（证据在仓库侧）

从这里开始：

- `release/docs/INSTALL` — 最少步骤
- `release/docs/QUICKSTART` — 第一次运行，逐步说明
- `release/docs/VERIFY-RELEASE` — 完整核验规程
- `release/docs/OVERVIEW` — 0.1 有什么、没有什么
- `release/docs/ARCHITECTURE` — 语义链、表面语法、身份与信任
- `release/docs/TRUST`、`GLOSSARY`、`STABILITY`、`FAQ`、
  `RELATED-WORK`、`CONTRIBUTING-SECURITY` — 0.1 信任什么、用语、
  承诺，以及与其他工作的关系（各在 `release/docs/` 下，英文附
  中文镜像）
- `release/MANIFEST.md` — 本归档按之构建的发布需求

## 0.1 的版本局限

- 单模块程序（不接受 `import`）
- 没有 I/O 执行层
- 没有证明检查（R-CIC 检查器不在本版本中；随附的 `theorem` 文本是钉住的规范，
  不是被检查的断言）
- 没有 UInt64；4 GiB 地址空间
- q 内容寻址格式尚未定稿
- 没有结果的发布/查询入口
- 0.1 的 `.rsd` 面是严格的引导子集——`theorem`、`axiom`、`class`、`abbrev`、
  `by` 均被拒绝（`release/docs/LANGUAGE`）

0.1 面向可复现、可审计的编译——供应链、可信执行之前的那一步——以及可验证、可
自举编译器的研究。它不以通用语言的面目发布。

## 0.1 之后的顺序

每项都带验收对象；不写日期。

1. 不信任对方即可使用其结果，第一个实例：R-CIC 内核（Lean Kernel Arena：任何非法
   输入都不被接受，然后 init/std，再然后 16 GiB 内的 mathlib）加上 q 格式和 Jig 的
   发布/查询入口——这是陌生人第一次能找到、检查并复用他人结果的点；排在编程
   特性之前。
2. 编程完备性：模块、真实程序、UInt64、执行层（I/O 作类型化效果）、64 位寻址，
   以及应用套件（Cedar、Anvil、Tendril、SQLite）作为验收。
3. 廉价的执行确认：wasm0 -> AIR -> zk。
4. 网络：通往外部语义的通用连接器（K/KORE、Lean/Rocq 导入），按一座桥能打开
   多少语义排序。

## 命名

Residua 是项目。`rsd` 是语言和工具链。`raisin` 留在内部。

closure_claim = 0

## 研究项目与致谢

Residua 是一个研究项目，建立在许多其他项目之上；[ACKNOWLEDGEMENTS.zh-CN.md](ACKNOWLEDGEMENTS.zh-CN.md) 列出了我们移植过的代码、用作测试参照的工具，以及研究过的设计。如果你发现自己的工作被使用却没有致谢，请开 issue 或使用私密漏洞报告；我们会补上致谢并修正发布。
