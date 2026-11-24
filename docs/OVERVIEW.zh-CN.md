# OVERVIEW — Residua 是什么、0.3 提供什么、它的边界

[English](OVERVIEW.md) | 中文

本文是长文档：设计、动机、证据、边界与参考文献。短版见
[`README.zh-CN.md`](../README.zh-CN.md)。

## 它是什么

Residua 是一个关于在互不信任的各方之间复用计算与演绎结果的研究项目。结果以内容地址
（[q](GLOSSARY.zh-CN.md)：对结果字节计算的带类型 SHA-256）标识，而非以生产者或构建它的
工具链版本标识；结果只有通过相对形式定义语义的机械检查才被接受。

项目的语言 [rsd](GLOSSARY.zh-CN.md) 的设计是：程序与证明是同一依赖类型论中的项——同一个
项既被编译为本机或 WebAssembly 代码，也被证明内核检查。已发布版本交付该设计的编译一半：
一条任何第三方都能从提交的 [seed](GLOSSARY.zh-CN.md) 验证其来源的自举编译器链，连同工具链的内容标识格式、
语法引擎与执行边界的形式语义。证明检查的一半（[R-CIC](GLOSSARY.zh-CN.md) 内核）属于后续版本。

## 为什么——四个事实

1. **维护主导了形式结果的成本。** 上游变更后的重检、修复、协调与评审，
   花费远高于内核检查本身。
2. **生产者日益自动化。** 自动化代理的产出不能凭生产者的话接受；
   只有机械检查与内容标识能适应这一情形。
3. **语义彼此孤立。** 结果存在于分离的系统（Lean、Rocq、K、WebAssembly、
   EVM），无法跨系统携带。
4. **结果绑定工具链版本。** 编译出的库绑死在构建它的工具链版本上
   （如 Lean 的 `.olean`）；版本一变，下游全部重建重检。以内容标识的
   结果跨版本仍是同一结果。

## 方法

- **以内容标识。** 产物或结果以其内容地址 q 标识。q 相等是复用的
  判据；名称、位置、生产者都不是。
- **以检查准入。** 结果只能通过相对形式语义的机械检查进入系统。
  生产者——人、编译器或自动化代理——都在可信基之外
  （de Bruijn 准则 [9]）。
- **程序与证明同一语言。** 按设计，rsd 项既被编译也被同一内核检查，
  因此关于程序的陈述就是关于所运行项的陈述。
- **可验证的工具链。** 产生其他一切产物的编译器本身可从提交的
  seed 复现，其来源是被检查的而非被假定的。

## 0.3 提供什么——且只有这些

**可验证来源的编译。** 给定一份源码与一个产物，任何人都能用 C 编译器和
钉住的 wasm 运行时（wasmtime v50.0.1 加 binaryen version_133 的
`wasm-opt`，均由用户下载），从提交的 WebAssembly seed 重建编译器，
并逐字节核对产物来自该源码——既不信任发布者，也不信任大型二进制
工具链。配方在 Linux x86-64 与 macOS arm64 上运行。

本版本携带：

- rsd 编译器链 `rsd → `[rscm](GLOSSARY.zh-CN.md)` → wasm`（前端 `rsdc`、后端 `rsc`），自举：
  两个编译器以提交的 seed 形式随附于 `bootstrap/seed/`，连同钉住的
  源码成员表与重建配方。
- `rsd` 构建工具（`rsd/` 与 `lib/rsd/`）：`rsd build` 经内容寻址存储
  编译程序、只重编译变化的部分；`rsd test` 跑端到端套件；
  `rsd run` 执行；`rsd cache` 即内容存储本身。见 `docs/BUILD.md`。
- 带类型的内容地址 `q`（格式 v1）：被寻址内容的类别在哈希字节之内，
  不同类别的地址不可能碰撞（`docs/QFORMAT.md`，检查
  `release/checks/qformat/`）。
- 语法引擎，在其文法类上闭合：文法数据上的一个函数，与机械验证的
  参考判定器核对一致（`semantics/Syntax/`；轮廓 `rsdc/profiles/*.syn`）。
- 自举语法检查：编译器自身的六个源文件去掉 `import` 行后按成员顺序
  拼成 1,325,136 字节的束，OCaml 参考前端解析无错（语料判定见
  `docs/LANGUAGE.md`）。
- 执行边界语义：线格式、准入与封签判断、一致性分类器与录制的传输
  会话，以 Lean 4.14 命题表述（`semantics/Effect/`）。
- 语言中的 `UInt64`。
- 各编译层的冻结形式语义（scm、[lambda-RC](GLOSSARY.zh-CN.md)、[wasm0](GLOSSARY.zh-CN.md)），按内容摘要钉住；
  其 `.lean`/`.rsd` 文本作为钉住的规范随附。其中的 `theorem` 声明是钉住的
  规范，不是被检查的证明；`semantics/Effect/AdmissionNF.lean` 为审计随附，
  其 import（`Lib.Exec9Core`、`Lib.Receipt`）为仓库侧——检查它需要开发仓库。
- 基准与差分测试套件（`benchmarks/`、`instruments/lrc-host/`）及逐版本
  性能记录（`perf/`、`docs/PERF-RECORD.md` 与 `.tsv`）。
- seed 按本版本源码重切（携带 `UInt64` 与当前编译器成员集）；
  新的 `bootstrap/seed/stage-*` 目录取代 0.1 时代的目录。

## 各层如何衔接

- `rsdc` 把 `.rsd` 源码编译为 `.rscm`——scm 层的二进制接口
  （`docs/EMITTER.md`）。
- `rsc` 在 seed 钉住的构造字上把 `.rscm` 降为 `.wasm`。
- C seed 宿主 `bootstrap/seed/stage-14274/seed-host.c` 把 seed 模块
  嵌入钉住的 wasmtime 引擎运行；`bootstrap/seed/stage-14274/` 携带
  宿主、钉文件与配方。
- 调用形态是 `docs/RSD-COMMAND.md` 记载的执行器文件契约。

## 声明的边界

- 仅单模块程序：前端拒绝 `import`。
- 无 I/O 执行层：程序输入输出是宿主的文件契约，不是语言效应。
- 无证明检查：R-CIC 内核与证书不在本版本；随附的 `theorem` 文本是
  钉住的规范。
- 无结果的发布/查询入口。
- 无可导入的标准库（`docs/STDLIB.md`）。
- 前端接受的 `.rsd` 表面是 `docs/LANGUAGE.md` 的自举子集，拒绝
  `theorem`、`axiom`、`class`、`abbrev`、`variable`、`opaque`、`by`、`import`。

0.3 面向：可复现、可审计的编译——供应链与可验证、可自举编译器研究。
它不是通用语言。

## 证据

- **独立复现。** seed 配方由无项目先验知识的独立 agent 仅凭文档在
  新装 Linux 虚拟机上复现：两个编译器均重建为与 seed 逐字节一致。
- **独立评审。** 本版本经两个独立模型族评审。
- **归档一致性。** 发布 tag 处的仓库树与已发布源码归档逐字节一致。
- **逐目标审计。** 本版本每个新特性各有一份独立签名审计；
  记录存于仓库侧。

## 研究议程

特性版本按目标完成顺序编号 0.3、0.4、…；没有目标预先绑定编号，
  也不承诺日期：

- **检查他人结果。** R-CIC 证明内核、q 格式终版、结果的发布与查询入口。
- **编程完备性。** 模块、64 位寻址、I/O 执行层、真实应用套件。
- **廉价的执行确认。** wasm0 → AIR → 零知识证明。
- **连接外部语义。** K/KORE、Lean 与 Rocq 导入。

## 相关工作

基于 seed 的自举处理 trusting-trust 问题 [1]；相关途径有 diverse
double-compiling [2] 与 bootstrappable builds [3]；编译器的可验证自举
由 CakeML [4] 确立。后端按引用计数加复用管理内存，源自 "Counting
Immutable Beans" [6] 与 Perceus [5]；其各 pass 移植自 Lean 4 编译器 [11]，
目标为 WebAssembly [12]。凭可检查证据接受不可信生产者的结果属于
proof-carrying code [8] 传统；逐层翻译检查属于 translation
validation [10] 传统。计划中的证明内核与 Lean4Lean [7] 比较。
`release/NOTICES.md` 与 `release/PROVENANCE.tsv` 列出本项目移植的代码、
用作测试 oracle 的工具与研究过的设计。

## 参考文献

1. K. Thompson. Reflections on trusting trust. *Communications of the
   ACM* 27(8), 1984.
2. D. A. Wheeler. Countering trusting trust through diverse
   double-compiling. *ACSAC*, 2005.
3. Bootstrappable Builds. https://bootstrappable.org
4. R. Kumar, M. O. Myreen, M. Norrish, S. Owens. CakeML: a verified
   implementation of ML. *POPL*, 2014.
5. A. Reinking, N. Xie, L. de Moura, D. Leijen. Perceus: garbage free
   reference counting with reuse. *PLDI*, 2021.
6. S. Ullrich, L. de Moura. Counting immutable beans: reference
   counting optimized for purely functional programming. *IFL*, 2019.
7. M. Carneiro. Lean4Lean: verifying a typechecker for Lean, in Lean.
   arXiv:2403.14064, 2024.
8. G. C. Necula. Proof-carrying code. *POPL*, 1997.
9. H. Barendregt, F. Wiedijk. The challenge of computer mathematics.
   *Philosophical Transactions of the Royal Society A* 363, 2005.
10. A. Pnueli, M. Siegel, E. Singerman. Translation validation.
    *TACAS*, 1998.
11. L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming
    language. *CADE*, 2021.
12. A. Haas et al. Bringing the web up to speed with WebAssembly.
    *PLDI*, 2017.
