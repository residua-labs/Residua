# OVERVIEW — Residua 是什么、0.4 提供什么、它的边界

[English](OVERVIEW.md) | 中文

本文是长文档：设计、动机、证据、边界与参考文献。短版见
[`README.zh-CN.md`](../README.zh-CN.md)。

## 它是什么

Residua 是一个关于在互不信任的各方之间复用计算与演绎结果的研究项目。结果以内容地址
（[q](GLOSSARY.zh-CN.md)：对结果字节计算的带类型 SHA-256）标识，而非以生产者或构建它的
工具链版本标识；结果只有通过相对形式定义语义的机械检查才被接受。

项目的语言 [rsd](GLOSSARY.zh-CN.md) 的设计是：程序与证明是同一依赖类型论中的项——同一个
项既被编译为本机或 WebAssembly 代码，也被证明内核检查。已发布版本交付该设计的编译一半：
任何第三方都能从提交的 [seed](GLOSSARY.zh-CN.md) 验证其来源的自举编译器链，连同工具链的内容标识格式、
语法引擎、`Proc` 执行宿主与执行边界的形式语义。证明检查的一半（[R-CIC](GLOSSARY.zh-CN.md) 内核）属于后续版本。

## 为什么——关键事实

1. **维护主导了形式结果的成本。** 上游变更后的重检、修复、协调与评审，
   花费远高于内核检查本身。
2. **生产者日益自动化。** 自动化代理的产出不能凭生产者的话接受；
   只有机械检查与内容标识能适应这一情形。
3. **语义彼此孤立。** 结果存在于分离的系统（Lean、Rocq、K、WebAssembly、
   EVM），无法跨系统携带。
4. **结果绑定工具链版本。** 编译出的库绑死在构建它的工具链版本上
   （如 Lean 的 `.olean`）；版本变更时下游全部重建重检。以内容标识的
   结果跨版本仍是同一结果。

## 方法

- **以内容标识。** 产物或结果以其内容地址 q 标识。q 相等是复用的
  判据；名称、位置、生产者都不是。
- **以检查准入。** 结果只能通过相对形式语义的机械检查进入系统。
  生产者——人、编译器或自动化代理——都在可信基之外
  （de Bruijn 准则 [^9]）。
- **程序与证明同一语言。** 按设计，rsd 项既被编译也被内核检查，
  因此关于程序的陈述就是关于所运行项的陈述。
- **可验证的工具链。** 产生其他产物的编译器本身可从提交的
  seed 复现，其来源是被检查的而非被假定的。

## 0.4 提供什么——且只有这些

**可验证来源的编译与命令行/文件执行。** 给定多模块 `.rsd` 源码与产物，
任何人都能用 C 编译器和钉住的 wasm 运行时（wasmtime v50.0.1 加 binaryen
version_133 的 `wasm-opt`，均由用户下载），从提交的 WebAssembly seed 重建
编译器，逐字节核对编译器复现其 seed，把多模块 `Proc` 程序编译为
WebAssembly 并在 C11 `procwt` 宿主上运行——既不信任发布者，也不信任大型
二进制工具链。配方在 Linux x86-64 与 macOS arm64 上运行。

本版本携带：

- rsd 编译器链 `rsd → `[rscm](GLOSSARY.zh-CN.md)` → wasm`（前端 `rsdc`、后端 `rsc`），自举：
  编译器以提交的 seed 形式随附于 `bootstrap/seed/stage-14274/`
  （`rsdc.wasm` `12,519,278` 字节，`rsc.wasm` `14,275,644` 字节），连同
  钉住的 `54` 成员源码闭包与重建配方（Linux x86-64 上 `105 s`，macOS
  arm64 上 `191 s`）。
- 多模块 `.rsd` 程序（`import`）、IEEE-754 `Float`（`binary64`）、`Proc`
  上的 `do` 记法、标准 `Proc` 库（`lib/ProcBytes.rsd`、`lib/Proc9.rsd`、
  `glue/std/`）、C11 WebAssembly 与 wasm2c `Proc` 执行宿主
  （`glue/host/procwt.c`、`glue/host/proc9core.h`、`glue/host/proc9.c`），
  以及多模块命令行示例（`examples/app04/`）。
- `rsd` 构建工具（`rsd/`、`glue/rsd/`、`lib/rsd/`、`lib/Rsd.rsd`）：
  `rsd build` 经内容寻址存储编译程序、只重编译变化的部分；`rsd test` 跑
  端到端套件；`rsd run` 在 `procwt` 上执行 `Proc` 程序；`rsd cache` 即
  内容存储本身。见 [docs/BUILD.zh-CN.md](BUILD.zh-CN.md)。
- Apache-2.0 许可的平衡映射表（`lib/AvlMap.rsd`），移植自 Lean v4.36.0
  （`Std.DTreeMap`），取代 0.3 中源于 OCaml `stdlib/map.ml` 的移植。
- 带类型的内容地址 `q`（格式 v1）：被寻址内容的类别在哈希字节之内，
  不同类别的地址不可能碰撞（`docs/QFORMAT.zh-CN.md`，检查
  `release/checks/qformat/`）。
- 语法引擎，在其文法类上闭合：文法数据上的函数，与机械验证的参考判定器
  核对一致（`semantics/Syntax/`；轮廓 `rsdc/profiles/*.syn`）。
- 自举语法检查：编译器自身的源码束去掉 `import` 行后按成员顺序拼成
  1,447,122 字节的束，OCaml 参考前端解析无错（语料判定见
  `docs/LANGUAGE.md`）。
- 执行边界语义（`semantics/Effect/`）与 MST-NF 复合包
  （`lean/nf-compose/`，0.4 新增 `HopCompose.lean` 中的多跳编译复合及
  `Rec.lean`、`NfRec/CheckedStatus.lean` 中的递归复合定理）。
- 各编译层的冻结形式语义（scm、[lambda-RC](GLOSSARY.zh-CN.md)、[wasm0](GLOSSARY.zh-CN.md)），按内容摘要钉住；
  其 `.lean`/`.rsd` 文本作为钉住的规范随附。其中的 `theorem` 声明是钉住的
  规范，不是被检查的证明；`semantics/Effect/AdmissionNF.lean` 为审计随附，
  其 import（`Lib.Exec9Core`、`Lib.Receipt`）为仓库侧——检查它需要开发仓库。
- 基准与差分测试套件（`benchmarks/`、`instruments/lrc-host/`，含 `Float`
  差分与变异检查）及逐版本性能记录（`perf/`、`docs/PERF-RECORD.md` 与
  `.tsv`）。

## 各层如何衔接

- `rsdc` 把 `.rsd` 源码编译为 `.rscm`——scm 层的二进制接口
  （`docs/EMITTER.md`），并在输入冠以 `\0RSDC-ENTRIES\n` 头时打印导出表。
- `rsc` 在 seed 钉住的构造字（`14274`）上把 `.rscm` 降为 `.wasm`。
- `seed-host.c` 把 seed 模块嵌入钉住的 wasmtime 引擎运行，并读取模块导出的
  `__heap_base` 全局量使堆分配从静态数据段之上开始；`glue/host/procwt.c`
  通过进程内 9P2000 响应器承载编译出的 `Proc` WebAssembly 模块。
- 编译器调用遵循 `docs/RSD-COMMAND.md` 记载的文件契约。

## 声明的边界

- 独立 `.rmod` 模块编译尚未覆盖 `Float`（类型码 `13`）及逐模块 `Proc`
  `do` 反糖化（`release/GAPS.tsv`）；多模块程序在交由 `rsdc` 前按拓扑序
  拼接源码模块。
- `glue/host/procwt.c` 通过进程内 9P2000 响应器提供命令行参数、时钟与本地
  文件读写（`release/GAPS.tsv`）；网络套接字与子进程派生不在本版范围。
- 无证明检查：R-CIC 内核与证书不在本版本；随附的 `theorem` 文本是钉住的规范。
- 无结果的发布/查询入口。
- 前端接受的 `.rsd` 表面是 `docs/LANGUAGE.md` 的自举子集，拒绝
  `theorem`、`axiom`、`class`、`abbrev`、`variable`、`opaque`、`by`。

0.4 面向：可复现、可审计的编译与自包含的命令行/文件程序——供应链与可验证、
可自举编译器研究。

## 证据

- **独立复现。** seed 配方在干净的 Linux x86-64 与 macOS arm64 环境上复现：
  编译器重建产物与提交的 seed 逐字节一致，`examples/app04` 在全部 `16` 个
  差分测试输入上与原版 Lean 4.14.0 预言机一致。
- **独立评审。** 各发布线经独立模型族评审。
- **归档一致性。** 发布 tag 处的仓库树与已发布源码归档逐字节一致。
- **逐目标审计。** 本版本各特性均有独立审计；记录存于仓库侧。

## 研究议程

特性版本按目标完成顺序编号 0.3、0.4、…；没有目标预先绑定编号，也不承诺日期：

- **检查他人结果。** R-CIC 证明内核、q 格式终版、结果的发布与查询入口。
- **编程完备性。** 覆盖完整语言的独立 `.rmod` 编译、64 位 WebAssembly 寻址、
  更广的宿主服务与更大规模应用套件（如 Cedar 与 mathlib4 导入）。
- **廉价的执行确认。** wasm0 → AIR → 零知识证明。
- **连接外部语义。** K/KORE、Lean 与 Rocq 导入。

## 相关工作

基于 seed 的自举处理 trusting-trust 问题 [^1]；相关途径有 diverse
double-compiling [^2] 与 bootstrappable builds [^3]；编译器的可验证自举
由 CakeML [^4] 确立。后端按引用计数加复用管理内存，源自 "Counting
Immutable Beans" [^6] 与 Perceus [^5]；其各 pass 移植自 Lean 4 编译器 [^11]，
目标为 WebAssembly [^12]。凭可检查证据接受不可信生产者的结果属于
proof-carrying code [^8] 传统；逐层翻译检查属于 translation
validation [^10] 传统。计划中的证明内核与 Lean4Lean [^7] 比较。
`release/NOTICES.md` 与 `release/PROVENANCE.tsv` 列出本项目移植的代码、
用作测试 oracle 的工具与研究过的设计。

## 参考文献

[^1]: K. Thompson. Reflections on trusting trust. *Communications of the
   ACM* 27(8), 1984.
[^2]: D. A. Wheeler. Countering trusting trust through diverse
   double-compiling. *ACSAC*, 2005.
[^3]: Bootstrappable Builds. https://bootstrappable.org
[^4]: R. Kumar, M. O. Myreen, M. Norrish, S. Owens. CakeML: a verified
   implementation of ML. *POPL*, 2014.
[^5]: A. Reinking, N. Xie, L. de Moura, D. Leijen. Perceus: garbage free
   reference counting with reuse. *PLDI*, 2021.
[^6]: S. Ullrich, L. de Moura. Counting immutable beans: reference
   counting optimized for purely functional programming. *IFL*, 2019.
[^7]: M. Carneiro. Lean4Lean: verifying a typechecker for Lean, in Lean.
   arXiv:2403.14064, 2024.
[^8]: G. C. Necula. Proof-carrying code. *POPL*, 1997.
[^9]: H. Barendregt, F. Wiedijk. The challenge of computer mathematics.
   *Philosophical Transactions of the Royal Society A* 363, 2005.
[^10]: A. Pnueli, M. Siegel, E. Singerman. Translation validation.
    *TACAS*, 1998.
[^11]: L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming
    language. *CADE*, 2021.
[^12]: A. Haas et al. Bringing the web up to speed with WebAssembly.
    *PLDI*, 2017.
