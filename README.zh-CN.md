# Residua

**以内容标识的可验证计算与证明。**

[English](README.md) | 中文

## 摘要

Residua 为研究项目，研究互不信任的各方之间如何复用计算结果与证明结果。结果由其内容地址（*q*，即结果内容的 SHA-256
摘要）标识，而不由产出者或构建它的工具链版本标识；结果只有经过对照形式语义的机械检查，才被接纳。

项目的语言 **rsd** 的设计目标是：程序和证明为同种依赖类型理论中的项，同项既被编译为原生或 WebAssembly 代码，又由证明内核
检查。0.1 版交付此设计中编译那部分：自举编译链，任何外部方都可从仓库中已提交的种子出发验证其来源。证明检查那部分
（R-CIC 内核）是后续版本的内容。

> **状态。** 研究版本 **0.1.2**（2026-11-20）：rsd 编译器的最小自举闭合，
> 附测试与基准套件。
> 目前还不是通用语言，见[限制](#限制)。

## 更新

- **0.1.2**（2026-11-20）：基准程序、Koka 对比工具和差分测试套件进入源码包，运行方法见 `release/docs/TESTING`。
- **0.1.1**（2026-11-20）：性能记录（`perf/`）进入源码包；署名补全（`ACKNOWLEDGEMENTS.zh-CN.md`）；版本规则修正
  （功能版本为 0.2、0.3……，修订版本为 0.1.x）。
- 两个修订版本的自举配方输入都与 0.1 逐字节相同。完整记录：[CHANGELOG.zh-CN.md](CHANGELOG.zh-CN.md)。

## 动机

1. **形式化结果的成本主要在维护。** 在形式化开发中，上游变化后的重新检查、修复、协调和审查，成本远高于内核检查本身。
2. **产出者越来越多地是自动化程序。** 本项目假定：未来的大多数结果将来自自动化 agent，其产出不能凭产出者的声明被接受。
   在此假定下，能扩展到该情形的只有机械检查和内容标识。
3. **语义彼此隔离。** 结果分散在不同系统中（Lean、Rocq、K、WebAssembly、EVM），彼此之间不能直接沿用。
4. **结果与工具链版本绑定。** 在现有的证明助手中，编译后的库只能用于构建它的那个工具链版本（例如 Lean 的 `.olean` 文件），所以
   版本变更，下游就要全部重新构建、重新检查。以内容标识的结果，跨版本仍是同个结果。

## 方法

- **以内容为身份。** 产物和结果都由内容地址 *q* 标识。能否复用只看 *q* 是否相等，不看名字、位置或产出者。
- **以检查为接纳。** 结果只有通过对照形式语义的机械检查才能进入系统。产出者无论是人、编译器还是自动化 agent，都在可信基之外
  （de Bruijn 准则 [9]）。
- **程序与证明同种语言。** 按设计，rsd 项既被编译，又由同个内核检查，所以关于程序的陈述，说的就是实际运行的那个项。
- **可验证的工具链。** 产出其他全部产物的编译器，本身可从已提交的种子复现，所以它的来源是被检查的，而不是被假定的。

## 0.1 版

### 贡献

**来源可验证的编译。** 给定源码与产物，任何外部方只用 C 编译器，就能从仓库中提交的 WebAssembly 种子重建编译器，并逐字节
核对该产物确实由这份源码得到；既不需要信任发布者，也不必信任庞大的 binary 工具链。

| 组成 | 内容 |
|---|---|
| 编译链 | `rsd → rscm → wasm`：前端 `rsdc` 和后端 `rsc`，附完整源码（54 个文件，以 SHA-256 钉住） |
| 种子 | `bootstrap/seed/stage-14274/`：`rsdc` 与 `rsc` 编译器的 WebAssembly 形式、重建配方及其核对的全部摘要 |
| 形式语义 | 各层（scm、λRC、wasm0）冻结的规范，以内容摘要钉住（`semantics/`、`gates/semalign/`、`lean/rsd-cert/`） |
| 性能记录 | 在固定硬件上与 Koka 及另外 6 门语言对比（[`perf/`](perf/README.zh-CN.md)） |
| 文档 | 安装、验证流程、架构、信任模型、术语表、稳定性策略、FAQ（`release/docs/`，中英文） |
| 测试与基准套件 | `benchmarks/`（基准程序与对比框架）与 `instruments/lrc-host/`（对拍测试套件），用法见 `release/docs/TESTING` |

### 证据

- **独立复现。** 某对项目全无了解的独立 agent，只凭文档，在全新的 Linux 虚拟机上复现了种子配方：`rsdc` 与 `rsc` 重建后与种子
  逐字节相同。
- **独立审查。** 本发布线的早期 head 经相互独立的模型家族审查（最近为 `891b1a122a`）；裁决记录保存在本归档之外。
- **源码包逐字节相同。** 标签 `rsd-0.1.2` 上的仓库内容与发布的源码包逐字节相同。

## 复现自举

环境要求：Linux x86-64、GCC、GNU binutils、coreutils、Bash、curl 和 tar。不需要 Lean、Node 或 OCaml。

```sh
# 1. 从 rsd-0.1.2 发布页下载并核对源码包
sha256sum -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src

# 2. 在干净环境中从种子重建两个编译器（20–45 分钟）
env -i PATH=/usr/bin:/bin bash --noprofile --norc
#    然后执行 bootstrap/seed/stage-14274/README.md 中的命令
```

配方会下载钉住版本的 WABT，把种子执行器翻译成 C 并编译，再从源码重新编译 `rsdc` 与 `rsc`；只有重建结果与提交的种子逐字节相同时
才返回 0。

延伸阅读：

- [`release/docs/QUICKSTART`](release/docs/QUICKSTART)：初次运行的详细步骤，以及如何编译源文件
- [`release/docs/VERIFY-RELEASE`](release/docs/VERIFY-RELEASE)：本版本的全部摘要核对
- [`release/docs/OVERVIEW.zh-CN`](release/docs/OVERVIEW.zh-CN) 和 [`release/docs/ARCHITECTURE.zh-CN`](release/docs/ARCHITECTURE.zh-CN)：0.1 是什么，各层如何衔接

## 评测

<!-- generated-from-perf -->
**方法。** GCP t2d-standard-4。Koka 两列：两台全新虚拟机，每个值是两台机器各自 5 次中位数的均值（固定核心）。
其他语言各列：三台全新虚拟机，固定核心上 5 次取中位数。比值 = Residua 的墙钟时间 / 参照的墙钟时间，小于 1
表示 Residua 更快。程序原样取自 Koka 的基准套件（Perceus 论文 [5] 所用的套件）和 Lean 4 的基准。

| 几何平均，Residua 0.1 / … | Koka（原生） | Koka（wasm） | C++ | OCaml | Haskell | Java | Swift | Lean 4.14 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 比值 | 0.973 | 1.047 | 0.822 | 0.586 | 0.281 | 0.451 | 0.164 | 0.570 |
<!-- end-generated-from-perf -->

从种子自举用时 1162 秒（峰值 3.6 GiB）。

**适用范围。** 这些数字描述某机型上的小型套件，刻画本版本，`并非对所比较语言的通用排名`。逐程序的表格、空格及其
原因、工具链版本和每个版本的历史，见 [`perf/`](perf/README.zh-CN.md)。

## 限制

0.1.2 用于可复现、可审计的编译，以及可验证、可自举编译器的研究。

- 只支持单模块程序（没有 `import`）。
- 没有 I/O 执行层。
- 不检查证明：R-CIC 内核不在本版本中，发布的 `theorem` 文本是规范，不是已检查的结论。
- 没有 `UInt64`；地址空间为 4 GiB。
- 内容标识（q）的格式尚未定稿。
- 0.1.2 的表面语言是严格的自举子集，拒绝 `theorem`、`axiom`、`class`、`abbrev` 和 `by`（[`release/docs/LANGUAGE`](release/docs/LANGUAGE)）。

## 研究议程

功能版本按目标完成的先后编号为 0.2、0.3……。哪个目标对应哪个编号不预先指定，也不承诺日期。目标如下：

- **检查他人的结果。** R-CIC 证明内核：结论与 Lean4Lean [7] 相符，并且不接受 Lean Kernel Arena 中的任何无效输入；最终的 q 格式；
  结果的发布与查询入口。
- **编程完整性。** 模块、`UInt64`、64 位寻址、I/O 执行层、真实应用套件。
- **低成本确认执行。** wasm0 → AIR → zero-knowledge 证明。
- **连接外部语义。** K/KORE、Lean 和 Rocq 导入。

## 相关工作

基于种子的自举针对的是"信任之信任"（trusting trust）问题 [1]；相关的途径有多编译器交叉构建（diverse double-compiling）[2] 和
可自举构建（bootstrappable builds）[3]，编译器的经验证自举由 CakeML [4] 确立。后端以带复用的引用计数管理内存，方法来自 "Counting Immutable Beans" [6] 和 Perceus [5]；其各遍移植自 Lean 4 的编译器
[11]，目标是 WebAssembly [12]。凭可检查的证据接受不可信产出者的结果，属于携带证明的代码（proof-carrying code）[8] 此传统；逐层的翻译检查属于
翻译验证（translation validation）[10] 此传统。计划中的证明内核以 Lean4Lean [7] 为对照。[ACKNOWLEDGEMENTS.zh-CN.md](ACKNOWLEDGEMENTS.zh-CN.md) 列出了
本项目移植的代码、用作测试参照的工具，以及研究过的设计。

## 版本记录

| 版本 | 日期 | 源码包 SHA-256 | 说明 |
|---|---|---|---|
| [0.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1) | 2026-11-19 | `59d0956e…` | 首个公开版本：最小自举闭合 |
| [0.1.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.1) | 2026-11-20 | `28a074e2…` | 修订版：性能记录进入源码包，署名补全，内部标识符移除 |
| [0.1.2](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2) | 2026-11-20 | `a3185221…` | 修订版：基准与对拍测试套件进入源码包 |

完整记录：[CHANGELOG.zh-CN.md](CHANGELOG.zh-CN.md)。

## 仓库结构

| 路径 | 内容 |
|---|---|
| `bootstrap/` | 提交的种子、重建配方和 C 主机桥接 |
| `rsdc/`、`rsc/`、`lib/` | 编译器源码（前端、后端、共享库和运行时） |
| `semantics/`、`gates/`、`lean/` | 冻结的形式语义和逐层翻译检查 |
| `release/` | 发布清单、来源记录、声明、许可证和文档 |
| `perf/` | 每个版本的性能记录 |
| `benchmarks/` | 基准程序、生成的模块、期望输出与对比框架 |
| `instruments/` | 宿主机测试工具，包括对拍测试套件 |

## 引用

请引用你所使用的版本，并附其源码包的摘要：

```bibtex
@software{residua_0_1_2,
  title   = {Residua: Verifiable Computation and Proof, Identified by Content},
  author  = {{Residua Labs contributors}},
  year    = {2026},
  version = {0.1.2},
  url     = {https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2},
  note    = {Source archive SHA-256 recorded on the release page}
}
```

## 贡献与安全

欢迎提交 issue。安全问题请通过本仓库的 GitHub 私密漏洞报告提交，见 [`release/docs/CONTRIBUTING-SECURITY.zh-CN`](release/docs/CONTRIBUTING-SECURITY.zh-CN)。

## 致谢

Residua 建立在许多其他项目之上。[ACKNOWLEDGEMENTS.zh-CN.md](ACKNOWLEDGEMENTS.zh-CN.md) 列出了我们移植的代码、用作测试参照的工具，
以及研究过的设计；逐文件的署名见 `release/NOTICES.md` 和 `release/PROVENANCE.tsv`。如果你发现自己的工作被使用却没有致谢，请开 issue
或使用私密漏洞报告，我们会改正。

## 参考文献

1. K. Thompson. Reflections on trusting trust. *Communications of the ACM* 27(8), 1984.
2. D. A. Wheeler. Countering trusting trust through diverse double-compiling. *ACSAC*, 2005.
3. Bootstrappable Builds project. "Bootstrappable builds". https://bootstrappable.org (accessed 2026-11).
4. R. Kumar, M. O. Myreen, M. Norrish, S. Owens. CakeML: a verified implementation of ML. *POPL*, 2014.
5. A. Reinking, N. Xie, L. de Moura, D. Leijen. Perceus: garbage free reference counting with reuse. *PLDI*, 2021.
6. S. Ullrich, L. de Moura. Counting immutable beans: reference counting optimized for purely functional programming.
   *IFL*, 2019.
7. M. Carneiro. Lean4Lean: Verifying a Typechecker for Lean, in Lean. arXiv:2403.14064, 2024.
8. G. C. Necula. Proof-carrying code. *POPL*, 1997.
9. H. Barendregt, F. Wiedijk. The challenge of computer mathematics. *Philosophical Transactions of the Royal Society A*
   363, 2005.
10. A. Pnueli, M. Siegel, E. Singerman. Translation validation. *TACAS*, 1998.
11. L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming language. *CADE*, 2021.
12. A. Haas et al. Bringing the web up to speed with WebAssembly. *PLDI*, 2017.

## 许可证

Apache License 2.0。见 [LICENSE](LICENSE) 和 [NOTICE](NOTICE)。
