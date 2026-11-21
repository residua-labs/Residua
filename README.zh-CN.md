# Residua

**以内容标识的可验证计算与证明。**

[English](README.md) | 中文

## 摘要

Residua 是一个研究项目，研究互不信任的各方之间如何复用计算结果与证明结果。一个结果由其内容地址（*q*，即结果内容的 SHA-256
摘要）标识，而不由产出者或构建它的工具链版本标识；结果只有经过对照形式语义的机械检查，才被接纳。

项目的语言 **rsd** 的设计目标是：程序和证明是同一个依赖类型理论中的项，同一个项既被编译为原生或 WebAssembly 代码，又由证明内核
检查。0.1–0.2 版交付这一设计中编译的那一半：一条自举的编译链，任何第三方都可以从仓库中提交的种子出发验证其来源，
连同工具链的内容标识格式、语法引擎与执行边界的形式语义。证明检查的那一半
（R-CIC 内核）是后续版本的内容。

> **状态。** 研究版本 **0.2**（2026-11-20）：rsd 编译器的自举闭合，另加带类型的内容标识、
> 闭合的语法引擎与执行边界语义。
> 目前还不是通用语言，见[限制](#限制)。

## 动机

1. **形式化结果的成本主要在维护。** 在形式化开发中，上游变化后的重新检查、修复、协调和审查，成本远高于内核检查本身。
2. **产出者越来越多地是自动化程序。** 未来的大多数结果来自自动化 agent，其产出不能凭产出者的声明被接受。能扩展到这种情形的，只有
   机械检查和内容标识。
3. **语义彼此隔离。** 结果分散在不同系统中（Lean、Rocq、K、WebAssembly、EVM），彼此之间不能直接沿用。
4. **结果与工具链版本绑定。** 在现有的证明助手中，编译后的库只能用于构建它的那个工具链版本（例如 Lean 的 `.olean` 文件），所以
   版本一变，下游就要全部重新构建、重新检查。以内容标识的结果，跨版本仍是同一个结果。

## 方法

- **以内容为身份。** 产物和结果都由内容地址 *q* 标识。能否复用只看 *q* 是否相等，不看名字、位置或产出者。
- **以检查为接纳。** 结果只有通过对照形式语义的机械检查才能进入系统。产出者无论是人、编译器还是自动化 agent，都在可信基之外
  （de Bruijn 准则 [9]）。
- **程序与证明同一种语言。** 按设计，一个 rsd 项既被编译，又由同一个内核检查，所以关于程序的陈述，说的就是实际运行的那个项。
- **可验证的工具链。** 产出其他一切产物的编译器，本身可以从一个已提交的种子复现，所以它的来源是被检查的，而不是被假定的。

## 0.2 版

### 贡献

**来源可验证的编译。** 给定一份源码和一个产物，任何一方只用 C 编译器，就能从仓库中提交的 WebAssembly 种子重建编译器，并逐字节
核对该产物确实由这份源码得到；既不需要信任发布者，也不需要信任庞大的二进制工具链。

| 组成 | 内容 |
|---|---|
| 编译链 | `rsd → rscm → wasm`：前端 `rsdc` 和后端 `rsc`，附完整源码（53 个文件，以 SHA-256 钉住） |
| 种子 | `bootstrap/seed/stage-14274/`：两个编译器的 WebAssembly 形式、重建配方及其核对的全部摘要 |
| 形式语义 | 每一层（scm、λRC、wasm0）冻结的规范，以内容摘要钉住（`semantics/`、`gates/semalign/`、`lean/rsd-cert/`） |
| 性能记录 | 在固定硬件上与 Koka 及另外六种语言对比（`docs/PERF-RECORD.md`、`docs/PERF-RECORD.tsv`） |
| 内容标识 | 带类型的地址 `q`（格式 v1）：规范与登记表 [`docs/QFORMAT.zh-CN.md`](docs/QFORMAT.zh-CN.md)，向量 [`release/checks/qformat/`](release/checks/qformat/) |
| 语法引擎 | 在其文法类上闭合的数据驱动引擎：源 `rsdc/syntax/`，类 `semantics/Syntax/`，profile `rsdc/profiles/*.syn` |
| 效果语义 | 执行边界语义 E0–E4（`semantics/Effect/`）；验收证据 `reports/effect-sem/` |
| 文档 | 安装、验证流程、架构、信任模型、术语表、稳定性策略、FAQ（`docs/`，中英文） |

### 证据

- **独立复现。** 一个对项目一无所知的独立 agent，只凭文档，在全新的 Linux 虚拟机上复现了种子配方：两个编译器重建后与种子
  逐字节一致。
- **独立审查。** 本版本经过两个相互独立的模型家族审查。
- **源码包一致。** 标签 `rsd-0.2` 上的仓库内容与发布的源码包逐字节一致。
- **逐项目标审核。** 0.2 新增的每个目标都有独立的已签署审核；记录汇总在
  `reports/release-02/evidence/`。

## 复现自举

环境要求：Linux x86-64、GCC、GNU binutils、coreutils、Bash、curl 和 tar。不需要 Lean、Node 或 OCaml。

```sh
# 1. 从 rsd-0.2 发布页下载并核对源码包
sha256sum -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src

# 2. 在干净环境中从种子重建两个编译器（20–45 分钟）
env -i PATH=/usr/bin:/bin bash --noprofile --norc
#    然后执行 bootstrap/seed/stage-14274/README.md 中的命令
```

配方会下载钉住版本的 WABT，把两个种子执行器翻译成 C 并编译，再从源码重新编译两个编译器；只有重建结果与提交的种子逐字节一致时
才返回 0。

延伸阅读：

- [`docs/QUICKSTART.md`](docs/QUICKSTART.md)：第一次运行的详细步骤，以及如何编译一个源文件
- [`docs/VERIFY-RELEASE.md`](docs/VERIFY-RELEASE.md)：本版本的全部摘要核对
- [`docs/OVERVIEW.zh-CN.md`](docs/OVERVIEW.zh-CN.md) 和 [`docs/ARCHITECTURE.zh-CN.md`](docs/ARCHITECTURE.zh-CN.md)：0.2 是什么，各层如何衔接

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

**适用范围。** 这些数字描述的是一种机型上的一个小套件，刻画的是本版本，并不是对所比较语言的一般性排名。逐程序的表格、空格及其
原因、工具链版本和每个版本的历史，见 `docs/PERF-RECORD.tsv`。

## 限制

0.2 用于可复现、可审计的编译，以及可验证、可自举编译器的研究。

- 只支持单模块程序（没有 `import`）。
- 没有 I/O 执行层：效果边界语义规定的是宿主机契约，语言本身没有副作用。
- 不检查证明：R-CIC 内核不在本版本中，发布的 `theorem` 文本是规范，不是已检查的结论。
- 没有 `UInt64`；地址空间为 4 GiB。
- 0.2 的表面语言是严格的自举子集，拒绝 `theorem`、`axiom`、`class`、`abbrev` 和 `by`（[`docs/LANGUAGE.md`](docs/LANGUAGE.md)）。

## 研究议程

功能版本按目标完成的先后编号为 0.2、0.3……。哪个目标对应哪个编号不预先指定，也不承诺日期。目标如下：

- **检查他人的结果。** R-CIC 证明内核：结论与 Lean4Lean [7] 一致，并且不接受 Lean Kernel Arena 中的任何无效输入；最终的 q 格式；
  结果的发布与查询入口。
- **编程完整性。** 模块、`UInt64`、64 位寻址、I/O 执行层、真实应用套件。
- **低成本确认执行。** wasm0 → AIR → 零知识证明。
- **连接外部语义。** K/KORE、Lean 和 Rocq 导入。

## 相关工作

基于种子的自举针对的是"信任之信任"（trusting trust）问题 [1]；相关的途径有多样化双重编译（diverse double-compiling）[2] 和
可自举构建（bootstrappable builds）[3]，编译器的经验证自举由 CakeML [4] 确立。后端以带复用的引用计数管理内存，方法来自 "Counting Immutable Beans" [6] 和 Perceus [5]；其各遍移植自 Lean 4 的编译器
[11]，目标是 WebAssembly [12]。凭可检查的证据接受不可信产出者的结果，属于携带证明的代码（proof-carrying code）[8] 这一传统；逐层的翻译检查属于
翻译验证（translation validation）[10] 这一传统。计划中的证明内核以 Lean4Lean [7] 为对照。`release/NOTICES.md` 与 `release/PROVENANCE.tsv` 列出了
本项目移植的代码、用作测试参照的工具，以及研究过的设计。

## 版本记录

| 版本 | 日期 | 源码包 SHA-256 | 说明 |
|---|---|---|---|
| [0.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1) | 2026-11-19 | `59d0956e…` | 首个公开版本：最小自举闭合 |
| [0.1.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.1) | 2026-11-19 | 见发布页 | 补丁版本：性能记录随源码包发货，署名补全，移除内部标识符 |
| [0.1.2](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2) | 2026-11-19 | 见发布页 | 补丁版本：基准与差分测试套件发货 |
| [0.2](https://github.com/residua-labs/Residua/releases/tag/rsd-0.2) | 2026-11-20 | 见发布页 | 功能版本：q 格式 v1、语法引擎、效果语义；[CHANGELOG](CHANGELOG.zh-CN.md) |

完整记录：[CHANGELOG.zh-CN.md](CHANGELOG.zh-CN.md)。

## 仓库结构

| 路径 | 内容 |
|---|---|
| `bootstrap/` | 提交的种子、重建配方和 C 主机桥接 |
| `rsdc/`、`rsc/`、`lib/` | 编译器源码（前端、后端、共享库和运行时） |
| `semantics/`、`gates/`、`lean/` | 冻结的形式语义和逐层翻译检查 |
| `docs/` | 面向外来者的文档（中英文） |
| `release/` | 发布清单、来源记录、声明、许可证、检查与逐目标说明 |
| `perf/` | 每个版本的性能记录 |

## 引用

请引用你所使用的版本，并附其源码包的摘要：

```bibtex
@software{residua_0_2,
  title   = {Residua: Verifiable Computation and Proof, Identified by Content},
  author  = {{Residua Labs contributors}},
  year    = {2026},
  version = {0.2},
  url     = {https://github.com/residua-labs/Residua/releases/tag/rsd-0.2}
}
```

## 贡献与安全

欢迎提交 issue。安全问题请通过本仓库的 GitHub 私密漏洞报告提交，见 [`docs/CONTRIBUTING-SECURITY.zh-CN.md`](docs/CONTRIBUTING-SECURITY.zh-CN.md)。

## 致谢

Residua 建立在许多其他项目之上。`release/NOTICES.md` 与 `release/PROVENANCE.tsv` 列出了我们移植的代码、用作测试参照的工具，
以及研究过的设计；逐文件的署名见 `release/NOTICES.md` 和 `release/PROVENANCE.tsv`。如果你发现自己的工作被使用却没有致谢，请开 issue
或使用私密漏洞报告，我们会改正。

## 参考文献

1. K. Thompson. Reflections on trusting trust. *Communications of the ACM* 27(8), 1984.
2. D. A. Wheeler. Countering trusting trust through diverse double-compiling. *ACSAC*, 2005.
3. Bootstrappable Builds. https://bootstrappable.org
4. R. Kumar, M. O. Myreen, M. Norrish, S. Owens. CakeML: a verified implementation of ML. *POPL*, 2014.
5. A. Reinking, N. Xie, L. de Moura, D. Leijen. Perceus: garbage free reference counting with reuse. *PLDI*, 2021.
6. S. Ullrich, L. de Moura. Counting immutable beans: reference counting optimized for purely functional programming.
   *IFL*, 2019.
7. M. Carneiro. Lean4Lean: verifying a typechecker for Lean, in Lean. arXiv:2403.14064, 2024.
8. G. C. Necula. Proof-carrying code. *POPL*, 1997.
9. H. Barendregt, F. Wiedijk. The challenge of computer mathematics. *Philosophical Transactions of the Royal Society A*
   363, 2005.
10. A. Pnueli, M. Siegel, E. Singerman. Translation validation. *TACAS*, 1998.
11. L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming language. *CADE*, 2021.
12. A. Haas et al. Bringing the web up to speed with WebAssembly. *PLDI*, 2017.

## 许可证

Apache License 2.0。见 [LICENSE](LICENSE) 和 [NOTICE](NOTICE)。
