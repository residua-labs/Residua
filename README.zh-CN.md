# Residua

**以内容标识的可验证计算与证明。**

[English](README.md) | 中文

Residua 是一个研究项目，目标是构建这样一套基础设施：使用别人的计算或证明，而不必信任对方。每个结果都由内容地址（*q*，即结果本身的 SHA-256
摘要）标识，而不是由谁产出、用哪个版本的工具链构建来标识；结果只有经过对照形式语义的机械检查，才会被接纳。

语言 **rsd** 的设计目标是：程序和证明是同一个依赖类型理论里的项，同一个项既被编译成原生或 WebAssembly 代码，又被证明内核检查。0.1 交付的是这个设计中
编译的那一半；证明检查的那一半（R-CIC 内核）是下一个版本的内容。

> **状态：** 研究版本 **0.1**，即 rsd 编译器的最小自举闭合。
> 目前还不是通用语言，见[限制](#限制)。

## 为什么

- **检查本身并不贵。** 对形式化结果来说，上游变化后的重新检查、修复、协调和审查，成本远高于内核检查本身。
- **产出者将是机器。** 未来大多数结果来自不可信的自动化 agent，能扩展到这种规模的只有机械检查和内容标识。
- **语义彼此隔离。** 结果分散在不同系统里（Lean、Rocq、K、WebAssembly、EVM），彼此之间无法直接组合。

## 0.1 提供什么

**来源可验证的编译。** 拿到一份源码和一个产物，任何人只用 C 编译器，就能从仓库里提交的 WebAssembly 种子重建编译器，并逐字节核对产物确实来自这份源码；
既不需要信任发布者，也不需要信任庞大的二进制工具链。

| 组成 | 内容 |
|---|---|
| 编译链 | `rsd → rscm → wasm`：前端 `rsdc` 和后端 `rsc`，附完整源码（54 个文件，以 SHA-256 钉住） |
| 种子 | `bootstrap/seed/stage-14274/`：两个编译器的 WebAssembly 形式、重建配方及其核对的全部摘要 |
| 形式语义 | 每一层（scm、λRC、wasm0）冻结的规范，以内容摘要钉住（`semantics/`、`gates/semalign/`、`lean/rsd-cert/`） |
| 性能记录 | 在固定硬件上与 Koka 及另外六种语言对比（[`perf/`](perf/README.zh-CN.md)） |
| 文档 | 安装、验证流程、架构、信任模型、术语表、稳定性策略、FAQ（`release/docs/`，中英文） |

### 本版本的验证

- 一个对项目一无所知的独立 agent，只凭文档，在全新的 Linux 虚拟机上复现了种子配方：两个编译器重建后与种子逐字节一致。
- 本版本经过两个相互独立的模型家族审查。
- 标签 `rsd-0.1` 上的仓库内容与发布的源码包逐字节一致。

## 快速开始

环境要求：Linux x86-64、GCC、GNU binutils、coreutils、Bash、curl 和 tar。不需要 Lean、Node 或 OCaml。

```sh
# 1. 从 rsd-0.1 发布页下载并核对源码包
sha256sum -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src

# 2. 在干净环境中从种子重建两个编译器（20–45 分钟）
env -i PATH=/usr/bin:/bin bash --noprofile --norc
#    然后执行 bootstrap/seed/stage-14274/README.md 中的命令
```

配方会下载钉住版本的 WABT，把两个种子执行器翻译成 C 并编译，再从源码重新编译两个编译器；只有重建结果与提交的种子逐字节一致时才返回 0。

接下来：

- [`release/docs/QUICKSTART`](release/docs/QUICKSTART)：第一次运行的详细步骤，以及如何编译一个源文件
- [`release/docs/VERIFY-RELEASE`](release/docs/VERIFY-RELEASE)：本版本的全部摘要核对
- [`release/docs/OVERVIEW.zh-CN`](release/docs/OVERVIEW.zh-CN) 和 [`release/docs/ARCHITECTURE.zh-CN`](release/docs/ARCHITECTURE.zh-CN)：0.1 是什么，各层如何衔接

## 性能

测于 GCP t2d-standard-4（两台全新虚拟机，5 次运行取中位数，固定核心）。比值 = Residua 用时 / 对方用时，小于 1 表示 Residua 更快。程序原样取自
Koka 的基准套件（Perceus 论文，PLDI 2021）和 Lean 4 的基准。

| 几何平均，Residua 0.1 / … | Koka（原生） | Koka（wasm） | C++ | OCaml | Haskell | Java | Lean 4.14 |
|---|---:|---:|---:|---:|---:|---:|---:|
| 比值 | 0.973 | 1.047 | 0.822 | 0.586 | 0.281 | 0.451 | 0.570 |

从种子自举用时 1162 秒（峰值 3.6 GiB）。逐程序的表格、空格及其原因、每个版本的历史，见 [`perf/`](perf/README.zh-CN.md)。

## 版本记录

| 版本 | 日期 | 源码包 SHA-256 | 说明 |
|---|---|---|---|
| [0.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1) | 2026-11-19 | `59d0956e…` | 首个公开版本：最小自举闭合 |

完整记录：[CHANGELOG.zh-CN.md](CHANGELOG.zh-CN.md)。

## 限制

0.1 用于可复现、可审计的编译，以及可验证、可自举编译器的研究。

- 只支持单模块程序（没有 `import`）。
- 没有 I/O 执行层。
- 不检查证明：R-CIC 内核不在本版本中，发布的 `theorem` 文本是规范，不是已检查的结论。
- 没有 `UInt64`；地址空间为 4 GiB。
- 内容标识（q）的格式尚未定稿。
- 0.1 的表面语言是严格的自举子集，拒绝 `theorem`、`axiom`、`class`、`abbrev` 和 `by`（[`release/docs/LANGUAGE`](release/docs/LANGUAGE)）。

## 路线图

版本按目标闭合的顺序编号为 0.2、0.3……，不承诺日期。

1. **检查他人的结果。** R-CIC 证明内核：在 Lean4Lean 检查过的语料上与其结论一致，并且不接受 Lean Kernel Arena 中的任何无效输入；最终的 q 格式；
   结果的发布与查询入口。
2. **编程完整性。** 模块、`UInt64`、64 位寻址、I/O 执行层、真实应用套件。
3. **低成本确认执行。** wasm0 → AIR → 零知识证明。
4. **连接外部语义。** K/KORE、Lean 和 Rocq 导入。

## 仓库结构

| 路径 | 内容 |
|---|---|
| `bootstrap/` | 提交的种子、重建配方和 C 主机桥接 |
| `rsdc/`、`rsc/`、`lib/` | 编译器源码（前端、后端、共享库和运行时） |
| `semantics/`、`gates/`、`lean/` | 冻结的形式语义和逐层翻译检查 |
| `release/` | 发布清单、来源记录、声明、许可证和文档 |
| `perf/` | 每个版本的性能记录 |

## 贡献与安全

欢迎提交 issue。安全问题请通过本仓库的 GitHub 私密漏洞报告提交，见 [`release/docs/CONTRIBUTING-SECURITY.zh-CN`](release/docs/CONTRIBUTING-SECURITY.zh-CN)。

## 致谢

Residua 建立在许多其他项目之上。[ACKNOWLEDGEMENTS.zh-CN.md](ACKNOWLEDGEMENTS.zh-CN.md) 列出了我们移植的代码、用作测试参照的工具，以及研究过的设计；
逐文件的署名见 `release/NOTICES.md` 和 `release/PROVENANCE.tsv`。如果你发现自己的工作被使用却没有致谢，请开 issue 或使用私密漏洞报告，我们会改正。

## 许可证

Apache License 2.0。见 [LICENSE](LICENSE) 和 [NOTICE](NOTICE)。
