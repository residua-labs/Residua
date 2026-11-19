# Residua

[English](README.md) | 中文

Residua 是一套基础设施，让人无需信任对方，就能使用对方的计算或证明。一个结果按其内容的地址（q）来识别，
而不是按谁产出了它、或用哪个版本的工具链构建了它；结果只凭机械检查准入，建立在一张形式化定义的语义网络之上。

Residua 的设计是计算和证明一体：在它的语言 rsd 中，程序和证明是同一个依赖类型论中的项，同一个项既被编译成
原生代码或 WebAssembly，又由内核检查。这一点尚未端到端证实；0.1 版本交付的是编译这一半。

## 为什么

- 形式化结果的成本主要花在重复检查、上游变化后的修补、协调和审查上；内核检查本身只占一小部分。
- 结果被绑定在工具链版本上：编译好的证明库不能跨编译器版本使用，所以每次升级都要把下游全部重新构建、重新检查。
  Residua 把结果及其依赖保存为一张由内容地址构成的图：升级时只重新检查变化的部分，检查过一次的事实始终是同一个事实。
- 将来的结果大多由不可信的机器产出。能扩展到这种规模的，只有机械检查和按内容识别。
- 形式语义彼此割裂（证明助手、编程语言、虚拟机），结果无法跨越它们组合。

## 0.1 版本

0.1 是最小的自举闭合：两个 rsd 编译器（前端 `rsdc`、后端 `rsc`）提交在仓库里的 WebAssembly 种子、构建这个种子所用的 54 个源文件、
运行时、每一层的形式语义，以及文档。它以一个源码包的形式发布在
[rsd-0.1 release](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1)：

- `rsd-src.tar`，sha256 `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`，201 个文件；
- `rsd-src.tar.sha256`。

可以验证什么：在一台干净的 Linux x86-64 机器上，只用 C 编译器和常用的命令行工具（不需要 Lean、Node 或 OCaml），按
`bootstrap/seed/stage-14274/README.md` 里的配方，从源码重建两个编译器，并逐字节复现提交的种子。从 `release/docs/QUICKSTART`
开始；`release/docs/VERIFY-RELEASE` 列出了每一项哈希核对。一个事先对项目一无所知的独立 agent，只凭文档，在全新的虚拟机上复现了这个不动点。

不包括什么：证明检查器、模块和 agent 工具在后续版本。限制见 `release/docs/RELEASE-NOTES`、`TRUST`、`STABILITY` 和 `RESIDUES`；
`release/docs/PERF-RECORD` 给出在固定硬件上和 Koka 对比的实测性能。

安全问题：请使用本仓库的 GitHub 私密漏洞报告。

## 许可证

Apache License 2.0。见 LICENSE 和 NOTICE。
