# 更新记录

[English](CHANGELOG.md) | 中文

**版本编号。** 功能版本按目标完成的先后编号为 0.2、0.3……。已发布版本的修订版（文档、署名、打包、随包发布的测试套件；自举配方的输入不变）
编号为 0.1.1、0.1.2……。已发布的标签永不移动。每个版本列出其源码包的 SHA-256；标签上的仓库内容与源码包一致。

## [0.1] — 2026-11-19

首个公开版本：rsd 编译器的最小自举闭合。

- 编译链 `rsd → rscm → wasm`（`rsdc`、`rsc`）及其 54 个源文件；提交的 WebAssembly 种子只用 C 编译器即可从源码逐字节重建两个编译器。
- 每一层（scm、λRC、wasm0）冻结的形式语义，以内容摘要钉住。
- 在 GCP t2d-standard-4 上与 Koka 对比的性能记录；同日在 [`perf/`](perf/README.zh-CN.md) 中补充了 C++、OCaml、Haskell、Java、Swift 和 Lean 4.14 的参照列。
- 证据：一个独立 agent 只凭文档，在全新的 Linux 虚拟机上复现了不动点；本版本经过两个相互独立的模型家族审查。
- 源码包：`rsd-src.tar`，SHA-256 `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`，201 个文件。
- 发布页：https://github.com/residua-labs/Residua/releases/tag/rsd-0.1
