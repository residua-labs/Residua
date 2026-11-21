# 更新记录

[English](CHANGELOG.md) | 中文

**版本编号。** 功能版本按目标完成的先后编号为 0.2、0.3……。已发布版本的修订版（文档、署名、打包、随包发布的测试套件；自举配方的输入不变）
编号为 0.1.1、0.1.2……。已发布的标签永不移动。每个版本列出其源码包的 SHA-256；标签上的仓库内容与源码包一致。

## [0.2] — 2026-11-20

功能版本：0.1 的自举闭合，加上此后闭合的三个目标。

- **带类型的内容地址（q 格式 v1）。** 每个内容身份把类别写进被哈希的字节：
  `q(kind, c) = SHA-256("<kind> <len>\0" ++ c)`，打印为 `sha256:<hex>`；原始 SHA-256 保留为 `digest`，
  仅用于文件完整性与互操作。跨类别的地址碰撞不再可能发生。规范与类别注册表：
  [`docs/QFORMAT.zh-CN.md`](docs/QFORMAT.zh-CN.md)；一致性检查：
  [`release/checks/qformat/`](release/checks/qformat/)；版本说明：
  [`release/notes/qformat-1.zh-CN.md`](release/notes/qformat-1.zh-CN.md)。
- **在其文法类上闭合的语法引擎。** 解析器是对文法数据的一个函数；在自类生成的文法上，其判定
  与树和经机器检查的参照判定器相等（`semantics/Syntax/`），并以埋入的变异体作对照。引擎源
  `rsdc/syntax/`；表面 profile 作为数据发货（`rsdc/profiles/*.syn`）；版本说明：
  [`release/notes/syntax-engine.zh-CN.md`](release/notes/syntax-engine.zh-CN.md)。
- **执行边界语义 E0–E4。** 线格式、准入与封签判断、一致性分类器与录制的传输会话，以
  Lean 4.14 陈述书写（`semantics/Effect/`）；验收证据 `reports/effect-sem/`（仓库侧）；
  版本说明：[`release/notes/effect-sem.zh-CN.md`](release/notes/effect-sem.zh-CN.md)。
- **文档。** 用户文档从 `release/` 移到 `docs/` 并作 Markdown（中文版为 `.zh-CN.md`）。
- 种子成员保持 0.1 的字节（未重新切割）；五个已声明的 0.2 增量豁免——种子 README 配方、
  `ASSEMBLY.tsv`、`CUT.tsv`、macOS WABT 钉与 `bootstrap/Wasm2CHost.c`；
  q 格式 v1 不改变发射出的字节。
- 自举配方新增 macOS arm64 宿主（Apple clang、`PATH=/usr/bin:/bin`、无 Lean），
  在两台 Darwin 宿主上逐字节复现。

## [0.1] — 2026-11-19

首个公开版本：rsd 编译器的最小自举闭合。

- 编译链 `rsd → rscm → wasm`（`rsdc`、`rsc`）及其 54 个源文件；提交的 WebAssembly 种子只用 C 编译器即可从源码逐字节重建两个编译器。
- 每一层（scm、λRC、wasm0）冻结的形式语义，以内容摘要钉住。
- 在 GCP t2d-standard-4 上与 Koka 对比的性能记录；同日在 `perf/`（仓库侧） 中补充了 C++、OCaml、Haskell、Java、Swift 和 Lean 4.14 的参照列。
- 证据：一个独立 agent 只凭文档，在全新的 Linux 虚拟机上复现了不动点；本版本经过两个相互独立的模型家族审查。
- 源码包：`rsd-src.tar`，SHA-256 `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`，201 个文件。
- 发布页：https://github.com/residua-labs/Residua/releases/tag/rsd-0.1
