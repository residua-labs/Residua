# 更新记录

[English](CHANGELOG.md) | 中文

**版本编号。** 功能版本按目标完成的先后编号为 0.2、0.3……。已发布版本的修订版（文档、署名、打包、随包发布的测试套件；自举配方的输入不变）
编号为 0.1.1、0.1.2……。已发布的标签永不移动。每个版本列出其源码包的 SHA-256；标签上的仓库内容与源码包逐字节相同。

## [0.1.2] — 2026-11-19

0.1.1 的修订版：测试与基准套件进入发布集；自举配方的输入与 0.1 逐字节相同。

- `benchmarks/`（186 个文件）：基准程序及其生成的 `.rscm` 模块、`expected/` 期望输出、Rust 参考实现、Koka 对比框架，
  以及 `benchmarks/langs/` 中移植所依据的 Koka `test/bench` 与 Lean 4.14 `test/bench` 上游源码（Koka Apache-2.0、
  Lean 4 Apache-2.0、Benchmarks Game BSD-3-Clause、Bend Apache-2.0）。
- `instruments/lrc-host/`（101 个文件）：对拍测试套件——`Diff.rsd`、Sides/Mutants 表、`Images.tsv`、`Peaks.tsv`
  及钉住的 `img/` 镜像。
- `release/docs/TESTING`（及 `.zh-CN`）：各套件的运行方式与性能记录的产生方式；`lean --run` 运行器是测试工具，
  不属于自举配方。
- 公开文档现采用与 0.1.1 文档相同样式的公开文本体例；发布门禁按内部标识符表对发布集做机械检查。
- 源码包：`rsd-src.tar`，SHA-256 见发布页，437 个文件。
- 发布：https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2

## [0.1.1] — 2026-11-19

0.1 的修订版：仅文档、署名与打包；自举配方的输入与 0.1 逐字节相同。

- 发布集移除应用树（`web/`，52 个应用文件转为仓库内文件，在
  `release/docs/LANGUAGE` 中按路径与摘要引用），并加入性能记录（`perf/`）：发布集现为
  148 个文件。
- 署名补全：声明文件为 Lean 4 移植部分逐文件收录上游原始头注释；`web/h5i` 设计增加
  6 条仓库内来源记录（上游 `9774f28a2a`，Apache-2.0）。
- 新增 `ACKNOWLEDGEMENTS.md` 与 `ACKNOWLEDGEMENTS.zh-CN.md`；README（中、英）按公开文本体例重写。
- 已发货的声明与来源记录中的内部发布者标识符已移除；发布门禁以机械方式拒绝它们，同时拒绝过期版本串与内部工具名。
- 版本编号规则更正：功能版本为 0.2、0.3……（0.11 会排在 0.10 之后）；修订版为 0.1.1、0.1.2……。已发布的 0.1 源码包不变。
- 源码包：`rsd-src.tar`（148 个文件），SHA-256 `165690af75bebf7841cbd3f14459d66b7d295aa65f2676b935eee5ee3a9b030b`。
- 发布页：https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.1

## [0.1] — 2026-11-19

首个公开版本：rsd 编译器的最小自举闭合。

- 编译链 `rsd → rscm → wasm`（`rsdc`、`rsc`）及其 54 个源文件；提交的 WebAssembly 种子只用 C 编译器即可从源码逐字节重建 `rsdc` 与 `rsc`。
- 各层（scm、λRC、wasm0）冻结的形式语义，以内容摘要钉住。
- 在 GCP t2d-standard-4 上与 Koka 对比的性能记录；同日在 [`perf/`](perf/README.zh-CN.md) 中补充了 C++、OCaml、Haskell、Java、Swift 和 Lean 4.14 的参照列。
- 证据：某独立 agent 只凭文档，在全新的 Linux 虚拟机上复现了不动点；本版本经过相互独立的模型家族审查。
- 源码包：`rsd-src.tar`，SHA-256 `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`；包内 201 个文件。
- 发布页：https://github.com/residua-labs/Residua/releases/tag/rsd-0.1
