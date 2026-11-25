# 更新日志

[English](CHANGELOG.md) | 中文

本项目所有重要变更记录于此。格式遵循
[Keep a Changelog](https://keepachangelog.com/zh-CN/1.1.0/)。特性版本按目标完成顺序编号
0.2、0.3、…；对已发布版本的补丁版本（文档、署名、打包、随附测试套件；自举配方的输入不变）编号
0.x.y。已发布的 tag 永不移动。每个版本列出其源码归档的 SHA-256；tag 处的仓库树与归档一致。

## [0.4] — 2026-11-25

### 新增

- `examples/app04/`（`examples/app04/Stats.rsd`、`examples/app04/Table.rsd`、
  `examples/app04/Main.rsd`）：多模块命令行程序，读取按行分隔的浮点数文件，
  用 `Float`（`binary64`）计算 `count`、`min`、`max`、`mean` 与总体
  `variance`，用 `String` 排版对齐的 ASCII 表格并写出文件，在行格式错误或
  I/O 错误时打印诊断并以非零码退出。
- `glue/host/`（`glue/host/procwt.c`、`glue/host/proc9core.h`、
  `glue/host/proc9.c`）：面向 WebAssembly（Wasmtime C API v50.0.1，读取导出
  的 `__heap_base` 并自动探测 `driveS`）与 wasm2c 的 C11 `Proc` 执行宿主，
  内置进程内 9P2000 响应器，提供 `/env/args`、`/dev/time`、`/dev/mono` 及
  宿主文件读写。
- `glue/std/`（`glue/std/Args.rsd`、`glue/std/Files.rsd`、
  `glue/std/Graph.rsd`、`glue/std/Json.rsd`、`glue/std/Map.rsd`、
  `glue/std/Proc.rsd`、`glue/std/Str.rsd`）及 `lib/ProcBytes.rsd`、
  `lib/Proc9.rsd`：命令行参数、分块文件 I/O、字符串、JSON、映射表、图、
  字节切片与 9P2000 帧的标准 `Proc` 模块。
- `glue/rsd/`（`glue/rsd/main.rsd`、`glue/rsd/build.rsd`）：`rsd run`
  入口与构建脚本，将含 `import` 的 `Proc` 程序接入 `procwt` 与
  `wasm-opt --translate-to-exnref`。
- `lean/nf-compose/NfCompose/HopCompose.lean`、
  `lean/nf-compose/NfCompose/Rec.lean` 与
  `lean/nf-compose/NfRec/CheckedStatus.lean`：钉住 `ExecModel` 上的多跳
  编译复合与有界/良基递归复合定理。
- `instruments/lrc-host/CheckFloat64.rsd`、
  `instruments/lrc-host/Float64Oracle.rsd`、
  `instruments/lrc-host/Wasm2CHost.c`、
  `instruments/lrc-host/MutantsBound.tsv`、
  `instruments/lrc-host/MutantsExcl.tsv`、
  `instruments/lrc-host/MutantsF64.tsv`、
  `instruments/lrc-host/MutantsFlow.tsv`、
  `instruments/lrc-host/MutantsKBox.tsv`、
  `instruments/lrc-host/MutantsLit.tsv`、
  `instruments/lrc-host/MutantsLoops.tsv`、
  `instruments/lrc-host/ProgArrFlow.rsd`、
  `instruments/lrc-host/ProgBound.rsd`、
  `instruments/lrc-host/ProgKBox.rsd`、
  `instruments/lrc-host/ProgLitCall.rsd`、
  `instruments/lrc-host/ProgLitWord.rsd`、
  `instruments/lrc-host/ProgNumTail.rsd` 与
  `instruments/lrc-host/ProgPad.rsd`：IEEE-754 `Float`（`binary64`）差分
  预言机、wasm2c 宿主及编译器变异与回归测试输入。

### 变更

- 在 `bootstrap/seed/stage-14274/` 重切 seed 并更新 `bootstrap/README.md`：
  以 `rsdc.wasm`（`12,519,278` B，`845b99ef…`，入口 `f896`，`__heap_base`
  `765288`）与 `rsc.wasm`（`14,275,644` B，`b52b07d1…`，入口 `f2615`，构造字
  `14274`，`__heap_base` `603704`）取代 0.3 的 seed 文件（`19.9 MB` /
  `20.5 MB`）；`seed-host.c` 读取加载模块导出的 `__heap_base` 全局量并支持
  `\0RSDC-ENTRIES\n` 查询头；干净环境重建在 Linux x86-64 上耗时 `105 s`，
  在 macOS arm64 上耗时 `191 s`。
- `rsdc/`、`rsc/`、`lib/`、`lib/lrc/`、`docs/EMITTER.md`、`semantics/`、
  `lean/rsd-cert/Residua/Bootstrap/R2/` 与 `instruments/lrc-host/`：加入
  IEEE-754 `Float`（`binary64`）、多模块 `import` 支持、`Proc` `do` 记法、
  `\0RSDC-ENTRIES\n` 入口查询，并更新数组、构造子布局与引用计数各 pass。
- `lib/AvlMap.rsd`：以 Lean `v4.36.0` 权重平衡树
  （`Std/Data/DTreeMap/Internal/Def.lean` 与 `Balancing.lean`）的 Apache-2.0
  移植取代 0.3 中源于 OCaml `stdlib/map.ml` 的移植。
- `rsd/`、`lib/rsd/` 与 `benchmarks/MANIFEST.tsv`：按 0.4 树更新构建工具
  模块与基准清单元数据。
- `lean/nf-compose/NfCompose/Hop.lean` 与
  `lean/nf-compose/lakefile.lean`：一跳的接纳现在还要求翻译出的程序在目标侧
  也可接纳；包里构建新增的模块。
- `gates/semalign/METHOD.md`、`reports/nf-compose/REPORT.md`、
  `benchmarks/koka/README.md` 与 `benchmarks/koka/README.zh-CN.md`：更正代码
  片段的标记与一处命令行，含义不变。
- `README.md`、`README.zh-CN.md`、`CHANGELOG.md`、`CHANGELOG.zh-CN.md`、
  `docs/`、`NOTICE` 与 `release/`：更新
  快速开始（从 seed 构建并运行 `examples/app04`）、`docs/BUILD.md` 与
  `.zh-CN.md`、`docs/VERIFY-RELEASE.md`、`docs/SPECS.md`、`docs/LANGUAGE.md`、
  `docs/STDLIB.md`、`docs/OVERVIEW.md` 与 `.zh-CN.md`、
  `docs/RELEASE-NOTES.md` 与 `.zh-CN.md`、`release/GAPS.tsv`、
  `release/SHIP-RULES.tsv`、`release/PROVENANCE.tsv`、`release/NOTICES.md`、
  `release/BUILD-INPUTS.tsv`、`release/MANIFEST.md` 与
  `release/PRIOR-SHIP-SETS.tsv`。

### 移除

- 无（0.3 随附的全部路径在 0.4 中均保留）。

## [0.3] — 2026-11-24

### 新增

- `rsd` 构建工具：`rsd build`、`rsd test`、`rsd run`、`rsd cache`
  （调度器与编译 worker 在 `rsd/`；存储、依赖图与会话层在 `lib/rsd/`、`lib/Rsd.rsd`；
  用户文档 `docs/BUILD.zh-CN.md`；植入行一致性检查 `release/checks/rsd-tool/`）。
  随附的是源码；`lib/laws/RsdScheduleLaws.rsd` 随附 `lib/rsd/schedule.rsd` 的
  调度定律。构建该工具本身需要开发仓库——本归档内可运行的编译器是
  seed 配方。
- 语言新增 `UInt64` 支持（编译器源码已使用它）。
- 恢复 0.1.1/0.1.2 归档随附而 0.2 丢弃的套件：
  `benchmarks/`、`instruments/lrc-host/`、`perf/`、
  `ACKNOWLEDGEMENTS.md` 与 `.zh-CN.md`、`lib/lrc/Closures.rsd`，以及 TESTING 指南
  （`TESTING.md` 与 `.zh-CN.md`）。
- `benchmarks/koka/entries.tsv`、`benchmarks/koka/images.tsv` 与
  `benchmarks/koka/modules.tsv`：narrow 表输入与按模块/按镜像的摘要，
  在 0.3 seed 上测得。
- `instruments/lrc-host/ProgWrap.rsd`（其发射的
  `instruments/lrc-host/img/progwrap.rscm` 像文件与其他生成像一样
  留在仓库侧）。
- `examples/surfaces/` 与 `docs/surfaces/`：五个程序各以 `.rsd`、
  `.rsj`、`.rsm` 三种表面写法打印，附往返检查验证三者解析到
  同一棵树。
- Lean 4.14 的 MST-NF 复合定理（`lean/nf-compose/`）：针对钉住的
  必然执行模型的复合规则，在发布工具链上构建并检查，独立审计通过
  （审计报告 `reports/nf-compose/REPORT.md` 随附）。MST-NF 是
  Residua 的基础理论：它在公共仓库
  [github.com/residua-labs/MST-NF](https://github.com/residua-labs/MST-NF)
  钉住提交 `4432a34`，证明由该仓持有。
- `semantics/Effect/AdmissionNF.lean`：执行层的带类型 `ExecModel`
  实例（`monitorModel`、`exec9AdmissionModel`），四条 Tier-1 定律
  已证——首批随附的带类型实例（0.1 与 0.2 没有；其 `Monitor.lean`
  引用的是三形式编码，并非定义）。回执：
  `reports/effect-sem/ADMISSION-NF.md`。
- `release/TERMS.tsv`：公开文本的用词策略（哪些内部词移除、哪些真实术语入词汇表），
  由门禁检查。
- 社区文件：`CONTRIBUTING.md`、`CODE_OF_CONDUCT.md`（Contributor Covenant 2.1）、
  `SECURITY.md`、`.github/` 下的 issue 与 PR 模板。
- `release/notes/` 下的按特性说明，中英双语。
- 门禁新增检查：任何更早已发布版本随附的路径不得被静默丢弃，除非 CHANGELOG 有
  一行声明该丢弃（`release/PRIOR-SHIP-SETS.tsv`）。

### 变更

- 公开文档面向外部读者重写：`README.md` 按开源社区常规顺序重写，
  `docs/` 按 Diátaxis 分类组织并附索引，发布说明改为白话，
  学术性文本移至 `docs/OVERVIEW.md`。
- `docs/GLOSSARY.md` 与 `.zh-CN.md`：按 0.3 新术语扩写。
- `semantics/Rsx/Lower.rsd`：充分性命题 `AdeqApp`、
  `AdeqLetE`、`AdeqConst`、`AdeqConstDelta` 与 `adequacyClosed` 增加了
  `EnvClosed` 假设，并补充了无该假设形式的反驳
  （`not_adeqApp`、`not_adeqLetE`、`not_adeqConstDelta`）。
- `rsdc/profiles/rsd.syn`、`rsj.syn`、`rsm.syn` 与 `rsv.syn`：文法
  新增 `syntax_124_max`/`imax`、`syntax_162_tactic`、`syntax_217`、
  `syntax_327`、`syntax_415`、`syntax_518` 与 `syntax_565_*`
  产生式族（`rsm.syn` 为表层记号，`rsd.syn` 为对应的词法单元
  与规则）。
- 新 seed cut：提交的 seed 在本头重建并携带当前编译器源码（含 `UInt64`）；
  自本次 cut 起 wasm 路线默认以 `narrow` 层编译，原生路线保持 64 位。
- 自举配方改为经 C 宿主 `bootstrap/seed/stage-14274/seed-host.c` 在钉住的
  wasmtime C API（v50.0.1）上以 Wasm 形态运行 seed，并以
  `wasm-opt --translate-to-exnref`（binaryen version_133）重编码
  seed 的遗留异常指令；wasm2c 转译与对 seed 的 C 优化器移除，
  配方在 Linux x86-64 与 macOS arm64 上运行。
- `CHANGELOG` 改为 Keep a Changelog 格式。

### 移除

- `bootstrap/seed/stage-14274/ASSEMBLY.tsv` —— 重切不再
  产出该文件；成员绑定改为按 `sources/rsdc.rsd` 与 `sources/rsc.rsd`
  内的 `RscSourceModule_<sha256>` 段标记核验。
- `release/FINDINGS.tsv` —— 发布检查导出的表，留在开发仓库。
- `bootstrap/seed/stage-14274/WABT-MACOS-ARM64-SHA256SUMS` —— 已被取代；
  新的 wasm 运行时配方在 Linux x86-64 与 macOS arm64 上运行，无需
  WABT 工具链。
- 生成物与二进制文件不再随源码归档发布（本版仅随附
  重切的一对 seed 文件；其余由用户构建或生成）。以下
  各路径在所注早前版本中曾随附：
  - `benchmarks/bfs.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/bfs.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/binarytrees.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/binarytrees.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/cfold.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/cfold.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/deriv.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/deriv.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/editdist.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/editdist.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/fannkuch.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/fannkuch.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/gameoflife.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/gameoflife.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/hashmap.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/hashmap.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/histogram.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/histogram.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/lexer.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/lexer.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/merkle.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/merkle.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/nqueens.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/nqueens.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/pidigits.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/pidigits.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/queens.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/queens.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/rbtree.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/rbtree.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/rbtreeck.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/rbtreeck.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/symreg.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/symreg.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/terrain.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/terrain.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/treebitonic.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/treebitonic.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/treematmul.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/treematmul.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `benchmarks/treeradix.rscm`（0.1.2）—— 发射模块（生成物）；.rsd 源随附。
  - `benchmarks/treeradix.rscm.meta`（0.1.2）—— 发射模块的生成副档。
  - `bootstrap/ProcWasm2CHost.c`（0.1/0.1.1/0.1.2/0.2）—— wasm2c C 宿主；seed 现经 stage-14274/seed-host.c 在钉住 wasmtime 上运行。
  - `bootstrap/seed/manifest.json`（0.1/0.1.1/0.1.2/0.2）—— 被取代的 seed 清单；stage-14274/CUT.tsv 为 cut 记录。
  - `bootstrap/seed/rsc.rscm`（0.1/0.1.1/0.1.2/0.2）—— 发射模块（生成物）；.rsd 源随附。
  - `bootstrap/seed/rsc.wasm`（0.1/0.1.1/0.1.2/0.2）—— 被取代的钉住 seed 块；重切的一对是唯一 seed。
  - `bootstrap/seed/rsdc.wasm`（0.1/0.1.1/0.1.2/0.2）—— 被取代的钉住 seed 块；重切的一对是唯一 seed。
  - `bootstrap/seed/stage-14274/EXECUTOR-SHA256SUMS`（0.1/0.1.1/0.1.2/0.2）—— wasm2c 路线钉文件；为内部检查工具保留于仓库侧。
  - `bootstrap/seed/stage-14274/WABT-RUNTIME-SHA256SUMS`（0.1/0.1.1/0.1.2/0.2）—— wasm2c 路线钉文件；为内部检查工具保留于仓库侧。
  - `bootstrap/seed/stage-14274/WABT-SHA256SUMS`（0.1/0.1.1/0.1.2/0.2）—— wasm2c 路线钉文件；为内部检查工具保留于仓库侧。
  - `bootstrap/sources.json`（0.1/0.1.1/0.1.2/0.2）—— 被取代的 seed 元数据。
  - `bootstrap/Wasm2CHost.c`（0.1/0.1.1/0.1.2/0.2）—— wasm2c C 宿主；seed 现经 stage-14274/seed-host.c 在钉住 wasmtime 上运行。
  - `instruments/lrc-host/img/binarytrees.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/binarytreeskk.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/cfold.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/deriv.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/litlong.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/nqueens.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/nqueenskk.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progarr.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progbtkoka.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progclosed.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progconv.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progeq.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progeq2.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progeq2x.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/proghead.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/proginl.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progkinds.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progloops.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progmag.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progmap.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progmap2.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/prognarrow.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/prognum.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/prognumeral.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/prognumind.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/prognumxlen.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/prognumxnum.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/prognumxtag.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progorder.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progpack.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progtest.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/progwidth.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/rbtree.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/rbtreeck.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/treebitonic.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `instruments/lrc-host/img/treematmul.rscm`（0.1.2）—— 钉住的像文件（生成物）；按其 Prog 源重新发射——见 TESTING。
  - `release/checks/qformat/vectors/crafted.bin`（0.2）—— 生成的一致性向量；检查 README 给出生成命令。
  - `release/checks/qformat/vectors/hello.bin`（0.2）—— 生成的一致性向量；检查 README 给出生成命令。
  - `release/checks/qformat/vectors/nf1.bin`（0.2）—— 生成的一致性向量；检查 README 给出生成命令。
  - `release/checks/qformat/vectors/one.bin`（0.2）—— 生成的一致性向量；检查 README 给出生成命令。
  - `reports/codex4-assign5-stage-word/Wasm2CHost.c`（0.1/0.1.1/0.1.2/0.2）—— wasm2c C 宿主；seed 现经 stage-14274/seed-host.c 在钉住 wasmtime 上运行。

### 修复

- 0.2 归档静默丢弃了 0.1.1/0.1.2 随附的套件；0.3 已恢复（见"新增"），
  新门禁检查防止今后再次发生。

#### 0.3 的 MST-NF 状态

每个随附组件要么已绑定到钉住的 `ExecModel` 并证出四条 Tier-1 定律，
要么记录为缺口。

| 随附组件 | 状态 |
|---|---|
| 编译器链（`rsdc`、`rsc`） | 缺口——尚无 `ExecModel` 实例 |
| 执行层（`semantics/Effect/`） | 实例已随附：`monitorModel`、`exec9AdmissionModel`；Tier-1 定律已证（`AdmissionNF.lean`） |
| 语法引擎 | 缺口——尚无 `ExecModel` 实例 |
| QFormat | 缺口——尚无 `ExecModel` 实例 |
| `rsd` 构建工具 | 缺口——尚无 `ExecModel` 实例 |
| NF 复合（`lean/nf-compose/`） | 框架已随附：钉住模型上的复合定理，经独立审计 |

## [0.2] — 2026-11-20

### 新增

- 带类型的内容地址（q 格式 v1）：`q(kind, c) =
  SHA-256("<kind> <len>\0" ++ c)`，打印为 `sha256:<hex>`；裸 SHA-256 保留为
  `digest`，仅用于文件完整性与互操作。（[`docs/QFORMAT.zh-CN.md`](docs/QFORMAT.zh-CN.md)，
  检查 [`release/checks/qformat/`](release/checks/qformat/)）。
- 在其文法类上闭合的语法引擎：文法数据上的一个函数，与机械验证的参考判定器
  核对一致（`semantics/Syntax/`；源码 `rsdc/syntax/`；轮廓 `rsdc/profiles/*.syn`）。
- 执行边界语义：线格式、准入与封签判断、一致性分类器与录制的传输会话，
  以 Lean 4.14 命题表述（`semantics/Effect/`）。
- 自举配方新增 macOS arm64 宿主（Apple clang、`PATH=/usr/bin:/bin`、无 Lean），
  两台 Darwin 宿主逐字节复现。
- 用户文档从 `release/docs/` 移到 `docs/`（Markdown，中英双语）。
- 归档：`rsd-src.tar`，SHA-256
  `151bfd4f6a910e9c4232e84b6cf6cfd7618a1009e5c32d41acd995b9b0d5b8fb`，212 文件。

### 变更

- seed 成员保持 0.1 字节（未重切）；五个声明过的增量豁免——seed README 配方、
  `ASSEMBLY.tsv`、`CUT.tsv`、macOS WABT 钉、`bootstrap/Wasm2CHost.c`。

## [0.1.2] — 2026-11-19

### 新增

- `benchmarks/`（186 文件）：基准程序及其发射的 `.rscm` 模块、`expected/` 输出、
  Rust 参考实现、Koka 对照框架，以及 `benchmarks/langs/`（移植所依据的
  Koka `test/bench` 与 Lean `4.14` `test/bench` 厂商源快照；Koka Apache-2.0、
  Lean 4 Apache-2.0、Benchmarks Game BSD-3-Clause、Bend Apache-2.0）。
- `instruments/lrc-host/`（101 文件）：差分测试套件——`Diff.rsd`、
  Sides/Mutants 表、`Images.tsv`、`Peaks.tsv` 与钉住的 `img/` 镜像。
- TESTING 指南（现 `TESTING.md` 与 `TESTING.zh-CN.md`）。

### 变更

- 公开文档遵循 0.1.1 文档的发布文体；发布门禁对照内部标识符表
  机械检查随附集。
- 归档：`rsd-src.tar`，SHA-256
  `a3185221854ccbf61642d65e88cc37102235ed06474dbd542a83a3eae0577a47`，437 文件。

## [0.1.1] — 2026-11-19

### 新增

- `ACKNOWLEDGEMENTS.md` 与 `ACKNOWLEDGEMENTS.zh-CN.md`；两份 README
  按发布文体重写。
- `perf/`：逐版本性能记录移入归档。

### 变更

- 署名补全：Lean 4 移植部分的逐文件 verbatim 上游头，以及 `web/h5i` 设计
  在上游 `9774f28a2a`（Apache-2.0）的 6 条仓库侧溯源行。
- 内部发布者标识符从随附声明与溯源中移除；发布门禁机械拒绝它们。
- 归档：`rsd-src.tar`，SHA-256
  `165690af75bebf7841cbd3f14459d66b7d295aa65f2676b935eee5ee3a9b030b`，148 文件。

### 移除

- `web/` 应用树（52 文件）：转为仓库侧，在 `docs/LANGUAGE.md` 中按路径与
  摘要引用。随附集变为 148 文件。

### 修复

- 版本编号修正：特性版本为 0.2、0.3、…（0.11 会排在 0.10 之后）；
  补丁版本为 0.1.1、0.1.2、…。

## [0.1] — 2026-11-19

### 新增

- 首个公开版本：rsd 编译器的最小自举闭包——`rsd → rscm → wasm`
  （`rsdc`、`rsc`）及其 54 个源文件，加上提交的 WebAssembly seed，
  仅用 C 编译器即可从源码逐字节重建两个编译器。
- 各层冻结的形式语义（scm、λRC、wasm0），按内容摘要钉住。
- 在 GCP t2d-standard-4 上对 Koka 的性能记录；C++、OCaml、Haskell、
  Java、Swift、Lean 4.14 参考列。
- 证据：[不动点](docs/GLOSSARY.zh-CN.md)由无先验知识的独立 agent 仅凭文档在新装 Linux 虚拟机上
  复现；发布经两个独立模型族评审。
- 归档：`rsd-src.tar`，SHA-256
  `59d0956e3bbaed0ddf176b9bc3ffa0e9fdb401acb1e021400f0e8b99ce110ef1`，201 文件。

[0.4]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.4
[0.3]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.3
[0.2]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.2
[0.1.2]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2
[0.1.1]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.1
[0.1]: https://github.com/residua-labs/Residua/releases/tag/rsd-0.1
