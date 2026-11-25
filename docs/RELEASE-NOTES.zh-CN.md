# RELEASE-NOTES — Residua 0.4

[English](RELEASE-NOTES.md) | 中文

0.4 版本保留自举闭合——仅用 C 编译器即可从提交的 WebAssembly
[seed](GLOSSARY.zh-CN.md) 逐字节重建可验证来源的编译器——并加入多模块
`.rsd` 程序、IEEE-754 `Float`（`binary64`）、`Proc` `do` 记法与 C11 +
Wasmtime 的 `procwt` 执行宿主、标准 `Proc` 库（`glue/std/`）、多模块
命令行示例 `examples/app04`、体积更小且速度更快的重切 seed、Apache-2.0
平衡映射表（`lib/AvlMap.rsd`），以及 `lean/nf-compose/` 中的多跳与递归
复合定理。MST-NF 是 Residua 的基础理论：它在公共仓库
[github.com/residua-labs/MST-NF](https://github.com/residua-labs/MST-NF)
钉住提交 `4432a34`，证明由该仓持有。

## 0.4 新增

- **模块、`Proc` `do` 记法与 `procwt` 执行宿主。** 多模块 `.rsd` 程序通过
  `import` 组合 `lib/`、`glue/std/` 与应用模块，以 `do { let x <- … }`
  串联效应，并以 WebAssembly 形态运行在 C11 + Wasmtime 宿主
  `glue/host/procwt.c`（`glue/host/proc9core.h`；wasm2c 对应宿主为
  `glue/host/proc9.c`）上。`glue/std/` 随附 `Args`、`Files`、`Graph`、
  `Json`、`Map`、`Proc` 与 `Str`；`lib/ProcBytes.rsd` 与 `lib/Proc9.rsd`
  随附字节切片与 9P2000 编解码；`glue/rsd/main.rsd` 与
  `glue/rsd/build.rsd` 将 `rsd run` 接入 `procwt`。
- **IEEE-754 `Float`（`binary64`）。** 贯通 `rsdc`、`.rscm` 线格式
  （`docs/EMITTER.md`）、`lambda-RC` 与 WebAssembly 发射，保留 `NaN`、
  `±Infinity` 与 `-0.0`，并在 `instruments/lrc-host/` 下随附差分预言机与
  变异测试套件。
- **多模块命令行示例（`examples/app04/`）。** `Stats.rsd`、`Table.rsd` 与
  `Main.rsd` 读取按行分隔的浮点数文件，计算 `count`、`min`、`max`、`mean`
  与总体 `variance`，用 `String` 排版对齐的 ASCII 表格并写出文件，在格式
  错误或 I/O 错误时以非零退出码诊断——全部 `16` 个差分输入与原版 Lean
  `4.14.0` 完全一致。
- **更小更快的重切 seed（`bootstrap/seed/stage-14274/`）。** `rsdc.wasm`
  从 0.3 的 `19.9 MB` 降至 `12,519,278` B（`845b99ef…`，入口 `f896`，
  `__heap_base` `765288`），`rsc.wasm` 从 `20.5 MB` 降至 `14,275,644` B
  （`b52b07d1…`，入口 `f2615`，构造字 `14274`，`__heap_base` `603704`）。
  `seed-host.c` 读取加载模块导出的 `__heap_base` 全局量并支持
  `\0RSDC-ENTRIES\n`。干净环境重建编译器在 Linux x86-64 上耗时 `105 s`
  （全配方 `193 s`），在 macOS arm64 上耗时 `191 s`（全配方 `337 s`）。
- **Apache-2.0 平衡映射表（`lib/AvlMap.rsd`）。** 从 Lean `v4.36.0`
  （`Std/Data/DTreeMap/Internal/Def.lean` 与 `Balancing.lean`）重新移植，
  取代 0.3 中源于 OCaml `stdlib/map.ml` 的移植，使全部随附编译器与库源码
  均采用宽松许可证。
- **多跳与递归 MST-NF 复合定理（`lean/nf-compose/`）。**
  `NfCompose/HopCompose.lean` 证出跨编译跳复合，
  `NfCompose/Rec.lean` 与 `NfRec/CheckedStatus.lean` 在钉住的 `ExecModel`
  上证出有界与良基递归复合。

## 0.4 的 MST-NF 状态

每个随附组件要么已绑定到钉住的 `ExecModel`
（`lean/nf-compose/pinned/MSTNecessityExecModelMWE.lean`）并证出 Tier-1
定律，要么记录为缺口。

| 随附组件 | 状态 |
|---|---|
| 编译器链（`rsdc`、`rsc`） | 缺口——逐跳 `ExecModel` 实例在仓库侧；多跳复合已证（`HopCompose.lean`） |
| 执行层（`semantics/Effect/`、`glue/host/`） | 实例已随附：`monitorModel`、`exec9AdmissionModel`；Tier-1 定律已证（`AdmissionNF.lean`） |
| 语法引擎（`rsdc/profiles/`、`semantics/Syntax/`） | 缺口——尚无随附 `ExecModel` 实例 |
| QFormat（`docs/QFORMAT.zh-CN.md`、`release/checks/qformat/`） | 缺口——尚无随附 `ExecModel` 实例 |
| `rsd` 构建工具（`rsd/`、`glue/rsd/`、`lib/rsd/`） | 缺口——尚无随附 `ExecModel` 实例 |
| NF 复合（`lean/nf-compose/`） | 框架已随附：积/和/序列/分派、多跳（`HopCompose.lean`）与递归（`Rec.lean`）复合已证 |

## 本归档内容

- 提交的 `rsdc`/`rsc` wasm 种子及其 `54` 成员源码闭包
  （`bootstrap/seed/stage-14274/`），附重建配方
- rsd 编译链 `rsd -> rscm -> wasm`（`docs/RSD-COMMAND.md`）
- `Proc` 执行宿主（`glue/host/`）、标准 `Proc` 模块
  （`lib/ProcBytes.rsd`、`lib/Proc9.rsd`、`glue/std/`）及多模块命令行程序
  `examples/app04/`
- `rsd` 构建工具（`rsd/`、`glue/rsd/`、`lib/rsd/`、`lib/Rsd.rsd`）
- 按内容摘要钉住的各编译层冻结形式语义（scm、lambda-RC、wasm0），以及
  `semantics/Syntax/` 与 `semantics/Effect/`
- MST-NF 复合包（`lean/nf-compose/`，含 `HopCompose.lean`、`Rec.lean` 与
  `NfRec/CheckedStatus.lean`）及其审计报告（`reports/nf-compose/REPORT.md`）
- 基准、差分与性能套件（`benchmarks/`、`instruments/lrc-host/`、`perf/`）
- 语言一致性语料（`docs/LANGUAGE.md`）与性能记录
  （`docs/PERF-RECORD.tsv`、`docs/PERF-RECORD.md`）
- 英文文档，以及 `README`、`CHANGELOG` 与成对 `docs/` 页面的中文
  `.zh-CN.md` 镜像
- 发布说明（`release/notes/`）、可运行一致性检查（`release/checks/`）、
  面向读者的 `release/GAPS.tsv`、溯源表（`release/PROVENANCE.tsv`）、
  第三方声明（`release/NOTICES.md`、`NOTICE`）与 vendored 许可证文本
  （`release/licenses/`）

## 验证

`docs/VERIFY-RELEASE.md` 为验证协议：核对种子摘要与归档摘要，在干净的
Linux x86-64 或 macOS arm64 环境中运行种子配方并核对重建编译器与提交种子
逐字节一致（`cmp` 核对 `rsdc.wasm` 与 `rsc.wasm` 并校验
`REBUILT-SHA256SUMS`），最后编译并在 `procwt` 上运行 `examples/app04`。

## 0.4 的既定限制

独立 `.rmod` 编译尚未覆盖 `Float` 及逐模块 `Proc` `do` 反糖化
（`release/GAPS.tsv`；多模块构建按拓扑序拼接源码模块）；`procwt` 通过进程内
9P2000 响应器提供命令行参数、时钟与本地文件 I/O（`release/GAPS.tsv` `G01`），
不含网络与子进程派生；`rsd` 原生编译工作器闭包的一部分留在仓库侧
（`release/GAPS.tsv` `G06`）；无证明检查（R-CIC 内核不在本版）；`4 GiB`
WebAssembly 线性内存地址空间；无结果发布/查询入口。自举 `.rsd` 文法拒绝
`theorem`、`axiom`、`class`、`abbrev`、`variable`、`opaque` 与 `by`。

## 0.4 之后

1. R-CIC 内核与结果的发布/查询入口——供外部读者查找、检查并复用他人结果。
2. 覆盖完整语言的独立 `.rmod` 编译、64 位寻址、更广的宿主能力与应用套件。
3. 执行的廉价确认：wasm0 -> AIR -> zk。
4. 外部语义连接器（K/KORE、Lean/Rocq 导入）。
