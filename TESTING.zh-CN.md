# TESTING — 随归档发货的测试与基准套件

[English](TESTING.md) | 中文

本归档发货 3 个套件：`benchmarks/`（本版本性能记录与正确性语料
背后的程序）、`instruments/lrc-host/`（移植编译遍做差分检查所用的
测试套件）与 `examples/surfaces/`（三表面往返检查）。
都不属于自举配方：配方只含[种子](docs/GLOSSARY.zh-CN.md)目录及其 C 宿主桥
（`docs/INSTALL.md`、`docs/VERIFY-RELEASE.md`）。

## benchmarks/ — 性能与正确性语料

内容：各 `.rsd` 基准程序（其发射的 `.rscm` 模块为仓库侧文件——
用下述链以 `rsdc <程序>.rsd` 重新发射）、
`benchmarks/MANIFEST.tsv`（逐程序来源与复核声明）、
`benchmarks/expected/`（逐字节期望输出）、`benchmarks/rust/`（对比引用的
Rust 参照移植）、`benchmarks/koka/`（Koka 对比工具，含 `timecell.c`），以及
`benchmarks/langs/`（移植所本的上游套件快照：Koka `test/bench` 与
Lean 4.14 test/bench 程序）。

用发货链跑单个程序：以 `rsdc` 编译其 `.rsd`，以 `rsc` 下降 `.rscm`，
在 wasm 运行时上执行——与种子自身程序相同的
`docs/RSD-COMMAND.md` 接口。输出与
`benchmarks/expected/<name>.txt` 逐字节比对；MANIFEST 行给出各程序核
查所用输入及状态词表（`rsd:equal`、`rscm:compiled_equal`、已命名
拒绝）。

工具链：rsd 链只需 C 编译器与已提交种子（同 QUICKSTART）。对比列为
可选外部项：Rust 参照需 `rustc`（记录用的是 1.99.1），Koka 工具需
C 编译器构建 `timecell.c` 及 Koka 工具链重建的 `.kk` 端。
`benchmarks/langs/` 下上游文件是为 provenance 保留的源码快照；重建
它们需要各自工具链，不属于这里的任何检查。

## instruments/lrc-host/ — 差分测试套件

内容：`Diff.rsd`（检查驱动）、`Images.tsv`（钉住的前端映像及其值）、
`Sides.rsd`/`SidesMutants.tsv` 与 `Mutants*.tsv` 各表（变异行）、
`Peaks.tsv`、`img/`（钉住的映像文件），以及映像所出的 `Prog*` 等
辅助 `.rsd` 程序。

以 `lean --run` 运行——`lean-toolchain` 钉住的 Lean 4.14.0 工具链。
这里 `lean --run` 是测试工具：发布配方中没有任何环节需要 Lean。

- `lean --run instruments/lrc-host/Diff.rsd`——全部检查：`lib/lrc/`
  中每个移植遍与其引用的 Lean 4.14.0 原版遍（oracle）做差分；退出
  码 0 即无差异。
- `lean --run instruments/lrc-host/Diff.rsd quick`——同上，映像检查
  取短式。
- `lean --run instruments/lrc-host/Diff.rsd mutants [TAG]`——
  `Mutants*.tsv` 全部行（或指定单个表）：每个变异必须改变该遍输出或
  被拒绝。
- `lean --run instruments/lrc-host/Diff.rsd plants`——每个变异行须
  植入：其 FROM 文本必须在其 FILE 中仅出现。
- `lean --run instruments/lrc-host/Diff.rsd ir` / `cite` / `mag`——
  写出映像 IR、核对移植模块的 Lean 行号引用、或前端整数运算表。

两个子命令需要仓库侧输入：`rsdc` 运行 OCaml 参考前端
`instruments/rsdc-ml/rsdc.ml`（OCaml 仪器，不发货），映像检查读取
`Images.tsv` 中十个仓库侧 `img/*.rscm` 映像（生成物，不发货）。其余
子命令只需发货文件加 Lean 工具链。

## examples/surfaces/ — 三表面往返检查

内容：五个小程序各写三遍——`.rsd`、`.rsj`、`.rsm` 三个表面各一遍——
以及 `docs/surfaces/`（表面文档与本节所依据的 `check.tsv` 表）。

该检查重新解析每个表面文本，并把所得语法树与同一程序另两个表面的
树做比较；每一行还必须能重印为自身。其驱动
（`tools/surface-docs/X3.rsd`，在同一 Lean 4.14.0 工具链下、
`LEAN_PATH=build/syntax/rsd/lib:build/syntax` 环境中运行）属仓库侧——
它导入已编译的语法库而非发货源码；发货的
`docs/surfaces/check.tsv` 记录了 `fast` 档每一行的结果。

## 性能记录如何产出

`docs/PERF-RECORD.tsv` 是测量记录（其形式与词表见
`docs/PERF-RECORD.md`）。产出规程——记录的运行命令——
在仓库侧 `reports/perf-record/` 之下的 `README.md` 按版本 `0.1` 归档：每台 VM 全新实例
GCP t2d-standard-4 作业，把种子提交的 `git archive` 提交进全新仓库，
在 `env -i PATH=/usr/bin:/bin` 下跑
`bootstrap/seed/stage-14274/README.md` 的 bash 块，然后 2 台 VM 上各
做 3 遍串行的自编译与编译速度测量；`wall_s` 列为 2 台 VM 均值，
`vm_spread_pct` 为逐行离散度。基准映像来自发货的 `benchmarks/` 程序；
Koka 列用同组 VM 上的 `benchmarks/koka/` 测得。
