# OVERVIEW — Residua 是什么，0.2 提供什么，它的局限

[English](OVERVIEW.md) | 中文

本文档是发布归档的一部分。标注*仓库侧*的引用所指文件不在本归档内；
它们写在这里，供同时持有源码仓库的审计者查阅。未带提交的引用，
即为本文件随附的那个头部。

## 一句话

Residua 是一套基础设施，让人无需信任对方，就能使用对方的计算或证明：
结果按内容（q）识别，只凭机械检查准入，建立在一张形式化定义的
语义网络之上。Residua 的设计是计算和证明一体：在它的语言 rsd 中，
程序和证明是同一个依赖类型论中的项——同一个对象既被编译成原生
代码或 WebAssembly，又由内核检查，而不是两个靠同步维持的系统。
这一点是设计，尚未端到端证实；0.2 交付的是编译这一半——证明检查
那一半（R-CIC 内核）在下文"版本局限"和"0.2 之后的顺序"中列名。

为什么——三个事实，首页不写使命宣言：形式化结果的成本主要花在
重复检查、上游变化后的修补、协调和审查上（内核检查只占一小部分）；
将来的结果大多由不可信的机器产出，能扩展的只有机械检查和按内容
识别；形式语义彼此割裂（Lean、Rocq、K、wasm、EVM），结果无法跨越
它们组合。

## 0.2 提供什么——且只有这些

可验证来源的编译：给定一份源码和一份产物，任何人都可以从提交的
wasm 种子出发，只用 C 编译器、不需要别的工具链，逐字节重建并核验
这份产物来自这份源码——既不必信任发布者，也不必信任庞大的二进制
工具链。

支撑它的：

- rsd 编译器链 `rsd -> rscm -> wasm`（`rsdc`、`rsc`），自举：两个
  编译器都以 wasm 种子发货，见 `bootstrap/seed/stage-14274/`
  （sha256 `dcd40993dcda…` 与 `ce2cff5b42fd…`，
  `bootstrap/seed/stage-14274/SHA256SUMS`），连同其 54 个成员的
  源码闭包（`SOURCE-MEMBERS-SHA256SUMS`）及成员到 bundle 的链接
  （`ASSEMBLY.tsv`：哪个成员在两个整模块源文件里位于哪个
  `RscSourceModule_` 节，按顺序）。
- 引导配方 `bootstrap/seed/stage-14274/README.md`：一台干净的
  Linux x86-64，装有 GCC/binutils/coreutils/Bash/curl/tar，
  且没有 Lean、elan、lake、Node、OCaml，即可重建两个编译器；配方
  重建出的映像与已提交的种子逐字节一致（`seed_roundtrip=2/2`）。
  本归档上该配方的一次第三方运行到达了不动点（证据在仓库侧）。
- 逐层冻结的形式语义（scm、lambda-RC、wasm0），按内容地址钉住：
  `lean/rsd-cert/Residua/Bootstrap/Semantics.lean` 的 `evalLF`
  （`1fef580a3`，q `4ffcb7d990e8c77fa5dce42bcb4e1ae798e3cddd04803ac7c1fcbd2cb7fa46d2`，
  冻结腰部 scm 行）。整个 `Residua.Bootstrap` 规范集发货（9 个文件），
  连同它导入的 `Residua.SHA256`，使被钉规范的 `import` 行在归档
  内部全部可解；这些文本里的 `theorem` 声明是被钉的规范内容，
  不是证明检查。
- 每版本一份的性能记录（`docs/PERF-RECORD.md` +
  `PERF-RECORD.tsv`，随本归档发货）。
- 发布标签的两族封签，以及该配方的第三方复现（证据在仓库侧）。

0.2 新增：

- 最终的带类型内容标识 `q`（格式 v1）：被寻址内容的种类进入哈希
  字节内部；裸 SHA-256 保留为 `digest`，仅用于文件完整性
  （`docs/QFORMAT.zh-CN.md`；向量 `release/checks/qformat/`）。
- 语法引擎，在其文法类上闭合：引擎源 `rsdc/syntax/`、含参照判
  定器与正确性证明的类 `semantics/Syntax/`、作为数据发货的表面
  profile `rsdc/profiles/*.syn`，以及在生成文法上的验收套件。
- 执行边界形式语义 E0–E4（`semantics/Effect/`）：线格式、准入
  与封签判断、一致性分类器以及录制的传输会话；验收证据
  `reports/effect-sem/`（仓库侧）。

## 本归档中的链

- `rsdc` 把 `.rsd` 源码编成 `.rscm`（scm 层的二进制形式；magic
  `52 53 43 4d` + 版本字节，写于 `rsdc/Compile.rsd`，读于 `rsc/rsc.rsd`）。
- `rsc` 在该阶段钉住的字（14274）把 `.rscm` 降成 `.wasm`。
- `execution-bridge` 组件的 C 宿主桥（文件名见
  `bootstrap/seed/stage-14274/EXECUTOR-SHA256SUMS`）加上
  `bootstrap/seed/stage-14274/WABT-SHA256SUMS` 钉住的外部拉取 wabt
  运行时执行种子；`bootstrap/Wasm2CHost.c` 与
  `bootstrap/ProcWasm2CHost.c` 是通用宿主变体。
- 调用即阶段宿主的文件契约：
  `"$out/rsdc/run" rsdc <in.rsd> <out.rscm> 0 cons` 与
  `"$out/rsc/run" rsc <in.rscm> <out.wasm> 14274 cons`
  （`docs/RSD-COMMAND.md`）。

## 文件格式

| 格式 | 是什么 | 出处 | 0.2 发货 |
|---|---|---|---|
| `.rsd` | 精化前树的文本拼写；0.2 前缘接受的是引导子集 | `docs/LANGUAGE.md` | 是——源码成员加上 `semantics/`/`gates/semalign/` 规范文本 |
| `.rsj` | 同一棵树的文本拼写，Reason 风格 | 仓库侧文法描述 | 否——仅仓库 |
| `.rsm` | 同一棵树的文本拼写，Racket 系（由 `.rsl` 改名） | 仓库侧文法描述 | 否——仅仓库 |
| `.rsx` | 规范内核形式：源码级 AST 的规范 S 表达式的 csexp | 仓库侧文法 | 否——仅仓库 |
| `.scm` | scm 语言的文本程序；也是规范树上的具名 Scheme 视图 | 仓库侧文法 | 否——仅仓库 |
| `.rscm` | 二进制 scm 层接口 | `docs/EMITTER.md` | 是——`bootstrap/seed/rsc.rscm`，配方重建时也会产出 `.rscm` |
| `.wasm` | 提交的编译器种子 | `bootstrap/seed/stage-14274/{rsdc,rsc}.wasm`、`bootstrap/seed/{rsdc,rsc}.wasm` | 是——4 个文件 |
| `.lean` | 冻结语义的 Lean 4.14 规范文本 | `lean/rsd-cert/Residua/Bootstrap/`、`lean/rsd-cert/Residua/SHA256.lean` | 是——仅此规范集；其余 `.lean` 均为仅仓库 |

`semantics/` 与 `gates/semalign/` 下的语义 `.rsd` 文件是作为规范
发货的 Lean 4.14 程序文本（`docs/SPECS.md` 标该行 GATED；
`gates/semalign/METHOD.md` 载明规程）。0.2 的 `rsdc` 前缘不接受
它们——0.2 的 `.rsd` 文法是 `docs/LANGUAGE.md` 的引导子集，
拒绝 `theorem`、`axiom`、`class`、`abbrev`、`variable`、`opaque`、
`by` 与 `import`。

## 0.2 的版本局限

- 单模块程序：前缘拒绝 `import`。
- 没有 I/O 执行层：程序的输入输出是阶段宿主的文件契约，不是语言效果。
- 没有证明检查：R-CIC 检查器、`rsd_proofs` 和证书都不在本版本；
  随附的 `theorem` 文本是被钉的规范，不是被检查的断言。
- 没有 UInt64；4 GiB 地址空间。
- 没有结果的发布/查询入口；没有调度器命令。
- 没有可导入的标准库（`docs/STDLIB.md`）。

0.2 面向谁：可复现、可审计的编译——供应链、可信执行之前的那一步——
以及可验证、可自举编译器的研究。它不以通用语言的面目发布。

## 0.2 之后的顺序

每项都带验收对象；不写日期。

1. 不信任对方即可使用其结果，第一个实例：R-CIC 内核（Lean Kernel
   Arena：任何非法输入都不被接受，然后 init/std，再然后 16 GiB 内的
   mathlib）加上结果的发布/查询入口——这是陌生人第一次能
   找到、检查并复用他人结果的点；排在编程特性之前。R-CIC 内核规则
   面向当前 Lean，含 4.32–4.34 健全性修复；输入是 4.35 导出格式。
2. 编程完备性：模块、真实程序、UInt64、执行层（I/O 作类型化效果）、
   64 位寻址，以及应用套件（Cedar、SQLite 等）作为
   验收。基本数据表示从 0.2 起跟随当前 Lean（Int8..Int64/ISize、
   Float32、String 作 UTF-8 ByteArray、Std.TreeMap），每类型一张卡。
3. 廉价的执行确认：wasm0 -> AIR -> zk。
4. 网络：通往外部语义的通用连接器（K/KORE、Lean/Rocq 导入），按一座
   桥能打开多少语义排序。

## 命名与面拼写

Residua 是项目；`rsd` 是语言和工具链。

仓库侧，Residua 源码以同一棵精化前树的三种面拼写存在——`surface rsd`
文法（Lean 4.14.0 语法子集，移植自 stock Lean 4.14.0 提交
`410fab7284703f41660ca2454218dcca9b2ec896`）、一个 Reason 风格拼写
和一个 Racket 系拼写——加上规范内核形式 `.rsx`。0.2 只发 `.rsd`
拼写，且只接受它的引导子集（`docs/LANGUAGE.md`：链自身源码
parse err=0，6/6 文件加 1,208,186 字节拼接 bundle；refuse 语料逐行
拒绝，54/54——证据在仓库侧）。

逐层的设计——语义链、表面语法、身份与信任——见
`docs/ARCHITECTURE.md`。面向外部读者的
`docs/{TRUST.md,GLOSSARY.md,STABILITY.md,FAQ.md,RELATED-WORK.md,
CONTRIBUTING-SECURITY.md}` 说明 0.2 信任什么、其用语、承诺与关系，
均以中英双语发货。

`closure_claim=0`（`release/MANIFEST.md`："No release tag, seal or
author attestation is made here"）。
