# RELEASE-NOTES — Residua 0.3

[English](RELEASE-NOTES.md) | 中文

0.3 版本保留自举闭合——可验证来源的编译，只用 C 编译器从提交的
wasm 种子逐字节重建——并加入 `rsd` 构建工具、语言中的 `UInt64`、
执行边界处的首批带类型 `ExecModel` 实例，以及 MST-NF 复合定理。
MST-NF 是 Residua 的基础理论：它在公共仓库
[github.com/residua-labs/MST-NF](https://github.com/residua-labs/MST-NF)
钉住提交 `4432a34`，证明由该仓持有。

## 0.3 新增

- **`rsd` 构建工具。** `rsd build` 经内容寻址存储编译程序，只重
  编译变化部分；`rsd test` 运行端到端套件；`rsd run` 执行；
  `rsd cache` 即存储本身。调度器 `rsd/`，存储与依赖图
  `lib/rsd/`、`lib/Rsd.rsd`；用户文档 `docs/BUILD.md`；说明
  `release/notes/rsd-tool.md`。
- **语言中的 `UInt64`。** 编译器源码已使用它。
- **套件恢复。** 0.1.1/0.1.2 随附而 0.2 遗漏的基准与测试套件按
  当前字节恢复：`benchmarks/`、`instruments/lrc-host/`、`perf/`、
  `ACKNOWLEDGEMENTS.md` 与 TESTING 指南。新增门禁检查拒绝再发生
  同类静默遗漏（除非更新日志有一行声明）。
- **执行边界的带类型 `ExecModel` 实例**
  （`semantics/Effect/AdmissionNF.lean`）：`monitorModel` 与
  `exec9AdmissionModel`，四条 Tier-1 定律已证——商分解、准入
  可靠、余数全性与代表元精确。仓库侧回执：
  `reports/effect-sem/ADMISSION-NF.md`（检查 11 条定理，公理在
  `propext`/`Quot.sound` 内，拒绝控制 1/1）。
- **三种表面写法。** `examples/surfaces/` 随附五个程序，各以
  `.rsd`、`.rsj`、`.rsm` 写法打印；`docs/surfaces/` 记录
  各剖面及三种写法解析到同一棵树的往返检查。
- **新种子切面；wasm 路线默认 `narrow`。** 提交的种子在钉住的
  主线头部重切；自本次切面起 wasm 路线默认以 `narrow` 层编译，
  原生路线保持 64 位。
- **MST-NF 复合定理**（`lean/nf-compose/`）：步骤必然性在积、
  和、序列与分派上的复合规则，基于目录内 vendored 的钉住
  必然性执行模型。独立审计通过
  （`reports/nf-compose/REPORT.md`，Lean 4.14，公理仅
  `propext`）。
- **面向外部读者的公共文档。** `README.md` 按开源惯例排序并附
  可复制的快速开始；`docs/` 按 Diátaxis 分类并有索引；
  `docs/GLOSSARY.md`；`CONTRIBUTING.md`；`CODE_OF_CONDUCT.md`
  （Contributor Covenant 2.1）；`SECURITY.md`；issue 与 PR 模板。
  构建工具源码以其公开名随附（`rsd/`、`lib/rsd/`、`lib/Rsd.rsd`）。
  钉定源字节的注释里仍有内部工作项和报告的名字；它们不含个人信息，
  在下一次重切 seed 时修改。

## 0.3 的 MST-NF 状态

每个随附组件要么已绑定到钉住的 `ExecModel`
（`lean/nf-compose/pinned/MSTNecessityExecModelMWE.lean`）并证出
四条 Tier-1 定律，要么记录为缺口。

| 随附组件 | 状态 |
|---|---|
| 编译器链（`rsdc`、`rsc`） | 缺口——尚无 `ExecModel` 实例 |
| 执行层（`semantics/Effect/`） | 实例已随附：`monitorModel`、`exec9AdmissionModel`；Tier-1 定律已证（`AdmissionNF.lean`） |
| 语法引擎（`rsdc/profiles/`、`semantics/Syntax/`） | 缺口——尚无 `ExecModel` 实例 |
| QFormat（`docs/QFORMAT.md`、`release/checks/qformat/`） | 缺口——尚无 `ExecModel` 实例 |
| `rsd` 构建工具（`rsd/`、`lib/rsd/`） | 缺口——尚无 `ExecModel` 实例 |
| NF 复合（`lean/nf-compose/`） | 框架已随附：钉住模型上的复合定理，经独立审计 |

0.1 与 0.2 没有随附任何此类实例：它们的 `Monitor.lean` 引用的是
三形式编码，并非 `ExecModel` 定义。0.3 随附首批带类型实例；上述
缺口仅作记录，不构成发布阻塞。

准入审计状态：wasm0 实例的准入审计已在开发 main 线上签发，晚于本
发布——该实例的判定器以类型变量合一运行，对照独立的
wasm-validate 预言机、双种子，无反签名。QFormat、rsx、scm 实例
在较早修订通过了空洞性检查；lambda-RC 准入仍未决，正在按更正后的
判据重建。

## 本归档内容

- 提交的 `rsdc`/`rsc` wasm 种子及其源码闭包（`bootstrap/seed/`
  之下），附重建配方
- 以 stage 宿主文件契约方式调用的 rsd 链 `rsd -> rscm -> wasm`
  （`docs/RSD-COMMAND.md`）
- `rsd` 构建工具（`rsd/`、`lib/rsd/`、`lib/Rsd.rsd`）
- 按内容摘要钉住的各编译层冻结形式语义（scm、lambda-RC、wasm0）
  规范文本；`semantics/Syntax/` 与 `semantics/Effect/`（含带类型
  `ExecModel` 实例）
- 语法引擎的文法轮廓（`rsdc/profiles/`）与规范
  （`semantics/Syntax/`）；引擎本体在随附的编译器源码内
- MST-NF 复合包（`lean/nf-compose/`，含钉住模型）及其审计报告
  （`reports/nf-compose/REPORT.md`）
- 基准、差分与性能套件（`benchmarks/`、`instruments/lrc-host/`、
  `perf/`）
- 自举文法测量所依据的语言一致性语料（`docs/LANGUAGE.md` 各表）
- 性能记录（`docs/PERF-RECORD.tsv`，形式见
  `docs/PERF-RECORD.md`）
- 面向陌生读者的英文文档，及 `README` 与各 `docs/` 中文
  `.zh-CN.md` 镜像
- 逐目标发布说明（`release/notes/`）、可运行的一致性检查
  （`release/checks/`）与 vendored 许可证文本
  （`release/licenses/`）

## 验证

`docs/VERIFY-RELEASE.md` 即协议：种子摘要、归档摘要，然后在干净
的 Linux x86-64 或 macOS arm64 账户上跑完整种子配方——配方重建
的编译器映像必须与提交的种子逐字节一致
（`seed_roundtrip=2/2`）。归档的宿主回执随附于 `release/`。

## 0.3 的既定限制

仅单模块程序（无 `import`）；无 I/O 执行层（执行边界语义规定宿
主契约，语言本身无副作用）；无证明检查（R-CIC 内核不在本版）；
4 GiB 地址空间；无结果发布/查询入口；无可导入标准库。自举
`.rsd` 文法拒绝 `theorem`、`axiom`、`class`、`abbrev`、
`variable`、`opaque`、`by` 与 `import` 作为源码构造。

## 0.3 之后

1. R-CIC 内核 + agent 入口的发布/查询入口——陌生人首次能找到、
   检查并复用他人结果的位置。
2. 编程完备性：模块、真实程序、执行层、64 位寻址、应用套件。
3. 执行的廉价确认：wasm0 -> AIR -> zk。
4. 外部语义的通用连接器（K/KORE、Lean/Rocq 导入）。
