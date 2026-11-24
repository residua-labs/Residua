# 文档索引

[English](INDEX.md) | 中文

文档按 [Diátaxis](https://diataxis.fr) 分类组织：教程用于学习，
操作指南用于完成任务，参考用于查事实，解释用于理解设计。
文档以英文为准；链接指向 `.zh-CN.md` 的条目有中文镜像，其余仅英文。

## 教程——动手学习

- [QUICKSTART.md](QUICKSTART.md)（仅英文） — 从 seed 重建编译器并完成
  第一次编译。
- [BUILD.zh-CN.md](BUILD.zh-CN.md) — `rsd` 构建工具：`rsd build`、
  `rsd test`、`rsd run`、`rsd cache`。

## 操作指南——完成任务

- [VERIFY-RELEASE.md](VERIFY-RELEASE.md)（仅英文） — 校验发布归档的每个摘要。
- [TESTING.zh-CN.md](../TESTING.zh-CN.md) — 运行基准与差分测试套件（仓库根）。
- [RSD-COMMAND.md](RSD-COMMAND.md)（仅英文） — 直接调用重建出的编译器
  （执行器文件契约）。
- [INSTALL.md](INSTALL.md)（仅英文） — 配方的宿主要求。

## 参考——查事实

- [LANGUAGE.md](LANGUAGE.md)（仅英文） — 前端接受的 `.rsd` 表面（自举子集，
  含接受/拒绝表）。
- [surfaces/](surfaces/README.md) — `.rsd`/`.rsj`/`.rsm` 三种表面写法
  与示例程序的往返检查。
- [STDLIB.md](STDLIB.md)（仅英文） — 随附的库源码。
- [QFORMAT.zh-CN.md](QFORMAT.zh-CN.md) — 带类型的内容地址格式 `q`。
- [GLOSSARY.zh-CN.md](GLOSSARY.zh-CN.md) — 全部技术术语，各定义一次。
- [PERF-RECORD.md](PERF-RECORD.md)（仅英文） 与 `.tsv` — 性能记录及其读法。
- [SPECS.md](SPECS.md)（仅英文） — 哪些文本是钉住的规范。
- [STABILITY.zh-CN.md](STABILITY.zh-CN.md) — 项目承诺保持什么。
- [FAQ.zh-CN.md](FAQ.zh-CN.md) — 常见问题。
- [EMITTER.md](EMITTER.md)（仅英文） — `.rscm` 文件格式。
- [TRUST.zh-CN.md](TRUST.zh-CN.md) — 运行配方时你信任（与不信任）什么。

- [CONTRIBUTING-SECURITY.zh-CN.md](CONTRIBUTING-SECURITY.zh-CN.md) — 贡献与安全报告。

## 解释——理解设计

- [OVERVIEW.zh-CN.md](OVERVIEW.zh-CN.md) — Residua 是什么、动机、
  证据、边界与参考文献。
- [ARCHITECTURE.zh-CN.md](ARCHITECTURE.zh-CN.md) — 语义链的逐层设计。
- [RELATED-WORK.zh-CN.md](RELATED-WORK.zh-CN.md) — 与其他工作的关系。
- [RELEASE-NOTES.zh-CN.md](RELEASE-NOTES.zh-CN.md) — 各版本改动，
  按目标展开。

仓库布局与发布账册（`release/MANIFEST.md`、`release/NOTICES.md`、
`release/PROVENANCE.tsv`）在 `release/` 下。
