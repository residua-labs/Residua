# 发布说明 — rsd 构建工具

[English](rsd-tool.md) | 中文

状态：**0.3 新增**；摘要同步收录于 `docs/RELEASE-NOTES.zh-CN.md`。

## 它提供什么

`rsd` 是本版本的构建与运行工具：

- `rsd build <source.rsd>` 计算具名文件的导入闭包，每个声明只编译
  一次，产物写入内容寻址存储；编辑后重建只重编译输入变了的声明。
- `rsd test` 运行端到端套件（`rsd/suite.rsd`）——源码、闭包、编译、
  降级、wasm、运行——逐行记录结果、拒绝级别、墙钟与峰值内存。
- `rsd run <source.rsd> -- <args>` 需要时先构建再执行。
- `rsd cache` 即内容存储：`key`、`get`、`put`；运行失败的结果
  绝不入库。

源码：调度器与编译 worker 在 `rsd/`；存储、依赖图与会话层在
`lib/rsd/` 与 `lib/Rsd.rsd`。用户文档 `docs/BUILD.md`；一致性检查
`release/checks/rsd-tool/`（植入行）。

## 验收证据

- 构建工具在开发主线以独立审计通过收尾；证据记录存于仓库侧。
- 工具源码随附，与树中其余内容受同一归档摘要约束。

## 边界

- 存储保证由植入行套件（`release/checks/rsd-tool/`）检验；尚未在
  公开配方中按编译器自身构建的规模检验。
- `rsd` 针对提交的 seed 对运行；seed 更新会改变执行器动作的输入并
  重新推导，而非复用陈旧产物。
- 该工具无法仅凭本归档编译：其构建闭包的一部分为仓库侧
  （`release/GAPS.tsv`）；此处的可运行编译器是 seed 配方。
