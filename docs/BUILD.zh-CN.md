# rsd 构建工具

[English](BUILD.md) | 中文

`rsd` 是本版本的构建与运行工具。其源码为 `rsd/`（调度器与编译工作器）
与 `lib/rsd/`（存储、依赖图与会话层）。

范围：工具的源码随附，但其构建闭包的一部分为仓库侧，故 `rsd` 无法
仅凭本归档编译——此处的可运行编译器是 [seed](GLOSSARY.zh-CN.md) 配方。`rsd test` 还需
读取仓库侧的端到端清单。两者均见 `release/GAPS.tsv`。

## 动词

- `rsd build <source.rsd>` 编译程序：计算具名文件的导入闭包，每个声明
  只编译一次，产物写入存储。编辑后重建只重编译输入变了的声明。
- `rsd test` 运行端到端套件（`rsd/suite.rsd`）：语料清单走过每一级——
  源码、闭包、编译、降级、wasm、运行——逐行记录结果、拒绝级别、
  墙钟时间与峰值内存。
- `rsd run <source.rsd> -- <args>` 需要时先构建再执行。
- `rsd cache` 是内容存储：`cache key <inputs...>` 打印配方存于的键；
  `cache get <key> <dest>` 恢复已记录的结果（`hit`）或退出 1
  （`miss`）；`cache put <key> <dir> --rc 0` 原子地发布结果——运行
  失败的结果绝不入库。

## 信任假设

存储中每个对象由产生它的字节的 sha256 寻址；`cache get` 拒绝其记录
输入与工作树不再匹配的载荷；已存运行只有在两次复现一致后才对外
服务。这些保证由埋入行套件（`release/checks/rsd-tool/`）检验，其
独立审核为 `reports/release-02/evidence/AUDIT-RSD-TOOL.e0c2404440.md`
（仓库侧）。

## 参考

- 源码：`rsd/`、`lib/rsd/`、`lib/Rsd.rsd`。
- 版本说明：`release/notes/rsd-tool.zh-CN.md`。
- 示例：`rsd/examples/`。
