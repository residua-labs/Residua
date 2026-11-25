# rsd 构建工具

[English](BUILD.md) | 中文

`rsd` 是本版本的构建与运行工具。其源码为 `rsd/`（调度器与编译工作器）、
`glue/rsd/`（`rsd run` 入口与构建脚本）、`glue/host/`（C11 WebAssembly
与 wasm2c 的 `Proc` 执行宿主），以及 `lib/rsd/` 与 `lib/Rsd.rsd`
（内容存储、依赖图与会话层）。

范围：C11 `Proc` 执行宿主（`glue/host/procwt.c`）仅凭本归档、C 编译器与
钉住的 Wasmtime C API 即可直接编译；若同时安装了原版 Lean `4.14.0`，则可
由 `glue/rsd/build.rsd` 编译 `rsd` 入口二进制。`rsd/rsdc.rsd` 原生编译
工作器闭包的一部分及 `rsd test` 语料清单留在仓库侧（见 `release/GAPS.tsv`）；
本归档内独立的完整编译链是 `bootstrap/seed/stage-14274/` 下的
[seed](GLOSSARY.zh-CN.md) 配方。

## 从本归档构建

设 `$capi` 指向解压后的 Wasmtime `v50.0.1` C API 目录（按 `README.zh-CN.md`
或 `bootstrap/seed/stage-14274/README.md` 下载并校验 SHA-256），Linux
x86-64 上设 `LDL=-ldl`、macOS arm64 上置空，即可在无需 Lean 的情况下编译
独立的 `Proc` WebAssembly 宿主：

```sh
mkdir -p out/rsd-build
cc -O2 -std=c11 -Wall -Wextra -Werror -I "$capi/include" \
    glue/host/procwt.c "$capi/lib/libwasmtime.a" -lpthread -lm $LDL \
    -o out/rsd-build/procwt
```

`procwt` 加载转译后的 `.wasm` 模块，读取其导出的 `__heap_base` 全局量使线性
内存分配从静态数据段之上开始，在步函数槽位传入 `auto` 时自动探测 `driveS`，
并通过进程内 9P2000 响应器（服务端槽位传 `-`）提供命令行参数、时钟与宿主
文件读写。

若环境中同时安装了原版 Lean `4.14.0`（`PATH` 上有 `lean` 与 `leanc`），可
一并构建 `rsd` 调度入口与 `procwt`：

```sh
mkdir -p out/rsd-oleans/rsd out/rsd-build
lean --root=. -o out/rsd-oleans/rsd/BuildAssembly.olean rsd/BuildAssembly.rsd
LEAN_PATH="$PWD/out/rsd-oleans" WASMTIME_INC="$capi/include" WASMTIME_LIB="$capi/lib" \
    RSD_BUILD="$PWD/out/rsd-build" lean --run glue/rsd/build.rsd -- --home .
```

## 动词

- `rsd build <source.rsd>` 编译程序：计算具名文件的导入闭包，每个声明只
  编译一次，产物写入存储。编辑后重建只重编译输入变了的声明。
- `rsd test` 运行端到端套件（`rsd/suite.rsd`）：语料清单走过每一级——源码、
  闭包、编译、降级、wasm、运行——逐行记录结果、拒绝级别、墙钟时间与峰值内存。
- `rsd run <source.rsd> -- <args>` 需要时先构建；在含 `import` 头时为
  `lib/`、`glue/` 与同目录 `.rsd` 模块建立库视图，通过 `wasm-opt` 将旧式
  异常 WebAssembly 一次性转译为 `exnref`，并在 `procwt` 上执行 `Proc` 程序。
- `rsd cache` 是内容存储：`cache key <inputs...>` 打印配方存于的键；
  `cache get <key> <dest>` 恢复已记录的结果（`hit`）或退出 `1`（`miss`）；
  `cache put <key> <dir> --rc 0` 原子地发布结果——运行失败的结果绝不入库。

## 信任假设

存储中每个对象由产生它的字节的 sha256 寻址；`cache get` 拒绝其记录输入与
工作树不再匹配的载荷；已存运行只有在复现一致后才对外服务。这些保证由埋入行
套件（`release/checks/rsd-tool/`）检验，其独立审核为
`reports/release-02/evidence/AUDIT-RSD-TOOL.e0c2404440.md`（仓库侧）。

## 参考

- 源码：`rsd/`、`glue/rsd/`、`glue/host/`、`lib/rsd/`、`lib/Rsd.rsd`。
- 版本说明：`release/notes/rsd-tool.zh-CN.md`。
- 示例：`examples/app04/`、`rsd/examples/`。
