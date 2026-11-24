# Residua

[English](README.md) | 中文

Residua 是一个可以逐字节核对自身构建的编译器：提交的 WebAssembly [seed](docs/GLOSSARY.zh-CN.md) 只需一个 C 编译器就能从源码重建工具链，每个产物按其内容哈希寻址，而非按生产者署名。

它存在的原因：可验证软件真正昂贵的部分不是检查，而是信任工具链。一个署着生产者名或编译器版本号的结果，在互不信任的各方之间无法安全地比较与复用。内容寻址加上经 seed 验证的工具链，把这两个假设都去掉。

更长远的设计是一门语言：程序与证明是同一依赖类型论中的项；本版本交付的是该设计的编译一半。

## 0.3 相对 0.2 的新内容

| 方面 | 0.2 | 0.3 |
|---|---|---|
| 构建工具 | 未随附 | `rsd build` / `rsd test` / `rsd run` / `rsd cache`（`rsd/`、`lib/rsd/`） |
| 语言 | 无 `UInt64` | 支持 `UInt64` |
| Seed | 0.1 时代字节 | 按本版本源码重切 |
| 测试套件 | benchmarks/, instruments/lrc-host/, perf/ 缺失 | 已恢复（0.2 回归已修复） |
| 文档 | 学术文体 | 面向外部读者重写；词汇表与社区文件 |
| 规范 | 仅分层语义规范 | + Lean 4.14 的 MST-NF 复合定理（`lean/nf-compose/`；理论见 [github.com/residua-labs/MST-NF](https://github.com/residua-labs/MST-NF) 钉住提交 `4432a34`，证明由该仓持有） |

## 状态

研究性版本 **0.3**。当前可用：在 Linux x86-64 和 macOS arm64 上从提交的 seed 重建编译器；把单模块 `.rsd` 源码编译为 WebAssembly；`rsd` 构建工具的四个动词；带类型的内容地址格式；语法引擎；执行边界的形式语义。执行边界工作背后的基础理论是 MST-NF，与其证明一同保存在独立仓库 [residua-labs/MST-NF](https://github.com/residua-labs/MST-NF)（提交 `4432a34`）。

尚不可用：模块、证明检查、I/O 执行层、真实应用套件。完整图景与限制见 [docs/OVERVIEW.zh-CN.md](docs/OVERVIEW.zh-CN.md)。

## 评测

<!-- generated-from-perf -->
**方法。** GCP t2d-standard-4。Koka 两列：两台全新虚拟机，每个值是两台机器各自 5 次中位数的均值（固定核心）。
其他语言各列：三台全新虚拟机，固定核心上 5 次取中位数。比值 = Residua 的墙钟时间 / 参照的墙钟时间，小于 1
表示 Residua 更快。程序原样取自 Koka 的基准套件（Perceus 论文所用套件，参照表见 `docs/OVERVIEW.zh-CN.md`）和 Lean 4 的基准。

| 几何平均，Residua 0.1 / … | Koka（原生） | Koka（wasm） | C++ | OCaml | Haskell | Java | Swift | Lean 4.14 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 比值 | 0.973 | 1.047 | 0.822 | 0.586 | 0.281 | 0.451 | 0.164 | 0.570 |
<!-- end-generated-from-perf -->

## 快速开始

需要 C 工具链、Bash、curl、tar，约 20–45 分钟。不需要 Lean、Node 或 OCaml。

```sh
# 1. 下载并校验源码归档（自发布页）
sha256sum -c rsd-src.tar.sha256       # macOS：shasum -a 256 -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src

# 2. 在干净环境中从 seed 重建两个编译器
env -i PATH=/usr/bin:/bin bash --noprofile --norc
#    然后执行 bootstrap/seed/ 下 seed 配方 README 中的命令
```

配方会取回钉住的 wasmtime 与 binaryen，把 seed 的旧式异常处理指令重编码，编译一个 C 宿主桥，并让全部四次编译器调用都运行在 seed 自身的 Wasm 形态上；仅当重建产物与提交的 seed 逐字节一致时才退出。

然后把一个程序编译为 WebAssembly（路径按配方留下的样子）：

```sh
"$out/run" rsdc f832  "$out/translated/rsdc.wasm" rsd/examples/answer.rsd answer.rscm 0 cons
"$out/run" rsc  f2268 "$out/translated/rsc.wasm"  answer.rscm answer.wasm 14274 cons
```

`answer.wasm` 可在任何 WebAssembly 运行时上运行。更高层的 `rsd build`/`rsd run` 动词见 `docs/BUILD.md`。

## 示例

```lean
-- rsd/examples/answer.rsd
def main : Int := 42
```

同一个程序的三种表面写法——`docs/surfaces/` 中的往返检查把每种写法解析到同一棵树：

```lean
-- examples/surfaces/do.rsd（.rsd 表面）
def sumList (xs : List Nat) : Nat := Id.run do
  let mut total := 0
  for x in xs do
    total := total + x
  return total
```

```js
// examples/surfaces/do.rsj（.rsj 表面）
let sumList = (xs: List(Nat), ): Nat => Id.run(do: {
  syntax_225(syntax_134(tree_name(total), tree_none, tree_num(0)))
  syntax_206(tree_12(syntax_207(tree_none, tree_name(x), tree_name(xs)), tree_none), tree_46_general(syntax_223(tree_name(total), tree_none, binary_1(tree_name(total), tree_name(x))), ))
  return total;
});
```

```racket
;; examples/surfaces/do.rsm（.rsm 表面）
#lang rsd
(define (sumList [xs : (List Nat)] ) : Nat (Id.run (do:
  (#:syntax225 (#:syntax134 (#:tree-name total) #:none (#:tree-num 0)))
  (#:syntax206 (#:tree12 (#:syntax207 #:none (#:tree-name x) (#:tree-name xs)) #:none) (#:tree46-general (#:syntax223 (#:tree-name total) #:none (#:binary1 (#:tree-name total) (#:tree-name x))) ))
  (return total)
)))
```

## 文档

入口 [docs/INDEX.zh-CN.md](docs/INDEX.zh-CN.md)：首次构建、校验版本、运行测试套件、语言子集、词汇表、架构说明——以英文为主，多数文档附中文镜像。

## 贡献

见 [CONTRIBUTING.zh-CN.md](CONTRIBUTING.zh-CN.md)。开发在项目的私有工作区进行；公开仓库通过 GitHub 接收 issue 与提案。

## 版本

| 版本 | 日期 | 归档 SHA-256 | 说明 |
|---|---|---|---|
| [0.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1) | 2026-11-19 | `59d0956e…` | 首个公开版本：最小自举闭包 |
| [0.1.1](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.1) | 2026-11-19 | `165690af…` | 补丁：性能记录随附，署名补全 |
| [0.1.2](https://github.com/residua-labs/Residua/releases/tag/rsd-0.1.2) | 2026-11-19 | `a3185221…` | 补丁：基准与差分测试套件随附 |
| [0.2](https://github.com/residua-labs/Residua/releases/tag/rsd-0.2) | 2026-11-20 | `151bfd4f…` | q 格式 v1、语法引擎、效应语义 |
| [0.3](https://github.com/residua-labs/Residua/releases/tag/rsd-0.3) | 2026-11-24 | 见发布页 | rsd 构建工具、UInt64、重切 seed、恢复套件、开源文档 |

完整历史：[CHANGELOG.zh-CN.md](CHANGELOG.zh-CN.md)。

## 安全

通过 GitHub 私密渠道报告漏洞；见 [SECURITY.md](SECURITY.md)。

## 许可证

Apache License 2.0。见 [LICENSE](LICENSE) 与 [NOTICE](NOTICE)。
