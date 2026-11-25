# Residua

[English](README.md) | 中文

Residua 是一个可以逐字节核对自身构建的编译器：提交的 WebAssembly [seed](docs/GLOSSARY.zh-CN.md) 只需 C 编译器就能从源码重建工具链，每个产物按其内容哈希寻址，而非按生产者署名。

它存在的原因：可验证软件真正昂贵的部分不是检查，而是信任工具链。署着生产者名或编译器版本号的结果，在互不信任的各方之间无法安全地比较与复用。内容寻址加上经 seed 验证的工具链，把这些假设去掉。

更长远的设计是一门语言：程序与证明是同一依赖类型论中的项；本版本交付的是该设计的编译与命令行/文件执行部分。

## 0.4 相对 0.3 的新内容

| 方面 | 0.3 | 0.4 |
|---|---|---|
| 模块与 I/O | 仅单模块；无 `Proc` 宿主 | 跨模块 `import`、`Proc` `do` 记法、`glue/std/` 及 C11 + Wasmtime 的 `procwt` 宿主（`glue/host/procwt.c`） |
| 语言 | `UInt64`、整数、数组、归纳类型 | + 全链路 IEEE-754 `Float`（`binary64`：`rsdc`、`.rscm`、`lambda-RC`、WebAssembly） |
| 示例 | 单行 `rsd/examples/answer.rsd` | 多模块 `examples/app04/{Stats,Table,Main}.rsd`（`Float` 统计 + `String` 表格 + 文件 I/O） |
| Seed 与编译器 | `19.9 MB` / `20.5 MB` wasm；重建 `20–45 min` | `12.5 MB` / `14.3 MB` wasm（`845b99ef…` / `b52b07d1…`）；`seed-host.c` 读取 `__heap_base`；Linux 重建 `105 s`、macOS `191 s` |
| 映射表许可证 | `lib/AvlMap.rsd` 移植自 OCaml `stdlib/map.ml`（LGPL-2.1） | `lib/AvlMap.rsd` 移植自 Lean `v4.36.0` `Std.DTreeMap`（Apache-2.0） |
| 规范 | 积/和/序列/分派复合 | + `lean/nf-compose/` 中的多跳（`HopCompose.lean`）与递归（`Rec.lean`、`NfRec/CheckedStatus.lean`）复合定理 |

## 状态

研究性版本 **0.4**。当前可用：在 Linux x86-64 和 macOS arm64 上从提交的 seed 逐字节重建编译器；把使用 `Float`（`binary64`）、`String`、`Proc` `do` 记法与 `glue/std/` 的多模块 `.rsd` 程序编译为 WebAssembly 并在 `glue/host/procwt.c` 上运行；`rsd` 构建工具各动词（[docs/BUILD.zh-CN.md](docs/BUILD.zh-CN.md)）；带类型的内容地址格式；语法引擎；执行边界形式语义与 MST-NF 复合包（`lean/nf-compose/`，基于独立仓库 [residua-labs/MST-NF](https://github.com/residua-labs/MST-NF) 提交 `4432a34` 的钉住模型）。

尚不可用：证明检查（R-CIC 内核）、面向 `Float` 与 `Proc` 的独立 `.rmod` 编译（`release/GAPS.tsv`）、网络/子进程宿主服务、64 位 WebAssembly 寻址、结果发布/查询入口。完整图景与限制见 [docs/OVERVIEW.zh-CN.md](docs/OVERVIEW.zh-CN.md)。

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

需要 C11 编译器（`cc`）、POSIX `sh`、`awk`、`curl`、`tar`（支持 `xz`）及 `sha256sum`（macOS 为 `shasum -a 256`）。不需要 Lean、Node、Python 或 OCaml。全程约 `3–6` 分钟（Linux x86-64 约 `193 s`，macOS arm64 约 `337 s`）。

在任意非 `.git` 目录下校验并解压源码归档：

```sh
sha256sum -c rsd-src.tar.sha256       # macOS：shasum -a 256 -c rsd-src.tar.sha256
mkdir rsd-src && tar -xf rsd-src.tar -C rsd-src && cd rsd-src
```

随后在解压后的归档根目录以干净环境（`env -i PATH=/usr/bin:/bin /bin/sh -eu`）运行以下脚本，从 seed 重建 `rsdc` 与 `rsc`、核对逐字节不动点，并编译与运行 `examples/app04`：

```sh
set -eu
export LC_ALL=C
seed=$PWD/bootstrap/seed/stage-14274
out=$PWD/out/app04-run
platform=$(uname -s)-$(uname -m)
case "$platform" in
    Linux-x86_64)
        SHASUM=sha256sum
        binaryen_tar=binaryen-version_133-x86_64-linux.tar.gz
        wasmtime_tar=wasmtime-v50.0.1-x86_64-linux-c-api.tar.xz
        LDL=-ldl ;;
    Darwin-arm64)
        SHASUM="shasum -a 256"
        binaryen_tar=binaryen-version_133-arm64-macos.tar.gz
        wasmtime_tar=wasmtime-v50.0.1-aarch64-macos-c-api.tar.xz
        LDL= ;;
    *) printf 'unsupported host: %s\n' "$platform" >&2; exit 1 ;;
esac

mkdir -p "$out/tools" "$out/translated" "$out/rebuilt" "$out/app"
( cd "$seed" && $SHASUM -c SHA256SUMS )
$SHASUM -c "$seed/SOURCE-MEMBERS-SHA256SUMS"
$SHASUM -c "$seed/SEED-HOST-SHA256SUMS"

[ -f "$out/tools/$binaryen_tar" ] || curl -fsSL --retry 3 -o "$out/tools/$binaryen_tar" \
    "https://github.com/WebAssembly/binaryen/releases/download/version_133/$binaryen_tar"
[ -f "$out/tools/$wasmtime_tar" ] || curl -fsSL --retry 3 -o "$out/tools/$wasmtime_tar" \
    "https://github.com/bytecodealliance/wasmtime/releases/download/v50.0.1/$wasmtime_tar"
grep " $binaryen_tar\$" "$seed/BINARYEN-SHA256SUMS" > "$out/tools/pins"
grep " $wasmtime_tar\$" "$seed/WASMTIME-SHA256SUMS" >> "$out/tools/pins"
( cd "$out/tools" && $SHASUM -c pins && tar -xf "$binaryen_tar" && tar -xf "$wasmtime_tar" )

wasmopt=$out/tools/binaryen-version_133/bin/wasm-opt
capi=""
for d in "$out/tools"/wasmtime-v50.0.1-*-c-api; do
    if [ -d "$d" ]; then capi=$d; fi
done

# 1. 将 seed Wasm 模块转译为 exnref，编译 C11 seed 宿主与 procwt 宿主
"$wasmopt" --all-features "$seed/rsdc.wasm" --translate-to-exnref -o "$out/translated/rsdc.wasm" &
p1=$!
"$wasmopt" --all-features "$seed/rsc.wasm" --translate-to-exnref -o "$out/translated/rsc.wasm" &
p2=$!
wait "$p1" "$p2"

cc -O2 -std=c11 -Wall -Wextra -Werror -I "$capi/include" -c "$seed/seed-host.c" -o "$out/seed-host.o"
cc "$out/seed-host.o" "$capi/lib/libwasmtime.a" -lpthread -lm $LDL -o "$out/run"
cc -O2 -std=c11 -Wall -Wextra -Werror -I "$capi/include" \
    glue/host/procwt.c "$capi/lib/libwasmtime.a" -lpthread -lm $LDL -o "$out/procwt"

rsdc_entry=$(awk -F'\t' '$1=="rsdc_entry"{print $2}' "$seed/CUT.tsv")
rsc_entry=$(awk -F'\t' '$1=="rsc_entry"{print $2}' "$seed/CUT.tsv")

# 2. 用 seed 从源码重建 rsdc 与 rsc，并核对逐字节不动点
"$out/run" rsdc "$rsdc_entry" "$out/translated/rsdc.wasm" \
    "$seed/sources/rsdc.rsd" "$out/rebuilt/rsdc.rscm" 0 cons
"$out/run" rsc "$rsc_entry" "$out/translated/rsc.wasm" \
    "$out/rebuilt/rsdc.rscm" "$out/rebuilt/rsdc.raw.wasm" 14274 cons
cmp -s "$seed/rsdc.wasm" "$out/rebuilt/rsdc.raw.wasm"
"$wasmopt" --all-features "$out/rebuilt/rsdc.raw.wasm" --translate-to-exnref -o "$out/rebuilt/rsdc.wasm"

"$out/run" rsdc "$rsdc_entry" "$out/translated/rsdc.wasm" \
    "$seed/sources/rsc.rsd" "$out/rebuilt/rsc.rscm" 0 cons
"$out/run" rsc "$rsc_entry" "$out/translated/rsc.wasm" \
    "$out/rebuilt/rsc.rscm" "$out/rebuilt/rsc.raw.wasm" 14274 cons
cmp -s "$seed/rsc.wasm" "$out/rebuilt/rsc.raw.wasm"
( cd "$out/rebuilt" && grep "\.rscm\$" "$seed/REBUILT-SHA256SUMS" | $SHASUM -c - )
"$wasmopt" --all-features "$out/rebuilt/rsc.raw.wasm" --translate-to-exnref -o "$out/rebuilt/rsc.wasm"

# 3. 用重建出的编译器与 procwt 编译并运行多模块 app04 命令行程序
awk '/^import / {next} {print}' \
    lib/ProcBytes.rsd lib/Proc.rsd lib/Proc9.rsd \
    glue/std/Str.rsd glue/std/Proc.rsd glue/std/Args.rsd glue/std/Files.rsd \
    examples/app04/Stats.rsd examples/app04/Table.rsd examples/app04/Main.rsd \
    > "$out/app/app04.rsd"

printf '\000RSDC-ENTRIES\n' | cat - "$out/app/app04.rsd" > "$out/app/app04.ent.in"
"$out/run" rsdc "$rsdc_entry" "$out/rebuilt/rsdc.wasm" \
    "$out/app/app04.ent.in" "$out/app/app04.entries" 0 cons
app_entry=$(awk -F'\t' '$1=="entry" && $3=="main" {print "f"$2}' "$out/app/app04.entries")

"$out/run" rsdc "$rsdc_entry" "$out/rebuilt/rsdc.wasm" \
    "$out/app/app04.rsd" "$out/app/app04.rscm" 0 cons
"$out/run" rsc "$rsc_entry" "$out/rebuilt/rsc.wasm" \
    "$out/app/app04.rscm" "$out/app/app04.raw.wasm" 14274 cons
"$wasmopt" --all-features "$out/app/app04.raw.wasm" --translate-to-exnref -o "$out/app/app04.wasm"

printf -- '-2.5\n0.0\n1.25\n2.75\n10.25\n' > "$out/app/numbers.txt"
"$out/procwt" "$out/app/app04.wasm" "$app_entry" auto 4000000000000000 "" "" - \
    "$out/app/numbers.txt" "$out/app/summary.txt"
cat "$out/app/summary.txt"
```

更高层的 `rsd` 构建与运行动词见 [docs/BUILD.zh-CN.md](docs/BUILD.zh-CN.md)。

## 示例

```rust
enum Tree<T> { leaf, node(Tree<T>, T, Tree<T>) }

fn sum(t: Tree<Nat>) -> Nat {
  match t {
    Tree::leaf => 0,
    Tree::node(l, x, r) => sum(l) + x + sum(r)
  }
}

fn mirror<T>(t: Tree<T>) -> Tree<T> {
  match t {
    Tree::leaf => Tree::leaf,
    Tree::node(l, x, r) => Tree::node(mirror(r), x, mirror(l))
  }
}

theorem sum_mirror(t: Tree<Nat>): sum(mirror(t)) = sum(t) by {
  induction t with
  | leaf => rfl
  | node l x r hl hr => simp [sum, mirror, hl, hr]; omega
}
```

程序和关于它的定理写在同一种语言里：`sum_mirror` 对每棵树都成立，证明由内核检查。写法是 Rust 的，含义是类型论的：值不可变，每个 `match` 覆盖所有情形，每个函数都终止。

在这里含义会不同的 Rust 写法，按名拒绝并给出该写的形式：

| 写下的形式 | 拒绝名 | 改写为 |
|---|---|---|
| `let mut x = 1;` | `closed_mut` | `let x = 1;` |
| `f(&x)` | `closed_borrow` | `f(x)` |
| `return x` | `closed_return` | `x`，作为块的末尾表达式 |
| `for y in xs { … }` | `closed_loop` | 递归或折叠 |
| `if b { 1 }` | `if_without_else` | `if b { 1 } else { 0 }` |
| `Nat` 上的 `a - b` | `nat_subtraction` | `Nat::sub(a, b)`，到 0 为止 |
| `Int` 上的 `a / b` | `int_division` | `Int::tdiv(a, b)`（截断）或 `Int::ediv(a, b)`（欧几里得） |

**状态。** 这套 Rust 拼写的证明表面语法还在开发中，不在 0.4 归档里。目前它是 Lean 4.14 的语法扩展：由原版 Lean 繁饰，上面的例子与其 Lean 写法的内核项相同。0.4 的编译器读的是自举表面，即 Lean 4.14 的子集（[docs/LANGUAGE.md](docs/LANGUAGE.md)）；编译器自身源码与快速开始中的多模块 `examples/app04/` 命令行程序均以它写成：

```lean
-- examples/app04/Main.rsd（入口节选）
def main : Proc := do {
  let rawArgs <- argvP 0;
  let out <- appDispatchArgs rawArgs;
  out
}
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
| [0.3](https://github.com/residua-labs/Residua/releases/tag/rsd-0.3) | 2026-11-24 | `b07ae731…` | rsd 构建工具、UInt64、重切 seed、恢复套件、开源文档 |
| [0.4](https://github.com/residua-labs/Residua/releases/tag/rsd-0.4) | 2026-11-25 | `d25d1c17…` | 模块、Proc 文件/命令行 I/O、Float（binary64）、app04 示例、更小更快的 seed、Apache-2.0 映射表 |

完整历史：[CHANGELOG.zh-CN.md](CHANGELOG.zh-CN.md)。

## 安全

通过 GitHub 私密渠道报告漏洞；见 [SECURITY.md](SECURITY.md)。

## 许可证

Apache License 2.0。见 [LICENSE](LICENSE) 与 [NOTICE](NOTICE)。
