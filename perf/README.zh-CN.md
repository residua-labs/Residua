# 性能记录

[English](README.md) | 中文

每个版本一份记录，按同一种固定方法测量，所以版本之间可以直接比较。所有版本的每一行都在 [HISTORY.tsv](HISTORY.tsv) 里（机器可读；新版本
追加自己的行）。记录的完整格式和规则，见该版本源码里的 `release/docs/PERF-RECORD`。

## 方法

**机器。** GCP t2d-standard-4（AMD EPYC 7B13，4 个 vCPU），Linux x86_64；每个版本用两台全新的虚拟机。每个值是两台机器各自 5 次运行
中位数的平均，固定在一个核上。**参照。** 同一台机器、同一套基准上的 Koka 3.2.9。**指标。** 比值 = Residua 的墙钟时间 / Koka 的墙钟
时间，小于 1 表示 Residua 更快。

**适用范围与局限。** 套件很小；其中的程序是分配密集的函数式负载，每个都固定在一个核上运行；并且只测了一种机型。这些比值刻画的是某个版本在这个套件上的
表现，不是对所比较语言的一般性排名。不是同等移植的行会被记录，但不计入几何平均，下文逐行标明。

## 汇总

| 版本 | 原生路线对 Koka 几何平均 | wasm 路线对 Koka 几何平均 | 从种子自举 | rsdc 编译自己 | rsc 编译自己 |
|---|---:|---:|---:|---:|---:|
| 0.1 | 0.973（6 行） | 1.047（4 行） | 1161.7 秒，3.6 GiB | 119.0 秒，0.67 GiB | 301.2 秒，2.0 GiB |

几何平均只计入下表标为"是"的行：也就是 Koka 自己程序的同等移植。标为"否"的是我们自己写的变体（源码不同），只记录，不参与比较。

## 0.1（编译器 4a639b7b0，种子 f640f43df；2026-11-19）

用时比值，residua / Koka：

| 基准 | 路线 | 规模 | 比值 | 计入几何平均 |
|---|---|---:|---:|---|
| binarytrees-kk | native | 21 | 0.969 | 否 |
| binarytrees-kk-qbe | native | 21 | 0.953 | 是 |
| binarytrees | native | 21 | 0.573 | 否 |
| binarytrees-qbe | native | 21 | 1.580 | 否 |
| cfold | native | 20 | 1.006 | 是 |
| cfold | wasm | 20 | 1.121 | 是 |
| deriv | native | 10 | 0.990 | 是 |
| deriv | wasm | 10 | 0.940 | 是 |
| nqueens-kk | native | 13 | 1.031 | 是 |
| nqueens-kk | wasm | 13 | 1.114 | 是 |
| nqueens | native | 13 | 1.795 | 否 |
| nqueens | wasm | 13 | 2.707 | 否 |
| rbtree-ck | native | 4200000 | 0.984 | 是 |
| rbtree-kk | native | 4200000 | 0.880 | 是 |
| rbtree-kk | wasm | 4200000 | 1.024 | 是 |
| rbtree | native | 4200000 | 1.315 | 否 |
| rbtree | wasm | 4200000 | 1.506 | 否 |

编译器自身的开销（Linux，用种子构建的 CPU 可执行文件）：从种子自举 1161.7 秒（峰值 3.6 GiB）；rsdc 编译自己 118.96 秒（0.67 GiB）；
rsc 编译自己 301.23 秒（2.0 GiB）；最大的测试源文件：生成 0.06 秒、降级 2.76 秒；deriv：生成 0.15 秒、降级 4.69 秒。

## 其他语言（0.1）

同样的 6 个程序，原样取自 Koka 的 `test/bench`（Perceus 论文 PLDI 2021 使用的套件，v3.2.9）和 Lean 4.14.0 的 `tests/bench`，在同一机型上测量
（三台全新 t2d-standard-4，5 次中位数，固定核心；引用的每两台机器相差不到 10%；计时前核对每格输出）。residua 列用每个程序的同等移植行。
比值 = residua 用时 / 该语言用时（小于 1 表示 residua 更快）。

| ratio | cpp | rust | ocaml | haskell | java | swift | lean |
|---|---|---|---|---|---|---|---|
| rbtree | 0.926 | 0.245 | 0.712 | 0.406 | 0.456 | 0.082 | 0.358 |
| rbtree-ck | - | 0.116 | 0.532 | 0.079 | 0.225 | 0.166 | 0.421 |
| nqueens | 0.790 | 0.320 | 0.601 | 0.087 | 0.572 | 0.189 | - |
| cfold | 0.436 | 0.205 | 0.379 | 0.422 | - | 0.168 | 0.696 |
| deriv | 0.543 | 0.203 | 0.623 | 0.335 | 0.234 | 0.284 | 0.649 |
| binarytrees | 2.168 | 0.408 | 0.751 | 1.240 | 1.362 | 0.161 | 0.881 |

| 几何平均 residua/语言 | C++ | OCaml | Haskell | Java | Swift | Lean 4.14 |
|---|---:|---:|---:|---:|---:|---:|
| 0.1 | 0.822 | 0.586 | 0.281 | 0.451 | 0.164 | 0.570 |

Rust 列（几何平均 0.232）是 residua 自己写的朴素移植（Box/Rc，未调优），不是公开套件里的程序，不能和套件各列比较。空格：rbtree-ck/C++ 在 12.5 GiB
上限被杀（上游程序每个检查点整体复制 map）；cfold/Java 默认线程栈溢出；Lean 的套件没有 nqueens。工具链：cpp = g++ 13.3.0 -O3 -pthread; rust = rustc 1.100.0 (0ef1bc386) -C opt-level=3 -C codegen-units=1; ocaml = ocamlopt 4.14.2 flambda=true -O3 (vm5+vm6; vm3 ran 4.14.1 flambda=false and its ocaml cells are kept as third-run evidence only); haskell = GHC 9.4.7 -O2; java = OpenJDK 21.0.13.1 default GC; lean = Lean 4.14.0 (commit 410fab728470) lean -c + leanc -O3; swift = swiftc 6.0.3 RELEASE -O。参照列只取决于机型和这些钉值，每组钉值测一次，之后版本复用。
