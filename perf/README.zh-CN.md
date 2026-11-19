# 性能记录

[English](README.md) | 中文

每个版本一份记录，测量方法相同，版本之间可以直接比较。所有版本的每一行都在 [HISTORY.tsv](HISTORY.tsv) 里（机器可读；新版本追加自己的行）。
记录的完整格式和规则，见该版本源码里的 `release/docs/PERF-RECORD`。

**机器**：GCP t2d-standard-4（AMD EPYC 7B13，4 个 vCPU），Linux x86_64；每个版本用两台全新的虚拟机；每个值是两台机器各自 5 次运行中位数的平均，
固定在一个核上。**参照**：同一台机器、同一套基准上的 Koka 3.2.9。比值 = residua 用时 / Koka 用时（小于 1 表示比 Koka 快）。

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
