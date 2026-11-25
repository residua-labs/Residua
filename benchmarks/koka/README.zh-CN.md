# benchmarks/koka —— 2 路线 Koka 对比表

产出实测的 Koka 对比表：residua 对 Koka v3.2.9，2 条路线——native
（residua wasm2c `-O2` C 可执行文件 对 `koka -O2` 可执行文件）与
wasm（2 个模块在同个 node 引擎下）——在固定规模上，于 1 台
GCP t2d-standard-4 VM 上，含 CPU 秒数（与 wall 并列）、峰值 RSS、
代码大小，以及 2 个
页面列（portable 与各自的主机最优；Koka 列按 host 规则读取）。完整
规则清单见驱动文件的头部注释。

运行驱动需要开发仓库（`instruments/rsdc-ml/` 与 `rsd` 工具的构建链
不在本归档内）；随附的文件与表格是供审计的副本。

## 结构

- `KokaBase.rsd` —— 驱动；`lean --run` 带 3 种命令
  （`images`、`table`、`report`）。
- `timecell.c` —— 单进程测量单元：fork/exec + wait4，
  CLOCK_MONOTONIC 壁钟、`ru_maxrss` 峰值 RSS、`ru_utime+ru_stime`
  CPU、wall 终止。输出：`wall_ns \t maxrss_kb \t cpu_us \t status`。
- `src/test/bench/koka/*.kk` —— 从 `v3.2.9` 发布版逐字收录的 Koka
  源（binarytrees、cfold、deriv、nqueens、rbtree、rbtree-ck）。
- `images/`、`modules/`、`refusals/`、`state/` —— 生成物、不跟踪：
  RSCM 映像、编译模块、前端拒绝文本、逐次运行的单元与表格。永不提交。

## 运行

```sh
# 1. 映像+模块步（分钟级；唯一构建 residua 产物的一步）：
#    今天的映像由 twin 构建，模块由 import 闭包在 --store 下构建的
#    编译器编译
lean --run benchmarks/koka/KokaBase.rsd images 14274 \
  [out/kbstore/build/rsc-native compile]
#    环境变量：KB_VARIANT_cfold / KB_VARIANT_deriv —— 为被拒程序提供
#    另一变体源（行标为 `variant, not the source`）
#         KB_STORE（默认 out/kbstore）、KB_TWIN（默认 out/lrc/twin）、
#         KB_NATIVE_COMPILER（默认：PATH 上一个先前构建的 `rsc-native`
#         二进制）—— 在另一台机器上运行时把这些指向某个状态目录
#         （`$KB_STATE`），使 store 与 twin 随工作区同行，例如：
#    KB_STORE=$KB_STATE/kbstore \
#    KB_TWIN=$KB_STATE/bin/twin \
#    KB_NATIVE_COMPILER=$KB_STATE/bin/rsc-native \
#    lean --run benchmarks/koka/KokaBase.rsd images 14274 \
#      $KB_STATE/kbstore/build/rsc-native compile
#    images 步记入 modules.tsv 的 MODCMD 就是 table 命令要逐字重复的
#    argv——它是出处记录，不在主机上执行。

# 2. 在一台 GCP t2d-standard-4 VM 上，全部行一次跑完：
lean --run benchmarks/koka/KokaBase.rsd table 14274 <runtag> <同一个 MODCMD>

# 3. 本地，把运行状态拷回之后：
lean --run benchmarks/koka/KokaBase.rsd report <报告目录>
```

主机步可续跑：每个完成的单元与产物都是 `$KB_STATE/<runtag>/` 下的
单文件；重跑从中断处继续。table 命令里的 `MODCMD` 必须等于 images
步记录在 `$KB_STATE/modules.tsv` 中的模块编译命令——模块出处是核查
项，不在主机上重建。

表格规则：规模 binarytrees 21、nqueens 13、rbtree 4,200,000、
rbtree-ck (5, 4,200,000)、cfold 20、deriv 10；单钉核
（`taskset -c`）；wall = 整进程 timecell 5 遍取中位数；计时前先判
等（按打印文本，binarytrees 的 `trees` 行有已声明的例外）；
binarytrees 跑 2 次——带等调用共享（标注、不入 geomean）与在
[qbe](../../docs/GLOSSARY.zh-CN.md) 层（入 geomean）；被拒源按路线各成行；模块对换控制行必须报
not equal。上限：wall 600 s、堆 4 GiB、fuel 10^12、栈提升并记录。
环境覆盖：`KB_REPS`、`KB_WALL`、`KB_FUEL`、`KB_CAP`、`KB_STACK`、
`KB_NODE_STACK`、`KB_CORE`、`KB_KOKA_TAG`、`KB_WABT_TAG`、
`KB_EMSDK_TAG`、`KB_BT_WASM_WALL`、`KB_COUNTER_DIR`。每次完成的
运行向 `KB_COUNTER_DIR`（默认 `benchmarks/koka/state/counter`，文件名 `local`，
`KB_COUNTER_NAME` 可覆盖）追加计数行。

