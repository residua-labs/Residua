# 0.3 seed cut

0.3 版本钉住 `main` 的一个切点：`fc0fb23a3a`（含 `d533e0ff3b`——
提交的 seed 前端重新读取 `rsdc/Compile.rsd`——与
`0b55499f61`——两路线 Koka 表的 narrow 列）。本版本不再合并
`main` 的后续提交。

从该切点起，WebAssembly 路线默认以 `narrow` 层编译；native 路线
保持 64 位。新切出的 seed 目录取代 `bootstrap/seed/stage-14274/`
成为正式的 seed；其 README、清单、哈希与各级条目由
`bootstrap/seed/Cut.rsd` 依据 `bootstrap/seed/Check.rsd` 的
检查输出生成，不手工编写。

切出后运行 `lean --run benchmarks/koka/KokaBase.rsd images 30658
<seed 编译命令>`，写出 `benchmarks/koka/modules.tsv` 与
`benchmarks/koka/images.tsv`；若模块摘要与
`reports/koka-table-narrow/`（仓库侧）中的钉值一致，Koka 表原样沿用，
无需重跑。
