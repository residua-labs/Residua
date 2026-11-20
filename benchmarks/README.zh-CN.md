# benchmarks/ —— `第三方性能语料与实测对比`

本目录是 0.1 性能记录背后的基准语料，以及记录所依据的实测对比。这里
没有门禁：每个数字都是随套件保存的原始运行的字面字段，比率由这些
字段计算。运行在某台持续负载下的非独占 Arm64 主机上进行（见
"方法"），故下述比率界于约 1.3 倍之内，不是交付数字。

内容：`.rsd` 基准源及其生成的 `.rscm` 模块、`MANIFEST.tsv`（逐程序
出处）、`expected/`（逐字节期望输出）、`rust/`（对比所引用的 Rust
参考移植）、`arena/`（arena 路线的 2 个源变体）、`koka/`（Koka 对比
框架）、`langs/`（移植所依据的上游套件收录）。

## 套件

下列上游页面均于 2026-11-04 抓取（Benchmarks Game 页面存为 HTML，
随原始运行保存；Koka 文件取自
`raw.githubusercontent.com/koka-lang/koka/master/test/bench/`，其余
README 取自 `raw.githubusercontent.com`）。标记 READ 的断言来自所抓
文本；MEASURED 来自下列某次运行。

主清单：binary-trees、fannkuch-redux、pidigits 来自 Computer
Language Benchmarks Game；nqueens、rbtree、rbtree-ck、deriv、cfold
来自 Koka/Perceus 套件（PLDI'21 基准，koka-lang/koka 的
`test/bench`）。浮点程序（n-body、spectral-norm、mandelbrot）按
构造排除：wire 构造子集没有浮点。fasta、k-nucleotide、
reverse-complement、regex-redux 不在主清单（需要 IO 流、哈希表或
正则引擎）；它们在此无行是因为不在主清单，而非尝试过失败。

| 程序 | 来源（URL）及其所述，READ | 输入规模 | Rust 参考 |
|---|---|---|---|
| binary-trees | benchmarksgame-team.pages.debian.net/benchmarksgame/description/binarytrees.html：分配 stretch 树、长存树、大量自底向上的树；"leaf nodes must be the same as interior nodes - the same memory allocation"；"please don't implement your own custom arena"；规模 10 对 1 KB 输出文件 diff，规模 21 测性能 | 规模 10（校验，存期望文件）、规模 21（性能） | Game 的 Rust 条目使用 `typed_arena`/`toolshed` arena（上述规则不接受 arena）与线程，以 `rustc -C opt-level=3 -C target-cpu=ivybridge -C codegen-units=1` 构建（rustc 1.84.1，Game 条目 1 页面）。不可离线构建、非单线程。改用：`rust/binarytrees.rs`，`每节点一个` `Box`，单线程，条目 1 的树类型；flags 见下 |
| fannkuch-redux | .../description/fannkuchredux.html：轮转计数排列序、交错符号校验和、最大翻转数；diff 规模 7（228，`Pfannkuchen(7) = 16`），规模 12 测性能（3968050，`Pfannkuchen(12) = 65`，条目 2 页面） | 规模 7 校验，规模 12 性能 | Game 的 Rust 条目 2（仅 std，`四线程`）逐字，`main` 换成重复计时框架（`rust/fannkuchredux_bg2.rs`）；另有同文件把线程常量 4 改为 1 的版本（`rust/fannkuchredux_bg2_t1.rs`），因受测对象是单线程 |
| pidigits | .../description/pidigits.html：任意精度算术，"the same step-by-step single-threaded algorithm"（Gibbons 无界 spigot，extract(3) 与 extract(4)），每行打印 10 位及累计数；diff 规模 30，规模 10000 测性能 | 规模 30 校验，规模 10000 | Game 的 Rust 条目需要 GMP/rug（不可离线构建）；`rust/pidigits.rs` 为本基准编写：`同一` Ledrug/TeXitoi 状态机，跑在手写的基 2^32 符号幅值 limb bignum 上（小乘/加、符号比较、Knuth 式 64/32 估计的截断除法）；pidigits-30 与 Game 输出文件逐字节相等，pidigits-10000 与 Lean native 运行（套件记录）逐字节相等 |
| nqueens | koka-lang/koka `test/bench/koka/nqueens.kk`；套件的 `readme-pldi40.txt.md` 说 "n-queens problem of size 13 ... returns the length of that list" | 规模 13（73712 解） | 套件中无 Rust 版本（其移植为 C++、OCaml、Haskell、Swift、Java、Lean、Koka）。`rust/nqueens.rs` 为本基准按套件的 C++ 版形态编写（共享尾的持久链表，`Rc` 单元） |
| rbtree | `test/bench/koka/rbtree.kk`（出自 Lean 4 IFL19 rbmap 基准）；源默认 4200000，打印结果 420000（套件 README 输出） | 规模 4,200,000 | `rust/rbtree.rs` 为本基准编写：受有的 `Box` 节点在每次 insert 中消耗并重建（`同一算法的复用形态`） |
| rbtree-ck | `rbtree-ck.kk`：每第 5 棵中间树保持存活（`make-tree(5, 4200000)`） | 规模 4,200,000（freq 5） | `rust/rbtreeck.rs` 为本基准编写（套件记录）：与 `rust/rbtree.rs` 相同的 insert 但用 `Rc` 节点（保持表与活树共享子树，如 Koka 的引用计数）；值映射在 2000/20000/4200000 上 Lean native == Rust |
| deriv | `deriv.kk`（出自 Lean 4 IFL19 `deriv.ml`）：对 `x^x` 的 10 层嵌套符号求导，逐步打印计数 | 源中固定 | `rust/deriv.rs` 为本基准编写（套件记录）：Box 表达式、按 deriv.kk 的 case 序的智能构造子；11 行输出与 Lean native 运行逐字节相等 |
| cfold | `cfold.kk`：`mk_expr(20, 1)`，再 `reassoc` 与 `cfold`，打印 2 次求值 | 源中固定（深度 20） | `rust/cfold.rs` 为本基准编写（套件记录）：Box 表达式、cfold.kk 的 match 分支；2 次求值与 Lean native 运行逐字节相等 |

此处每个 Rust 构建的编译器与 flags：`rustc 1.99.1`（Homebrew），
`-C opt-level=3 -C codegen-units=1`（即 Game 的 flags 去掉
`-C target-cpu=ivybridge`——它指名 x86 核，而本机是 arm64）。无
`target-cpu=native`。

**读过而未采纳的套件，各自附理由：**
- *Are We Fast Yet*（github.com/smarr/are-we-fast-yet，README 与贡献
  指南）：14 项基准按单条规则（"the benchmark is identical for all
  languages"；"use the language idiomatically"）移植到 10 门语言，
  测量*预热后的语言实现*而非最优程序。其 Queens（"solves the 8
  queens problem"）、Permute（"generates permutations of an
  array"）、Storage（"creates and verifies a tree of arrays"）与
  List（"recursively creates and traverses lists"）与 nqueens、
  fannkuch-redux、binary-trees 同族，但以数组与对象为原语。其
  README 未列 Rust 移植（C++、Crystal、Java、JavaScript、Lua、
  Python、Ruby、SOM、SOMns、Smalltalk），并称 Rust 移植需要显式
  内存管理的附加规则。未采纳因为主清单已于 2026-11-02 定案，且其
  核心语言假定构造子集所没有的数组与对象；留作日后数组/对象扩展
  的对照。
- *plb2*（attractivechaos/plb2）：4 类任务（位运算 nqueen、浮点
  matmul、sudoku、bedcov）覆盖 25 种语言；基于数组与浮点，多数行
  会以其他原因"今日不可行"。
- *hanabi1224/Programming-Language-Benchmarks*：重新发布 Game 的
  程序并附 CI 生成数字；不增程序清单，其数字出自其 CI 机器，非本
  测量环境。
- *kostya/benchmarks*：Brainfuck、Base64、JSON、Matmul、Primes；
  重 IO 与库。

## 覆盖 —— 3 类路线，每程序行

共尝试 3 类路线。做过运行为 MEASURED，否则为 READ。
- **无类型路线**（U）：`.rsd` -> 原版 Lean 4.14 -> 无类型 emitter
  -> 提升后的 evaluator wire。值是动态记录，故允许递归
  `inductive`。引擎：wire 解释器，以及 wire 的 wasm 降阶在 V8 与
  wasmtime 上。
- **类型化路线**（T）：类型化发射原型 -> 类型化 `SCMPrograms` ->
  源 wire 编码器 -> 重建编译器 -> wasm，及 Lean 中的 `evalSCM`。
  类型化对象语言无递归类型、无浮点、无 bignum。
- **驻留 arena 路线**（A）：arena 生成器取*无类型* emitter 的
  `.scm` 模块，产出类型化 RSCM——其中每个递归族都是泛在驻留
  arena（节点的基数 trie，以记录传入传出）的句柄，再过同个重建
  编译器。其代价见结果。

| 程序 | U（wire 解释器、wasm 降阶） | T（类型化发射 + 重建编译器） | A（驻留 arena + 重建编译器） | 确切缺什么 |
|---|---|---|---|---|
| binary-trees | 现可写、已写（`binarytrees.rsd`）；规模 10 输出在解释器与 wasm 降阶上均与 Game 文件逐字节相等 | **T 拒绝**：`[typed_unrepresentable] recursive_or_indexed(Tree) (in bt.bottom_up)`（MEASURED） | **可跑**，需源变体（`binarytrees_arena.rsd`）：未变源在 `[unknown_prim] (* arity 2)`、`(/ arity 2)`、`(mod arity 2)` 处使生成器停止。变体的规模 10 输出（自 arena 解码）与 Game 文件逐字节相等；V8 上 6.5 s | T：类型化对象语言中的递归类型或某种编码。A：生成器没有 `*`、`/`、`mod` 原语。与 Game 的差异：arena 驻留，`结构相等的子树合为一个节点`（见结果；Game 禁止自定义 arena） |
| fannkuch-redux | 现可写、已写（`fannkuchredux.rsd`），以表代数组 | 现可写、已写：12 模块、0 拒绝；重建编译器编译通过；规模 7 结果与 Game 的相等（MEASURED） | 不需要（无递归数据） | O(1) 下标访问与原位交换：`nth`/`setNth`/前缀反转是 O(n) 的表重建。不挡程序，但定其代价 |
| pidigits | 今日不可行 | 今日不可行 | 今日不可行 | 任意精度整数：`Int` 是带溢出检查的 `i64`（越界即拒绝），构造子集没有 bignum，本树也不随带（检索 2 次：对发货源的文本检索只找到经与 Python bigints 对拍的 64 位字段及 reject 语料用例；文件名检索无 bignum 或 limb 库）。由 `listAppend`/`listDrop`/`mul`/`divE` `组一个` limb-list 库原则上可行，每 limb 访问 O(n)，未写 |
| nqueens | 现可写、已写（`nqueens.rsd`）；计数 92 与 352 与已知值相等 | 现可写、已写：6 模块；evalSCM 值相等；重建编译器 wasm 值相等（MEASURED） | 不需要 | 无 |
| rbtree | 现可写、已写（`rbtree.rsd`） | **T 拒绝**：`[typed_unrepresentable] recursive_or_indexed(Tree) (in rb.fold_count)`（MEASURED） | **可跑**，需源变体（`rbtree_arena.rsd`：否则停在 `[unknown_prim] (mod arity 2)`）；规模 200 与规模 2000 给 20 与 200；规模 2000 在 V8 上 36.9 s | 同 binary-trees；arena 在结果包中返回（规模 2000 时 21.8 MB） |
| rbtree-ck | 现可写（与 rbtree 只差保持树表）；未写 | T 拒绝，同 rbtree（READ：同类型） | 未试 | 同 rbtree；此时共享只能经 arena 观测 |
| deriv | 可写但需小心；未写：递归 `expr`、字符串名（`eqE` 在 `str` 上存在），而 Koka 的 `int` 是 bignum、此处 `Int` 是检查 `i64`；打印计数须先对照 i64 范围才可断言成行 | T 拒绝（READ：递归类型） | 未试 | 递归类型；导数系数的 i64 范围未验证 |
| cfold | 现可写；未写（`mk_expr` 只构造 `Add`，深度 20 给 2^21 叶，值远在 i64 内）；套件称需 `ulimit -s unlimited` | T 拒绝（READ：递归类型） | 未试 | 递归类型；栈深（解释器需 `RUST_MIN_STACK`，V8 需 `--stack-size`） |

### 其余程序的类型化发射（MEASURED 2026-11-05）

为本套件所写的语料程序被推过类型化发射原型（emitter 保持态，
递归 inductive 在该态下降为驻留 arena 表示）。与 binarytrees/rbtree
行相同的框架（库根编入每个程序）；多处 `Lib.Arena.walk*` 拒绝在每
行重复（去函数化，未完成）。

| 程序 | 发射结果 | walk* 之外的拒绝 | 确切缺什么 |
|---|---|---|---|
| rbtree-ck | 19 模块，205,111 B，发射 1.1 s | 无 | 发射时无缺失；运行需要 arena 求值路径（同 rbtree） |
| deriv | 0 模块，101 次拒绝 | `[typed_refused_int_mod] Int % is not the chain's floor modulus; write Int.fmod`（在 `pownAux`）；`application of non-constant head fvar` 与 `non_constant_type_head(forallE)`（在 `nest`/`nestAux`，该程序传递函数实参） | 移植 `pownAux` 中的 Int `%`（Koka 的 `%` 是 floor；链上的是 `fmod`）；高阶程序形态（去函数化） |
| cfold | 17 模块，144,027 B，发射 2.2 s | 无 | 发射时无缺失；运行需要 arena 求值路径与大栈 |
| pidigits | 15 模块，43,063 B，发射 1.2 s | 无 | 能发射（状态是 Int/Nat 算术），但值在数项内越出 i64：在无 bignum 前所有类型化路线都不可得 |

这些拒绝对语言的含义（不动核心）：(1) **递归数据是类型化路线的
主要缺口**（非浮点非 bignum 程序中占 4 个；类型化发射器全部
拒绝），但**并非不可能**：其中 2 个经路线 A 到达重建编译器，代价
已测（源限于生成器原语、比 V8 上无类型 wasm 模块慢 34 倍
（binary-trees 规模 10）到 900 倍（rbtree 规模 2000）、每个签名带
arena）。更快的答案是把 emitter 设计中的 arena 做进类型化发射
原型，未做。(2) bignum 是库问题不是核心问题：先做 limb-list 模块并
计价。(3) 数组：其缺席是代价（下标访问 O(n)）而非拒绝。

## 所写的程序与每个输出的核对方式

本目录的 `.rsd` 源：`nqueens.rsd`、`binarytrees.rsd`、
`fannkuchredux.rsd`、`rbtree.rsd`，以及 `rbtreeck.rsd`、
`deriv.rsd`、`cfold.rsd`、`pidigits.rsd`（其余 Koka/Game 程序
的忠实移植；pidigits 是 Game 的 C/Rust 条目所跑的 Gibbons 无界
spigot，基于任意精度带符号整数），外加 `arena/` 中 2 个 arena 路线
变体。每个都是纯 Lean 4.14（移植子集：结构、归纳类型、首阶定义、
结构递归；循环是对 `Nat` 计数的结构递归；无 `partial`、`Int` 上无
`%`、除截断外无 `Nat` 减法技巧）。头注释指名源程序与各偏离处。
deriv 的智能构造子带显式 `Nat` fuel（移植的终止性证明，在其头注释
中如此声明；不改变 case 序）。pidigits 的项合成循环带 1000 的 fuel
界（已声明；单数字需要若干项）。

每个源都被原版 Lean 4.14 接受（`lean <name>.rsd`）。语料检查器用
钉定的无类型 emitter 构建每个源，跑 wire 解释器，与 `expected/`
比较；每个断言打印行 PASS/FAIL。主机侧文本渲染只用 `jq`
（binary-trees 用 `render_bt.jq`；fannkuch 打印 `checksum` 与
`Pfannkuchen(n) = maxflips`），因为构造子集没有数字转字符串。

这些语料程序另经 Lean native 运行与 Rust 参考对比：每个程序
`lean -o <m>.olean <m>.rsd`、打印套件文本格式入口值的小 IO
驱动、每模块 `lean --c=<m>.c`、`leanc -c` 出目标文件，再用系统
clang 与工具链的 Lean 库重链，加 `-Wl,-stack_size,0x10000000`
（工具链自身的链接输出被本系统加载器拒绝，且 cfold 的深度递归需要
该栈）；Rust 按上述 flags 构建。对比如下表。

输出与套件期望输出（`expected/`）的比较位置：

| 程序 | 输入 | 期望（来源） | wire 解释器 | wasm 降阶 V8 | wasm 降阶 wasmtime | 类型化 evalSCM | 重建编译器 wasm（V8、wasmtime） |
|---|---|---|---|---|---|---|---|
| binary-trees | 10 | Game 的输出文件（逐字节相等） | equal | equal（全值） | equal（1037 字节的前 256） | refused | refused（T）；arena 路线 equal（解码后） |
| fannkuch-redux | 7 | Game 的输出（228，`Pfannkuchen(7) = 16`） | equal | equal | equal | equal | equal（V8 与 wasmtime） |
| fannkuch-redux | 8 | 派生：Rust 条目 2（4 线程与 1 线程）打印 1616、`Pfannkuchen(8) = 22` | equal | equal | equal | not run | 无结果：wasmtime 在 `0x100001f0` 处 `out of bounds memory access`（`0x10000000` 字节内存）；V8 加 `--stack-size=60000` 段错误（exit 139） |
| nqueens | 8, 9 | 已知计数 92、352（OEIS A000170），规模 13：73712（套件文本） | equal | equal | equal | 6、8 时 equal | 4、6、8、9 时 equal |
| rbtree | 2000, 20000 | 值为规模的 1/10（套件打印的 420000 对应规模 4,200,000） | equal | equal | equal | refused | refused（T）；arena 路线在 200、2000 时 equal |
| rbtree-ck（语料移植） | 2000, 20000, 4200000 | `expected/rbtreeck.txt`（各规模 Lean native == Rust；freq 5 时为规模的 1/10） | not run | not run | not run | not run | not run；类型化发射能发（见上） |
| deriv（语料移植） | 源中固定 | `expected/deriv.txt`（11 行 Lean native == Rust） | not run | not run | not run | refuses | refuses |
| cfold（语料移植） | 源中固定（深度 20） | `expected/cfold.txt`（`两次求值` Lean native == Rust） | not run | not run | not run | not run | not run；类型化发射能发（见上） |
| pidigits（语料移植） | 30, 10000 | 30：Game 的输出文件，逐字节相等（Lean native 与 Rust）；10000：`expected/pidigits-10000.txt`，逐字节 Lean native == Rust | 不可行（bignum） | 不可行 | 不可行 | refuses（i64 溢出） | refuses；类型化发射能发但值不可得 |

wasm 降阶的 "equal (value)" 指模块返回的 JSON 值与解释器在同载荷
上的值相等；Game 文本形只由解释器从该值渲染。

## 方法、机器、负载对数字的限界

- 机器：某台持续负载下的非独占 Arm64 主机（Apple silicon，16 核）：
  Rust 与 wasm 运行期间 1 分钟负载均值读数 25 至 99（每条原始行带
  `load1_start`；短窗读到 214）。作业在 `nice` 下运行。因此同
  运行重复之间 wall 最多差 2 倍（Rust 上 nqueens 13：wall 2.19 s、
  CPU 1.39 s）。**以下每个比率用 CPU 时间（单次调用的 user+system，
  单进程时钟）、重复取最小**，因其比 wall 稳定；wall 在原始文件
  中。这把数字限界到约 1.3 倍内有效的比率；这里没有交付数字
  （独占机器，范围之外）。
- Rust：`rustc 1.99.1`，`-C opt-level=3 -C codegen-units=1`，进程
  内 N 次取优，`clock_gettime(CLOCK_PROCESS_CPUTIME_ID)` 包单次
  运行；程序为完整计算含分配与析构。
  复现：`rustc -C opt-level=3 -C codegen-units=1 -o bin rust/<name>.rs && ./bin <n> <reps>`
  （stdout 是 Game 格式输出，stderr 是 `best_s best_cpu_s`）。
- 无类型 wasm 降阶：模块是烤入输入的程序；计时器是全新实例上的
  `eval_wire` 调用。V8：node v26.12.0，`--stack-size=60000`。
  wasmtime 50.0.1，默认 Cranelift，1 GiB wasm 栈（默认 512 KiB 在
  fannkuch 7 上触发 "call stack exhausted"）。
- 重建编译器 wasm：类型化路线的 `SCMPrograms` 经源 wire 编码器
  编码，由钉定的重建编译器（3,576,344 B）经钉定 runner
  （`--profile-bootstrap512 --compile-source`，Node 22）编译，再
  以 V1-invocation/V2-outcome ABI（`compile(1024, len)`）运行，
  每次重复新实例。该路线是为测量而重建，不属于发货产物集。
- 仪器：`wasmtime` fuel（每条 wasm 指令计 1 单位，是计数不是时
  间）；Rust 的 `/usr/bin/time -l` instructions retired（进程总
  量，减去在小输入上测得的启动开销）；Lean `evalSCM` 与数节点
  twin（`cev`，逐行核对与 `evalSCM` 的相符性；twin 缺构造子时标
  `cev_agrees=false` 并弃其计数）；200 微秒间隔的 V8 采样剖面。

## 结果

单次运行的 CPU 秒数、重复取最小；括号内为与同输入 Rust CPU 秒数
之比。"untyped" 是 wire 的 wasm 降阶；"compiled" 是重建编译器的
输出。wire 解释器是进程总量，不是受测对象。短横为"无行：被拒或
未跑"（见覆盖表）。wasmtime 的无类型数字在分配密集行上最高胜过
V8 约 3 倍（V8 `付出一块永不释放的内存的增长`）。

| 程序 输入 | Rust cpu s | untyped wasmtime cpu s (x Rust) | untyped V8 cpu s (x Rust) | compiled wasmtime cpu s (x Rust) | compiled V8 cpu s (x Rust) | interpreter proc cpu s (x Rust) |
|---|---|---|---|---|---|---|
| nqueens 8 | 0.000271 | 0.0194 (72x) | 0.0198 (73x) | 0.0761 (281x) | 0.0784 (289x) | 0.0723 (267x) |
| nqueens 9 | 0.00135 | 0.121 (90x) | 0.36 (268x) | 0.704 (523x) | 0.685 (509x) | 0.427 (317x) |
| binary-trees 10 | 0.00548 | 0.0542 (10x) | 0.108 (20x) | - | - | 0.298 (54x) |
| binary-trees 12 | 0.0276 | 0.27 (10x) | 2.74 (99x) | - | - | - |
| fannkuch-redux 7 | 0.000197 | 0.146 (742x) | 0.373 (1895x) | 0.549 (2786x) | 0.489 (2482x) | 0.583 (2957x) |
| fannkuch-redux 8 | 0.00198 | 1.41 (715x) | 36 (18201x) | - | - | 1.81 (918x) |
| rbtree 2000 | 0.00165 | 0.0422 (26x) | 0.0387 (23x) | - | - | 0.159 (96x) |
| rbtree 20000 | 0.0203 | 0.686 (34x) | 1.96 (97x) | - | - | 2.04 (101x) |

套件标准规模下的 Rust（表中 Rust 行，使其时间不为亚毫秒；residua 各行跑
不了这些规模）：

| Rust 程序 | 输入 | CPU s（min） | wall s（min） | reps |
|---|---|---|---|---|
| nqueens（Rust nqueens.rs） | 13 | 1.39 | 2.19 | 5 |
| binary-trees（Box 版） | 21 | 27.56 | 31.90 | 3 |
| fannkuch-redux（Game 条目 2，单线程） | 12 | 45.77 | 59.58 | 3 |
| fannkuch-redux（Game 条目 2，4 线程） | 12 | 48.76 | 21.22 | 3 |
| rbtree（受有 Box 节点） | 4200000 | 9.49 | 16.45 | 3 |

（Game 自己的 Rust 条目比此处同输入数字更快，因为它们用 arena 与
4 线程、在另台机器：发布条目 1 在 binary-trees 21 为 2.10 s，条
目 2 在 fannkuch-redux 12 为 9.19 s；此处测得的单线程 Box 版分别
为 27.6 s CPU 与 45.8 s CPU。是不同的程序与机器；不构成比率。）

同运行比率小结：无类型降阶（wasmtime）在各组数据上为 Rust 的 10x
到 742x；编译输出（wasmtime）`在其能跑的两组数据上为` 281x 到 2786x。
同程序同跑时，编译输出的 CPU 时间为无类型降阶（wasmtime）
的 3.9x（nqueens 8）、5.8x（nqueens 9）、3.8x（fannkuch-redux 7）。

指令计数（wasmtime fuel 单位，每程序单次运行，`来自单独一轮开计量`
的走查）：

| 程序，输入 | untyped units | compiled units | Rust instructions retired（去启动） | compiled / untyped | untyped / Rust | compiled / Rust |
|---|---|---|---|---|---|---|
| nqueens 8 | 242,703,833 | 1,045,713,249 | 2,871,616 | 4.3x | 85x | 364x |
| nqueens 9 | 1,428,194,158 | 10,507,584,060 | 7,805,265 | 7.4x | 183x | 1346x |
| binary-trees 10 | 609,004,302 | - | 57,694,635 | - | 11x | - |
| fannkuch-redux 7 | 1,347,679,108 | 4,821,007,204 | 2,599,387 | 3.6x | 518x | 1855x |
| rbtree 2000 | 507,718,884 | - | 18,122,636 | - | 28x | - |

类型化路线解释器（Lean 的 `evalSCM`，不是速度对象）：nqueens 6：
96,274 节点，0.28 s；nqueens 8：2,072,140 节点，5.4 s——故重建编
译器的输出在 nqueens 8 上每源节点折合 505 单位 wasm 指令
（1,045,713,249 units / 2,072,140），无类型降阶合 117 单位
（242,703,833 / 2,072,140；`二者为同源函数集的` 2 种降阶）。
fannkuch-redux 7 在 `evalSCM` 上：值相等，20.8 s；数节点 twin 缺
此处用到的构造子。

### 驻留 arena 路线，与上表分开

| 程序 | 源改动 | 生成器 | 编译（node 22，载入） | wasm | 运行 | 输出 |
|---|---|---|---|---|---|---|
| binary-trees 规模 10 | 去掉 `*`、`/`（否则生成器停在 `[unknown_prim]`，MEASURED） | RSCM 20,303 B，7 模块 + 31 辅助，0 残余 | 19.9 s | 257,076 B | V8 上 6.55 s wall（`三回取最小`） | 解码 arena 后与 Game 文件逐字节相等 |
| rbtree 规模 200 / 2000 | 去掉 `mod`（否则停在 `[unknown_prim] (mod arity 2)`，MEASURED） | RSCM 102,971 B，6 模块 + 31 辅助，0 残余 | 41.9 s | 853,701 B | 0.65 s / 36.9 s | 20 / 200，equal；规模 2000 时结果包 21.8 MB（返回 arena） |

对 V8 上无类型降阶的同程序（binary-trees 规模 10：0.189 s wall；
rbtree 规模 2000：0.041 s wall）即慢 34 倍与 900 倍。Rust：5.5 ms 与
1.6 ms。该路线可作为桥，但不是按现有构造的性能路线。路线自身的
代价：源子集（无 `*`、`/`、`mod`）、生成器逐步进行且需要无类型
emitter 先行、每个签名增加 arena 参数、每次调用返回 arena。

## 归因（时间花在哪）

**方法。** 3 套仪器，各有局限：(1) V8 采样剖面，wasm 函数按角色
识别（无类型模块带调试名；编译模块不带，故函数下标的角色从 wasm
文本读出：下标 9 与 10 以范围检查 `1024 <= p <= 536870904 && p & 7 == 0` 开头，是带防的 tag/field 读取辅助，1 与 7 分配并装箱，
26、27 按大小是 `listAppend` 与 `listDrop`，24、25 仅按大小推断
为 `listLen` 与 `listFirst`，54 是调用 9 的小型类型分派谓词，
56、57 是生成的程序体）；(2) wasmtime fuel 计数；(3) 提升程序的
重复计数（下）。样本为自身时间；微小叶函数可能少记。

**编译路线，wasm 自身时间占比（nqueens 8 / fannkuch-redux 7）：**

| 角色 | nqueens 8 | fannkuch 7 | 消除它需要什么 |
|---|---|---|---|
| tag 与 field 读取辅助（fn 9、10） | 24.5% | 25.6% | 折叠带防读取的冗余重载；在记录密集的 checker 上同类折叠发现带防调用约 50% 可折叠 |
| 分配与装箱（fn 1、7） | 10.5% | 19.4% | region 与独占性复用；非装箱 `i64` |
| 表辅助（fn 24-27） | 15.6% | 12.3% | O(1) cons 或扁平数组表示（此处代价是 `listAppend`/`listDrop` 复制） |
| 类型分派谓词（fn 54） | 6.8% | 10.1% | 同样的表示工作 |
| 生成的体（fn 56、57） | 33.8% | 20.1% | fuel 与调用开销加后端质量，此处不可分 |
| 其他 | 8.8% | 12.5% | |

**无类型降阶**：分配器 `$bump_val`（函数 2）在 nqueens 9 上占
25.3% 自身时间、fannkuch-redux 7 上 54.8%、rbtree 20000 上
66.6%；`list_concat` 在 nqueens 9 上 9.5%、fannkuch 上 5.1%；
名称比较（`$8`）在 rbtree 20000 上 6.2%。其内存是永不释放的
bump arena：nqueens 9 占 145 MB，fannkuch-redux 8 占 1.37 GB，
binary-trees 12 占 366 MB。

**仪器所示的与 Rust 的差距。** compiled/Rust 在 CPU 时间上为
281x 至 2786x、在指令数（去启动）上为 364x 至 1855x：差距主要在
指令数而非指令速度。编译输出内部，22% 至 25% 花在每次值读取的
检查上，10% 至 19% 在分配与装箱，12% 至 16% 在表复制。
fannkuch-redux 比 nqueens 差 5 倍比率，因下标在表上是 O(n) 且每
次前缀反转都重建表；这是表示代价而非代码生成代价。

**按这些程序上的实测占比排序的后续优化**（占比是收益上界；均未
应用）：(1) tag/field 读取辅助，22% 至 26%——折叠冗余重载可消除
记录密集 checker 上带防调用约 50%，若同比例成立此处约 11% 至 13%
（此处未测）；(2) 分配与装箱，10% 至 19%（region、uniqueness 复用、
非装箱 `i64`）；(3) 表复制辅助，12% 至 16%（O(1) cons 或扁平数
组）；(4) fuel 与调用开销不可分离，藏在 20% 至 34% 的生成体中。
此排序在这些程序上把表示与内存工作排在 fuel 削减之前；不支持
"先减 fuel"，但 fuel 份额未单独隔离。

**重复计数。** 小解释器（提升 wire 程序的这些程序所用算子）
重跑基准输入，统计在无 memo 下执行的每个 `call`、其中不同的
（callee，规范实参）对、以及每对经 memo 后要跑体的调用（命中跳过
体及其下全部）。结果与 wire 解释器在每行的值相符（已断言）。

| 程序，输入 | calls，无 memo | distinct（callee，args） | 重复调用占比 |
|---|---|---|---|
| nqueens 6 | 3,071 | 2,739 | 10.8% |
| nqueens 8 | 62,099 | 49,369 | 20.5% |
| fannkuch-redux 6 | 51,021 | 21,830 | 57.2% |
| binary-trees 10 | 547,542 | 1,407 | 99.74% |
| rbtree 2000 | 34,837 | 33,037 | 5.2% |

（fannkuch-redux 7 与 rbtree 20000 未能在会话内跑完解释器。）
binary-trees 上 memo 化消去近乎全部工作——正是 Game 禁止优化掉
的工作（"don't optimize away the work"）；记作数据点而非结果。
fannkuch-redux 的重复是表辅助（`nth`、`setNth`、`takeN`、`dropN`）
以相同小实参被调，不是重复排列。无重复时 memo 化代价 2 至 3 倍，
故在 rbtree 与 nqueens 上会输；在 binary-trees 与 fannkuch-redux
上按重复占比会赢。arena 路线的驻留是程序内部的同机制：结构相
等的节点合并成单个节点，而它使 binary-trees 比无类型模块慢 34 倍而
非更快，因为在该规模下查询比省下的分配更贵。

## 调用编解码：逐步代价对状态大小

**模块与 ABI。** 仪器是*钉定重建编译器*（3,576,344 B，种子引导
构建）从 4 份手写的单函数 RSCM 源（各 13 至 15 字节）生成的模块：
`bytes -> bytes` 恒等、`bytes -> i64`（`bytesLen`）、
`list i64 -> list i64` 恒等、`list i64 -> i64`（`listLen`）。每
个都是 V1 ABI（`SourceInvocationV1`：tag 1、fuel、参数个数、类
型化值；`bytes` 是 tag 11，表是 tag 3、每元素带 tag 字对）的
生成调用解码器与 V2 结果包（值种类、体长、体）写出器——正是钉定
runner 所查的 ABI。剖面 `bootstrap512`（public memory 8192
pages）。node v26.12.0 的 V8 中计时，只测 `compile()`，每次重复
新实例，输入的主机拷贝与 instantiate 时间不计（instantiate 在末
列）。只测解码的行取结果 `i64`，其包 32 字节，故其时间为解码器
加 O(1)。21 次取最小；负载均值约 29。

| 状态（wire 字节） | bytes: 解码 ms | bytes: 解码+写 ms | bytes: 写 ms（差） | list: 解码 ms | list: 解码+写 ms | list: 写 ms（差） | instantiate ms（min） |
|---|---|---|---|---|---|---|---|
| 0（0 / 0 元素） | 0.006 | 0.005 | `-0.001` | 0.004 | 0.004 | `-0.001` | 0.06 |
| 3000（3000 / 187 元素） | 0.019 | 0.024 | 0.005 | 0.008 | 0.016 | 0.007 | 0.05 |
| 50000（50000 / 3125 元素） | 0.077 | 0.179 | 0.102 | 0.063 | 0.099 | 0.036 | 0.07 |
| 800000（800000 / 50000 元素） | 0.836 | 2.095 | 1.259 | 0.902 | 1.387 | 0.485 | 0.18 |
| 3000000（3000000 / 187500 元素） | 3.088 | 8.161 | 5.073 | 3.452 | 5.475 | 2.024 | 0.56 |

3 MB 处每 MB：bytes 解码 1.03、写 1.69、往返 2.72；list 解码
1.15、写 0.67、往返 1.83 ms/MB；800 KB 处：bytes 往返 2.10 ms、
list 1.39 ms。

**解读。** 解码器与写出器随状态线性，0.01 ms 以上无可见固定开销。
3 MB 处每 MB：bytes 解码 1.03 ms、写 1.69 ms、往返 2.72 ms；
`i64` 表解码 1.15 ms、写 0.67 ms、往返 1.83 ms。800 KB 处往返
2.10 ms（bytes）与 1.39 ms（list）。运行时的工作界约为每 MB 每步
1 至 3 ms、1 MB 处 3 ms 上限：**测量落在界内**（1.8 至 2.7
ms/MB；800 KB 处 1.4 至 2.1 ms，低于 3 ms 上限；3 MB 花 5.5 至
8.2 ms，超过上限）。Instantiate 为 0.05 至 0.9 ms，不随状态增
长。

**V1 能走多远。** 这是钉定 runner 所用的 V1 调用加 V2 结果，在*生成的*模块上。未确立：(1) 候选编译器模块（4,851,154 B，32768
pages）**未被驱动**：其 `compile` 对 2 参数编译器调用与 6 参数全
`bytes` 调用（试过 3 种变体）返回 16 字节的 `0x82` 拒绝；其可用的
6 槽调用由运行时适配器中的前导构造，其构造未完整阅读。(2) 只计时
了 `bytes` 与 `list i64` 共 2 种状态形，未测记录或和；嵌套状态
（arena 路线的记录套表）在规模 2000 时见到 21.8 MB 输出代价，未计
时。(3) V2 未在此 head 确立，故所测写出器是重建编译器为 runner
所期望的 V2 包生成的那个，不是冻结的 V2 写出器。(4) 仅 V8；未对
同批模块做 wasmtime 检查。(5) 负载中的机器。

## 未测量项

同批程序的 Zig、Koka、OCaml、Lean 构建（对比只保留 Rust 作参
考语言；同套件的 Koka 列由 `benchmarks/koka/` 单独测量）；
pidigits 的性能运行（只做正确性：30 与 10000 位）；语料程序在
wasm 路线上（覆盖行停留在 READ 级的"现可写"，类型化发射列除外，
它们是实测）；fannkuch-redux 7 与 rbtree 20000 的重复计数；codec
节的候选编译器模块；独占机器上的交付数字；Game 的 flags
`target-cpu=ivybridge` 下的 Rust（在 arm64 上无效）。

## 参考

- The Computer Language Benchmarks Game —— binary-trees、
  fannkuch-redux、pidigits 的程序描述页
  （`benchmarksgame-team.pages.debian.net/benchmarksgame/description/`），
  2026-11-04 抓取；Game 的输出文件与已发布的 Rust 条目是表中引用
  的逐字节相等与范围参照。
- Koka —— `koka-lang/koka`，发布版 `v3.2.9` 的 `test/bench/`
  （PLDI'21 Perceus 基准套件：nqueens、rbtree、rbtree-ck、deriv、
  cfold）；A. Reinking, N. Xie, L. de Moura, D. Leijen. Perceus: garbage
  free reference counting with reuse. *PLDI*, 2021。
- OEIS A000170 —— 套件打印的 n-queens 解数。
- 读过而未采纳的套件（理由见上文）：S. Marr, B. Daloze,
  H. Mössenböck. Cross-language compiler benchmarking: Are we fast
  yet? *DLS*, 2016（`smarr/are-we-fast-yet`）；attractivechaos.
  plb2: a programming language benchmark. GitHub
  `attractivechaos/plb2`, 2023；hanabi1224.
  Programming-Language-Benchmarks: yet another implementation of
  the computer language benchmarks game. GitHub
  `hanabi1224/Programming-Language-Benchmarks`, 2021；kostya.
  benchmarks: some benchmarks of different languages. GitHub
  `kostya/benchmarks`, 2014。
- `benchmarks/MANIFEST.tsv` —— 本目录每个源的逐程序出处（上游路
  径、许可证、移植作者）。
- `release/docs/TESTING` —— 语料在发布内的核对方式。

closure_claim = 0.
