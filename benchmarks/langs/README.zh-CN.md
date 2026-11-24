# benchmarks/langs —— 参考列的上游套件收录

0.1 性能记录的参考语言列：套件程序——rbtree、rbtree-ck、
nqueens、cfold、deriv、binarytrees——按记录的规则（1 台 VM、单钉
核、timecell 5 遍取中位、整进程 wall、峰值 RSS、代码字节）在所钉
`第三方套件自带的每种语言下编译并运行`。

## 来源（逐字收录、未改动）

- `src/koka/test/bench/{cpp,haskell,java,ocaml,swift}/` —— Perceus
  套件，出自 `koka-lang/koka` 提交
  `facb7932ce6871fdb063f762a304bd8238f35fba`（tag `v3.2.9`，Koka
  列自身的钉）。每语言 6 程序；`java/rbtreeck.java` 保留其上游名。
- `src/lean4/tests/bench/` —— `binarytrees.lean`、
  `const_fold.lean`（套件的 cfold）、`deriv.lean`、`rbmap.lean`
  （rbtree）、`rbmap_checkpoint.lean`（rbtree-ck），连同其 `.args`
  与 `.expected.out`，出自 `leanprover/lean4` tag `v4.14.0` 提交
  `410fab7284703f41660ca2454218dcca9b2ec896`。Lean 列没有 nqueens
  程序（所钉套件中没有）：空单元。
- Rust：上级目录中的
  `benchmarks/rust/{rbtree,rbtreeck,nqueens,binarytrees,cfold,deriv}.rs`
  —— 对比所引用的参考移植（rustc
  `-C opt-level=3 -C codegen-units=1`）；不重复收录。

## 运行

测量作业在 1 台 VM 上运行：把所钉工具链安装到
`$LANGS_STATE/toolchains`（版本逐次记录于 `pins.txt`），编译每个
（语言，程序）对，然后串行测量：`benchmarks/koka/` 的
`timecell.c`，单钉核上 5 轮，`ulimit -s unlimited`，每单元 1 次值
检查（程序打印数字对套件规范值）。单元与原始重复落在
`$LANGS_STATE/<runtag>/cells/` 并拷回。2 台 VM 上 2 次运行；相差超
过 10% 的单元重跑。

`state/` 为生成物且不跟踪。永不提交构建输出、工具链或下载的归档。
