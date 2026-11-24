# 致谢与参考

[English](ACKNOWLEDGEMENTS.md) | 中文

Residua 为研究项目，建立在许多其他工作之上。本文件按我们的记录，列出所有被我们移植过代码、被用作测试参照（oracle）的工具或数据，
以及我们研究过其设计的项目。每个版本逐文件的记录，见该版本中的 `release/NOTICES.md` 和 `release/PROVENANCE.tsv`。下文提到的论文，
其文献条目见 [docs/OVERVIEW.zh-CN.md](docs/OVERVIEW.zh-CN.md#参考文献) 的参考文献。

**如果你发现我们使用了你的代码或思想却没有在这里致谢，请告诉我们**：在本仓库开 issue，或使用私密漏洞报告。我们会补上致谢，并更正相应的发布。

## 移植进 Residua 的代码（许可证以上游发布为准）
- Lean 4 — leanprover/lean4（Apache-2.0）：编译器 IR 的各遍（引用计数、借用、reset/reuse、死代码消除、case 化简、代码生成），移植为
  `lib/lrc/`；基础数据表示；内核算法的部分内容作为参照。
- Koka — koka-lang/koka（Apache-2.0）：基准程序；Perceus 引用计数模型（Reinking、Xie、de Moura、Leijen，PLDI 2021）。
- Bend / HVM2 — bendlang/bend（Apache-2.0）：基准程序；Taelin 等人的论文。
- The Computer Language Benchmarks Game — benchmarksgame-team（BSD-3-Clause）：基准程序。
- earley-lean — Daniel1854/earley-lean（Apache-2.0）：Earley 解析器。
- elaboration-zoo 和 smalltt — AndrasKovacs（BSD-3-Clause、MIT）：推导（elaboration）算法。
- Cedar — cedar-policy/cedar-spec（Apache-2.0，证明已重新检查）和 cedar-integration-tests（测试参照）。
- lean-regex — pandaman64/lean-regex（Apache-2.0，证明已重新检查）。
- matching-logic-lean — eveil-labs（Apache-2.0）。
- CosmWasm cw-plus（Apache-2.0）：合约代码和测试参照。
- libuv（ISC）：地址表示，用于应用目录。

## 用作测试参照的工具和数据（不作为代码发布）
- Lean 4 内核和工具链、Lean4Lean（digama0/lean4lean）、Mathlib、Batteries、Aesop、quote4、ProofWidgets4、plausible、
  import-graph、LeanSearchClient、lean4-cli、LNSym。
- wasmtime（Apache-2.0 WITH LLVM-exception）和 binaryen（Apache-2.0）：种子配方各下载一个钉住版本，用来运行种子。
- WebAssembly Binary Toolkit（WABT，Apache-2.0）：基准套件下载钉住版本，用来构建它的原生可执行文件。
- K 框架、KEVM、KWasm、kevm-plugin、proof-generation（Runtime Verification）；Metamath（metamath-exe 和数据库）。
- HTTP：llhttp（经由 httptools）、h11、hyper、hyper-util、http-body-util、tokio、bytes、oha。
- z3、verina、serde_json、schemars、anyhow。

## 研究过的设计与论文
- Lean Kernel Arena（leanprover/lean-kernel-arena）和 nanoda：作为内核检查器的参照。
- Perceus 和 FBIP（Koka 的论文）；Lean 4 的编译器（lambda-RC IR）。
- h5i（h5i-dev/h5i，Apache-2.0）：经验证的 HTTP 内核；我们的 web 实验以它的请求策略为模型。
- Ninja-go 和 ABFS（Google）：分阶段的内容寻址动作缓存。
- Bazel、Buck2、Nix：动作键和输入寻址。Salsa：增量计算。
- Datomic 和 DataScript（tonsky/datascript）；Prolly 树（Dolt/Noms）；Merkle Search Trees（Auvolat、Taïani，2019）；
  DBSP（Budiu 等，VLDB 2023）。
- CakeML（经验证的自举）；Zig（从提交的种子自举）。
- 基准集合：plb2、Programming-Language-Benchmarks、kostya/benchmarks、are-we-fast-yet。
- 设计笔记中引用的其他资料：CPython 文法、XNU Mach-O 头文件、Berkeley SoftFloat 与 IEEE 754、Knuth《TAOCP》4.3.1、
  ring（Clojure）、rust-lang/regex、Chen 等人的 OOPSLA'23 artifact。
