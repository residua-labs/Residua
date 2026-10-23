# Residua

[English](README.md) · **中文**

**一个自身可靠性被证明了的证明内核：机器生成的证明，可以被检查，而不是被相信。**

这里是 Residua 的公开仓库。目前收录的是 **R-CIC**：Residua 证明内核所检查的那门依赖类型论的 Lean 4 元理论。其他组件经过验收后陆续发布，见下文"发布状态"。

## 为什么

Lean、Coq 这样的证明助手，都建立在一个用 C++ 或 OCaml 写的小内核上，由它检查每一个证明。这个内核是被相信的，而不是被证明的。当证明主要由机器、越来越多地由 AI agent 产生，数量远超人能阅读时，所有东西都依赖于这个被相信的内核。

Residua 的做法是让内核本身成为被证明的对象：

- **R-CIC** 是一门归纳构造演算，为一个小的、全函数的、内容寻址的内核设计。它的目标输入，就是外部 Lean 检查器所消费的那份 Lean 导出。
- 内核的可靠性在本仓库里用 Lean **证明一次**，并按内容哈希钉住，不需要每次检查都重新论证。
- 真正运行的检查器，应当**由已证明的定义生成**，而不是手写。语言链条绝不手写。
- 当内核由 Residua 经过验证的自举编译器编译出来，并能独立检查 Lean 导出时，Lean 就从可信基里退出，成为导入数学的**预言机**。这最后一步还在计划中，尚未完成，见信任表。

Residua 的每个组件都是 [MST-NF](https://github.com/residua-labs/MST-NF)（Minimal Structure Theory Normal Form，最小结构理论范式）的实例：每个输入要么以规范形式被接受，要么带着具名理由被拒绝，绝不悄无声息。

## R-CIC 的现状

状态按每一条说法报告，从不往上取整。整个仓库的 `closure_claim = 0`。

**可靠性层：**发布所需要的那一层，即"R-CIC 接受的东西是可靠的"。

| 合取项 | 陈述 | 状态 |
|---|---|---|
| F1 | 被接受的 `infer` / `check` / `whnf` / `conv` 结果都带有声明式推导 | 对参考机器**已证**：RM015T / RM016T（infer、check），以及 `RM014T'_whnf_conv`、`RM017T'_conv`、`RM017T'_tyConv`（`lean/rcic/RcicCertKernel.lean`），不带作用域前提 |
| F2 | 实际运行的检查器由那台机器生成，而不是手写 | **进行中**：生成的检查器模块及其与 Lean 机器的差分对照正在审阅；当前部署的 SCM 检查器仍是手写的 |
| F3 | 一致性：在无公理的良构环境里，不存在 `False` 的封闭证明 | **进行中**：一个集合模型已经对几类归纳组证明了这一点；其余类别和覆盖定理正在推进 |

F3 是相对一致性结果：它相对于写明的模型前提成立，并且每次只针对一个宇宙上界，这是哥德尔第二不完备定理所要求的。

**完整闭合：**理论的三条内核"行"在全部良构环境上成立（apex 谓词 `NativeRCICClosed`）。

- 在**所有通过作用域检查的良构环境上，这三行都已证明**（`typedRowsWf_of_scopeCheck`）。
- 超出作用域检查的部分是**开放的**。其中最难的一块，是在任意 sort 上存在 Lean 式 `Eq` 和 `Acc` 时的单射性，这在文献中是一个公开问题。
- 这一点如实报告为开放。apex 永不改写。

## 当前的信任边界

| 组件 | 需要信任的东西 |
|---|---|
| R-CIC 元理论（本仓库） | Lean 4 内核和 seal 过的 Lean 证明；除非定理另有说明，公理限于 `propext`、`Quot.sound` |
| 当前部署的 SCM 检查器 | 手写代码，正在被生成的代码替换（F2） |
| 作为导入证明来源的 Lean | 仍在可信基内，直到内核由经过验证的自举编译器编译出来，并能独立检查 Lean 导出 |

## 构建

```
lake build RCIC
```

seal 文件 `lean/rcic/RcicKernelSeal.lean` 检查每一条 seal 过的定理都存在，并且公理在允许的范围之内。[`lean/rcic/README.md`](lean/rcic/README.md) 说明这门理论本身、已经证明了什么、排除了什么，以及文件怎样组织；[`lean/rcic/MODULES.md`](lean/rcic/MODULES.md) 列出每一个模块。

## 发布状态

Residua 按版本发布，从 **0.1** 开始：每个版本包含该版本的自举编译器、R-CIC 的当前状态和它们的依赖闭包，并各自附带信任表。在 0.1 通过验收之前，本仓库镜像的是 R-CIC 的开发状态。

## 相关仓库

- [MST-NF](https://github.com/residua-labs/MST-NF)：Residua 每个组件所实例化的范式。已闭合并发布。
- [RCC](https://github.com/residua-labs/RCC)：相对闭合演算（Relative Closure Calculus）。对说法和证明的闭合是计算出来的，不是声称出来的。
- [residua-sdk](https://github.com/residua-labs/residua-sdk)：从宿主语言中嵌入 Residua。

## 许可

Apache-2.0。见 [LICENSE](LICENSE) 和 [NOTICE](NOTICE)。

