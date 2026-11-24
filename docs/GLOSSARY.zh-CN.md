# GLOSSARY — 术语表

[English](GLOSSARY.md) | 中文

- **q** — 对象的内容地址：`docs/QFORMAT.zh-CN.md` 中带类型、带版本的 q 格式 v1，建立在 SHA-256 摘要之上。
- **qbe** — `-qbe` 基准变体所经由的后端层。
- **rsd** — Residua 的语言与工具链。
- **rsx** — rsd 项的规范语法树（依赖类型论）。
- **scm** — 每个程序都被降到的、擦除后的函数核。
- **lambda-RC** — 带引用计数与原地复用的函数式 IR。
- **wasm0** — 编译器发射的 WebAssembly 整数核子集。
- **种子（seed）** — 提交的、能重建编译器的 wasm 模块。
- **不动点（fixed point）** — 编译器由自身构建等于自身，逐字节。
- **封签（Seal）** — 独立模型族对候选发布的评审签名。
- **残余项（Residue）** — 被命名、被记录的局限或未决项，绝不沉默。
- **阶段字（Stage word）** — 产出一个镜像的编译器阶段修订的标识。
- **R-CIC** — Residua 的、用于 Lean 兼容证明的内核检查器
  （未随附）。
- **rscm** — 前端发射的 `.rscm` 模块：为后端编码的 scm。
- **模板（stencil）** — 后端实例化的、钉住的程序片段。
- **回执（receipt）** — 一次检查运行的签名机器可读记录，与其所查
  字节绑定。
- **孪生端（twin）** — 差分检查中与被随附前端对照运行的 OCaml 参考前端。
- **ExecModel** — NF 准入检查所建立的执行模型实例；各层状态见
  `docs/RELEASE-NOTES.zh-CN.md`。
- **MST-NF** — NF 结果所归入的范式组合定理框架；证明由上游仓库
  `https://github.com/residua-labs/MST-NF` 持有（钉住提交 `4432a34`）。
