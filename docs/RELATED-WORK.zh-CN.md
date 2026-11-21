# RELATED WORK — Residua 取用了什么，又如何不同

[English](RELATED-WORK.md) | 中文

- **Lean 4** — 内核规则、解析器、IR 设计（lambda-RC）与基本数据
  表示取自于它。Residua 的不同在于跨版本按内容识别身份，以及
  自我复现的种子。
- **CakeML 与 CompCert** — 验证编译是逐层跳转的范本；Residua 尚
  没有端到端的正确性证明。
- **Zig** — 提交的、能重建编译器的 wasm 种子是 Zig 的做法。
- **可自举构建**（stage0、GNU Mes、Guix 全源码引导）— 它们把
  二进制种子缩减到可直接审计的几百字节；Residua 的种子更大，其
  信任改为落在不动点与复现上。
- **Koka 与 Perceus** — 带复用的引用计数；Koka 是性能记录中的
  参照（`docs/PERF-RECORD.md`）。
- **lean4lean、nanoda** — 独立的 Lean 内核，用作 R-CIC 的交叉
  检查。
