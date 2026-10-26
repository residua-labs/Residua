# Residua

**English** · [中文](README.zh-CN.md)

**A proof kernel whose own soundness is proved, built so that machine-produced proofs can be checked rather than trusted.**

This repository is the public home of Residua. Today it contains **R-CIC**: the Lean 4 metatheory of the dependent type theory that the Residua proof kernel checks. More components are published as they are accepted; see *Release status* below.

## Why

Proof assistants such as Lean and Coq rest on a small kernel, written in C++ or OCaml, that checks every proof. The kernel is trusted, not proved. Once proofs come mostly from machines, and increasingly from AI agents producing far more than anyone can read, that trusted kernel is the point everything else depends on.

Residua's answer is to make the kernel itself an object of proof:

- **R-CIC** is a calculus of inductive constructions designed for a small, total, content-addressed kernel. Its target input is the same Lean export that external Lean checkers consume.
- The kernel's soundness is proved **once**, in Lean, in this repository, and pinned by content hash instead of being re-argued for each check.
- The checker that actually runs is meant to be **generated from the proved definitions**, not written by hand. The language chain is never hand-written.
- Once the kernel is compiled by Residua's verified bootstrap compiler and checks Lean exports on its own, Lean becomes an **oracle** for imported mathematics instead of part of the trusted base. That last step is planned, not done; see the trust table.

Every component of Residua is an instance of [MST-NF](https://github.com/residua-labs/MST-NF) (Minimal Structure Theory Normal Form): each input is admitted in canonical form or refused with a named reason, never silently.

## Where R-CIC stands

Status is reported per claim and never rounded up. `closure_claim = 0` for the repository as a whole.

**The soundness tier:** what a release needs. "What R-CIC accepts is sound."

| Conjunct | Statement | Status |
|---|---|---|
| F1 | an accepted `infer` / `check` / `whnf` / `conv` result carries a declarative derivation | **proved** for the reference machine: RM015T / RM016T (infer, check) and `RM014T'_whnf_conv`, `RM017T'_conv`, `RM017T'_tyConv` (`lean/rcic/RcicCertKernel.lean`), with no scope premise |
| F2 | the checker that runs is generated from that machine, not hand-written | **in progress**: the generated checker modules and a differential against the Lean machine are in review; the currently deployed SCM checker is still hand-written |
| F3 | consistency: no closed proof of `False` in an axiom-free well-formed environment | **in progress**: a set model proves it for several classes of inductive groups; the remaining classes and the coverage theorem are being worked on |

F3 is a relative consistency result: it holds relative to explicit model premises and one universe bound at a time, as Gödel's second incompleteness theorem requires.

**Full closure:** the theory's three kernel rows over every well-formed environment (the apex predicate `NativeRCICClosed`).

- The rows are **proved for every well-formed environment that passes a scope check** (`typedRowsWf_of_scopeCheck`).
- Beyond the scope check they are **open**. The hardest part, injectivity in the presence of Lean-style `Eq` and `Acc` at every sort, is an open problem in the literature.
- This is reported as open. The apex is never relabelled.

## Trust boundary today

| Component | What is trusted |
|---|---|
| R-CIC metatheory (this repository) | the Lean 4 kernel and the sealed Lean proofs; axioms within `propext`, `Quot.sound` unless a theorem says otherwise |
| the deployed SCM checker | hand-written code, being replaced by generated code (F2) |
| Lean as the source of imported proofs | still in the trusted base, until the kernel is compiled by the verified bootstrap and checks Lean exports independently |

## Build

```
lake build RCIC
```

The seal `lean/rcic/RcicKernelSeal.lean` checks that every sealed theorem exists and that its axioms are within the allowed set. [`lean/rcic/README.md`](lean/rcic/README.md) describes the theory, what is proved, what is excluded and how the files are organised; [`lean/rcic/MODULES.md`](lean/rcic/MODULES.md) lists every module.

## Release status

Residua is released in versions, starting with **0.1**: the bootstrap compiler at that version, R-CIC in its current state, and their dependency closure, each with a trust table. Until 0.1 is accepted, this repository mirrors R-CIC's development state.

## Related repositories

- [MST-NF](https://github.com/residua-labs/MST-NF): the normal form every Residua component instantiates. Closed and published.
- [RCC](https://github.com/residua-labs/RCC): the Relative Closure Calculus. Closure of claims and proofs is computed, not asserted.
- [residua-sdk](https://github.com/residua-labs/residua-sdk): embedding Residua from host languages.

## License

Apache-2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).

<!-- BEGIN RCIC -->
_R-CIC mirror: `lean/rcic/` is synced one way from Residua `0874fdae50`. Build: `lake build RCIC`._
<!-- END RCIC -->
