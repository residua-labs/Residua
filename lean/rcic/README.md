# RCIC: the R-CIC kernel theory

A Lean 4 formalization of **R-CIC-0**, the dependent type theory that the Residua proof kernel targets. R-CIC-0 is a calculus of inductive constructions with:

- dependent functions, a universe hierarchy, `let`, and content-addressed constants;
- transparent definitions, and rigid theorem/opaque members;
- function η, definitional proof irrelevance, and canonical literals;
- one indexed inductive family per declaration group, with strict positivity, kernel-derived recursors, ι-reduction and a fixed `Prop` elimination policy.

This directory holds:

- the declarative theory: typing `HasTyT`, conversion `ConvT`, context and environment well-formedness;
- typed parallel reduction and its inversions;
- the reference checking machine and its soundness;
- the inductive-admission rules;
- the ongoing work on the three kernel rows: sort inversion (`sortRow`), Π-injectivity (`piRow`) and family-application injectivity (`famAppRow`).

## Status

`closure_claim = 0`. The three kernel rows are **open**.

What is here is a set of kernel-checked results together with named open walls. Open walls appear as named `Prop`s or explicit hypotheses of the theorems that use them. A result whose premise is an open wall is a conditional result, not a closure.

## What is *not* claimed

- **Not a closure.** The three kernel rows are open. Their named walls are stated as `Prop`s in the modules and are not assumed anywhere as axioms.
- **Not the live checker.** This is the target theory. The checker that Residua runs today is a separate, smaller fragment.
- **Not the runtime.** Modules that depend on Residua's runtime, bootstrap or admission layers are not included.
- **Many named interfaces are open.** Many modules name interfaces whose later obligations are deliberately left open. Read each module's docstring for its exact scope.

## Trust base

- Lean 4 core only (`leanprover/lean4:v4.14.0`). No Mathlib, no dependencies.
- No `sorry`, `admit`, `axiom` declarations, `native_decide` or `implemented_by` in the sources. The `rcic-source-check` workflow enforces this on every push.
- Object-language axioms are environment members (`EnvWfT.axiom`), which are data, not Lean axioms.
- The seal (below) bounds the axioms of every sealed theorem by `propext` and `Quot.sound`. None uses `Classical.choice`.

## Build

The only dependency is the Lean toolchain pinned in `lean-toolchain` (Lean 4.14.0). There are no Lake packages, and no Mathlib.

```sh
lake build RCIC
```

A cold build compiles about 1,360 modules and needs a large-memory machine; the seal alone takes about 40 minutes on one core. For this reason, continuous integration currently runs only the source check. The full build is run locally.

`lean/rcic/RcicKernelSeal.lean` is the seal. Building it checks two things:

- every sealed theorem (about 31,000) depends only on the axioms `propext` and `Quot.sound`;
- the structural guards hold:
  - no judgment constructor mentions a machine artifact;
  - every entry-adding `EnvWfT` constructor carries its admission premise.

## Layout

- `lean/rcic/`: the theory, one module per file.
  - `Rcic*` modules: the calculus and its metatheory.
  - `ScmSrcGroups*` and the other `Scm*` modules here: the source environments and the SCM machine model that the kernel results are stated over.
- `lean/Residua/SHA256.lean`: the SHA-256 model used for content addresses.

## Provenance

This directory mirrors `lean/rcic` of the Residua development tree at commit `0335be80845919c06dc48276e8e96ddbfe33c483`. It is regenerated from there after each landing. Every Lean file except the seal is byte-identical to the development tree.

It holds exactly the modules whose import closure stays inside `lean/rcic` (plus `Residua.SHA256`). The modules that also depend on Residua's runtime, bootstrap and admission layers are not published yet: Apex, SCM certificate and contract checking, the optimized kernel, and Forge.

The seal is the development tree's foundation seal restricted to these modules.

## License

Apache-2.0. See `LICENSE` and `NOTICE` at the repository root.
