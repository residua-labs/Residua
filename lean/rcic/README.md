# RCIC: the R-CIC kernel theory

This directory is the Lean 4 metatheory of **R-CIC-0**, the dependent type theory that the Residua proof kernel checks.

It does three things:

- it states the theory as a declarative calculus;
- it proves the theory's metatheorems;
- it proves that the kernel's reference checking machine is sound with respect to the calculus.

**Status:** `closure_claim = 0`. The metatheory reduces to three *kernel rows*. The rows are proved for every well-formed environment that passes a scope check. What is open is the rows for **every** well-formed environment. See [Current status](#current-status).

## Why Residua needs a kernel

Residua is a small, pure, total, first-order language in which a computation's content hash `q` identifies it exactly. Residua programs come with correctness claims: totality, exact outcome contracts, and refusal of named failure cases. For those claims to be checked inside Residua itself, rather than trusted, Residua needs a proof kernel written in its own SCM language and running on its own substrates. That kernel is a dependent type checker, and R-CIC-0 is the theory it checks.

The scope was settled on 2026-08-26: the in-SCM kernel targets **full CIC**, and its concrete closure criterion is that **it checks a Lean export**, the same input that external Lean checkers consume. Three bindings stay in force alongside that scope:

- the kernel is fuel-bounded, because a total language cannot host unbounded reduction;
- it is built only by composing existing SCM operators;
- its soundness for CIC is validated **once**, in Lean, and the result is pinned by content hash, instead of being re-run per check.

This directory is that one-time validation: the place where the theory and the machine are related by kernel-checked proofs.

## What R-CIC-0 is

R-CIC-0 is a calculus of inductive constructions with:

- dependent functions, a universe hierarchy with `imax`, `let`, and content-addressed constants;
- transparent definitions, and rigid theorem/opaque members;
- function η, definitional proof irrelevance, and canonical literals;
- one indexed inductive family per declaration group, with strict positivity, kernel-derived recursors, ι-reduction, and a fixed `Prop` elimination policy.

It deliberately leaves out mutual and nested inductives, projections, structure η, `Quot`, classical choice, `propext`, metavariables, tactics, unsafe declarations, and general recursion.

The specification is layered, and this directory formalizes the first layers:

| layer | name | what it fixes |
|---|---|---|
| declarative calculus | `D-RCIC-0` | which terms are well typed, and which well-typed terms are convertible |
| algorithm profile | `A-RCIC-0` | how a checker decides those judgments |
| reference machine | `K-Ref-RCIC-0` | the fuel-bounded checking machine |
| artifacts | `K0.scm`, `K0.wasm` | the SCM kernel and its compiled form; not in this directory |

## What is proved here

- **The declarative theory** (`RcicDeclarative`, `RcicTyped*`, `RcicLevelCalc`):
  - expressions, levels, environments and contexts;
  - typing `HasTyT`, conversion `ConvT`, type conversion `TyConvT`;
  - context and environment well-formedness `CtxWfT`, `EnvWfT`.
- **Inductive admission** (`RcicIndGroupJudgment`, `RcicInductivePolicy`, `RcicIota*`):
  - strict positivity and derived recursors;
  - ι-reduction through admitted witnesses;
  - the environment's admission premises.
- **Metatheory:**
  - typed parallel reduction (`RcicParRedT*`) and its inversions;
  - weakening and substitution;
  - one-step and multi-step subject reduction;
  - type uniqueness and the absence of cumulativity, each from the rows below (`DT012T_type_uniqueness_of_sortRow_piRow`, `DT021T_no_cumulativity_of_sortRow`).
- **Machine soundness** (`RcicMachine*`, `RcicTypedMachine*`): the reference machine's reduction and acceptance steps imply the declarative judgments.
- **Source environments** (`ScmSrcGroups*`) and the **SCM machine model** (`Scm*`) that these results are stated over.

Every result above is kernel-checked, and the seal (below) bounds its axioms.

## The three kernel rows

The metatheory reduces to three properties of type conversion. They are collected in `TypedRowsWf` (`RcicTypedRowsWf`):

```lean
-- sortRow: convertible sorts have equal levels
∀ {Γ}, CtxWfT E n Γ → ∀ {u v}, TyConvT E n Γ (.sort u) (.sort v) → eqN u v

-- piRow: Π-injectivity
∀ {Γ}, CtxWfT E n Γ → ∀ {A B A' B'},
  TyConvT E n Γ (.pi A B) (.pi A' B') →
  Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B')

-- famAppRow: injectivity of a full application of an inductive family
-- (equal levels, equal lengths, pointwise-convertible arguments)
```

Subject reduction and type uniqueness are proved from the rows (`DT010T_one_step_subject_reduction_of_typedRowsWf`, `DT011T_multi_step_subject_reduction_of_typedRowsWf`, `DT012T_type_uniqueness_of_sortRow_piRow`).

The rows are where the hard part of CIC metatheory lives here. This theory has definitional proof irrelevance and η. Under those, untyped conversion is not confluent, so the usual Church–Rosser route to injectivity is not available as is.

For environments outside the scope check (next section), `RcicKernelRowsAssembly` assembles `TypedRowsWf` for every well-formed environment from three remaining inputs:

1. `AllBelowScoped`: the target of the sortRow closer below;
2. `PiConvValleyData`: Π-convertible types have a common parallel reduct;
3. `FamRelevantSlotConv`: convertibility at the relevant argument slots of a family application.

## Current status

**Proved within the scope check.** `typedRowsWf_of_scopeCheck` (`RcicTypedScopeCheck`) proves all three rows for every `EnvWfT` environment that passes the scope check `EnvWfT.ScopeCheck`.

- **How.** The proof is a logical relation on an annotated copy of the theory (`RcicAnn*`). Π-injectivity is a corollary of its fundamental lemma (`tyConvA_pi_inj`).
- **Consequence.** On those environments, subject reduction and type uniqueness hold without further premises (`DT010T_one_step_subject_reduction`, `DT011T_multi_step_subject_reduction`).

**Open: the rows over every well-formed environment.** The scope (`EnvWfT.InScope`, `GroupInScopeT`) leaves out three kinds of inductive group that admission accepts:

- groups with function-recursive fields;
- groups whose recursive fields are reached only by δ-reduction;
- groups that fail the elimination profile.

One admitted environment shows that the annotated model cannot simply be stretched further. It is a recursive proposition with a large-eliminating recursor. There, a proposition is convertible to its own self-arrow, and the model's semantic environment is provably empty (`pinLoop_envSem_false`).

So the open part is concentrated in specific classes of inductive declarations, and in how the theory's elimination policy treats them.

**Work toward the full rows** runs along three lines:

- **A scope-free sortRow closer** (`RcicSyn*`).
  - It issues induction-hypothesis queries on strictly smaller derivations through a proof-erasing translation. The erased calculus is confluent, and erased Π-inversion holds in it.
  - What remains is a set of narrow named obligations: alignment of the erasure with environments, substitutions and display contexts. Several reduce to sort uniqueness on strict subderivations, which the closer must obtain from its own induction hypothesis.
- **A semantic observation model** (`RcicNativeTypedModel*`).
  - Types and terms are observed at typed demands. It is aligned to `ConvT`: ι only through admitted witnesses, K only where derivable. Universe levels are carried in its codes. Completeness is proved on fragments.
  - The global question is open, including whether stuck terms with identical observations can fail to be convertible.
- **Valleys** (`RcicNativeKProjection`, `RcicNativePiValleyContract`).
  - `PiConvValleyData` (Π-convertible types have a common parallel reduct) is, under the sorting premises, inhabited exactly when Π-injectivity is (`nonempty_piConvValleyData_iff_piInj`). It is an equivalent interface, not a reduction.

**Measured negatives.** Several natural formulations turned out to be false. They are kept as kernel-checked refutations, and they explain the shape of the statements:

- raw reduction is not confluent (`admitted_no_raw_star_confluence`);
- general native conversion valleys fail at an admitted environment (`admitted_no_nativeConvValleyData`);
- an unguarded Π-row contract is uninhabited (`RcicPiRowInjTRefutation`);
- the annotated model fails at the large-eliminating recursive proposition above (`pinLoop_envSem_false`).

No result here claims closure. A theorem whose premise is an open wall is conditional, and the wall is a named `Prop` or an explicit hypothesis.

## How the work is done

- **Kernel-checked only.** No `sorry`, no `Classical.choice`, and no Lean `axiom` declarations. Object-language axioms are environment members (`EnvWfT.axiom`): data, not Lean axioms.
- **Statements are never weakened after landing.** A corrected statement gets a new name, and the old one stays.
- **Refutations count only when every premise is inhabited.** A counterexample that assumes something false refutes nothing.
- **Independent review.** Each change is reviewed by someone other than its author before it lands, and the review is pinned to the exact commit that lands.

## Trust base

- Lean 4 core only (`leanprover/lean4:v4.14.0`). No Mathlib, no dependencies.
- No `sorry`, `admit`, `axiom` declarations, `native_decide` or `implemented_by` in the sources. The `rcic-source-check` workflow enforces this on every push.
- The seal bounds the axioms of every sealed theorem by `propext` and `Quot.sound`.

## Build

```sh
lake build RCIC
```

A cold build compiles about 1,360 modules and needs a large-memory machine. The seal alone takes about 40 minutes on one core. Continuous integration currently runs only the source check; the full build is run locally.

`lean/rcic/RcicKernelSeal.lean` is the seal. Building it checks two things:

- every sealed theorem (about 31,000) depends only on `propext` and `Quot.sound`;
- the structural guards hold:
  - no judgment constructor mentions a machine artifact;
  - every entry-adding `EnvWfT` constructor carries its admission premise.

## Where to start reading

`RcicCore` imports exactly the core results: the in-scope rows, subject reduction, type uniqueness and machine soundness, about 190 modules. It is grouped by layer: `RcicCoreSyntax`, `RcicCoreEnv`, `RcicCoreJudgments`, `RcicCoreRelation`, `RcicCoreRows`, `RcicCoreMetatheory`, `RcicCoreMachine`. To build only the core, run `lake build RCICCore`.

`lean/rcic/MODULES.md` classifies every module:

- core;
- active: live routes outside the core;
- measurement: refutations, boundaries and superseded routes, kept on purpose;
- support.

Most of the tree is measurement and support. The core is the place to start.

| module | contents |
|---|---|
| `RcicDeclarative` | syntax, levels, environments, `HasTyT`, `ConvT`, `TyConvT` |
| `RcicTypedRowsWf` | the three kernel rows |
| `RcicDTRowFields`, `RcicDT1011Rows` | type uniqueness and subject reduction from the rows |
| `RcicTypedScopeCheck`, `RcicAnnRowsSupply` | the three rows within the scope check |
| `RcicKernelRowsAssembly` | the rows from their three remaining inputs, outside the scope |
| `RcicSynSortRow`, `RcicSynAllBelow`, `RcicSynBelowScoped` | the sortRow closer |
| `RcicPiRowProj`, `RcicNativeKProjection` | native valleys and `PiConvValleyData` |
| `RcicMachineSoundTyped` | machine soundness on the typed judgments |

## Provenance

This directory mirrors `lean/rcic` of the Residua development tree at commit `7ba88229cce5f8309f09094695972a99be095c7c`. It is regenerated from there after each landing.

Every Lean file except the seal is byte-identical to the development tree.

It holds exactly the modules whose import closure stays inside `lean/rcic` (plus `Residua.SHA256`). The modules that also depend on Residua's runtime, bootstrap and admission layers are not published yet: Apex, SCM certificate and contract checking, the optimized kernel, and Forge.

The seal is the development tree's foundation seal restricted to these modules.

## License

Apache-2.0. See `LICENSE` and `NOTICE` at the repository root.
