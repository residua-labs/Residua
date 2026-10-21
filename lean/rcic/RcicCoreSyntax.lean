import rcic.RcicArity
import rcic.RcicSubstCalc
import rcic.RcicUniverseClass

/-!
# RcicCoreSyntax — core layer 1: syntax, levels, substitution calculus

Mathematical-map entry module (swe-mathmap, 2026-10-21): imports this layer's
maximal elements and adds no declarations. Part of the `rcic` core map; the
core is exactly the import closure of `rcic.RcicCore`.

Key definitions and theorems of the layer:

* `Rcic.Declarative.Level` — universe levels (`zero`, `succ`, `max`, `imax`, `param`)
* `Rcic.Declarative.Expr` — raw terms (de Bruijn, level-annotated constants)
* `Rcic.Declarative.LocalDecl` / `Rcic.Declarative.LCtx` — local contexts
* `Rcic.Declarative.lift` / `Rcic.Declarative.instantiate` / `Rcic.Declarative.instantiate0` — de Bruijn operations
* `Rcic.Declarative.lvlSubst` / `Rcic.Declarative.instLevel` / `Rcic.Declarative.instantiateLevels` — level substitution
* `Rcic.Declarative.eval` / `Rcic.Declarative.eqN` / `Rcic.Declarative.leN` — level semantics under valuations
* `Rcic.Declarative.lift_lift_permute` / `Rcic.Declarative.lift_instantiate_high` / `Rcic.Declarative.instantiate_instantiate` — substitution calculus
* `Rcic.Declarative.isArity` / `Rcic.Declarative.peelPis` / `Rcic.Declarative.applyTel` / `Rcic.Declarative.piCount` — arity and telescope operations
* `Rcic.Declarative.levelIsZero` / `Rcic.Declarative.levelNeverZero` — decided level predicates
* `Rcic.Declarative.UniformProp` / `Rcic.Declarative.UniformType` / `Rcic.Declarative.MixedUniverse` — universe classification

Layer members: `RcicDeclarative`, `RcicLevelCalc`, `RcicLevelDec`,
`RcicLevelZero`, `RcicSortLevelBridge`, `RcicUniverseClass`, `RcicArity`,
`RcicSubstCalc`.
-/
