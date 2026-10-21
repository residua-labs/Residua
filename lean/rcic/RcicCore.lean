import rcic.RcicCoreSyntax
import rcic.RcicCoreEnv
import rcic.RcicCoreJudgments
import rcic.RcicCoreMetatheory
import rcic.RcicCoreRelation
import rcic.RcicCoreRows
import rcic.RcicCoreMachine

/-!
# RcicCore — the rcic core library

Mathematical-map entry module (swe-mathmap, 2026-10-21): imports the seven
layer entry modules and adds no declarations. Its import closure is exactly
the core set — the modules the in-scope rows, subject reduction (DT-010/011),
type uniqueness (DT-012) and machine soundness need — recorded in
`lean/rcic/MODULES.md`.

Layers, in dependency order: `RcicCoreSyntax` (syntax, levels, substitution),
`RcicCoreEnv` (environments, inductive groups and admission, ι, source
environments), `RcicCoreJudgments` (typed judgments), `RcicCoreMetatheory`
(weakening, substitution, inversion, typed parallel reduction, subject
reduction), `RcicCoreRelation` (the annotated copy and its logical relation),
`RcicCoreRows` (the three rows and their consumers), `RcicCoreMachine`
(machine soundness).
-/
