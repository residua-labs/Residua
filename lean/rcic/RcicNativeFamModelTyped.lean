import rcic.RcicNativeTypedModelTyping
import rcic.RcicNativeTypedModelIotaSound
import rcic.RcicNativeTypedModelProbe
import rcic.RcicNativePiCycleProbe
import rcic.RcicNativePiCycleRestatement
import rcic.RcicNativePiProbeAlgebra
import rcic.RcicNativePiProbeComputation
import rcic.RcicNativePiProbeConstants
import rcic.RcicNativePiProbeCongruence
import rcic.RcicNativePiProbeKObstruction
import rcic.RcicNativePiProbeModelBoundary
import rcic.RcicPinEqEraseWf
import rcic.RcicPinLoopEraseWf

/-!
# RcicNativeFamModelTyped — `PiRowField`-Free Typed PER, `FamProbeCpt` Chain-from-Links Assembly,
the Family-Head Model Fragment Over `ApproxT`/`ElT`/`LRSCoreT`, Off-Diagonal `ConvT.app`/`eta`
Closure, `NormalUniqueR`-Free `FamObsEquiv`, Whole-Spine `piTowerCpt` Alignment, `eqEnvT`/`pinLoopEnvT`
K-Readback Controls, and 18-Constructor 3-Observation Audit + `Exists` Iota Resolution

1. **§1 (`PiRowField`-Free Typed PER for `LRSCoreT` / `LRST` Under `EnvWfT E` Alone):**
   - Reuses `PiCycleAudit.convArgsSymmT_of_envWfT`, `PiCycleAudit.convArgsTransT_of_envWfT`, and `PiCycleAudit.typedPER_of_envWfT` (`RcicNativePiCycleRestatement`), eliminating the `PiRowField` hypothesis that coupled the family row to the Π row.
   - Derives `typeSpineT_symm_of_envWfT`, `typeSpineT_trans_of_envWfT`, `lrSCoreT_irrel_of_envWfT`, `lrSCoreT_symm_of_envWfT`, `lrSCoreT_trans_of_envWfT`, `lrSCoreT_symm_tm_of_envWfT`, `lrSCoreT_trans_tm_of_envWfT`, and the proposition-collapsed `LRST` counterparts from `ReadbackLaws E R`, `NormalUniqueR R`, and `EnvWfT E` alone.
2. **§2 (`PiRowField`-Free `BotFamCpt E` PER for `LRSCore` / `LRS`, `FamProbeCpt E` Chain-from-Links Assembly `famAppRow_of_links`, and Canonical Deterministic K-Readback `WhStepRecKCanon` Instance):**
   - Extends `lrSCore_symm_botPiCpt` and `lrSCore_trans_botPiCpt` (`RcicNativeFamModelLRSPER`) to all `BotFamCpt E` compacts (`lrSCore_symm_botFamCpt`, `lrSCore_trans_botFamCpt`) under `EnvWfT E` alone.
   - Extends `modelAt_right_of_lrSCore_probe` and `fundamentalLRSTMProbe_of_links` to `FamProbeCpt E` (`modelAt_right_of_lrSCore_famProbeCpt`, `fundamentalLRSTMFamProbe_of_links`), yielding `famAppRow_of_links`, `famRelevantSlotConv_of_links`, and `typedRowsWf_of_allBelowScoped_links`.
   - Instantiates `ReadbackLaws`, `DetR`, and `NormalUniqueR` at the canonical deterministic K-readback `WhStepRecKCanon E` (`readbackLaws_whStepRecKCanon`, `detR_whStepRecKCanon`, `normalUniqueR_whStepRecKCanon`) and verifies the `W-K-OPEN` and `W-K-AND` controls in `LRSCore (WhStepRecKCanon E)`.
3. **§3 (Family-Head Model Fragment Over the Typed-Demand Model `CptT` / `ApproxT` / `ElT` / `SemEqT`):**
   - Defines `ApproxTArgs`, `botVecT`, and `slotVecT`, and proves `not_propCtorT_of_inductiveM`, `approxT_famApp`, exact inversion `approxT_famApp_iff`, model family-head injectivity (`semEqT_famApp_head_length`, `semEqT_famApp_slot`, `semEqT_famApp_inj`), and constructor disjointness (`semEqT_pi_famApp_disjoint`, `semEqT_sort_famApp_disjoint`).
   - Proves semantic proposition/universe typing (`tyCodeCT_of_approxT_famApp`, `isPropCT_of_approxT_famApp_prop`, `elT_famApp_prop_bot`, `not_isPropCT_spine_of_piBody_ne_zero`, `elT_famApp_nonprop_spine`, `typingLemma_at_famApp_prop`, `typingLemma_at_famApp_nonprop`).
4. **§4 (`LRSCoreT` Family-Spine & Π Read-Off and Expansion Lemmas):**
   - Proves `lrSCoreT_spine_sort_iff`, `lrSCoreT_spine_sort_args_irrel`, `typeSpineT_expand`, `lrSCoreT_spine_sort_expand`, `lrSCoreT_famApp_components`, `lrSCoreT_famApp_of_components`, `lrSCoreT_famApp_refl_of_saturated`, and `lrSCoreT_pi_components`.
5. **§5 (`FamProbeCptT E`, Refutation of `ReadbackModelInvT`, Relation-Seeded `FamProbeLinkT`, Single-Link Probe Constructors, and `famAppRow` / `PiRowField` / `TypedRowsWf` / `DT-012`–`IA-024` Consumers Over `LRSCoreT`):**
   - Refutes `ReadbackModelInvT R E` under `ReadbackLaws E R` (`not_readbackModelInvT_of_readbackLaws`) because `ApproxT`'s typed `CTyS` application guard collapses lambda-typed identity β-redexes to `.bot`.
   - Defines relation-seeded `FamProbeLinkT R E n` and proves `famProbe_chainT` via `lrSCoreT_right_diag_of_envWfT` and `lrSCoreT_trans_of_envWfT` (preserving the exact compact `c` across `TyConvT.trans` with **zero** `ReadbackModelInvT`), yielding `piRowField_of_linksT`, `famApp_saturated_of_linksT`, `famAppRow_of_linksT`, `famRelevantSlotConv_of_linksT`, and `typedRowsWf_of_allBelowScoped_linksT` from `(hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (hlink : FamProbeLinkT R E n)` alone.
6. **§6 (Off-Diagonal `ConvT.app` Decomposition, Step-by-Step Family-Spine Application, and `ConvT.eta` Closure in `LRTermFamSemBiProbeRKCanon`):**
   - Lifts step-by-step `.inductiveM` spine application (`lrTermFamSemBiProbeRKCanon_famSpine_step_app_partial`, `lrTermFamSemBiProbeRKCanon_famSpine_step_app_saturated`) to `LRTermFamSemBiProbeRKCanon`, proves off-diagonal `ConvT.app` decomposition (`lrTermFamSemBiProbeRKCanon_app_of_fn_and_arg`, `lrTermFamSemBiProbeRKCanon_app_fn_of_letBinding`), and proves unconditional `ConvT.eta` closure (`lrTermFamSemBiProbeRKCanon_eta_of_left_probe_bot`, `lrTermFamSemBiProbeRKCanon_eta_lam`, `lrTermFamSemBiProbeRKCanon_eta_bvarSpine`, `lrTermFamSemBiProbeRKCanon_eta_ctorSpine`, `lrTermFamSemBiProbeRKCanon_eta_famSpine_partial`, `lrTermFamSemBiProbeRKCanon_eta_of_whRedRecKCanon`).
7. **§7 (All-Member / Unsaturated-Prefix `DomsRel` & `ConvArgsT` PER Under `EnvWfT E` Alone, Exact Diagonal Adequacy Characterizations, and Off-Diagonal `ConvT.app` Reduction in `LRTermFamSemBiProbeRKCanon`):**
   - Generalizes `DomsRel` and `PiRowField`-free `ConvArgsT` symmetry/transitivity from saturated `.inductiveM` type spines to **every** admitted member `E.members r = some m` (`.inductiveM`, `.constructorM`, `.recursorM`, `.definitionM`, `.axiomM`, `.quotM`) and **every** (possibly unsaturated, data-typed) argument prefix `xs, ys` under `EnvWfT E` alone (`convArgs_symm_member_of_typedSpines`, `convArgs_trans_member_of_typedSpines`, `convArgs_symm_member_of_convSpines`, `convArgs_trans_member_of_convSpines`).
   - Characterizes the diagonal `LRTypeFamINBiProbeRKCanon E n Γ A A` and `LRTermFamSemBiProbeRKCanon E n Γ e e T` (`lrTypeFamINBiProbeRKCanon_diag_iff`, `lrTermFamSemBiProbeRKCanon_diag_iff`) and reduces off-diagonal `ConvT.app` (`f₁ a₁ ~ f₂ a₂`) to `.letBinding` diagonal adequacy + 0-instantiation congruence (`lrTermFamSemBiProbeRKCanon_app_of_letDiag_and_subst0Congr`).
8. **§8 (`convArgsT_length_le_piDoms` Refutation on Polymorphic Axiom Members vs. `NonBvarTail` Sufficiency, and `NormalUniqueR`-Free `FamObsTransport` / `FamObsEquiv` / `FamObsConvLinks`):**
   - Refutes unguarded `convArgsT_length_le_piDoms` on polymorphic axiom members (`not_allMember_convArgsT_length_le_piDoms`) and proves `NonBvarTail` sufficiency (`convArgsT_length_le_piDoms_of_nonBvarTail`, `convArgsT_length_le_piDoms_of_inductiveM`).
   - Defines `NormalUniqueR`-free `FamObsTransport`, `FamObsEquiv`, and `FamObsConvLinks`, proving reflexivity, symmetry, transitivity, chain closure, and `piRowField_of_famObsConvLinks` / `famAppRow_of_famObsConvLinks` / `typedRowsWf_of_allBelowScoped_famObsConvLinks` with **zero** `NormalUniqueR R`.
9. **§9 (Whole-Spine `piTowerCpt` / `piTowerCptT` Alignment Without Backward `ApproxT` Transport Resolving `#7725` §§1–2, and Positive `WhStepRecKCanon` Resolution of `#7689`/`#7733`'s `eqGapRedex` & `pinLoopEnvT` K Obstructions):**
   - Defines `piTowerCpt : Nat → CptI` and `piTowerCptT : Nat → CptT` (`BotPiCpt` / `BotPiCptT`), proving `piTower_typed_iff`, `PiRowField`-free PER (`piTower_symm`, `piTower_trans`, `piTower_right_diagonal`), `TelescopeConvRel` seeding (`lrSCore_piTowerCpt_of_telescopeConvRel`), relation-seeded chain transport (`piTower_chain` / `piTower_chainT` with **zero** backward `ApproxT` transport), and whole-spine all-slot continuation (`wholeSpine_piTower_of_links`, `wholeSpine_nodeDeclAlign_of_links`, `wholeSpine_convArgsT_snoc_of_links`).
   - Proves that `WhStepRecKCanon` reduces `#7689`/`#7733`'s convertible-index `eqEnvT` gap redex (`eqCanonGapRedex`) and `pinLoopEnvT`'s recursive-singleton K redex (`loopCanonRedex`) to `.sort .zero`, inhabiting `LRSCore`, `LRSCoreT`, `LRTypeFamINRKCanon`, `LRTypeFamINBiProbeRKCanon`, `LRTermFamSemBiProbeRKCanon`, and `FamObsEquiv`.
10. **§10 (Exact Bridge to `RcicNativePiProbe*`, Complete 18-Constructor `ConvT` Closure Audit for 3-Observation `FamConvObsMotive` at `WhStepRecKCanon` & `WhStepK`, and Positive Resolution of `RcicNativeTypedModelIotaSound`'s `Exists` Non-Proof-Field Witness `wEx` in `ApproxDI` / `WhStepRecKCanon` / `ApproxDIKCanon`):**
   - Proves exact two-way factorizations (`famObsTransport_iff_probeTransportT_and_famSpine`, `famObsEquiv_iff_probeEquivT_and_famSpineEquiv`, `famObsConvLinks_iff_probeConvLinksT_and_famSpineConvLinks`) connecting the 3-observation motive (`FamObsEquiv`) to `RcicNativePiProbeAlgebra`'s 2-observation motive (`ProbeEquivT`) + `FamSpineEquiv`.
   - Closes `ConvT.consts` unconditionally for `FamConvObsMotive` (`famConvObs_whStepRecKCanon_consts`, `famConvObs_whStepK_consts`), including the non-vacuous 0-arity `.inductiveM` family-spine case (`constsFam_trueEnvU_nonvacuity`), and closes all 14/18 constructors (`refl`, `symm`, `trans`, `tyConv`, `sorts`, `pi`, `beta`, `zeta`, `zetaLocal`, `delta`, `iota`, `lit`, `lam`, `consts`) at `WhStepRecKCanon E` under `EnvWfT E` alone (including forward & reverse `ConvT.iota` via `detR_whStepRecKCanon`) plus the 4 remaining ports (`FamFunctionNoTypeProbe`, `FamPropNoTypeProbe`, `FamAppHeadAction`/`FamAppArgAction`, `FamMixedSubstEdges`), step-by-step family-spine application (`famObsEquiv_whStepRecKCanon_famSpine_step_app_partial`, `famObsEquiv_whStepRecKCanon_famSpine_step_app_saturated`), and the 3-head model boundary (`famFunctionNoTypeProbe_of_typing_realization`, `famPropNoTypeProbe_of_typing_realization`).
   - Resolves `RcicNativeTypedModelIotaSound`'s `Exists` counterexample `wEx` (`not_iotaSoundT_ex`) positively in `ApproxDI exEnv`, `WhStepRecKCanon exEnv`, `ApproxDIKCanon exEnv`, `SemEqDIKCanon exEnv`, and `FamObsEquiv (WhStepRecKCanon exEnv)` (`semEqDI_wEx`, `approxDI_exRhs`, `approxDI_exLhs`, `whStepRecKCanon_wEx`, `whRedRecKCanon_wEx_to_fieldVal`, `approxDIKCanon_exLhs`, `approxDIKCanon_exRhs`, `elT_exEnv_famApp_bot`).
11. **§11 (Level-Fact-Strengthened Unified Spine Relation `SpineClauseSL` / `LRSCoreSL` / `LRSSL` Resolving `#7673` Items 2.1–2.2 & §8 Part A, Unconditional `typedPERSL_of_envWfT`, 3-Observation Typed-Relation Bridge & Spine-Growth Application / Substitution Adapters `famObsEquiv_app_of_lrSCoreSL` / `famMixedSubstEdges_of_lrSCoreSL`, and End-to-End 18-Constructor `WhStepRecKCanon` Assembly):**
    - Defines `SpineClauseSL`, `LRSCoreSL`, and `LRSSL` over `CptT`, incorporating `ls₁.length = m.arity ∧ levelsBounded n ls₁ = true ∧ levelsBounded n ls₂ = true ∧ xs₁.length ≤ (piDomsOf m.mtype).length` (`#7673` Items 2.1–2.2 + §8 Part A resolution), proves `hasTyT_famApp_both_of_levelFacts_convArgsT`, and proves the full 5-part mutual PER (`typedPERSL_of_envWfT`, `lrSCoreSL_irrel_of_envWfT`, `lrSCoreSL_symm_of_envWfT`, `lrSCoreSL_trans_of_envWfT`, `lrSCoreSL_symm_tm_of_envWfT`, `lrSCoreSL_trans_tm_of_envWfT`) under `ReadbackLaws E R`, `NormalUniqueR R`, and `EnvWfT E` alone (with **zero** `ConvArgsSymmS` / `ConvArgsTransS` / `PiRowField` premises).
    - Proves the 3-observation bridge (`famSpineRead_of_lrSCoreSL_left`, `famObsTransport_of_lrSCoreSL_probes`, `famObsEquiv_of_lrSCoreSL_probes`) at **any** ambient index `I : Expr Nat` (recovering saturation and sort typings from `hasTyT_famApp_both_of_levelFacts_convArgsT` without requiring `∃ l, RedR R Γ I (.sort l)`), proves both application branches (`lrSCoreSL_app_of_lambda_demand` and `lrSCoreSL_app_of_famSpine_step` via `wholeSpine_piTower_of_links` + `wholeSpine_convArgsT_snoc_of_links`), proves the 3-observation related-substitution let adapters (`FamModelProbeAtSubst`, `famObsEquiv_of_substRelation_lrSCoreSL`, `famBodyAtValue_of_lrSCoreSL`, `famValueInBody_of_lrSCoreSL`, `famMixedSubstEdges_of_lrSCoreSL`), and wires all 18 `ConvT` constructors at `WhStepRecKCanon E` (`FamProbeAdapterInputsRKCanon`, `famObsConvLinks_whStepRecKCanon_of_adapterInputs`) with positive `eqEnvT`, `pinLoopEnvT`, `trueEnvU`, and `andEnvU` witnesses.
12. **§12 (Refutation of Unrestricted `TypingLemmaT` vs. Saturated-Probe `FamProbeTypingLemmaT`, Type-Discipline-Guarded `SpineClauseSLT` / `LRSCoreSLT` / `LRSSLT` Resolving `#7726`/`#7731`'s Escape Obstruction, and Semantic Non-Sort Proposition Classifier `IsSemNoSortPropRecKCanon` / `LRTermFamNoSortRKCanon`):**
    - Proves `not_typingLemmaT_of_inductiveM_posArity` (refuting unrestricted `TypingLemmaT E n` on every environment with an indexed/parameterized `.inductiveM` family, including `andEnvU`, `exEnv`, and `eqEnvT`) and `not_typingLemmaT_all` (refuting `TypingLemmaT E n` on every `E, n` via a two-step `.lam` compact on `λ (α : Type 0) (x : α), Prop`), while proving that `FamProbeTypingLemmaT E n` (restricted to `FamSatProbeCptT E`) suffices for `famFunctionNoTypeProbe_of_typing_realization`, `famPropNoTypeProbe_of_typing_realization`, and `FamProbeAdapterInputsRKCanon` and holds unconditionally across all 6 canonical RCIC value/type families (`famProbeTyping_at_sort`, `famProbeTyping_at_pi`, `famProbeTyping_at_lam`, `famProbeTyping_at_famApp_unsaturated`, `famProbeTyping_at_famApp_allArity`, `famProbeTyping_at_nonInductive_rigidSpine`, `famProbeTyping_at_bvarSpine_of_lookupValue_none`).
    - Defines `SpineClauseSLT`, `LRSCoreSLT`, and `LRSSLT` (adding `((∃ D B, RedR R Γ A (.pi D B)) → ∃ m, E.members r = some m ∧ m.mclass = .inductiveM ∧ args.length < (piDomsOf m.mtype).length)`), proves the full 5-part mutual PER (`typedPERSLT_of_envWfT`) under `ReadbackLaws E R`, `NormalUniqueR R`, and `EnvWfT E` alone, refutes `.axiomM`/`.constructorM` and saturated spines at Π-indices (`not_lrSCoreSLT_nonInductive_at_pi`, `not_lrSCoreSLT_satSpine_at_pi`), and proves exact Π-index probe collapse (`lrSCoreSLT_satProbe_at_pi_iff_eq_bot : LRSCoreSLT R E n Γ M M' A c ↔ c = .bot` for all `FamSatProbeCptT E c` when `RedR R Γ A (.pi D B)`).
    - Defines `IsSemNoSortPropRecKCanon`, `LRTermFamNoSortRKCanon`, and `LRTermFamNoSortBiProbeRKCanon` (replacing the rigid-head disjunction of `IsSemRigidPropRecKCanon` with `¬ ApproxDIKCanon E Γ A .sort`), strictly extending proof irrelevance to open proposition variables `.bvar i : Prop` and applied open predicate spines `foldApps (.bvar i) xs : Prop` (`lookupValue Γ i = none`) while retaining unconditional all-type PER and 4-line local `TyConvT` transport (`isSemNoSortPropRecKCanon_transport_of_typeRel`, `lrTermFamNoSortBiProbeRKCanon_transport_of_typeRel`) with **zero** `EnvWfT E` and **zero** `ZeroSortCoherence E n`.
13. **§13 (Family-Head Algebra & `ConvArgsSymmS`-Free Probe PER for Landed `LRSCoreS`, Unconditional `RelSubstIdT` Discharge at `EnvT.bot` & `ctxEnvT` From `FundamentalSAtT`, and `LRSCoreS` Family-Spine Application Step Resolving `W-FAMSPINE`):**
    - Discharges `RcicNativeTypedModelFamSpine.LevelCongrT E n` unconditionally from `EnvWfT E` (`levelCongrT_of_envWfT`), proves `ConvArgsSymmS`/`ConvArgsTransS`-free symmetry, transitivity, and right-diagonal extraction for landed `LRSCoreS` across all `FamProbeCptT E` and `piTowerCptT k` compacts (`spineClauseS_inductiveM_sort_symm`, `spineClauseS_inductiveM_sort_trans`, `famProbeS_symm`, `famProbeS_trans`, `famProbeS_right_diag`, `piTowerS_iff`, `piTowerS_symm`, `piTowerS_trans`, `piTowerS_right_diagonal`), and proves relation-seeded `FamProbeLinkS` chain assembly (`famProbe_chainS`, `piRowField_of_famProbeLinkS`, `famAppRow_of_famProbeLinkS`, `famRelevantSlotConv_of_famProbeLinkS`, `typedRowsWf_of_allBelowScoped_famProbeLinkS`) and the 3-observation `LRSCoreS` bridge (`famObsTransport_of_lrSCoreS_probes`, `famObsEquiv_of_lrSCoreS_probes`).
    - Discharges `RcicNativeTypedModelProbe.RelSubstIdT` at both `EnvT.bot` and `ctxEnvT E Γ` (`relSubstIdT_bot_of_fundamentalSAtT`, `relSubstIdT_ctxEnvT_of_fundamentalSAtT`, `relSubstTypedAtT_bot_id_of_fundamentalSAtT`) **unconditionally** from `ReadbackLaws E R`, `EnvWfT E`, `FundamentalSAtT`, and `CtxWfT E n Γ` alone by induction on `CtxWfT`, yielding `RelSubstIdT`-free `FundamentalSAtT` adapters (`fundConvAt_bot_of_fundamentalSAtT`, `fundConvAt_ctxEnvT_of_fundamentalSAtT`, `convT_pi_inj_of_fundamentalSAtT`, `convT_famApp_inj_of_fundamentalSAtT`, `convT_famApp_relevantSlotConv_of_fundamentalSAtT`, `famProbeLinkS_of_fundamentalSAtT_realization`, `famAppRow_of_fundamentalSAtT_realization`, `famRelevantSlotConv_of_fundamentalSAtT_realization`, `typedRowsWf_of_allBelowScoped_fundamentalSAtT_realization`), and refutes unrestricted `TypingLemmaEnvT (ctxModelT_approxT E) n` (`not_typingLemmaEnvT_all`).
    - Proves the `LRSCoreS` family-spine application step (`lrSCoreS_app_of_famSpine_step`, `lrSCoreS_app_of_famSpine_syntactic`, `lrSCoreS_app_of_approxT_famProbe`) resolving `W-FAMSPINE` in `RcicNativeTypedModelFund.fundT_app`, and provides concrete `LRSCoreS (WhStepRecKCanon E)` witnesses across `trueEnvU`, `andEnvU`, `eqEnvT`, and `pinLoopEnvT`.

`closure_claim = 0`. No `sorry`, axioms `⊆ {propext, Quot.sound}`.
-/

namespace Rcic.Declarative.NativeValleys.FamModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiCycleAudit
open Rcic.Declarative.KernelRowsAssembly
open Rcic.Syn

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — `PiRowField`-Free Typed PER for `LRSCoreT` / `LRST` Under `EnvWfT E` Alone -/

/-- Symmetry of `TypeSpineT` under `EnvWfT E` and `CtxWfT E n Γ` alone (zero `PiRowField`). -/
theorem typeSpineT_symm_of_envWfT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' : Expr Nat} {r : Nat} (h : TypeSpineT R E n Γ M M' r) :
    TypeSpineT R E n Γ M' M r :=
  typeSpineT_symm (convArgsSymmT_of_envWfT hW) hΓ h

/-- Transitivity of `TypeSpineT` under `ReadbackLaws E R`, `NormalUniqueR R`, `EnvWfT E`, and
    `CtxWfT E n Γ` alone (zero `PiRowField`). -/
theorem typeSpineT_trans_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' M'' : Expr Nat} {r : Nat}
    (h₁ : TypeSpineT R E n Γ M M' r) (h₂ : TypeSpineT R E n Γ M' M'' r) :
    TypeSpineT R E n Γ M M'' r :=
  typeSpineT_trans hL hNU hW (convArgsTransT_of_envWfT hW) hΓ h₁ h₂

/-- **Irrelevance (`lrSCoreT_irrel_of_envWfT`) Under `EnvWfT E` Alone:** -/
theorem lrSCoreT_irrel_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreT R E n Γ A₁ A₂ (.sort w) a) (hu : CTyS E u a) {N N' : Expr Nat}
    (h : LRSCoreT R E n Γ N N' A₁ u) : LRSCoreT R E n Γ N N' A₂ u :=
  lrSCoreT_irrel hL hNU hW (convArgsSymmT_of_envWfT hW) (convArgsTransT_of_envWfT hW) hΓ hAA hu h

/-- **Type-Level Symmetry (`lrSCoreT_symm_of_envWfT`) at Every Compact `c : CptT` Under `EnvWfT E` Alone:** -/
theorem lrSCoreT_symm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {w : Level} {c : CptT}
    (h : LRSCoreT R E n Γ A₁ A₂ (.sort w) c) :
    LRSCoreT R E n Γ A₂ A₁ (.sort w) c :=
  lrSCoreT_symm hL hNU hW (convArgsSymmT_of_envWfT hW) (convArgsTransT_of_envWfT hW) hΓ h

/-- **Type-Level Transitivity (`lrSCoreT_trans_of_envWfT`) at Every Compact `c : CptT` Under `EnvWfT E` Alone:** -/
theorem lrSCoreT_trans_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ A₃ : Expr Nat} {w : Level} {c : CptT}
    (h₁ : LRSCoreT R E n Γ A₁ A₂ (.sort w) c) (h₂ : LRSCoreT R E n Γ A₂ A₃ (.sort w) c) :
    LRSCoreT R E n Γ A₁ A₃ (.sort w) c :=
  lrSCoreT_trans hL hNU hW (convArgsSymmT_of_envWfT hW) (convArgsTransT_of_envWfT hW) hΓ h₁ h₂

/-- **Term-Level Symmetry (`lrSCoreT_symm_tm_of_envWfT`) Under `EnvWfT E` Alone:** -/
theorem lrSCoreT_symm_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' : Expr Nat} (h : LRSCoreT R E n Γ N N' A u) :
    LRSCoreT R E n Γ N' N A u :=
  lrSCoreT_symm_tm hL hNU hW (convArgsSymmT_of_envWfT hW) (convArgsTransT_of_envWfT hW) hΓ hAA hu h

/-- **Term-Level Transitivity (`lrSCoreT_trans_tm_of_envWfT`) Under `EnvWfT E` Alone:** -/
theorem lrSCoreT_trans_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' N'' : Expr Nat} (h₁ : LRSCoreT R E n Γ N N' A u) (h₂ : LRSCoreT R E n Γ N' N'' A u) :
    LRSCoreT R E n Γ N N'' A u :=
  lrSCoreT_trans_tm hL hNU hW (convArgsSymmT_of_envWfT hW) (convArgsTransT_of_envWfT hW) hΓ hAA hu h₁ h₂

/-- Top-level `LRST` symmetry at a sort index under `EnvWfT E` alone. -/
theorem lrST_symm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {w : Level} {c : CptT}
    (h : LRST R E n Γ A₁ A₂ (.sort w) c) :
    LRST R E n Γ A₂ A₁ (.sort w) c := by
  rcases h with hP | h
  · exact Or.inl hP
  · exact Or.inr (lrSCoreT_symm_of_envWfT hL hNU hW hΓ h)

/-- Top-level `LRST` transitivity at a sort index under `EnvWfT E` alone. -/
theorem lrST_trans_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ A₃ : Expr Nat} {w : Level} {c : CptT}
    (h₁ : LRST R E n Γ A₁ A₂ (.sort w) c) (h₂ : LRST R E n Γ A₂ A₃ (.sort w) c) :
    LRST R E n Γ A₁ A₃ (.sort w) c := by
  rcases h₁ with hP | h₁
  · exact Or.inl hP
  · rcases h₂ with hP | h₂
    · exact Or.inl hP
    · exact Or.inr (lrSCoreT_trans_of_envWfT hL hNU hW hΓ h₁ h₂)

/-- Top-level `LRST` term symmetry under `EnvWfT E` alone. -/
theorem lrST_symm_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' : Expr Nat} (h : LRST R E n Γ N N' A u) :
    LRST R E n Γ N' N A u := by
  rcases h with hP | h
  · exact Or.inl hP
  · exact Or.inr (lrSCoreT_symm_tm_of_envWfT hL hNU hW hΓ hAA hu h)

/-- Top-level `LRST` term transitivity under `EnvWfT E` alone. -/
theorem lrST_trans_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' N'' : Expr Nat} (h₁ : LRST R E n Γ N N' A u) (h₂ : LRST R E n Γ N' N'' A u) :
    LRST R E n Γ N N'' A u := by
  rcases h₁ with hP | h₁
  · exact Or.inl hP
  · rcases h₂ with hP | h₂
    · exact Or.inl hP
    · exact Or.inr (lrSCoreT_trans_tm_of_envWfT hL hNU hW hΓ hAA hu h₁ h₂)


/-! ### §2 — `PiRowField`-Free `BotFamCpt E` PER for `LRSCore` / `LRS`, `FamProbeCpt E` Chain-from-Links Assembly `famAppRow_of_links`, and Canonical Deterministic K-Readback `WhStepRecKCanon` Instance -/

/-- Symmetry of `TypeSpineR` under `EnvWfT E` and `CtxWfT E n Γ` alone (zero `PiRowField`). -/
theorem typeSpineR_symm_of_envWfT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' : Expr Nat} {r : Nat} (h : TypeSpineR R E n Γ M M' r) :
    TypeSpineR R E n Γ M' M r := by
  rcases h with ⟨m, ls, ls', xs, xs', w, w', hm, hind, h1, h2, ⟨hty⟩, ⟨hty'⟩, ⟨hc⟩, heqN, hlen, hlen', hargs⟩
    | ⟨hnot, X, X', h1, h2, ⟨hc⟩⟩
  · exact Or.inl ⟨m, ls', ls, xs', xs, w', w, hm, hind, h2, h1, ⟨hty'⟩, ⟨hty⟩, ⟨hc.symmT⟩,
      eqNList_symm'' heqN, hlen', hlen,
      convArgs_symm_instMtype_of_envWfT hW hΓ hm hind hty hty' heqN hargs⟩
  · exact Or.inr ⟨hnot, X', X, h2, h1, ⟨hc.symmT⟩⟩

/-- Transitivity of `TypeSpineR` at an admitted `.inductiveM` head `r` under `ReadbackLaws E R`,
    `NormalUniqueR R`, `EnvWfT E`, and `CtxWfT E n Γ` alone (zero `PiRowField`). -/
theorem typeSpineR_trans_of_inductiveM (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {M M' M'' : Expr Nat}
    (h₁ : TypeSpineR R E n Γ M M' r) (h₂ : TypeSpineR R E n Γ M' M'' r) :
    TypeSpineR R E n Γ M M'' r := by
  rcases h₁ with ⟨m₁, ls, ls', xs, xs', w, w', hm₁, _, h1, h2, ⟨hty⟩, ⟨hty'⟩, ⟨hc₁⟩, heqN, hlen, _, hargs⟩
    | ⟨hnot, _⟩
  · rcases h₂ with ⟨m₂, ls₂, ls'', xs₂, xs'', _, w'', hm₂, _, h2', h3, _, ⟨hty''⟩, ⟨hc₂⟩, heqN', _, hlen'', hargs'⟩
      | ⟨hnot, _⟩
    · cases hm.symm.trans hm₁
      cases hm.symm.trans hm₂
      have e := hNU Γ h2 (fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs)
        h2' (fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs)
      obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
      injection hconst with _ hls
      subst hls; subst hxs
      exact Or.inl ⟨m, ls, ls'', xs, xs'', w, w'', hm, hind, h1, h3, ⟨hty⟩, ⟨hty''⟩,
        ⟨TyConvT.trans _ _ _ _ hc₁ hc₂⟩, eqNList_trans'' heqN heqN', hlen, hlen'',
        convArgs_trans_instMtype_of_envWfT hW hΓ hm hind hty hty' heqN hargs hargs'⟩
    · exact (hnot m hm hind).elim
  · exact (hnot m hm hind).elim

/-- **Symmetry of `LRSCore` on All `BotFamCpt E` Compacts (`lrSCore_symm_botFamCpt`):**
    Extends `lrSCore_symm_botPiCpt` from `BotPiCpt` to `BotFamCpt E` (including `.spine r args` for
    saturated admitted `.inductiveM` heads with `BotDemand args`) under `EnvWfT E` and `CtxWfT E n Γ`
    alone — with **zero** `PiRowField` hypothesis! -/
theorem lrSCore_symm_botFamCpt (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {c : CptI} (hc : BotFamCpt E c) :
    ∀ {M M' A : Expr Nat}, LRSCore R E n Γ M M' A c → LRSCore R E n Γ M' M A c := by
  induction hc with
  | bot => intro M M' A _; exact lrSCore_bot _ _ _ _
  | sort =>
      intro M M' A h
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | @pi a f _ hbd _ iha ihf =>
      intro M M' A h
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      obtain ⟨hA, A₁, B₁, A₂, B₂, h1, h2, ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩, ⟨u₁, hra⟩, hrf⟩ := h
      cases hΓ₁ with
      | assumption _ _ u _ hA₁ =>
          obtain ⟨v, hA₂⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hdom hA₁
          refine ⟨hA, A₂, B₂, A₁, B₁, h2, h1, ⟨.assumption Γ A₂ v hΓ hA₂⟩, ⟨hdom.symmT⟩,
            ⟨tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT⟩, ⟨u₁, iha hra⟩, ?_⟩
          intro s hs N N' hN hN' hcN _
          obtain ⟨hcN⟩ := hcN
          have hN₁ : HasTyT E n Γ N A₁ := hasTyT_of_tyConvT hN hdom.symmT
          have hN'₁ : HasTyT E n Γ N' A₁ := hasTyT_of_tyConvT hN' hdom.symmT
          have hc₁ : ConvT E n Γ N' N A₁ := convT_of_tyConv (.symm _ _ _ _ hcN) hdom.symmT
          obtain ⟨v', hv'⟩ := hrf s hs N' N hN'₁ hN₁ ⟨hc₁⟩
            (fun u hu => by rw [hbd s hs u hu]; exact lrSCore_bot _ _ _ _)
          exact ⟨v', ihf s hs hv'⟩
  | @famSpine r m args hm _ _ hbd =>
      intro M M' A h
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      rcases h with ⟨hA, hT⟩ | ⟨hns, ls₁, ls₂, args₁, args₂, h1, h2, hn1, hn2, ⟨hconv⟩, Ts, hb1, hb2, hl, _⟩
      · exact Or.inl ⟨hA, typeSpineR_symm_of_envWfT hW hΓ hT⟩
      · refine Or.inr ⟨hns, ls₂, ls₁, args₂, args₁, h2, h1, hn2, hn1, ⟨.symm _ _ _ _ hconv⟩,
          Ts, hb2, hb1, hl, fun i => Or.inr ?_⟩
        rw [hbd (args.get i) (List.get_mem args i.val i.isLt)]
        exact lrSCore_bot _ _ _ _

/-- **Transitivity of `LRSCore` on All `BotFamCpt E` Compacts (`lrSCore_trans_botFamCpt`):**
    Extends `lrSCore_trans_botPiCpt` from `BotPiCpt` to `BotFamCpt E` under `ReadbackLaws E R`,
    `NormalUniqueR R`, `EnvWfT E`, and `CtxWfT E n Γ` alone — with **zero** `PiRowField` hypothesis! -/
theorem lrSCore_trans_botFamCpt (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {c : CptI} (hc : BotFamCpt E c) :
    ∀ {M N P A : Expr Nat}, LRSCore R E n Γ M N A c → LRSCore R E n Γ N P A c →
      LRSCore R E n Γ M P A c := by
  induction hc with
  | bot => intro M N P A _ _; exact lrSCore_bot _ _ _ _
  | sort =>
      intro M N P A h₁ h₂
      rw [LRSCore.eq_def] at h₁ h₂
      rw [LRSCore.eq_def]
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h2⟩ := h₂
      exact ⟨hA, u, u'', h1, h2⟩
  | @pi a f _ hbd _ iha ihf =>
      intro M N P A h₁ h₂
      rw [LRSCore.eq_def] at h₁ h₂
      rw [LRSCore.eq_def]
      obtain ⟨hA, A₁, B₁, A₂, B₂, h1, h2, ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩, ⟨u₁, hra⟩, hrf⟩ := h₁
      obtain ⟨_, A₂', B₂', A₃, B₃, h2', h3, _, ⟨hdom'⟩, ⟨hcod'⟩, ⟨_, hra'⟩, hrf'⟩ := h₂
      have e := hNU Γ h2 (fun _ hs => hL.pi_normal _ _ _ _ hs) h2'
        (fun _ hs => hL.pi_normal _ _ _ _ hs)
      injection e with eA eB
      subst eA; subst eB
      refine ⟨hA, A₁, B₁, A₃, B₃, h1, h3, ⟨hΓ₁⟩, ⟨.trans _ _ _ _ hdom hdom'⟩,
        ⟨.trans _ _ _ _ hcod (tyConvT_assump_dom hW hΓ hdom hcod')⟩,
        ⟨u₁, iha hra (lrSCore_sort_index_irrel hL a hra')⟩, ?_⟩
      intro s hs N N' hN hN' hcN _
      obtain ⟨hcN⟩ := hcN
      obtain ⟨v, hv⟩ := hrf s hs N N hN hN ⟨.refl _ _ _ hN⟩
        (fun u hu => by rw [hbd s hs u hu]; exact lrSCore_bot _ _ _ _)
      have hN₂ : HasTyT E n Γ N A₂ := hasTyT_of_tyConvT hN hdom
      have hN'₂ : HasTyT E n Γ N' A₂ := hasTyT_of_tyConvT hN' hdom
      obtain ⟨_, hv'⟩ := hrf' s hs N N' hN₂ hN'₂ ⟨convT_of_tyConv hcN hdom⟩
        (fun u hu => by rw [hbd s hs u hu]; exact lrSCore_bot _ _ _ _)
      exact ⟨v, ihf s hs hv (lrSCore_sort_index_irrel hL s.2 hv')⟩
  | @famSpine r m args hm hind _ hbd =>
      intro M N P A h₁ h₂
      rw [LRSCore.eq_def] at h₁ h₂
      rw [LRSCore.eq_def]
      rcases h₁ with ⟨hA, hT₁⟩ | ⟨hns, ls₁, ls₂, args₁, args₂, h1, h2, hn1, hn2, ⟨hconv₁⟩, Ts, hb1, _, hl, _⟩
      · rcases h₂ with ⟨_, hT₂⟩ | ⟨hns, _⟩
        · exact Or.inl ⟨hA, typeSpineR_trans_of_inductiveM hL hNU hW hΓ hm hind hT₁ hT₂⟩
        · obtain ⟨l, hl⟩ := hA
          exact (hns l hl).elim
      · rcases h₂ with ⟨⟨l, hl⟩, _⟩ | ⟨_, ls₂', ls₃, args₂', args₃, h2', h3, hn2', hn3, ⟨hconv₂⟩, _, _, hb3, _, _⟩
        · exact (hns l hl).elim
        · have e := hNU Γ h2 hn2 h2' hn2'
          obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
          injection hconst with _ hls
          subst hls; subst hxs
          refine Or.inr ⟨hns, ls₁, ls₃, args₁, args₃, h1, h3, hn1, hn3,
            ⟨.trans _ _ _ _ _ hconv₁ hconv₂⟩, Ts, hb1, hb3, hl, fun i => Or.inr ?_⟩
          rw [hbd (args.get i) (List.get_mem args i.val i.isLt)]
          exact lrSCore_bot _ _ _ _

theorem lrS_symm_botFamCpt (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {c : CptI} (hc : BotFamCpt E c) {M M' A : Expr Nat}
    (h : LRS R E n Γ M M' A c) : LRS R E n Γ M' M A c := by
  rcases h with hP | h
  · exact Or.inl hP
  · exact Or.inr (lrSCore_symm_botFamCpt hW hΓ hc h)

theorem lrS_trans_botFamCpt (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {c : CptI} (hc : BotFamCpt E c) {M N P A : Expr Nat}
    (h₁ : LRS R E n Γ M N A c) (h₂ : LRS R E n Γ N P A c) : LRS R E n Γ M P A c := by
  rcases h₁ with hP | h₁
  · exact Or.inl hP
  · rcases h₂ with hP | h₂
    · exact Or.inl hP
    · exact Or.inr (lrSCore_trans_botFamCpt hL hNU hW hΓ hc h₁ h₂)

/-- Every `args : List CptI` with `BotDemand args` and `args.length = xs.length` equals `botVecI xs`. -/
theorem eq_botVecI_of_botDemand :
    ∀ {args : List CptI} {xs : List (Expr Nat)},
      BotDemand args → args.length = xs.length → args = botVecI xs
  | [], [], _, _ => rfl
  | _ :: _, [], _, hlen => by cases hlen
  | [], _ :: _, _, hlen => by cases hlen
  | u :: args, x :: xs, hbd, hlen => by
      have hu : u = .bot := hbd u (List.mem_cons_self u args)
      have hrest : BotDemand args := fun v hv => hbd v (List.mem_cons_of_mem u hv)
      subst hu
      simp only [botVecI, List.map]
      exact congrArg (List.cons .bot) (eq_botVecI_of_botDemand hrest (Nat.succ.inj hlen))

/-- **Compact Transport Across `LRSCore` on All `FamProbeCpt E` Compacts
    (`modelAt_right_of_lrSCore_famProbeCpt`):**
    Extends `modelAt_right_of_lrSCore_probe` (`RcicNativeFamModelLRSPER`) from `ProbeCpt` to
    `FamProbeCpt E`, including `.spine r args` for saturated admitted `.inductiveM` heads! -/
theorem modelAt_right_of_lrSCore_famProbeCpt {M : CtxModel} (hM : CtxModelLaws E M)
    (hinv : ReadbackModelInv R M) (hW : EnvWfT E)
    {Γ : LCtx} {A B : Expr Nat} {u : Level} {c : CptI}
    (hc : FamProbeCpt E c) (h : LRSCore R E n Γ A B (.sort u) c) : M.at Γ B c := by
  cases hc with
  | bot => exact hM.bot_mem _ _
  | sort => exact modelAt_right_of_lrSCore_probe hM hinv .sort h
  | pi_bot_nil => exact modelAt_right_of_lrSCore_probe hM hinv .piBotNil h
  | @famSpine r m args hm hind hlen hbd =>
      rw [LRSCore.eq_def] at h
      rcases h with ⟨_, hT⟩ | ⟨hns, _⟩
      · rcases hT with ⟨m', _, ls', _, xs', _, _, hm', _, _, h2, _, _, _, _, _, hlen', _⟩ | ⟨hnot, _⟩
        · have em : m' = m := Option.some.inj (hm'.symm.trans hm)
          subst em
          have hargs : args = botVecI xs' := eq_botVecI_of_botDemand hbd (hlen.trans hlen'.symm)
          rw [hargs]
          exact (redR_modelInv hinv h2 _).mpr (hM.famApp_botVecI hW _ hm hind ls' xs')
        · exact (hnot m hm hind).elim
      · exact (hns u (.refl _)).elim

/-- **The Chain Form of `FundamentalLRSTM` Restricted to `FamProbeCpt E` Compacts
    (`FundamentalLRSTMFamProbe M R E n`):** -/
def FundamentalLRSTMFamProbe (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' →
    ∀ c, FamProbeCpt E c → M.at Γ A c → LRSCore R E n Γ A A' (.sort u) c

theorem fundamentalLRSTM_to_famProbe {M : CtxModel} (F : FundamentalLRSTM M R E n) :
    FundamentalLRSTMFamProbe M R E n :=
  fun {_} hΓ {_ _ _} hA hc c _ hcA => F hΓ hA hc c hcA

theorem fundamentalLRSTMProbe_of_famProbe {M : CtxModel} (F : FundamentalLRSTMFamProbe M R E n) :
    FundamentalLRSTMProbe M R E n := by
  intro Γ hΓ A A' u hA hc c hpc hcA
  cases hpc with
  | bot => exact F hΓ hA hc .bot .bot hcA
  | sort => exact F hΓ hA hc .sort .sort hcA
  | piBotNil => exact F hΓ hA hc (.pi .bot []) .pi_bot_nil hcA

/-- **The Chain Form at All `FamProbeCpt E` Compacts from Diagonal + Single `ConvT` Links
    (`fundamentalLRSTMFamProbe_of_links`):**
    Composes `TyConvT.trans` structurally via `lrSCore_trans_botFamCpt` and
    `modelAt_right_of_lrSCore_famProbeCpt` under `EnvWfT E` alone — with **zero** `PiRowField` and
    **zero** model soundness! -/
theorem fundamentalLRSTMFamProbe_of_links {M : CtxModel} (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hM : CtxModelLaws E M) (hinv : ReadbackModelInv R M) (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
      ∀ c, FamProbeCpt E c → M.at Γ A c → LRSCore R E n Γ A A (.sort u) c)
    (hlink : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) →
      ∀ c, FamProbeCpt E c → M.at Γ A c → LRSCore R E n Γ A B (.sort u) c) :
    FundamentalLRSTMFamProbe M R E n := by
  intro Γ hΓ A A' u hA hc
  revert u
  induction hc with
  | refl A => intro u hA c hpc hcA; exact hdiag hΓ hA c hpc hcA
  | of A B v hc => intro u _ c hpc hcA; exact lrSCore_sort_index_irrel hL c (hlink hΓ hc c hpc hcA)
  | trans A B C c₁ c₂ ih₁ ih₂ =>
      intro u hA c hpc hcA
      obtain ⟨v, hB⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ c₁ hA
      have r₁ := ih₁ hA c hpc hcA
      have hcB := modelAt_right_of_lrSCore_famProbeCpt hM hinv hW hpc r₁
      exact lrSCore_trans_botFamCpt hL hNU hW hΓ (botFamCpt_of_famProbeCpt hpc) r₁
        (lrSCore_sort_index_irrel hL c (ih₂ hB c hpc hcB))

theorem piRowField_of_fundamentalLRSTMFamProbe {M : CtxModel} (hL : ReadbackLaws E R)
    (hM : CtxModelLaws E M) (hW : EnvWfT E) (F : FundamentalLRSTMFamProbe M R E n) :
    PiRowField E n :=
  piRowField_of_fundamentalLRSTMProbe hL hM hW (fundamentalLRSTMProbe_of_famProbe F)

theorem not_tyConvT_pi_sort_of_fundamentalLRSTMProbe {M : CtxModel} (hL : ReadbackLaws E R)
    (hM : CtxModelLaws E M) (hW : EnvWfT E) (F : FundamentalLRSTMProbe M R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.pi A B) (.sort l)) : False := by
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · exact Expr.noConfusion heq
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    have hLR := F hΓ hPi hc (.pi .bot []) .piBotNil (hM.pi_bot_nil _ A B)
    rw [LRSCore.eq_def] at hLR
    obtain ⟨_, _, _, _, _, _, hred', _⟩ := hLR
    exact Expr.noConfusion (redR_sort_eq hL hred')

theorem not_tyConvT_sort_pi_of_fundamentalLRSTMProbe {M : CtxModel} (hL : ReadbackLaws E R)
    (hM : CtxModelLaws E M) (F : FundamentalLRSTMProbe M R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.sort l) (.pi A B)) : False := by
  have hLR := F hΓ (.sort Γ l) hc .sort .sort (hM.sort_mem _ l)
  rw [LRSCore.eq_def] at hLR
  obtain ⟨_, _, _, _, hred'⟩ := hLR
  exact Expr.noConfusion (redR_pi_eq hL hred')

theorem famApp_saturated_of_fundamentalLRSTMProbe {M : CtxModel} (hL : ReadbackLaws E R)
    (hM : CtxModelLaws E M) (hW : EnvWfT E) (F : FundamentalLRSTMProbe M R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (_hind : m.mclass = .inductiveM)
    {doms : List (Expr Nat)} {u : Level}
    (hpi : instantiateLevels ls m.mtype = policyPi doms (.sort u))
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = doms.length := by
  have hprow : PiRowField E n := piRowField_of_fundamentalLRSTMProbe hL hM hW F
  rcases Nat.lt_trichotomy xs.length doms.length with hlt | heq | hgt
  · exfalso
    have hne : doms.drop xs.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hlt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hpi' : instantiateLevels ls m.mtype =
        policyPi (doms.take xs.length) (policyPi (doms.drop xs.length) (.sort u)) := by
      rw [← List.take_append_drop xs.length doms] at hpi
      rw [hpi, policyPi_append]
    have hlen' : (doms.take xs.length).length = xs.length := by
      rw [List.length_take]
      first
        | exact Nat.min_eq_right (Nat.le_of_lt hlt)
        | exact Nat.min_eq_left (Nat.le_of_lt hlt)
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi' xs hlen' hty
    rw [hrest] at hconv
    simp only [policyPi] at hconv
    rw [instPrefix_pi] at hconv
    exact not_tyConvT_pi_sort_of_fundamentalLRSTMProbe hL hM hW F hΓ hconv
  · exact heq
  · exfalso
    have hne : xs.drop doms.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hgt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hsplit : foldApps (.const r ls) xs =
        foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
      calc foldApps (.const r ls) xs
          = foldApps (.const r ls) (xs.take doms.length ++ xs.drop doms.length) := by
              rw [List.take_append_drop]
        _ = foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
            foldApps_append _ _ _
    obtain ⟨_, _, ⟨hf⟩⟩ := hasTyT_foldApps_prefix_pi
      (f := foldApps (.const r ls) (xs.take doms.length))
      (hsplit ▸ hty) hrest
    have hlen' : doms.length = (xs.take doms.length).length := by
      rw [List.length_take]
      first
        | exact (Nat.min_eq_right (Nat.le_of_lt hgt)).symm
        | exact (Nat.min_eq_left (Nat.le_of_lt hgt)).symm
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi
      (xs.take doms.length) hlen' hf
    rw [instPrefix_sort] at hconv
    exact not_tyConvT_sort_pi_of_fundamentalLRSTMProbe hL hM F hΓ hconv

theorem famApp_length_eq_piDomsOf_of_fundamentalLRSTMProbe {M : CtxModel} (hL : ReadbackLaws E R)
    (hM : CtxModelLaws E M) (hW : EnvWfT E) (F : FundamentalLRSTMProbe M R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = (piDomsOf m.mtype).length := by
  have hlen := famApp_saturated_of_fundamentalLRSTMProbe hL hM hW F hΓ hm hind
    (instMtype_policyPi_of_inductiveM hW hm hind ls) hty
  rwa [List.length_map] at hlen

theorem famAppRow_of_fundamentalLRSTMFamProbe {M : CtxModel} (hL : ReadbackLaws E R)
    (hM : CtxModelLaws E M) (hW : EnvWfT E) (F : FundamentalLRSTMFamProbe M R E n) :
    FamAppRowLink E n := by
  intro Γ hΓ r m ls ls' xs xs' _ hm hind hty hc
  have hl : xs.length = (piDomsOf m.mtype).length :=
    famApp_length_eq_piDomsOf_of_fundamentalLRSTMProbe hL hM hW
      (fundamentalLRSTMProbe_of_famProbe F) hΓ hm hind hty
  exact lrSCore_famApp_components hL hW hm hind
    (F hΓ hty hc (.spine r (botVecI xs))
      (famProbeCpt_famSpine_botVecI hm hind hl)
      (hM.famApp_botVecI hW _ hm hind ls xs))

theorem famRelevantSlotConv_of_fundamentalLRSTMFamProbe {M : CtxModel} (hL : ReadbackLaws E R)
    (hM : CtxModelLaws E M) (hW : EnvWfT E) (F : FundamentalLRSTMFamProbe M R E n) :
    FamRelevantSlotConv E n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty hc
  have hrow := famAppRow_of_fundamentalLRSTMFamProbe hL hM hW F hΓ hm hind hty hc
  exact relevantSlotConv_of_convArgsT hW hm hind hrow.2.2

theorem typedRowsWf_of_allBelowScoped_fundamentalLRSTMFamProbe {M : CtxModel}
    (hL : ReadbackLaws E R) (hM : CtxModelLaws E M) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (F : FundamentalLRSTMFamProbe M R E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_build hW hBel
  piRow := piRowField_of_fundamentalLRSTMFamProbe hL hM hW F
  famAppRow := famAppRow_of_fundamentalLRSTMFamProbe hL hM hW F

/-- **`FamAppRowLink E n` Directly from Diagonal + Single `ConvT` Links at `FamProbeCpt E` Compacts
    (`famAppRow_of_links`):**
    The family-row counterpart of `piRowField_of_links` (`RcicNativeFamModelLRSPER` §4)! -/
theorem famAppRow_of_links {M : CtxModel} (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hM : CtxModelLaws E M) (hinv : ReadbackModelInv R M) (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
      ∀ c, FamProbeCpt E c → M.at Γ A c → LRSCore R E n Γ A A (.sort u) c)
    (hlink : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) →
      ∀ c, FamProbeCpt E c → M.at Γ A c → LRSCore R E n Γ A B (.sort u) c) :
    FamAppRowLink E n :=
  famAppRow_of_fundamentalLRSTMFamProbe hL hM hW
    (fundamentalLRSTMFamProbe_of_links hL hNU hM hinv hW hdiag hlink)

/-- **`FamRelevantSlotConv E n` (#7525) Directly from Diagonal + Single `ConvT` Links at
    `FamProbeCpt E` Compacts (`famRelevantSlotConv_of_links`):** -/
theorem famRelevantSlotConv_of_links {M : CtxModel} (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hM : CtxModelLaws E M) (hinv : ReadbackModelInv R M) (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
      ∀ c, FamProbeCpt E c → M.at Γ A c → LRSCore R E n Γ A A (.sort u) c)
    (hlink : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) →
      ∀ c, FamProbeCpt E c → M.at Γ A c → LRSCore R E n Γ A B (.sort u) c) :
    FamRelevantSlotConv E n :=
  famRelevantSlotConv_of_fundamentalLRSTMFamProbe hL hM hW
    (fundamentalLRSTMFamProbe_of_links hL hNU hM hinv hW hdiag hlink)

/-- **`TypedRowsWf E n` Directly from Diagonal + Single `ConvT` Links at `FamProbeCpt E` Compacts
    (`typedRowsWf_of_allBelowScoped_links`):** -/
theorem typedRowsWf_of_allBelowScoped_links {M : CtxModel} (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hM : CtxModelLaws E M) (hinv : ReadbackModelInv R M) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
      ∀ c, FamProbeCpt E c → M.at Γ A c → LRSCore R E n Γ A A (.sort u) c)
    (hlink : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) →
      ∀ c, FamProbeCpt E c → M.at Γ A c → LRSCore R E n Γ A B (.sort u) c) :
    TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_fundamentalLRSTMFamProbe hL hM hW hBel
    (fundamentalLRSTMFamProbe_of_links hL hNU hM hinv hW hdiag hlink)

/-- Right-hand diagonal recovery on `BotFamCpt E`: from `LRSCore R E n Γ A B (.sort u) c`,
    symmetry and transitivity (`lrSCore_symm_botFamCpt` + `lrSCore_trans_botFamCpt`) yield
    `LRSCore R E n Γ B B (.sort u) c` at the **exact same compact `c`** under `EnvWfT E` alone! -/
theorem lrSCore_right_diag_botFamCpt (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B : Expr Nat} {u : Level} {c : CptI}
    (hc : BotFamCpt E c) (h : LRSCore R E n Γ A B (.sort u) c) :
    LRSCore R E n Γ B B (.sort u) c :=
  lrSCore_trans_botFamCpt hL hNU hW hΓ hc (lrSCore_symm_botFamCpt hW hΓ hc h) h

/-- Unconditional diagonal of `.sort l` at `.sort` in `LRSCore`. -/
theorem lrSCore_sort_self (Γ : LCtx) (l u : Level) :
    LRSCore R E n Γ (.sort l) (.sort l) (.sort u) .sort := by
  rw [LRSCore.eq_def]
  exact ⟨⟨u, .refl _⟩, l, l, .refl _, .refl _⟩

/-- Unconditional diagonal of a well-typed `.pi A B` at `.pi .bot []` in `LRSCore`. -/
theorem lrSCore_pi_self_of_hasTyT {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B : Expr Nat} {u : Level} (hPi : HasTyT E n Γ (.pi A B) (.sort u)) :
    LRSCore R E n Γ (.pi A B) (.pi A B) (.sort u) (.pi .bot []) := by
  obtain ⟨u₁, _, hA, _, _⟩ := hasTyTInv_pi hPi rfl
  rw [LRSCore.eq_def]
  exact ⟨⟨u, .refl _⟩, A, B, A, B, .refl _, .refl _,
    ⟨.assumption Γ A u₁ hΓ hA⟩, ⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩,
    ⟨u₁, lrSCore_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- Building `LRSCore` on an admitted `.inductiveM` family spine from `TyConvT` and `ConvArgsT`. -/
theorem lrSCore_famApp_of_components {Γ : LCtx} {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w w' u : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hconv : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs'))
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (hty' : HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w'))
    (heqN : eqNList ls ls')
    (hlen : xs.length = (piDomsOf m.mtype).length)
    (hlen' : xs'.length = (piDomsOf m.mtype).length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs')
    (args : List CptI) :
    LRSCore R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')
      (.sort u) (.spine r args) := by
  rw [LRSCore.eq_def]
  exact Or.inl ⟨⟨u, .refl _⟩, Or.inl ⟨m, ls, ls', xs, xs', w, w', hm, hind, .refl _, .refl _,
    ⟨hty⟩, ⟨hty'⟩, ⟨hconv⟩, heqN, hlen, hlen', hargs⟩⟩

/-- Reflexivity of `LRSCore` on a saturated well-typed admitted `.inductiveM` family spine. -/
theorem lrSCore_famApp_refl_of_saturated (hW : EnvWfT E) (hpi : PiRowField E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level} {xs : List (Expr Nat)} {u : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort u))
    (hsat : xs.length = (piDomsOf m.mtype).length)
    (args : List CptI) :
    LRSCore R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls) xs)
      (.sort u) (.spine r args) :=
  lrSCore_famApp_of_components hm hind (.refl Γ _) hty hty (eqNList_refl ls) hsat hsat
    (convArgs_refl_instMtype hW hpi hΓ hm hind hsat hty) args

/-- **Model-Free Relation-Seeded Single `ConvT` Link Interface on `FamProbeCpt E`
    (`FamProbeLink R E n`):**
    Because `LRSCore` is a PER on `BotFamCpt E` under `EnvWfT E` alone (`lrSCore_symm_botFamCpt`,
    `lrSCore_trans_botFamCpt`), a single `ConvT` link seeded by the left diagonal
    `LRSCore R E n Γ A A (.sort u) c` chains across arbitrary `TyConvT.trans` steps with **zero**
    `CtxModel` and **zero** `ReadbackModelInv`! -/
def FamProbeLink (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level},
    ConvT E n Γ A B (.sort u) →
    ∀ c, FamProbeCpt E c →
      LRSCore R E n Γ A A (.sort u) c → LRSCore R E n Γ A B (.sort u) c

/-- **Model-Free `TyConvT` Chaining on `FamProbeCpt E` (`famProbe_chain`):**
    Chains `TyConvT E n Γ A A'` from `hAA : LRSCore R E n Γ A A (.sort u) c` at any
    `hpc : FamProbeCpt E c` using `lrSCore_right_diag_botFamCpt` and `lrSCore_trans_botFamCpt` —
    with **zero** `CtxModel` and **zero** `ReadbackModelInv`! -/
theorem famProbe_chain (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hlink : FamProbeLink R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hc : TyConvT E n Γ A A')
    {c : CptI} (hpc : FamProbeCpt E c)
    (hAA : LRSCore R E n Γ A A (.sort u) c) :
    LRSCore R E n Γ A A' (.sort u) c := by
  revert u
  induction hc with
  | refl A => intro u _ hAA; exact hAA
  | of A B v hc =>
      intro u _ hAA
      exact lrSCore_sort_index_irrel hL c
        (hlink hΓ hc c hpc (lrSCore_sort_index_irrel hL c hAA))
  | trans A B C c₁ _ ih₁ ih₂ =>
      intro u hA hAA
      obtain ⟨v, hB⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ c₁ hA
      have hbf : BotFamCpt E c := botFamCpt_of_famProbeCpt hpc
      have r₁ : LRSCore R E n Γ A B (.sort u) c := ih₁ hA hAA
      have hBB_u : LRSCore R E n Γ B B (.sort u) c :=
        lrSCore_right_diag_botFamCpt hL hNU hW hΓ hbf r₁
      have hBB_v : LRSCore R E n Γ B B (.sort v) c :=
        lrSCore_sort_index_irrel hL c hBB_u
      have r₂ : LRSCore R E n Γ B C (.sort v) c := ih₂ hB hBB_v
      exact lrSCore_trans_botFamCpt hL hNU hW hΓ hbf r₁
        (lrSCore_sort_index_irrel hL c r₂)

/-- **`PiRowField E n` Directly from Model-Free `FamProbeLink R E n` (`piRowField_of_famProbeLink`):** -/
theorem piRowField_of_famProbeLink (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLink R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrSCore_pi_components hL
      (famProbe_chain hL hNU hW hlink hΓ hPi hc .pi_bot_nil
        (lrSCore_pi_self_of_hasTyT hΓ hPi))

theorem not_tyConvT_pi_sort_of_famProbeLink (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLink R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.pi A B) (.sort l)) : False := by
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · exact Expr.noConfusion heq
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    have hLR := famProbe_chain hL hNU hW hlink hΓ hPi hc .pi_bot_nil
      (lrSCore_pi_self_of_hasTyT hΓ hPi)
    rw [LRSCore.eq_def] at hLR
    obtain ⟨_, _, _, _, _, _, hred', _⟩ := hLR
    exact Expr.noConfusion (redR_sort_eq hL hred')

theorem not_tyConvT_sort_pi_of_famProbeLink (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLink R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.sort l) (.pi A B)) : False := by
  have hLR := famProbe_chain hL hNU hW hlink hΓ (.sort Γ l) hc .sort
    (lrSCore_sort_self Γ l (.succ l))
  rw [LRSCore.eq_def] at hLR
  obtain ⟨_, _, _, _, hred'⟩ := hLR
  exact Expr.noConfusion (redR_pi_eq hL hred')

theorem famApp_saturated_of_famProbeLink (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLink R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (_hind : m.mclass = .inductiveM)
    {doms : List (Expr Nat)} {u : Level}
    (hpi : instantiateLevels ls m.mtype = policyPi doms (.sort u))
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = doms.length := by
  have hprow : PiRowField E n := piRowField_of_famProbeLink hL hNU hW hlink
  rcases Nat.lt_trichotomy xs.length doms.length with hlt | heq | hgt
  · exfalso
    have hne : doms.drop xs.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hlt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hpi' : instantiateLevels ls m.mtype =
        policyPi (doms.take xs.length) (policyPi (doms.drop xs.length) (.sort u)) := by
      rw [← List.take_append_drop xs.length doms] at hpi
      rw [hpi, policyPi_append]
    have hlen' : (doms.take xs.length).length = xs.length := by
      rw [List.length_take]
      first
        | exact Nat.min_eq_right (Nat.le_of_lt hlt)
        | exact Nat.min_eq_left (Nat.le_of_lt hlt)
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi' xs hlen' hty
    rw [hrest] at hconv
    simp only [policyPi] at hconv
    rw [instPrefix_pi] at hconv
    exact not_tyConvT_pi_sort_of_famProbeLink hL hNU hW hlink hΓ hconv
  · exact heq
  · exfalso
    have hne : xs.drop doms.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hgt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hsplit : foldApps (.const r ls) xs =
        foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
      calc foldApps (.const r ls) xs
          = foldApps (.const r ls) (xs.take doms.length ++ xs.drop doms.length) := by
              rw [List.take_append_drop]
        _ = foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
            foldApps_append _ _ _
    obtain ⟨_, _, ⟨hf⟩⟩ := hasTyT_foldApps_prefix_pi
      (f := foldApps (.const r ls) (xs.take doms.length))
      (hsplit ▸ hty) hrest
    have hlen' : doms.length = (xs.take doms.length).length := by
      rw [List.length_take]
      first
        | exact (Nat.min_eq_right (Nat.le_of_lt hgt)).symm
        | exact (Nat.min_eq_left (Nat.le_of_lt hgt)).symm
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi
      (xs.take doms.length) hlen' hf
    rw [instPrefix_sort] at hconv
    exact not_tyConvT_sort_pi_of_famProbeLink hL hNU hW hlink hΓ hconv

theorem famApp_length_eq_piDomsOf_of_famProbeLink (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLink R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = (piDomsOf m.mtype).length := by
  have hlen := famApp_saturated_of_famProbeLink hL hNU hW hlink hΓ hm hind
    (instMtype_policyPi_of_inductiveM hW hm hind ls) hty
  rwa [List.length_map] at hlen

/-- **`FamAppRowLink E n` Directly from Model-Free `FamProbeLink R E n`
    (`famAppRow_of_famProbeLink`):**
    Requires **only** `ReadbackLaws E R`, `NormalUniqueR R`, `EnvWfT E`, and `FamProbeLink R E n` —
    with **zero** `CtxModel`, **zero** `ReadbackModelInv`, and **zero** separate `hdiag` hypothesis! -/
theorem famAppRow_of_famProbeLink (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLink R E n) : FamAppRowLink E n := by
  intro Γ hΓ r m ls ls' xs xs' _ hm hind hty hc
  have hprow : PiRowField E n := piRowField_of_famProbeLink hL hNU hW hlink
  have hsat : xs.length = (piDomsOf m.mtype).length :=
    famApp_length_eq_piDomsOf_of_famProbeLink hL hNU hW hlink hΓ hm hind hty
  exact lrSCore_famApp_components hL hW hm hind
    (famProbe_chain hL hNU hW hlink hΓ hty hc
      (famProbeCpt_famSpine_botVecI hm hind hsat)
      (lrSCore_famApp_refl_of_saturated hW hprow hΓ hm hind hty hsat (botVecI xs)))

/-- **`FamRelevantSlotConv E n` (#7525) Directly from Model-Free `FamProbeLink R E n`
    (`famRelevantSlotConv_of_famProbeLink`):** -/
theorem famRelevantSlotConv_of_famProbeLink (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLink R E n) : FamRelevantSlotConv E n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty hc
  exact relevantSlotConv_of_convArgsT hW hm hind
    (famAppRow_of_famProbeLink hL hNU hW hlink hΓ hm hind hty hc).2.2

/-- **`TypedRowsWf E n` Directly from Model-Free `FamProbeLink R E n`
    (`typedRowsWf_of_allBelowScoped_famProbeLink`):** -/
theorem typedRowsWf_of_allBelowScoped_famProbeLink (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlink : FamProbeLink R E n) : TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_build hW hBel
  piRow := piRowField_of_famProbeLink hL hNU hW hlink
  famAppRow := famAppRow_of_famProbeLink hL hNU hW hlink

/-- Equivalence between `WhRedRecKCanon E Γ a b` and `RedR (WhStepRecKCanon E) Γ a b`. -/
theorem redR_of_whRedRecKCanon {Γ : LCtx} {a b : Expr Nat} (h : WhRedRecKCanon E Γ a b) :
    RedR (WhStepRecKCanon E) Γ a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step hs ih

theorem whRedRecKCanon_of_redR {Γ : LCtx} {a b : Expr Nat} (h : RedR (WhStepRecKCanon E) Γ a b) :
    WhRedRecKCanon E Γ a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step hs ih

/-- **Canonical Deterministic K-Readback `WhStepRecKCanon E` Satisfies `ReadbackLaws E`
    (`readbackLaws_whStepRecKCanon`):** -/
theorem readbackLaws_whStepRecKCanon (E : ResolvedEnv) : ReadbackLaws E (WhStepRecKCanon E) where
  sort_normal := fun _ _ _ h => whStepRecKCanon_sort_false h
  pi_normal := fun _ _ _ _ h => whStepRecKCanon_pi_false h
  famApp_normal := fun hW _ _ _ hm hind _ _ _ h => whStepRecKCanon_famApp_false hW hm hind h
  appHead := fun _ _ _ _ h => .appHead h
  beta := fun _ A b a => .beta A b a

/-- **Canonical Deterministic K-Readback `WhStepRecKCanon E` Satisfies `DetR` Under `EnvWfT E` Alone
    (`detR_whStepRecKCanon`):** -/
theorem detR_whStepRecKCanon (hW : EnvWfT E) : DetR (WhStepRecKCanon E) :=
  fun Γ _ _ _ h₁ h₂ => whDetRecKCanon_of_envWfT hW Γ h₁ h₂

/-- **Canonical Deterministic K-Readback `WhStepRecKCanon E` Satisfies `NormalUniqueR` Under
    `EnvWfT E` Alone (`normalUniqueR_whStepRecKCanon`):** -/
theorem normalUniqueR_whStepRecKCanon (hW : EnvWfT E) : NormalUniqueR (WhStepRecKCanon E) :=
  normalUniqueR_of_det (detR_whStepRecKCanon hW)

/-- `FamAppRowLink E n` instantiated at `WhStepRecKCanon E` from `EnvWfT E` + `FamProbeLink` alone. -/
theorem famAppRow_of_famProbeLink_whStepRecKCanon (hW : EnvWfT E)
    (hlink : FamProbeLink (WhStepRecKCanon E) E n) : FamAppRowLink E n :=
  famAppRow_of_famProbeLink (readbackLaws_whStepRecKCanon E) (normalUniqueR_whStepRecKCanon hW)
    hW hlink

/-- `FamRelevantSlotConv E n` instantiated at `WhStepRecKCanon E` from `EnvWfT E` + `FamProbeLink` alone. -/
theorem famRelevantSlotConv_of_famProbeLink_whStepRecKCanon (hW : EnvWfT E)
    (hlink : FamProbeLink (WhStepRecKCanon E) E n) : FamRelevantSlotConv E n :=
  famRelevantSlotConv_of_famProbeLink (readbackLaws_whStepRecKCanon E)
    (normalUniqueR_whStepRecKCanon hW) hW hlink

/-- `TypedRowsWf E n` instantiated at `WhStepRecKCanon E` from `EnvWfT E` + `AllBelowScoped` +
    `FamProbeLink` alone. -/
theorem typedRowsWf_of_allBelowScoped_famProbeLink_whStepRecKCanon (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlink : FamProbeLink (WhStepRecKCanon E) E n) : TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_famProbeLink (readbackLaws_whStepRecKCanon E)
    (normalUniqueR_whStepRecKCanon hW) hW hBel hlink

/-- Positive `W-K-OPEN` verification in `LRSCore (WhStepRecKCanon trueEnvU)` on `trueVarSort`. -/
theorem lrSCore_whStepRecKCanon_trueVarSort (n : Nat) :
    LRSCore (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarSort (.sort .zero) (.sort (.succ .zero)) .sort := by
  rw [LRSCore.eq_def]
  exact ⟨⟨_, .refl _⟩, _, _, redR_of_whRedRecKCanon whRedRecKCanon_trueVarSort, .refl _⟩

theorem lrSCore_whStepRecKCanon_trueVarSort_symm (n : Nat) :
    LRSCore (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      (.sort .zero) trueVarSort (.sort (.succ .zero)) .sort := by
  rw [LRSCore.eq_def]
  exact ⟨⟨_, .refl _⟩, _, _, .refl _, redR_of_whRedRecKCanon whRedRecKCanon_trueVarSort⟩

/-- Positive `W-K-OPEN` verification in `LRSCore (WhStepRecKCanon trueEnvU)` on `trueVarPi` at
    `.pi .bot []`. -/
theorem lrSCore_whStepRecKCanon_trueVarPi (n : Nat) :
    LRSCore (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarPi PiModelDeltaIotaAudit.idPiProp (.sort (.succ .zero)) (.pi .bot []) := by
  rw [LRSCore.eq_def]
  exact ⟨⟨_, .refl _⟩, .sort .zero, .bvar 0, .sort .zero, .bvar 0,
    redR_of_whRedRecKCanon whRedRecKCanon_trueVarPi, .refl _,
    ⟨.assumption trueVarCtx (.sort .zero) (.succ .zero) (trueVarCtx_wf n) (.sort trueVarCtx .zero)⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.succ .zero, lrSCore_bot _ _ _ _⟩,
    fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- Positive `W-K-OPEN` verification in `LRSCore (WhStepRecKCanon trueEnvU)` on `trueVarFam` at
    `.spine 0 []`. -/
theorem lrSCore_whStepRecKCanon_trueVarFam (n : Nat) :
    LRSCore (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarFam (.const 0 []) (.sort .zero) (.spine 0 []) := by
  rw [LRSCore.eq_def]
  refine Or.inl ⟨⟨_, .refl _⟩, Or.inl ⟨trueFamMember, [], [], [], [], .zero, .zero,
    rfl, rfl, redR_of_whRedRecKCanon whRedRecKCanon_trueVarFam, .refl _,
    ⟨.const trueVarCtx 0 [] trueFamMember rfl rfl rfl⟩,
    ⟨.const trueVarCtx 0 [] trueFamMember rfl rfl rfl⟩,
    ⟨.refl trueVarCtx (.const 0 [])⟩, trivial, rfl, rfl, .nil _⟩⟩

/-- Positive `W-K-AND` verification in `LRSCore (WhStepRecKCanon andEnvU)` on `mixAndRedex` at
    `.pi .bot []`. -/
theorem lrSCore_whStepRecKCanon_mixAnd :
    LRSCore (WhStepRecKCanon andEnvU) andEnvU 0 mixAndCtx
      mixAndRedex mixPi (.sort (.succ .zero)) (.pi .bot []) := by
  rw [LRSCore.eq_def]
  exact ⟨⟨_, .refl _⟩, .sort .zero, .sort .zero, .sort .zero, .sort .zero,
    redR_of_whRedRecKCanon whRedRecKCanon_mixAndRedex, .refl _,
    ⟨.assumption mixAndCtx (.sort .zero) (.succ .zero)
      Rcic.Domain.Model.PiInversion.mixAndCtx_wf (.sort mixAndCtx .zero)⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.succ .zero, lrSCore_bot _ _ _ _⟩,
    fun _ hs => (List.not_mem_nil _ hs).elim⟩


/-! ### §3 — Family-Head Model Fragment Over the Typed-Demand Model `CptT` / `ApproxT` / `ElT` / `SemEqT` -/

/-- Pointwise `ApproxT` along an argument spine `xs : List (Expr Nat)` and compact list `us : List CptT`. -/
inductive ApproxTArgs (E : ResolvedEnv) (ρ : EnvT) : List (Expr Nat) → List CptT → Prop
  | nil : ApproxTArgs E ρ [] []
  | cons {x : Expr Nat} {xs : List (Expr Nat)} {u : CptT} {us : List CptT}
      (hx : ApproxT E ρ x u) (hxs : ApproxTArgs E ρ xs us) :
      ApproxTArgs E ρ (x :: xs) (u :: us)

theorem approxTArgs_length {ρ : EnvT} :
    ∀ {xs : List (Expr Nat)} {us : List CptT}, ApproxTArgs E ρ xs us → xs.length = us.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hxs => congrArg Nat.succ (approxTArgs_length hxs)

theorem approxTArgs_snoc {ρ : EnvT} :
    ∀ {xs : List (Expr Nat)} {us : List CptT} {x : Expr Nat} {u : CptT},
      ApproxTArgs E ρ xs us → ApproxT E ρ x u →
      ApproxTArgs E ρ (xs ++ [x]) (us ++ [u])
  | [], [], _, _, .nil, hx => .cons hx .nil
  | _ :: _, _ :: _, _, _, .cons hy hys, hx => .cons hy (approxTArgs_snoc hys hx)

theorem approxTArgs_snoc_inv {ρ : EnvT} :
    ∀ {xs : List (Expr Nat)} {x : Expr Nat} {us : List CptT},
      ApproxTArgs E ρ (xs ++ [x]) us →
      ∃ us₀ u, us = us₀ ++ [u] ∧ ApproxTArgs E ρ xs us₀ ∧ ApproxT E ρ x u
  | [], x, us, h => by
      cases h with
      | cons hx hnil =>
          cases hnil
          exact ⟨[], _, rfl, .nil, hx⟩
  | y :: xs, x, us, h => by
      cases h with
      | cons hy hrest =>
          obtain ⟨us₀, u, rfl, hxs, hx⟩ := approxTArgs_snoc_inv hrest
          exact ⟨_ :: us₀, u, rfl, .cons hy hxs, hx⟩

/-- Applying a `.spine r args` compact across `foldApps f xs` in `ApproxT`. -/
theorem approxT_foldApps_spine {ρ : EnvT} {f : Expr Nat} {r : Nat}
    {args : List CptT} {xs : List (Expr Nat)} {us : List CptT}
    (hf : ApproxT E ρ f (.spine r args)) (hxs : ApproxTArgs E ρ xs us) :
    ApproxT E ρ (foldApps f xs) (.spine r (args ++ us)) := by
  induction hxs generalizing f args with
  | nil =>
      simp only [foldApps, List.append_nil]
      exact hf
  | @cons x xs u us hx hxs ih =>
      simp only [foldApps]
      have h' := ih (.appSpine hf hx)
      simpa only [List.append_assoc, List.singleton_append] using h'

/-- An admitted `.inductiveM` member `r` is never a `PropCtorT` (`m.mclass = .inductiveM ≠ .constructorM`). -/
theorem not_propCtorT_of_inductiveM {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) :
    ¬ PropCtorT E r := by
  rintro ⟨m', _, _, hm', hctor, _⟩
  have e : m = m' := Option.some.inj (hm.symm.trans hm')
  subst e
  rw [hind] at hctor
  exact MemberClass.noConfusion hctor

/-- Under `EnvWfT E`, an admitted `.inductiveM` constant `.const r ls` has `.spine r []` in `ApproxT`. -/
theorem approxT_const_inductiveM (hW : EnvWfT E) (ρ : EnvT) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (ls : List Level) :
    ApproxT E ρ (.const r ls) (.spine r []) :=
  .const ρ r ls (rigidConst_of_inductiveM hW hm hind) (not_propCtorT_of_inductiveM hm hind)

/-- Exact inversion of `ApproxT E ρ (.const r ls) c` for an admitted `.inductiveM` member `r`. -/
theorem approxT_const_inductiveM_inv (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) {ls : List Level} {c : CptT}
    (h : ApproxT E ρ (.const r ls) c) :
    c = .bot ∨ c = .spine r [] :=
  approxT_rigid_const_inv (rigidConst_of_inductiveM hW hm hind) h

/-- **Family-Spine Approximation in `ApproxT` (`approxT_famApp`):**
    For any admitted `.inductiveM` member `r`, `ApproxTArgs E ρ xs us` yields
    `ApproxT E ρ (foldApps (.const r ls) xs) (.spine r us)`. -/
theorem approxT_famApp (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (ls : List Level)
    {xs : List (Expr Nat)} {us : List CptT} (hxs : ApproxTArgs E ρ xs us) :
    ApproxT E ρ (foldApps (.const r ls) xs) (.spine r us) := by
  have h := approxT_foldApps_spine (approxT_const_inductiveM hW ρ hm hind ls) hxs
  simpa only [List.nil_append] using h

theorem approxT_foldApps_const_inductiveM_inv_aux {ρ : EnvT} {r : Nat} :
    ∀ (xs : List (Expr Nat)) {f : Expr Nat} {pre : List (Expr Nat)} {c : CptT},
      (∀ {d : CptT}, ApproxT E ρ f d → d = .bot ∨ ∃ us₀, d = .spine r us₀ ∧ ApproxTArgs E ρ pre us₀) →
      ApproxT E ρ (foldApps f xs) c →
      c = .bot ∨ ∃ us, c = .spine r us ∧ ApproxTArgs E ρ (pre ++ xs) us
  | [], _, pre, _, hf, h => by
      simp only [foldApps, List.append_nil] at h ⊢
      exact hf h
  | x :: xs, f, pre, c, hf, h => by
      simp only [foldApps] at h
      have hf' : ∀ {d : CptT}, ApproxT E ρ (.app f x) d →
          d = .bot ∨ ∃ us₀, d = .spine r us₀ ∧ ApproxTArgs E ρ (pre ++ [x]) us₀ := by
        intro d hd
        rcases approxT_app_inv hd with rfl | ⟨g, s, rfl, hfg, _, _⟩ | ⟨r', args, u, rfl, hfs, hx⟩
        · exact Or.inl rfl
        · rcases hf hfg with hbot | ⟨_, hsp, _⟩
          · exact CptT.noConfusion hbot
          · exact CptT.noConfusion hsp
        · rcases hf hfs with hbot | ⟨us₀, hsp, hpre⟩
          · exact CptT.noConfusion hbot
          · injection hsp with hr hus
            subst hr; subst hus
            exact Or.inr ⟨args ++ [u], rfl, approxTArgs_snoc hpre hx⟩
      have hres := approxT_foldApps_const_inductiveM_inv_aux xs hf' h
      simpa only [List.append_assoc, List.singleton_append] using hres

/-- **Exact Inversion of `ApproxT` on an Admitted `.inductiveM` Spine
    (`approxT_foldApps_const_inductiveM_inv`):**
    Because `.const r ls` only has `.bot` and `.spine r []` compacts (never `.lam g`), applying
    `foldApps (.const r ls) xs` can only produce `.bot` or `.spine r us` with `ApproxTArgs E ρ xs us`! -/
theorem approxT_foldApps_const_inductiveM_inv (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (ls : List Level)
    (xs : List (Expr Nat)) {c : CptT}
    (h : ApproxT E ρ (foldApps (.const r ls) xs) c) :
    c = .bot ∨ ∃ us, c = .spine r us ∧ ApproxTArgs E ρ xs us := by
  refine approxT_foldApps_const_inductiveM_inv_aux (pre := []) xs (fun hd => ?_) h
  rcases approxT_const_inductiveM_inv hW hm hind hd with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨[], rfl, .nil⟩

/-- Two-way characterization (`↔`) of `ApproxT` on an admitted `.inductiveM` spine. -/
theorem approxT_famApp_iff (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (ls : List Level)
    (xs : List (Expr Nat)) (c : CptT) :
    ApproxT E ρ (foldApps (.const r ls) xs) c ↔
      c = .bot ∨ ∃ us, c = .spine r us ∧ ApproxTArgs E ρ xs us :=
  ⟨approxT_foldApps_const_inductiveM_inv hW hm hind ls xs,
   fun h => h.elim (fun e => e ▸ .bot ρ _) (fun ⟨_, e, hxs⟩ => e ▸ approxT_famApp hW hm hind ls hxs)⟩

/-- All-`.bot` probe vector over `CptT` matching an argument spine `xs`. -/
def botVecT : List (Expr Nat) → List CptT
  | [] => []
  | _ :: xs => .bot :: botVecT xs

theorem botVecT_length : ∀ (xs : List (Expr Nat)), (botVecT xs).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (botVecT_length xs)

theorem botVecT_eq_of_length_eq :
    ∀ {xs ys : List (Expr Nat)}, xs.length = ys.length → botVecT xs = botVecT ys
  | [], [], _ => rfl
  | _ :: _, [], h => Nat.noConfusion h
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, _ :: _, h => congrArg (List.cons CptT.bot) (botVecT_eq_of_length_eq (Nat.succ.inj h))

theorem botDemandT_botVecT : ∀ (xs : List (Expr Nat)), BotDemandT (botVecT xs)
  | [], _, h => (List.not_mem_nil _ h).elim
  | _ :: xs, u, h => by
      rcases List.mem_cons.mp h with rfl | hrest
      · rfl
      · exact botDemandT_botVecT xs u hrest

theorem eq_botVecT_of_botDemandT :
    ∀ {args : List CptT} {xs : List (Expr Nat)},
      BotDemandT args → args.length = xs.length → args = botVecT xs
  | [], [], _, _ => rfl
  | _ :: _, [], _, hlen => Nat.noConfusion hlen
  | [], _ :: _, _, hlen => Nat.noConfusion hlen
  | u :: args, _ :: xs, hbd, hlen => by
      have hu : u = .bot := hbd u (List.mem_cons_self u args)
      have hrest : BotDemandT args := fun v hv => hbd v (List.mem_cons_of_mem u hv)
      subst hu
      exact congrArg (List.cons .bot) (eq_botVecT_of_botDemandT hrest (Nat.succ.inj hlen))

theorem approxTArgs_botVecT (ρ : EnvT) :
    ∀ (xs : List (Expr Nat)), ApproxTArgs E ρ xs (botVecT xs)
  | [] => .nil
  | x :: xs => .cons (.bot ρ x) (approxTArgs_botVecT ρ xs)

/-- Every admitted `.inductiveM` spine `foldApps (.const r ls) xs` has `.spine r (botVecT xs)` in `ApproxT`. -/
theorem approxT_famApp_botVecT (hW : EnvWfT E) (ρ : EnvT) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (ls : List Level) (xs : List (Expr Nat)) :
    ApproxT E ρ (foldApps (.const r ls) xs) (.spine r (botVecT xs)) :=
  approxT_famApp hW hm hind ls (approxTArgs_botVecT ρ xs)

theorem approxT_famApp_botVecT_of_length_eq (hW : EnvWfT E) (ρ : EnvT) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (ls : List Level) {xs ys : List (Expr Nat)} (hlen : xs.length = ys.length) :
    ApproxT E ρ (foldApps (.const r ls) xs) (.spine r (botVecT ys)) := by
  rw [← botVecT_eq_of_length_eq hlen]
  exact approxT_famApp_botVecT hW ρ hm hind ls xs

/-- Single-slot probe vector over `CptT`: `u` at index `i`, `.bot` elsewhere. -/
def slotVecT : List (Expr Nat) → Nat → CptT → List CptT
  | [], _, _ => []
  | _ :: xs, 0, u => u :: botVecT xs
  | _ :: xs, i + 1, u => .bot :: slotVecT xs i u

theorem approxTArgs_slotVecT {ρ : EnvT} :
    ∀ (xs : List (Expr Nat)) (i : Nat) {u : CptT},
      ApproxT E ρ (xs.getD i (.sort .zero)) u →
      ApproxTArgs E ρ xs (slotVecT xs i u)
  | [], _, _, _ => .nil
  | _ :: xs, 0, _, hu => .cons hu (approxTArgs_botVecT ρ xs)
  | x :: xs, i + 1, _, hu => .cons (.bot ρ x) (approxTArgs_slotVecT xs i hu)

theorem approxTArgs_slotVecT_inv {ρ : EnvT} :
    ∀ {xs xs' : List (Expr Nat)} {i : Nat} {u : CptT},
      i < xs.length →
      ApproxTArgs E ρ xs' (slotVecT xs i u) →
      ApproxT E ρ (xs'.getD i (.sort .zero)) u
  | [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], 0, _, _, h => by cases h
  | _ :: _, [], _ + 1, _, _, h => by cases h
  | _ :: _, _ :: _, 0, _, _, .cons hx _ => hx
  | _ :: xs, _ :: xs', i + 1, _, hi, .cons _ hrest =>
      approxTArgs_slotVecT_inv (xs := xs) (xs' := xs') (i := i) (Nat.lt_of_succ_lt_succ hi) hrest

theorem approxT_famApp_slotVecT (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (ls : List Level) (xs : List (Expr Nat)) (i : Nat) {u : CptT}
    (hu : ApproxT E ρ (xs.getD i (.sort .zero)) u) :
    ApproxT E ρ (foldApps (.const r ls) xs) (.spine r (slotVecT xs i u)) :=
  approxT_famApp hW hm hind ls (approxTArgs_slotVecT xs i hu)

/-- **Model Family-Head & Length Injectivity in `SemEqT` (`semEqT_famApp_head_length`):** -/
theorem semEqT_famApp_head_length (hW : EnvWfT E) {ρ : EnvT}
    {r r' : Nat} {m m' : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hm' : E.members r' = some m') (hind' : m'.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    (heq : SemEqT E ρ (foldApps (.const r ls) xs) (foldApps (.const r' ls') xs')) :
    r = r' ∧ xs.length = xs'.length := by
  have hL := approxT_famApp_botVecT hW ρ hm hind ls xs
  have hR := (heq (.spine r (botVecT xs))).mp hL
  rcases approxT_foldApps_const_inductiveM_inv hW hm' hind' ls' xs' hR with hbot | ⟨us, he, hxs'⟩
  · exact CptT.noConfusion hbot
  · injection he with hr hus
    subst hr; subst hus
    exact ⟨rfl, (botVecT_length xs).symm.trans (approxTArgs_length hxs').symm⟩

/-- **Model Family-Slot Injectivity in `SemEqT` (`semEqT_famApp_slot`):** -/
theorem semEqT_famApp_slot (hW : EnvWfT E) {ρ : EnvT}
    {r r' : Nat} {m m' : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hm' : E.members r' = some m') (hind' : m'.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    (heq : SemEqT E ρ (foldApps (.const r ls) xs) (foldApps (.const r' ls') xs'))
    {i : Nat} (hi : i < xs.length) :
    SemEqT E ρ (xs.getD i (.sort .zero)) (xs'.getD i (.sort .zero)) := by
  obtain ⟨rfl, hlen⟩ := semEqT_famApp_head_length hW hm hind hm' hind' heq
  intro u
  constructor
  · intro hu
    have hL := approxT_famApp_slotVecT hW hm hind ls xs i hu
    have hR := (heq (.spine r (slotVecT xs i u))).mp hL
    rcases approxT_foldApps_const_inductiveM_inv hW hm' hind' ls' xs' hR with hbot | ⟨us, he, hxs'⟩
    · exact CptT.noConfusion hbot
    · injection he with _ hus
      subst hus
      exact approxTArgs_slotVecT_inv hi hxs'
  · intro hu
    have hi' : i < xs'.length := hlen ▸ hi
    have hR := approxT_famApp_slotVecT hW hm' hind' ls' xs' i hu
    have hL := (heq (.spine r (slotVecT xs' i u))).mpr hR
    rcases approxT_foldApps_const_inductiveM_inv hW hm hind ls xs hL with hbot | ⟨us, he, hxs⟩
    · exact CptT.noConfusion hbot
    · injection he with _ hus
      subst hus
      exact approxTArgs_slotVecT_inv hi' hxs

/-- **Full Model Family-Spine Injectivity in `SemEqT` (`semEqT_famApp_inj`):** -/
theorem semEqT_famApp_inj (hW : EnvWfT E) {ρ : EnvT}
    {r r' : Nat} {m m' : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hm' : E.members r' = some m') (hind' : m'.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    (heq : SemEqT E ρ (foldApps (.const r ls) xs) (foldApps (.const r' ls') xs')) :
    r = r' ∧ xs.length = xs'.length ∧
      ∀ i, i < xs.length → SemEqT E ρ (xs.getD i (.sort .zero)) (xs'.getD i (.sort .zero)) :=
  ⟨(semEqT_famApp_head_length hW hm hind hm' hind' heq).1,
   (semEqT_famApp_head_length hW hm hind hm' hind' heq).2,
   fun _ hi => semEqT_famApp_slot hW hm hind hm' hind' heq hi⟩

/-- Π-types and admitted `.inductiveM` family spines are semantically disjoint in `SemEqT`. -/
theorem semEqT_pi_famApp_disjoint (hW : EnvWfT E) {ρ : EnvT} {A B : Expr Nat}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {xs : List (Expr Nat)}
    (heq : SemEqT E ρ (.pi A B) (foldApps (.const r ls) xs)) : False := by
  have hL : ApproxT E ρ (.pi A B) (.pi .bot []) := approxT_pi_bot_nil E ρ A B
  have hR := (heq (.pi .bot [])).mp hL
  rcases approxT_foldApps_const_inductiveM_inv hW hm hind ls xs hR with hbot | ⟨_, he, _⟩
  · exact CptT.noConfusion hbot
  · exact CptT.noConfusion he

/-- Sorts and admitted `.inductiveM` family spines are semantically disjoint in `SemEqT`. -/
theorem semEqT_sort_famApp_disjoint (hW : EnvWfT E) {ρ : EnvT} {u : Level}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {xs : List (Expr Nat)}
    (heq : SemEqT E ρ (.sort u) (foldApps (.const r ls) xs)) : False := by
  have hL : ApproxT E ρ (.sort u) (sortCode u) := .sort ρ u
  have hR := (heq (sortCode u)).mp hL
  rcases approxT_foldApps_const_inductiveM_inv hW hm hind ls xs hR with hbot | ⟨_, he, _⟩
  · rcases sortCode_prop_or_sort u with hsc | hsc <;> (rw [hsc] at hbot; exact CptT.noConfusion hbot)
  · rcases sortCode_prop_or_sort u with hsc | hsc <;> (rw [hsc] at he; exact CptT.noConfusion he)

/-- Pointwise `SemEqT` along two argument spines `xs, xs' : List (Expr Nat)`. -/
inductive SemEqTArgs (E : ResolvedEnv) (ρ : EnvT) : List (Expr Nat) → List (Expr Nat) → Prop
  | nil : SemEqTArgs E ρ [] []
  | cons {x x' : Expr Nat} {xs xs' : List (Expr Nat)}
      (hx : SemEqT E ρ x x') (hxs : SemEqTArgs E ρ xs xs') :
      SemEqTArgs E ρ (x :: xs) (x' :: xs')

theorem semEqTArgs_refl (ρ : EnvT) : ∀ (xs : List (Expr Nat)), SemEqTArgs E ρ xs xs
  | [] => .nil
  | _ :: xs => .cons (fun _ => Iff.rfl) (semEqTArgs_refl ρ xs)

theorem semEqTArgs_symm {ρ : EnvT} :
    ∀ {xs xs' : List (Expr Nat)}, SemEqTArgs E ρ xs xs' → SemEqTArgs E ρ xs' xs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hx hxs => .cons (fun c => (hx c).symm) (semEqTArgs_symm hxs)

theorem semEqTArgs_trans {ρ : EnvT} :
    ∀ {xs ys zs : List (Expr Nat)},
      SemEqTArgs E ρ xs ys → SemEqTArgs E ρ ys zs → SemEqTArgs E ρ xs zs
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons hx₁ hxs₁, .cons hx₂ hxs₂ =>
      .cons (fun c => (hx₁ c).trans (hx₂ c)) (semEqTArgs_trans hxs₁ hxs₂)

theorem approxTArgs_congr {ρ : EnvT} :
    ∀ {xs xs' : List (Expr Nat)} {us : List CptT},
      SemEqTArgs E ρ xs xs' → (ApproxTArgs E ρ xs us ↔ ApproxTArgs E ρ xs' us)
  | [], [], _, .nil => Iff.rfl
  | _ :: _, _ :: _, [], .cons _ _ => Iff.intro (fun h => by cases h) (fun h => by cases h)
  | _ :: _, _ :: _, u :: _, .cons hx hxs =>
      Iff.intro
        (fun h => match h with | .cons hu hus => .cons ((hx u).mp hu) ((approxTArgs_congr hxs).mp hus))
        (fun h => match h with | .cons hu hus => .cons ((hx u).mpr hu) ((approxTArgs_congr hxs).mpr hus))

theorem semEqT_const_inductiveM_ls (hW : EnvWfT E) (ρ : EnvT) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (ls ls' : List Level) :
    SemEqT E ρ (.const r ls) (.const r ls') := by
  intro c
  constructor
  · intro h
    rcases approxT_const_inductiveM_inv hW hm hind h with rfl | rfl
    · exact .bot ρ _
    · exact approxT_const_inductiveM hW ρ hm hind ls'
  · intro h
    rcases approxT_const_inductiveM_inv hW hm hind h with rfl | rfl
    · exact .bot ρ _
    · exact approxT_const_inductiveM hW ρ hm hind ls

/-- Congruence of `SemEqT` across an admitted `.inductiveM` family spine. -/
theorem semEqT_famApp_congr (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (ls ls' : List Level) {xs xs' : List (Expr Nat)} (hxs : SemEqTArgs E ρ xs xs') :
    SemEqT E ρ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') := by
  intro c
  rw [approxT_famApp_iff hW hm hind ls xs c, approxT_famApp_iff hW hm hind ls' xs' c]
  exact or_congr_right (exists_congr fun _ => and_congr_right fun _ => approxTArgs_congr hxs)

/-- Every `ApproxT` compact of an admitted `.inductiveM` family spine is a type code (`TyCodeCT`). -/
theorem tyCodeCT_of_approxT_famApp (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {xs : List (Expr Nat)} {u : CptT}
    (hu : ApproxT E ρ (foldApps (.const r ls) xs) u) :
    TyCodeCT u := by
  rcases approxT_foldApps_const_inductiveM_inv hW hm hind ls xs hu with rfl | ⟨us, rfl, _⟩
  · exact .bot
  · exact .spine r us

/-- Every `ApproxT` compact of a proposition family spine (`piBody m.mtype = .sort .zero`) is a
    proposition code (`IsPropCT E`). -/
theorem isPropCT_of_approxT_famApp_prop (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hprop : piBody m.mtype = .sort .zero)
    {ls : List Level} {xs : List (Expr Nat)} {u : CptT}
    (hu : ApproxT E ρ (foldApps (.const r ls) xs) u) :
    IsPropCT E u := by
  rcases approxT_foldApps_const_inductiveM_inv hW hm hind ls xs hu with rfl | ⟨_, rfl, _⟩
  · exact .bot
  · exact .spine hm hprop

/-- **T1 Collapse on Proposition Family Spines (`elT_famApp_prop_bot`):**
    If an admitted `.inductiveM` family `r` is declared into `Sort 0` (`piBody m.mtype = .sort .zero`),
    then every element of `ElT E ρ (foldApps (.const r ls) xs)` is `.bot`. -/
theorem elT_famApp_prop_bot (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hprop : piBody m.mtype = .sort .zero)
    {ls : List Level} {xs : List (Expr Nat)} {u : CptT}
    (h : ElT E ρ (foldApps (.const r ls) xs) u) :
    u = .bot :=
  elT_bot_of_propIdeal (fun _ ha => isPropCT_of_approxT_famApp_prop hW hm hind hprop ha) h

/-- A spine compact `.spine r args` of a family with `piBody m.mtype ≠ .sort .zero` is not a
    proposition code. -/
theorem not_isPropCT_spine_of_piBody_ne_zero {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hne : piBody m.mtype ≠ .sort .zero) (args : List CptT) :
    ¬ IsPropCT E (.spine r args) := by
  intro h
  cases h with
  | spine hm' hsort =>
      have e : m = _ := Option.some.inj (hm.symm.trans hm')
      subst e
      exact hne hsort

/-- For a non-proposition admitted `.inductiveM` family (`piBody m.mtype ≠ .sort .zero`), every
    spine compact `.spine r' args'` is in `ElT E ρ (foldApps (.const r ls) xs)`. -/
theorem elT_famApp_nonprop_spine (hW : EnvWfT E) (ρ : EnvT) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hne : piBody m.mtype ≠ .sort .zero)
    (ls : List Level) (xs : List (Expr Nat)) (r' : Nat) (args' : List CptT) :
    ElT E ρ (foldApps (.const r ls) xs) (.spine r' args') :=
  ⟨.spine r (botVecT xs), approxT_famApp_botVecT hW ρ hm hind ls xs,
   by rw [CTyS]; exact Or.inr ⟨⟨r', args', rfl⟩, not_isPropCT_spine_of_piBody_ne_zero hm hne _⟩⟩

/-- **Model Typing Lemma Instance on Proposition Family Spines (`typingLemma_at_famApp_prop`):**
    Every `ApproxT` compact of a proposition family spine `foldApps (.const r ls) xs` is an element
    of `ElT E ρ (.sort l)` for every universe level `l : Level`. -/
theorem typingLemma_at_famApp_prop (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hprop : piBody m.mtype = .sort .zero)
    (ls : List Level) (xs : List (Expr Nat)) (l : Level) {u : CptT}
    (hu : ApproxT E ρ (foldApps (.const r ls) xs) u) :
    ElT E ρ (.sort l) u := by
  have hP : IsPropCT E u := isPropCT_of_approxT_famApp_prop hW hm hind hprop hu
  rcases sortCode_prop_or_sort l with hsc | hsc
  · exact ⟨.prop, hsc ▸ approxT_sort_code E ρ l, by rw [CTyS]; exact Or.inr hP⟩
  · exact ⟨.sort, hsc ▸ approxT_sort_code E ρ l, by rw [CTyS]; exact Or.inr (tyCodeCT_of_isPropCT hP)⟩

/-- **Model Typing Lemma Instance on Non-Prop Universe Family Spines (`typingLemma_at_famApp_nonprop`):**
    For any admitted `.inductiveM` family `r` and any non-Prop level `l` (`¬ eqN l .zero`), every
    `ApproxT` compact of `foldApps (.const r ls) xs` is an element of `ElT E ρ (.sort l)`. -/
theorem typingLemma_at_famApp_nonprop (hW : EnvWfT E) {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (ls : List Level) (xs : List (Expr Nat)) {l : Level} (hl : ¬ eqN l .zero) {u : CptT}
    (hu : ApproxT E ρ (foldApps (.const r ls) xs) u) :
    ElT E ρ (.sort l) u :=
  (elT_sort_iff E ρ hl u).mpr (Or.inr (tyCodeCT_of_approxT_famApp hW hm hind hu))


/-! ### §4 — `LRSCoreT` Family-Spine & Π Read-Off and Expansion Lemmas -/

/-- Exact unfolding of `LRSCoreT` at `.spine r args` when the index is `.sort u`. -/
theorem lrSCoreT_spine_sort_iff (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (M M' : Expr Nat) (u : Level) (r : Nat) (args : List CptT) :
    LRSCoreT R E n Γ M M' (.sort u) (.spine r args) ↔
      Nonempty (TyConvT E n Γ M M') ∧ TypeSpineT R E n Γ M M' r := by
  rw [LRSCoreT.eq_def]
  constructor
  · rintro (⟨_, hc, hT⟩ | ⟨hns, _⟩)
    · exact ⟨hc, hT⟩
    · exact (hns u (.refl _)).elim
  · rintro ⟨hc, hT⟩
    exact Or.inl ⟨⟨u, .refl _⟩, hc, hT⟩

/-- At `.sort u`, `LRSCoreT` at `.spine r args` is independent of the compact argument list `args`. -/
theorem lrSCoreT_spine_sort_args_irrel {Γ : LCtx} {M M' : Expr Nat} {u : Level}
    {r : Nat} (args args' : List CptT) :
    LRSCoreT R E n Γ M M' (.sort u) (.spine r args) ↔
      LRSCoreT R E n Γ M M' (.sort u) (.spine r args') :=
  (lrSCoreT_spine_sort_iff R E n Γ M M' u r args).trans
    (lrSCoreT_spine_sort_iff R E n Γ M M' u r args').symm

/-- Weak-head expansion for `TypeSpineT` on both sides. -/
theorem typeSpineT_expand {Γ : LCtx} {M M' N N' : Expr Nat} {r : Nat}
    (hM : RedR R Γ M N) (hM' : RedR R Γ M' N')
    (h : TypeSpineT R E n Γ N N' r) :
    TypeSpineT R E n Γ M M' r := by
  rcases h with ⟨m, ls, ls', xs, xs', w, w', hm, hind, h1, h2, hty, hty', heqN, hlen, hlen', hargs⟩
    | ⟨hnot, ls, ls', xs, xs', h1, h2, hn1, hn2⟩
  · exact Or.inl ⟨m, ls, ls', xs, xs', w, w', hm, hind,
      redR_trans hM h1, redR_trans hM' h2, hty, hty', heqN, hlen, hlen', hargs⟩
  · exact Or.inr ⟨hnot, ls, ls', xs, xs', redR_trans hM h1, redR_trans hM' h2, hn1, hn2⟩

/-- Weak-head expansion for `LRSCoreT` at `.spine r args` and `.sort u`. -/
theorem lrSCoreT_spine_sort_expand {Γ : LCtx} {M M' N N' : Expr Nat} {u : Level}
    {r : Nat} {args : List CptT}
    (hconv : TyConvT E n Γ M M') (hM : RedR R Γ M N) (hM' : RedR R Γ M' N')
    (h : LRSCoreT R E n Γ N N' (.sort u) (.spine r args)) :
    LRSCoreT R E n Γ M M' (.sort u) (.spine r args) := by
  rw [lrSCoreT_spine_sort_iff] at h ⊢
  exact ⟨⟨hconv⟩, typeSpineT_expand hM hM' h.2⟩

/-- **Family-Spine Inversion of `LRSCoreT` (`lrSCoreT_famApp_components`):**
    If two family spines `foldApps (.const r ls) xs` and `foldApps (.const r ls') xs'` are related
    in `LRSCoreT R E n Γ ... (.sort u) (.spine r args)`, then `eqNList ls ls'`, both spines are
    saturated (`xs.length = (piDomsOf m.mtype).length` and `xs'.length = (piDomsOf m.mtype).length`),
    and `ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs'` holds. -/
theorem lrSCoreT_famApp_components (hL : ReadbackLaws E R) (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    {u : Level} {args : List CptT}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (h : LRSCoreT R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')
      (.sort u) (.spine r args)) :
    eqNList ls ls' ∧
      xs.length = (piDomsOf m.mtype).length ∧
      xs'.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  have hT := ((lrSCoreT_spine_sort_iff R E n Γ _ _ u r args).mp h).2
  rcases hT with ⟨m', ls₁, ls₁', xs₁, xs₁', _, _, hm', _, h1, h2, _, _, heqN, hlen, hlen', hargs⟩
    | ⟨hnot, _⟩
  · cases hm.symm.trans hm'
    have e₁ := redR_famApp_eq hL hW hm hind h1
    have e₂ := redR_famApp_eq hL hW hm hind h2
    obtain ⟨hconst₁, hxs₁⟩ := foldApps_const_inj e₁
    obtain ⟨hconst₂, hxs₂⟩ := foldApps_const_inj e₂
    injection hconst₁ with _ hls₁
    injection hconst₂ with _ hls₂
    subst hls₁; subst hxs₁; subst hls₂; subst hxs₂
    exact ⟨heqN, hlen, hlen', hargs⟩
  · exact (hnot m hm hind).elim

/-- **Building `LRSCoreT` on a Family Spine from `TyConvT` and `ConvArgsT`
    (`lrSCoreT_famApp_of_components`):** -/
theorem lrSCoreT_famApp_of_components {Γ : LCtx} {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w w' u : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hconv : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs'))
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (hty' : HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w'))
    (heqN : eqNList ls ls')
    (hlen : xs.length = (piDomsOf m.mtype).length)
    (hlen' : xs'.length = (piDomsOf m.mtype).length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs')
    (args : List CptT) :
    LRSCoreT R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')
      (.sort u) (.spine r args) :=
  (lrSCoreT_spine_sort_iff R E n Γ _ _ u r args).mpr
    ⟨⟨hconv⟩, Or.inl ⟨m, ls, ls', xs, xs', w, w', hm, hind, .refl _, .refl _,
      ⟨hty⟩, ⟨hty'⟩, heqN, hlen, hlen', hargs⟩⟩

/-- **Reflexivity of `LRSCoreT` on Any Saturated Well-Typed Family Spine
    (`lrSCoreT_famApp_refl_of_saturated`):** -/
theorem lrSCoreT_famApp_refl_of_saturated (hW : EnvWfT E) (hpi : PiRowField E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level} {xs : List (Expr Nat)} {u : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort u))
    (hsat : xs.length = (piDomsOf m.mtype).length)
    (args : List CptT) :
    LRSCoreT R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls) xs)
      (.sort u) (.spine r args) :=
  lrSCoreT_famApp_of_components hm hind (.refl Γ _) hty hty (eqNList_refl ls) hsat hsat
    (convArgs_refl_instMtype hW hpi hΓ hm hind hsat hty) args

/-- Π-components extraction from `LRSCoreT R E n Γ (.pi A B) (.pi A' B') (.sort u) (.pi .bot [])`. -/
theorem lrSCoreT_pi_components (hL : ReadbackLaws E R) {Γ : LCtx} {A B A' B' : Expr Nat} {u : Level}
    (h : LRSCoreT R E n Γ (.pi A B) (.pi A' B') (.sort u) (.pi .bot [])) :
    Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  rw [LRSCoreT.eq_def] at h
  obtain ⟨_, A₁, B₁, A₂, B₂, h1, h2, _, hdom, hcod, _⟩ := h
  have e₁ := redR_pi_eq hL h1
  have e₂ := redR_pi_eq hL h2
  injection e₁ with eA₁ eB₁
  injection e₂ with eA₂ eB₂
  subst eA₁; subst eB₁; subst eA₂; subst eB₂
  exact ⟨hdom, hcod⟩


/-! ### §5 — `FamProbeCptT E`, Refutation of `ReadbackModelInvT`, Relation-Seeded `FamProbeLinkT`,
    Single-Link Probe Constructors, and `famAppRow` / `PiRowField` / `TypedRowsWf` Over `LRSCoreT` -/

/-- Typed probe compacts over `CptT` for sorts, Π-types, and admitted `.inductiveM` family spines:
    - `.bot`
    - `.prop` and `.sort` (`sortCode l` for any `l : Level`)
    - `.pi .bot []`
    - `.spine r args` for any admitted `.inductiveM` head `r` and all-`.bot` demand list `BotDemandT args`. -/
inductive FamProbeCptT (E : ResolvedEnv) : CptT → Prop
  | bot : FamProbeCptT E .bot
  | prop : FamProbeCptT E .prop
  | sort : FamProbeCptT E .sort
  | piBotNil : FamProbeCptT E (.pi .bot [])
  | spine {r : Nat} {m : CheckedMember} {args : List CptT}
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
      (hbd : BotDemandT args) : FamProbeCptT E (.spine r args)

theorem famProbeCptT_sortCode (l : Level) : FamProbeCptT E (sortCode l) := by
  rcases sortCode_prop_or_sort l with h | h <;> (rw [h]; constructor)

theorem famProbeCptT_spine_botVecT {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (xs : List (Expr Nat)) :
    FamProbeCptT E (.spine r (botVecT xs)) :=
  .spine hm hind (botDemandT_botVecT xs)

/-- Both universe codes `.prop` and `.sort` have the exact same `LRSCoreT` clause (`SortClauseT`). -/
theorem lrSCoreT_sortCode_iff {Γ : LCtx} {M M' A : Expr Nat} {c : CptT}
    (hc : c = .prop ∨ c = .sort) (l : Level) :
    LRSCoreT R E n Γ M M' A (sortCode l) ↔ LRSCoreT R E n Γ M M' A c := by
  rcases sortCode_prop_or_sort l with hl | hl
  · rw [hl]
    rcases hc with rfl | rfl
    · exact Iff.rfl
    · exact lrSCoreT_prop_iff_sort Γ M M' A
  · rw [hl]
    rcases hc with rfl | rfl
    · exact (lrSCoreT_prop_iff_sort Γ M M' A).symm
    · exact Iff.rfl

/-- Readback-to-`ApproxT` invariance for a readback `R` over `ctxEnvT E Γ`. -/
def ReadbackModelInvT (R : Readback) (E : ResolvedEnv) : Prop :=
  ∀ (Γ : LCtx) {a b : Expr Nat}, R Γ a b →
    ∀ c, ApproxT E (ctxEnvT E Γ) a c ↔ ApproxT E (ctxEnvT E Γ) b c

theorem redR_modelInvT {R : Readback} {E : ResolvedEnv} (hinv : ReadbackModelInvT R E)
    {Γ : LCtx} {a b : Expr Nat} (h : RedR R Γ a b) (c : CptT) :
    ApproxT E (ctxEnvT E Γ) a c ↔ ApproxT E (ctxEnvT E Γ) b c := by
  induction h with
  | refl => exact Iff.rfl
  | step hs _ ih => exact (hinv Γ hs c).trans ih

/-- Every compact `d` of a syntactic lambda `.lam D₀ b₀` in `ApproxT E ρ` has only `.bot` in `CTyS E · d`,
    because `approxT_lam_inv` forces `d = .bot ∨ d = .lam g`, and `CTyS` at `.bot` or `.lam g` only
    admits `u = .bot` (`ctyS_bot_inv`, `ctyS_lam_inv`). -/
theorem ctyS_of_approxT_lam_eq_bot {ρ : EnvT} {D₀ b₀ : Expr Nat} {d u : CptT}
    (hd : ApproxT E ρ (.lam D₀ b₀) d) (hu : CTyS E u d) : u = .bot := by
  rcases approxT_lam_inv hd with rfl | ⟨_, _, rfl, _, _⟩
  · exact ctyS_bot_inv hu
  · exact ctyS_lam_inv hu

/-- Because `ApproxT.lam` checks `CTyS E u a` on the domain compact `a` of `.lam (.lam D₀ b₀) (.bvar 0)`,
    applying `.lam (.lam D₀ b₀) (.bvar 0)` to any argument `arg` in `ApproxT` only produces `c = .bot`. -/
theorem approxT_app_lamDomain_id_eq_bot {ρ : EnvT} {D₀ b₀ arg : Expr Nat} {c : CptT}
    (h : ApproxT E ρ (.app (.lam (.lam D₀ b₀) (.bvar 0)) arg) c) : c = .bot := by
  rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hfn, hmem, _⟩ | ⟨_, _, _, _, hfn, _⟩
  · rfl
  · rcases approxT_lam_inv hfn with hbot | ⟨a, g', heq, ha, hg⟩
    · exact CptT.noConfusion hbot
    · injection heq with hg_eq
      subst hg_eq
      obtain ⟨hdom, hzero⟩ := hg.2 s hmem
      rcases approxT_bvar_inv hzero with hs₂ | hu
      · exact hs₂
      · exact ctyS_of_approxT_lam_eq_bot ha (hdom s.2 hu)
  · rcases approxT_lam_inv hfn with hbot | ⟨_, _, heq, _, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion heq

/-- **Refutation of `ReadbackModelInvT R E` at `.pi .bot []` Under `ReadbackLaws E R`
    (`not_readbackModelInvT_pi_bot_nil_of_readbackLaws`):**
    Under `hL : ReadbackLaws E R`, `hL.beta` steps `(.app (.lam (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.pi (.sort .zero) (.sort .zero)))`
    to `.pi (.sort .zero) (.sort .zero)` (which has `.pi .bot []` in `ApproxT`), whereas the source
    β-redex has only `.bot` in `ApproxT` (`approxT_app_lamDomain_id_eq_bot`). -/
theorem not_readbackModelInvT_pi_bot_nil_of_readbackLaws (hL : ReadbackLaws E R) :
    ¬ (∀ (Γ : LCtx) {a b : Expr Nat}, R Γ a b →
        (ApproxT E (ctxEnvT E Γ) a (.pi .bot []) ↔ ApproxT E (ctxEnvT E Γ) b (.pi .bot []))) := by
  intro hinv
  have hstep : R []
      (.app (.lam (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.pi (.sort .zero) (.sort .zero)))
      (.pi (.sort .zero) (.sort .zero)) := by
    have hb := hL.beta [] (.lam (.sort .zero) (.bvar 0)) (.bvar 0) (.pi (.sort .zero) (.sort .zero))
    have hinst : instantiate0 (.pi (.sort .zero) (.sort .zero) : Expr Nat) (.bvar 0) =
        (.pi (.sort .zero) (.sort .zero) : Expr Nat) := by
      simp only [instantiate0, instantiate, ite_true, lift_zero]
    rwa [hinst] at hb
  have hpi : ApproxT E (ctxEnvT E []) (.pi (.sort .zero) (.sort .zero)) (.pi .bot []) :=
    approxT_pi_bot_nil E (ctxEnvT E []) (.sort .zero) (.sort .zero)
  have hredex : ApproxT E (ctxEnvT E [])
      (.app (.lam (.lam (.sort .zero) (.bvar 0)) (.bvar 0)) (.pi (.sort .zero) (.sort .zero)))
      (.pi .bot []) :=
    (hinv [] hstep).mpr hpi
  exact CptT.noConfusion (approxT_app_lamDomain_id_eq_bot hredex)

/-- **`ReadbackModelInvT R E` is Refuted for Every `E` and `R` Satisfying `ReadbackLaws E R`
    (`not_readbackModelInvT_of_readbackLaws`):** -/
theorem not_readbackModelInvT_of_readbackLaws (hL : ReadbackLaws E R) :
    ¬ ReadbackModelInvT R E :=
  fun hinv => not_readbackModelInvT_pi_bot_nil_of_readbackLaws hL
    (fun Γ {_ _} hs => hinv Γ hs (.pi .bot []))

/-- Concrete refutation of `ReadbackModelInvT (WhStepRecKCanon E) E` for every `E : ResolvedEnv`. -/
theorem not_readbackModelInvT_whStepRecKCanon (E : ResolvedEnv) :
    ¬ ReadbackModelInvT (WhStepRecKCanon E) E :=
  not_readbackModelInvT_of_readbackLaws (readbackLaws_whStepRecKCanon E)

/-- **Right-Hand Diagonal Recovery in `LRSCoreT` (`lrSCoreT_right_diag_of_envWfT`):**
    Because `LRSCoreT` is symmetric and transitive at every compact `c : CptT` under `ReadbackLaws E R`,
    `NormalUniqueR R`, and `EnvWfT E` alone (§1 `lrSCoreT_symm_of_envWfT` + `lrSCoreT_trans_of_envWfT`),
    any `LRSCoreT R E n Γ A₁ A₂ (.sort w) c` immediately yields the right diagonal
    `LRSCoreT R E n Γ A₂ A₂ (.sort w) c` at the **exact same compact `c`** — with **zero**
    `ReadbackModelInvT`! -/
theorem lrSCoreT_right_diag_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ A₂ : Expr Nat} {w : Level} {c : CptT}
    (h : LRSCoreT R E n Γ A₁ A₂ (.sort w) c) :
    LRSCoreT R E n Γ A₂ A₂ (.sort w) c :=
  lrSCoreT_trans_of_envWfT hL hNU hW hΓ (lrSCoreT_symm_of_envWfT hL hNU hW hΓ h) h

/-- Unconditional diagonal of `.sort l` at `.sort` in `LRSCoreT`. -/
theorem lrSCoreT_sort_self (Γ : LCtx) (l u : Level) :
    LRSCoreT R E n Γ (.sort l) (.sort l) (.sort u) .sort := by
  rw [lrSCoreT_sort_iff]
  exact ⟨⟨u, .refl _⟩, l, l, .refl _, .refl _⟩

/-- Unconditional diagonal of a well-typed `.pi A B` at `.pi .bot []` in `LRSCoreT`. -/
theorem lrSCoreT_pi_self_of_hasTyT {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B : Expr Nat} {u : Level} (hPi : HasTyT E n Γ (.pi A B) (.sort u)) :
    LRSCoreT R E n Γ (.pi A B) (.pi A B) (.sort u) (.pi .bot []) := by
  obtain ⟨u₁, _, hA, _, _⟩ := hasTyTInv_pi hPi rfl
  rw [LRSCoreT.eq_def]
  exact ⟨⟨u, .refl _⟩, A, B, A, B, .refl _, .refl _,
    ⟨.assumption Γ A u₁ hΓ hA⟩, ⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩,
    ⟨u₁, lrSCoreT_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- **Relation-Seeded Single `ConvT` Link Interface on `FamProbeCptT E` (`FamProbeLinkT R E n`):**
    Replaces `ReadbackModelInvT` by seeding single `ConvT` links with the left diagonal
    `LRSCoreT R E n Γ A A (.sort u) c` at `FamProbeCptT E` compacts. -/
def FamProbeLinkT (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level},
    ConvT E n Γ A B (.sort u) →
    ∀ c, FamProbeCptT E c →
      LRSCoreT R E n Γ A A (.sort u) c → LRSCoreT R E n Γ A B (.sort u) c

/-- **`TyConvT` Chaining Across `FamProbeCptT E` Compacts (`famProbe_chainT`):**
    Chains `TyConvT.trans A B C` at the **exact same compact `c`** using `lrSCoreT_right_diag_of_envWfT`
    and `lrSCoreT_trans_of_envWfT` under `ReadbackLaws E R`, `NormalUniqueR R`, and `EnvWfT E` alone —
    with **zero** `ReadbackModelInvT` and **zero** `PiRowField`! -/
theorem famProbe_chainT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hlink : FamProbeLinkT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hc : TyConvT E n Γ A A')
    {c : CptT} (hpc : FamProbeCptT E c)
    (hAA : LRSCoreT R E n Γ A A (.sort u) c) :
    LRSCoreT R E n Γ A A' (.sort u) c := by
  revert u
  induction hc with
  | refl A => intro u _ hAA; exact hAA
  | of A B v hc =>
      intro u _ hAA
      have hAA_v : LRSCoreT R E n Γ A A (.sort v) c :=
        lrSCoreT_sortIdx_irrel hL hNU ⟨u, .refl _⟩ ⟨v, .refl _⟩ c hAA
      exact lrSCoreT_sortIdx_irrel hL hNU ⟨v, .refl _⟩ ⟨u, .refl _⟩ c
        (hlink hΓ hc c hpc hAA_v)
  | trans A B C c₁ _ ih₁ ih₂ =>
      intro u hA hAA
      obtain ⟨v, hB⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ c₁ hA
      have r₁ : LRSCoreT R E n Γ A B (.sort u) c := ih₁ hA hAA
      have hBB_u : LRSCoreT R E n Γ B B (.sort u) c :=
        lrSCoreT_right_diag_of_envWfT hL hNU hW hΓ r₁
      have hBB_v : LRSCoreT R E n Γ B B (.sort v) c :=
        lrSCoreT_sortIdx_irrel hL hNU ⟨u, .refl _⟩ ⟨v, .refl _⟩ c hBB_u
      have r₂ : LRSCoreT R E n Γ B C (.sort v) c := ih₂ hB hBB_v
      have r₂_u : LRSCoreT R E n Γ B C (.sort u) c :=
        lrSCoreT_sortIdx_irrel hL hNU ⟨v, .refl _⟩ ⟨u, .refl _⟩ c r₂
      exact lrSCoreT_trans_of_envWfT hL hNU hW hΓ r₁ r₂_u

/-- Type-level `TyConvT` chain form over `LRSCoreT` and `ApproxT E (ctxEnvT E Γ)` at all compacts. -/
def FundamentalLRSTTTyped (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' →
    ∀ c, ApproxT E (ctxEnvT E Γ) A c → LRSCoreT R E n Γ A A' (.sort u) c

/-- Type-level `TyConvT` chain form restricted to `FamProbeCptT E` probe compacts. -/
def FundamentalLRSTTFamProbe (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' →
    ∀ c, FamProbeCptT E c → ApproxT E (ctxEnvT E Γ) A c → LRSCoreT R E n Γ A A' (.sort u) c

theorem fundamentalLRSTTFamProbe_of_fundamentalLRSTTTyped
    (F : FundamentalLRSTTTyped R E n) : FundamentalLRSTTFamProbe R E n :=
  fun {_} hΓ {_ _ _} hA hc c _ hcA => F hΓ hA hc c hcA

/-- **`FundamentalLRSTTFamProbe R E n` from the Diagonal and `FamProbeLinkT R E n`
    (`fundamentalLRSTTFamProbe_of_links`):**
    Chains `TyConvT.trans A B C` across `FamProbeCptT E` compacts via `famProbe_chainT` — with
    **zero** `ReadbackModelInvT` and **zero** `PiRowField`! -/
theorem fundamentalLRSTTFamProbe_of_links (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
      ∀ c, FamProbeCptT E c → ApproxT E (ctxEnvT E Γ) A c → LRSCoreT R E n Γ A A (.sort u) c)
    (hlink : FamProbeLinkT R E n) :
    FundamentalLRSTTFamProbe R E n :=
  fun {_} hΓ {_ _ _} hA hc c hpc hcA =>
    famProbe_chainT hL hNU hW hlink hΓ hA hc hpc (hdiag hΓ hA c hpc hcA)

/-- **`PiRowField E n` from `FundamentalLRSTTFamProbe R E n` (`piRowField_of_fundamentalLRSTTFamProbe`):** -/
theorem piRowField_of_fundamentalLRSTTFamProbe (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (F : FundamentalLRSTTFamProbe R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrSCoreT_pi_components hL
      (F hΓ hPi hc (.pi .bot []) .piBotNil (approxT_pi_bot_nil E (ctxEnvT E Γ) A B))

/-- **`FamAppRowLink E n` from `FundamentalLRSTTFamProbe R E n`
    (`famAppRow_of_fundamentalLRSTTFamProbe`):** -/
theorem famAppRow_of_fundamentalLRSTTFamProbe (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (F : FundamentalLRSTTFamProbe R E n) : FamAppRowLink E n :=
  fun {_} hΓ {r _ ls _ xs _ _} hm hind hty hc =>
    let h := lrSCoreT_famApp_components hL hW hm hind
      (F hΓ hty hc (.spine r (botVecT xs)) (famProbeCptT_spine_botVecT hm hind xs)
        (approxT_famApp_botVecT hW (ctxEnvT E _) hm hind ls xs))
    ⟨h.1, h.2.1.trans h.2.2.1.symm, h.2.2.2⟩

/-- **`FamRelevantSlotConv E n` (#7525) from `FundamentalLRSTTFamProbe R E n`
    (`famRelevantSlotConv_of_fundamentalLRSTTFamProbe`):** -/
theorem famRelevantSlotConv_of_fundamentalLRSTTFamProbe (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (F : FundamentalLRSTTFamProbe R E n) : FamRelevantSlotConv E n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty hc
  exact relevantSlotConv_of_convArgsT hW hm hind
    (famAppRow_of_fundamentalLRSTTFamProbe hL hW F hΓ hm hind hty hc).2.2

/-- **`TypedRowsWf E n` from `FundamentalLRSTTFamProbe R E n` + `AllBelowScoped`
    (`typedRowsWf_of_allBelowScoped_fundamentalLRSTTFamProbe`):** -/
theorem typedRowsWf_of_allBelowScoped_fundamentalLRSTTFamProbe (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (F : FundamentalLRSTTFamProbe R E n) : TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_build hW hBel
  piRow := piRowField_of_fundamentalLRSTTFamProbe hL hW F
  famAppRow := famAppRow_of_fundamentalLRSTTFamProbe hL hW F

/-- **`PiRowField E n` Directly from `FamProbeLinkT R E n` (`piRowField_of_linksT`):**
    Requires **only** `ReadbackLaws E R`, `NormalUniqueR R`, `EnvWfT E`, and `FamProbeLinkT R E n` —
    with **zero** `ReadbackModelInvT` and **zero** separate `hdiag` hypothesis! -/
theorem piRowField_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkT R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrSCoreT_pi_components hL
      (famProbe_chainT hL hNU hW hlink hΓ hPi hc .piBotNil
        (lrSCoreT_pi_self_of_hasTyT hΓ hPi))

theorem not_tyConvT_pi_sort_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.pi A B) (.sort l)) : False := by
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · exact Expr.noConfusion heq
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    have hLR := famProbe_chainT hL hNU hW hlink hΓ hPi hc .piBotNil
      (lrSCoreT_pi_self_of_hasTyT hΓ hPi)
    rw [LRSCoreT.eq_def] at hLR
    obtain ⟨_, _, _, _, _, _, hred', _⟩ := hLR
    exact Expr.noConfusion (redR_sort_eq hL hred')

theorem not_tyConvT_sort_pi_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.sort l) (.pi A B)) : False := by
  have hLR := famProbe_chainT hL hNU hW hlink hΓ (.sort Γ l) hc .sort
    (lrSCoreT_sort_self Γ l (.succ l))
  rw [LRSCoreT.eq_def] at hLR
  obtain ⟨_, _, _, _, hred'⟩ := hLR
  exact Expr.noConfusion (redR_pi_eq hL hred')

theorem famApp_saturated_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (_hind : m.mclass = .inductiveM)
    {doms : List (Expr Nat)} {u : Level}
    (hpi : instantiateLevels ls m.mtype = policyPi doms (.sort u))
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = doms.length := by
  have hprow : PiRowField E n := piRowField_of_linksT hL hNU hW hlink
  rcases Nat.lt_trichotomy xs.length doms.length with hlt | heq | hgt
  · exfalso
    have hne : doms.drop xs.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hlt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hpi' : instantiateLevels ls m.mtype =
        policyPi (doms.take xs.length) (policyPi (doms.drop xs.length) (.sort u)) := by
      rw [← List.take_append_drop xs.length doms] at hpi
      rw [hpi, policyPi_append]
    have hlen' : (doms.take xs.length).length = xs.length := by
      rw [List.length_take]
      first
        | exact Nat.min_eq_right (Nat.le_of_lt hlt)
        | exact Nat.min_eq_left (Nat.le_of_lt hlt)
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi' xs hlen' hty
    rw [hrest] at hconv
    simp only [policyPi] at hconv
    rw [instPrefix_pi] at hconv
    exact not_tyConvT_pi_sort_of_linksT hL hNU hW hlink hΓ hconv
  · exact heq
  · exfalso
    have hne : xs.drop doms.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hgt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hsplit : foldApps (.const r ls) xs =
        foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
      calc foldApps (.const r ls) xs
          = foldApps (.const r ls) (xs.take doms.length ++ xs.drop doms.length) := by
              rw [List.take_append_drop]
        _ = foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
            foldApps_append _ _ _
    obtain ⟨_, _, ⟨hf⟩⟩ := hasTyT_foldApps_prefix_pi
      (f := foldApps (.const r ls) (xs.take doms.length))
      (hsplit ▸ hty) hrest
    have hlen' : doms.length = (xs.take doms.length).length := by
      rw [List.length_take]
      first
        | exact (Nat.min_eq_right (Nat.le_of_lt hgt)).symm
        | exact (Nat.min_eq_left (Nat.le_of_lt hgt)).symm
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi
      (xs.take doms.length) hlen' hf
    rw [instPrefix_sort] at hconv
    exact not_tyConvT_sort_pi_of_linksT hL hNU hW hlink hΓ hconv

theorem famApp_length_eq_piDomsOf_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = (piDomsOf m.mtype).length := by
  have hlen := famApp_saturated_of_linksT hL hNU hW hlink hΓ hm hind
    (instMtype_policyPi_of_inductiveM hW hm hind ls) hty
  rwa [List.length_map] at hlen

/-- **`FamAppRowLink E n` Directly from `FamProbeLinkT R E n` (`famAppRow_of_linksT`):**
    Requires **only** `ReadbackLaws E R`, `NormalUniqueR R`, `EnvWfT E`, and `FamProbeLinkT R E n` —
    with **zero** `ReadbackModelInvT` and **zero** separate `hdiag` hypothesis! -/
theorem famAppRow_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkT R E n) :
    FamAppRowLink E n := by
  intro Γ hΓ r m ls ls' xs xs' _ hm hind hty hc
  have hprow : PiRowField E n := piRowField_of_linksT hL hNU hW hlink
  have hsat : xs.length = (piDomsOf m.mtype).length :=
    famApp_length_eq_piDomsOf_of_linksT hL hNU hW hlink hΓ hm hind hty
  have h := lrSCoreT_famApp_components hL hW hm hind
    (famProbe_chainT hL hNU hW hlink hΓ hty hc
      (famProbeCptT_spine_botVecT hm hind xs)
      (lrSCoreT_famApp_refl_of_saturated hW hprow hΓ hm hind hty hsat (botVecT xs)))
  exact ⟨h.1, h.2.1.trans h.2.2.1.symm, h.2.2.2⟩

/-- **`FamRelevantSlotConv E n` (#7525) Directly from `FamProbeLinkT R E n`
    (`famRelevantSlotConv_of_linksT`):** -/
theorem famRelevantSlotConv_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkT R E n) :
    FamRelevantSlotConv E n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty hc
  exact relevantSlotConv_of_convArgsT hW hm hind
    (famAppRow_of_linksT hL hNU hW hlink hΓ hm hind hty hc).2.2

/-- **`TypedRowsWf E n` Directly from `FamProbeLinkT R E n` + `AllBelowScoped`
    (`typedRowsWf_of_allBelowScoped_linksT`):** -/
theorem typedRowsWf_of_allBelowScoped_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlink : FamProbeLinkT R E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_build hW hBel
  piRow := piRowField_of_linksT hL hNU hW hlink
  famAppRow := famAppRow_of_linksT hL hNU hW hlink

/-- `FamAppRowLink E n` instantiated at `WhStepRecKCanon E` from `EnvWfT E` + `FamProbeLinkT` alone. -/
theorem famAppRow_of_linksT_whStepRecKCanon (hW : EnvWfT E)
    (hlink : FamProbeLinkT (WhStepRecKCanon E) E n) : FamAppRowLink E n :=
  famAppRow_of_linksT (readbackLaws_whStepRecKCanon E) (normalUniqueR_whStepRecKCanon hW)
    hW hlink

/-- `FamRelevantSlotConv E n` instantiated at `WhStepRecKCanon E` from `EnvWfT E` + `FamProbeLinkT` alone. -/
theorem famRelevantSlotConv_of_linksT_whStepRecKCanon (hW : EnvWfT E)
    (hlink : FamProbeLinkT (WhStepRecKCanon E) E n) : FamRelevantSlotConv E n :=
  famRelevantSlotConv_of_linksT (readbackLaws_whStepRecKCanon E)
    (normalUniqueR_whStepRecKCanon hW) hW hlink

/-- `TypedRowsWf E n` instantiated at `WhStepRecKCanon E` from `EnvWfT E` + `AllBelowScoped` +
    `FamProbeLinkT` alone. -/
theorem typedRowsWf_of_allBelowScoped_linksT_whStepRecKCanon (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlink : FamProbeLinkT (WhStepRecKCanon E) E n) : TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_linksT (readbackLaws_whStepRecKCanon E)
    (normalUniqueR_whStepRecKCanon hW) hW hBel hlink

/-- Single-link constructor for `ConvT.sorts` / `TyConvT` on sorts in `LRSCoreT` at every `c : CptT`. -/
theorem lrSCoreT_sorts_probe {Γ : LCtx} {ρ : EnvT} {u u' w : Level} {c : CptT}
    (happrox : ApproxT E ρ (.sort u) c) :
    LRSCoreT R E n Γ (.sort u) (.sort u') (.sort w) c := by
  rcases approxT_sort_inv happrox with rfl | rfl
  · exact lrSCoreT_bot _ _ _ _
  · refine (lrSCoreT_sortCode_iff (Or.inl rfl) u).mpr ?_
    rw [lrSCoreT_prop_iff]
    exact ⟨⟨w, .refl _⟩, u, u', .refl _, .refl _⟩

/-- Diagonal constructor for `.sort u` in `LRSCoreT` at every `c : CptT`. -/
theorem lrSCoreT_sort_diag_probe {Γ : LCtx} {ρ : EnvT} (u w : Level) {c : CptT}
    (happrox : ApproxT E ρ (.sort u) c) :
    LRSCoreT R E n Γ (.sort u) (.sort u) (.sort w) c :=
  lrSCoreT_sorts_probe happrox

/-- Inversion of `ApproxT E (ctxEnvT E Γ)` on an assumption variable (`lookupValue Γ i = none`). -/
theorem approxT_ctxEnvT_bvar_of_lookupValue_none {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) {c : CptT}
    (h : ApproxT E (ctxEnvT E Γ) (.bvar i) c) : c = .bot := by
  rcases approxT_bvar_inv h with rfl | hmem
  · rfl
  · exact ctxEnvT_none_bot E Γ i hnone c hmem

/-- Inversion of `ApproxT E (ctxEnvT E Γ)` on an assumption-variable spine `foldApps (.bvar i) xs`
    (`lookupValue Γ i = none`). -/
theorem approxT_ctxEnvT_foldApps_bvar_of_lookupValue_none {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) :
    ∀ (xs : List (Expr Nat)) {f : Expr Nat} {c : CptT},
      (∀ {d : CptT}, ApproxT E (ctxEnvT E Γ) f d → d = .bot) →
      ApproxT E (ctxEnvT E Γ) (foldApps f xs) c → c = .bot
  | [], _, _, hf, h => hf h
  | x :: xs, f, c, hf, h => by
      simp only [foldApps] at h
      refine approxT_ctxEnvT_foldApps_bvar_of_lookupValue_none hnone xs (fun hd => ?_) h
      rcases approxT_app_inv hd with rfl | ⟨_, _, _, hfg, _, _⟩ | ⟨_, _, _, _, hfs, _⟩
      · rfl
      · exact CptT.noConfusion (hf hfg)
      · exact CptT.noConfusion (hf hfs)

/-- Every assumption-variable spine `foldApps (.bvar i) xs` (`lookupValue Γ i = none`) has only
    `.bot` in `ApproxT E (ctxEnvT E Γ)`, so it satisfies `LRSCoreT` at every `c : CptT`. -/
theorem lrSCoreT_bvar_of_lookupValue_none_probe {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) (xs : List (Expr Nat)) (M' A : Expr Nat) {c : CptT}
    (happrox : ApproxT E (ctxEnvT E Γ) (foldApps (.bvar i) xs) c) :
    LRSCoreT R E n Γ (foldApps (.bvar i) xs) M' A c := by
  have hbot : c = .bot :=
    approxT_ctxEnvT_foldApps_bvar_of_lookupValue_none hnone xs
      (approxT_ctxEnvT_bvar_of_lookupValue_none hnone) happrox
  subst hbot
  exact lrSCoreT_bot _ _ _ _

/-- On `FamProbeCptT E c`, `ApproxT E ρ (.pi A B) c` forces `c = .bot ∨ c = .pi .bot []`. -/
theorem approxT_pi_famProbeCptT {ρ : EnvT} {A B : Expr Nat} {c : CptT}
    (hpc : FamProbeCptT E c) (h : ApproxT E ρ (.pi A B) c) :
    c = .bot ∨ c = .pi .bot [] := by
  cases hpc with
  | bot => exact Or.inl rfl
  | piBotNil => exact Or.inr rfl
  | prop | sort | spine _ _ _ =>
      rcases approxT_pi_inv h with hbot | ⟨_, _, he, _, _⟩
      · exact Or.inl hbot
      · exact CptT.noConfusion he

/-- Single-link constructor for `ConvT.pi` in `LRSCoreT` at every `FamProbeCptT E` compact. -/
theorem lrSCoreT_pi_probe {Γ : LCtx} {ρ : EnvT} {A₁ B₁ A₂ B₂ : Expr Nat} {u w : Level} {c : CptT}
    (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
    (hdom : TyConvT E n Γ A₁ A₂)
    (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
    (hpc : FamProbeCptT E c)
    (happrox : ApproxT E ρ (.pi A₁ B₁) c) :
    LRSCoreT R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort w) c := by
  rcases approxT_pi_famProbeCptT hpc happrox with rfl | rfl
  · exact lrSCoreT_bot _ _ _ _
  · rw [LRSCoreT.eq_def]
    exact ⟨⟨w, .refl _⟩, A₁, B₁, A₂, B₂, .refl _, .refl _, ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩,
      ⟨u, lrSCoreT_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- Diagonal constructor for `HasTyT.pi` in `LRSCoreT` at every `FamProbeCptT E` compact. -/
theorem lrSCoreT_pi_diag_probe {Γ : LCtx} {ρ : EnvT} {A B : Expr Nat} (w : Level) {c : CptT}
    (hΓ₁ : CtxWfT E n (.assumption A :: Γ))
    (hpc : FamProbeCptT E c)
    (happrox : ApproxT E ρ (.pi A B) c) :
    LRSCoreT R E n Γ (.pi A B) (.pi A B) (.sort w) c :=
  lrSCoreT_pi_probe (u := w) hΓ₁ (.refl Γ A) (.refl (.assumption A :: Γ) B) hpc happrox

/-- Single-link constructor for saturated admitted `.inductiveM` family spines in `LRSCoreT` at
    every `c : CptT` with `ApproxT E ρ (foldApps (.const r ls) xs) c`. -/
theorem lrSCoreT_famSpine_of_convArgsT_probe (hW : EnvWfT E) {Γ : LCtx} {ρ : EnvT}
    {r : Nat} {m : CheckedMember} {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    {w w' u : Level} {c : CptT}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hconv : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs'))
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (hty' : HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w'))
    (heqN : eqNList ls ls')
    (hlen : xs.length = (piDomsOf m.mtype).length)
    (hlen' : xs'.length = (piDomsOf m.mtype).length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs')
    (happrox : ApproxT E ρ (foldApps (.const r ls) xs) c) :
    LRSCoreT R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort u) c := by
  rcases approxT_foldApps_const_inductiveM_inv hW hm hind ls xs happrox with rfl | ⟨us, rfl, _⟩
  · exact lrSCoreT_bot _ _ _ _
  · exact lrSCoreT_famApp_of_components hm hind hconv hty hty' heqN hlen hlen' hargs us

/-- Diagonal constructor for a saturated well-typed admitted `.inductiveM` family spine in `LRSCoreT`. -/
theorem lrSCoreT_famSpine_diag_probe (hW : EnvWfT E) (hpi : PiRowField E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {ρ : EnvT}
    {r : Nat} {m : CheckedMember} {ls : List Level} {xs : List (Expr Nat)} {u : Level} {c : CptT}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort u))
    (hsat : xs.length = (piDomsOf m.mtype).length)
    (happrox : ApproxT E ρ (foldApps (.const r ls) xs) c) :
    LRSCoreT R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls) xs) (.sort u) c :=
  lrSCoreT_famSpine_of_convArgsT_probe hW hm hind (.refl Γ _) hty hty (eqNList_refl ls)
    hsat hsat (convArgs_refl_instMtype hW hpi hΓ hm hind hsat hty) happrox

/-- **DT-012** (type uniqueness) from `ReadbackLaws E R` + `EnvWfT E` + `AllBelowScoped` +
    `FundamentalLRSTTFamProbe R E n` alone. -/
theorem dt012_of_allBelowScoped_fundamentalLRSTTFamProbe (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (F : FundamentalLRSTTFamProbe R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_build hW hBel)
    (piRowField_of_fundamentalLRSTTFamProbe hL hW F) hΓ hA hB

/-- **DT-010** (one-step subject reduction) from `ReadbackLaws E R` + `EnvWfT E` + `AllBelowScoped` +
    `FundamentalLRSTTFamProbe R E n` alone. -/
theorem dt010_of_allBelowScoped_fundamentalLRSTTFamProbe (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (F : FundamentalLRSTTFamProbe R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_fundamentalLRSTTFamProbe hL hW hBel F) hΓ h hs

/-- **DT-011** (multi-step subject reduction) from `ReadbackLaws E R` + `EnvWfT E` + `AllBelowScoped` +
    `FundamentalLRSTTFamProbe R E n` alone. -/
theorem dt011_of_allBelowScoped_fundamentalLRSTTFamProbe (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (F : FundamentalLRSTTFamProbe R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_fundamentalLRSTTFamProbe hL hW hBel F) hΓ h hs

/-- **DT-019** (typed ι subject reduction) from `ReadbackLaws E R` + `EnvWfT E` + `AllBelowScoped` +
    `FundamentalLRSTTFamProbe R E n` alone. -/
theorem dt019_of_allBelowScoped_fundamentalLRSTTFamProbe (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (F : FundamentalLRSTTFamProbe R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_fundamentalLRSTTFamProbe hL hW hBel F) hΓ hd hlhs

/-- **IA-024** (`IotaSRTN`) from `ReadbackLaws E R` + `EnvWfT E` + `AllBelowScoped` +
    `FundamentalLRSTTFamProbe R E n` alone. -/
theorem ia024_of_allBelowScoped_fundamentalLRSTTFamProbe (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (F : FundamentalLRSTTFamProbe R E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_fundamentalLRSTTFamProbe hL hW hBel F)


/-! ### §6 — Off-Diagonal `ConvT.app` Decomposition, Step-by-Step Family-Spine Application, and
    `ConvT.eta` Closure in `LRTermFamSemBiProbeRKCanon` -/

/-- **Step-by-Step `ConvT.app` on Partial `.inductiveM` Spines in `LRTermFamSemBiProbeRKCanon`
    (`lrTermFamSemBiProbeRKCanon_famSpine_step_app_partial`):**
    If `(xs ++ [x]).length < (piDomsOf m.mtype).length` and `(xs' ++ [x']).length = (xs ++ [x]).length`,
    then applying `foldApps (.const r ls) xs` to `x` and `foldApps (.const r ls') xs'` to `x'` yields
    `LRTermFamSemBiProbeRKCanon` at **every** type `T` under `EnvWfT E` alone! -/
theorem lrTermFamSemBiProbeRKCanon_famSpine_step_app_partial (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {x x' : Expr Nat}
    (hlt : (xs ++ [x]).length < (piDomsOf m.mtype).length)
    (hlen : (xs' ++ [x']).length = (xs ++ [x]).length)
    (T : Expr Nat) :
    LRTermFamSemBiProbeRKCanon E n Γ
      (.app (foldApps (.const r ls) xs) x)
      (.app (foldApps (.const r ls') xs') x') T := by
  rw [← foldApps_snoc, ← foldApps_snoc]
  exact lrTermFamSemBiProbeRKCanon_famSpines_of_length_ne hW hm hind hm hind
    (Nat.ne_of_lt hlt) (hlen ▸ Nat.ne_of_lt hlt) T

/-- **Step-by-Step `ConvT.app` Reaching a Saturated `.inductiveM` Spine in
    `LRTermFamSemBiProbeRKCanon` (`lrTermFamSemBiProbeRKCanon_famSpine_step_app_saturated`):**
    Appending `a, a'` with `ConvT E n Γ a a' A` where `instTelescope (instantiateLevels ls m.mtype) xs = .pi A B`
    produces `LRTermFamSemBiProbeRKCanon` at `.sort w`! -/
theorem lrTermFamSemBiProbeRKCanon_famSpine_step_app_saturated (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    {A B a a' : Expr Nat} {w w' : Level}
    (heqN : eqNList ls ls')
    (hpre : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs')
    (hpi : instTelescope (instantiateLevels ls m.mtype) xs = .pi A B)
    (ha : ConvT E n Γ a a' A)
    (hlen : (xs ++ [a]).length = (piDomsOf m.mtype).length)
    (hty : HasTyT E n Γ (.app (foldApps (.const r ls) xs) a) (.sort w))
    (hty' : HasTyT E n Γ (.app (foldApps (.const r ls') xs') a') (.sort w'))
    (hc : TyConvT E n Γ (.app (foldApps (.const r ls) xs) a) (.app (foldApps (.const r ls') xs') a')) :
    LRTermFamSemBiProbeRKCanon E n Γ
      (.app (foldApps (.const r ls) xs) a)
      (.app (foldApps (.const r ls') xs') a') (.sort w) :=
  (lrTermFamSemBiProbeRKCanon_sort_iff _ _ w).mpr
    (lrTypeFamINBiProbeRKCanon_famSpine_step_app hW hm hind heqN hpre hpi ha hlen hty hty' hc)

/-- **Off-Diagonal `ConvT.app` Decomposition in `LRTermFamSemBiProbeRKCanon`
    (`lrTermFamSemBiProbeRKCanon_app_of_fn_and_arg`):**
    Decomposes `LRTermFamSemBiProbeRKCanon E n Γ (.app f₁ a₁) (.app f₂ a₂) T` into a function
    conversion step at fixed argument `a₁` (`(.app f₁ a₁) ~ (.app f₂ a₁)`) and an argument conversion
    step at fixed function `f₂` (`(.app f₂ a₁) ~ (.app f₂ a₂)`) via `lrTermFamSemBiProbeRKCanon_trans_of_envWfT`
    under `EnvWfT E` and `CtxWfT E n Γ` alone! -/
theorem lrTermFamSemBiProbeRKCanon_app_of_fn_and_arg (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f₁ f₂ a₁ a₂ T : Expr Nat}
    (hfn : LRTermFamSemBiProbeRKCanon E n Γ (.app f₁ a₁) (.app f₂ a₁) T)
    (harg : LRTermFamSemBiProbeRKCanon E n Γ (.app f₂ a₁) (.app f₂ a₂) T) :
    LRTermFamSemBiProbeRKCanon E n Γ (.app f₁ a₁) (.app f₂ a₂) T :=
  lrTermFamSemBiProbeRKCanon_trans_of_envWfT hW hΓ hfn harg

/-- **Let-Binding Reduction for the Function-Step of `ConvT.app` in `LRTermFamSemBiProbeRKCanon`
    (`lrTermFamSemBiProbeRKCanon_app_fn_of_letBinding`):**
    Reduces `LRTermFamSemBiProbeRKCanon E n Γ (.app f₁ a) (.app f₂ a) (instantiate0 a B)` to
    `LRTermFamSemRKCanon E n (.letBinding A a :: Γ) (.app (lift 0 1 f₁) (.bvar 0)) (.app (lift 0 1 f₂) (.bvar 0)) B c`
    via `lrTermFamSemRKCanon_substLet0_botFamCpt`! -/
theorem lrTermFamSemBiProbeRKCanon_app_fn_of_letBinding (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B f₁ f₂ a : Expr Nat} (ha : HasTyT E n Γ a A)
    (hlet : ∀ c, FamProbeCpt E c →
      (ApproxDIKCanon E Γ (.app f₁ a) c ∨ ApproxDIKCanon E Γ (.app f₂ a) c) →
      LRTermFamSemRKCanon E n (.letBinding A a :: Γ)
        (.app (lift 0 1 f₁) (.bvar 0)) (.app (lift 0 1 f₂) (.bvar 0)) B c) :
    LRTermFamSemBiProbeRKCanon E n Γ (.app f₁ a) (.app f₂ a) (instantiate0 a B) := by
  intro c hc happrox
  have h0 := lrTermFamSemRKCanon_substLet0_botFamCpt hW hΓ ha
    (botFamCpt_of_famProbeCpt hc) (hlet c hc happrox)
  have heq₁ : instantiate0 a (.app (lift 0 1 f₁) (.bvar 0)) = .app f₁ a := by
    simp only [instantiate0, instantiate, ite_true, lift_zero,
      instantiate_lift_cancel 1 0 0 a (by omega) (by omega), Nat.sub_self]
  have heq₂ : instantiate0 a (.app (lift 0 1 f₂) (.bvar 0)) = .app f₂ a := by
    simp only [instantiate0, instantiate, ite_true, lift_zero,
      instantiate_lift_cancel 1 0 0 a (by omega) (by omega), Nat.sub_self]
  rwa [heq₁, heq₂] at h0

/-- **Unconditional `ConvT.eta` Closure Whenever `f` Has Only `.bot` on `FamProbeCpt E`
    (`lrTermFamSemBiProbeRKCanon_eta_of_left_probe_bot`):**
    Because the η-expansion `.lam A (.app (lift 0 1 f) (.bvar 0))` is a syntactic lambda, its only
    `FamProbeCpt E` compact in `ApproxDIKCanon` is `.bot` (`approxDIKCanon_lam_botFamCpt_eq_bot`).
    Therefore, if `f` also has only `.bot` on `FamProbeCpt E`, `LRTermFamSemBiProbeRKCanon E n Γ f (.lam A (.app (lift 0 1 f) (.bvar 0))) T`
    holds unconditionally across **all** types `T`! -/
theorem lrTermFamSemBiProbeRKCanon_eta_of_left_probe_bot {Γ : LCtx}
    (f A T : Expr Nat)
    (hf : ∀ c, FamProbeCpt E c → ApproxDIKCanon E Γ f c → c = .bot) :
    LRTermFamSemBiProbeRKCanon E n Γ f (.lam A (.app (lift 0 1 f) (.bvar 0))) T :=
  lrTermFamSemBiProbeRKCanon_of_probe_eq_bot T fun c hc happrox =>
    happrox.elim (hf c hc)
      (approxDIKCanon_lam_botFamCpt_eq_bot A (.app (lift 0 1 f) (.bvar 0))
        (botFamCpt_of_famProbeCpt hc))

/-- Unconditional `ConvT.eta` in `LRTermFamSemBiProbeRKCanon` when `f = .lam A₀ b`. -/
theorem lrTermFamSemBiProbeRKCanon_eta_lam {Γ : LCtx} (A₀ b A T : Expr Nat) :
    LRTermFamSemBiProbeRKCanon E n Γ (.lam A₀ b)
      (.lam A (.app (lift 0 1 (.lam A₀ b)) (.bvar 0))) T :=
  lrTermFamSemBiProbeRKCanon_lam E n Γ A₀ b A (.app (lift 0 1 (.lam A₀ b)) (.bvar 0)) T

/-- Unconditional `ConvT.eta` in `LRTermFamSemBiProbeRKCanon` when `f = foldApps (.bvar i) xs` is an
    assumption-variable spine (`lookupValue Γ i = none`). -/
theorem lrTermFamSemBiProbeRKCanon_eta_bvarSpine {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) (xs : List (Expr Nat)) (A T : Expr Nat) :
    LRTermFamSemBiProbeRKCanon E n Γ (foldApps (.bvar i) xs)
      (.lam A (.app (lift 0 1 (foldApps (.bvar i) xs)) (.bvar 0))) T :=
  lrTermFamSemBiProbeRKCanon_eta_of_left_probe_bot (foldApps (.bvar i) xs) A T fun c _ h =>
    (approxDIKCanon_foldApps_bvar_of_lookupValue_none_iff hnone xs c).mp h

/-- Unconditional `ConvT.eta` in `LRTermFamSemBiProbeRKCanon` when `f = foldApps (.const c₀ ls) ys`
    is an admitted `.constructorM` spine. -/
theorem lrTermFamSemBiProbeRKCanon_eta_ctorSpine (hW : EnvWfT E) {Γ : LCtx}
    {c₀ : Nat} {m : CheckedMember} (hm : E.members c₀ = some m) (hctor : m.mclass = .constructorM)
    (ls : List Level) (ys : List (Expr Nat)) (A T : Expr Nat) :
    LRTermFamSemBiProbeRKCanon E n Γ (foldApps (.const c₀ ls) ys)
      (.lam A (.app (lift 0 1 (foldApps (.const c₀ ls) ys)) (.bvar 0))) T :=
  lrTermFamSemBiProbeRKCanon_eta_of_left_probe_bot (foldApps (.const c₀ ls) ys) A T fun _ hc h =>
    approxDIKCanon_ctorApp_botFamCpt_eq_bot hW hm hctor ls ys (botFamCpt_of_famProbeCpt hc) h

/-- Unconditional `ConvT.eta` in `LRTermFamSemBiProbeRKCanon` when `f = foldApps (.const r ls) xs`
    is a non-saturated admitted `.inductiveM` spine (`xs.length ≠ (piDomsOf m.mtype).length`). -/
theorem lrTermFamSemBiProbeRKCanon_eta_famSpine_partial (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {xs : List (Expr Nat)}
    (hne : xs.length ≠ (piDomsOf m.mtype).length) (A T : Expr Nat) :
    LRTermFamSemBiProbeRKCanon E n Γ (foldApps (.const r ls) xs)
      (.lam A (.app (lift 0 1 (foldApps (.const r ls) xs)) (.bvar 0))) T :=
  lrTermFamSemBiProbeRKCanon_eta_of_left_probe_bot (foldApps (.const r ls) xs) A T fun _ hc h =>
    approxDIKCanon_famApp_botFamCpt_of_length_ne hW hm hind hne (botFamCpt_of_famProbeCpt hc) h

/-- Weak-head reduction `WhRedRecKCanon E Γ f f₀` reduces `ConvT.eta` on `f` to `f₀` having only
    `.bot` on `FamProbeCpt E`. -/
theorem lrTermFamSemBiProbeRKCanon_eta_of_whRedRecKCanon (hW : EnvWfT E) {Γ : LCtx}
    {f f₀ : Expr Nat} (A T : Expr Nat)
    (hred : WhRedRecKCanon E Γ f f₀)
    (hf₀ : ∀ c, FamProbeCpt E c → ApproxDIKCanon E Γ f₀ c → c = .bot) :
    LRTermFamSemBiProbeRKCanon E n Γ f (.lam A (.app (lift 0 1 f) (.bvar 0))) T :=
  lrTermFamSemBiProbeRKCanon_eta_of_left_probe_bot f A T fun c hc hf =>
    hf₀ c hc ((whRedRecKCanon_approxDIKCanon_iff_of_envWfT hW hred c).mp hf)

/-! ### §7 — All-Member / Unsaturated-Prefix `DomsRel` & `ConvArgsT` PER Under `EnvWfT E` Alone,
    Exact Diagonal Adequacy Characterizations, and Off-Diagonal `ConvT.app` Reduction -/

/-- Every expression `e : Expr Nat` decomposes under `instantiateLevels ls` as
    `policyPi ((piDomsOf e).map (instantiateLevels ls)) (instantiateLevels ls (piTailOf e))`. -/
theorem instantiateLevels_policyPi_piDomsOf_piTailOf (ls : List Level) (e : Expr Nat) :
    instantiateLevels ls e =
      policyPi ((piDomsOf e).map (instantiateLevels ls)) (instantiateLevels ls (piTailOf e)) := by
  have h := congrArg (instantiateLevels ls) (policyPi_piDomsOf_piTailOf e).symm
  rwa [instantiateLevels_policyPi] at h

/-- **General `DomsRel` for `(piDomsOf m.mtype).map (instantiateLevels ls)` of Any Admitted Member `m`
    (`domsRel_of_levelFacts`):**
    Requires only `EnvWfT E`, `CtxWfT E n Γ`, `E.members r = some m`, level well-formedness
    (`ls.length = m.arity`, `levelsBounded n ls = true`), and `eqNList ls ls'` — holds for **every**
    `CheckedMember` `m` (`.inductiveM`, `.constructorM`, `.recursorM`, `.definitionM`, `.axiomM`,
    `.quotM`), not only `.inductiveM`! -/
theorem domsRel_of_levelFacts (hW : EnvWfT E) {Γ : LCtx} (_hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls ls' : List Level}
    (hlsl : ls.length = m.arity) (hwfL : levelsBounded n ls = true)
    (hlsl' : ls'.length = m.arity) (hwfR : levelsBounded n ls' = true)
    (heqN : eqNList ls ls') :
    DomsRel E n Γ ((piDomsOf m.mtype).map (instantiateLevels ls))
      ((piDomsOf m.mtype).map (instantiateLevels ls')) := by
  obtain ⟨um, hmty⟩ := envWfT_mtypeSortTyped hW r m hm
  have hpol : m.mtype = policyPi (piDomsOf m.mtype) (piTailOf m.mtype) :=
    (policyPi_piDomsOf_piTailOf m.mtype).symm
  have hmtyPol : HasTyT E m.arity [] (policyPi (piDomsOf m.mtype) (piTailOf m.mtype)) (.sort um) :=
    hpol ▸ hmty
  obtain ⟨hdoms, _⟩ := hasTyT_policyPi_inv (piDomsOf m.mtype) hmtyPol
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro i D₁ hD₁
    rw [List.getElem?_map] at hD₁
    cases hdi : (piDomsOf m.mtype)[i]? with
    | none => rw [hdi] at hD₁; cases hD₁
    | some d =>
        rw [hdi] at hD₁
        injection hD₁ with hD₁_eq
        subst hD₁_eq
        obtain ⟨hi, hd_eq⟩ := List.getElem?_eq_some_iff.mp hdi
        subst hd_eq
        obtain ⟨u₀, ⟨hdTy⟩⟩ := hdoms i hi
        have h1 := hasTyT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW)
          hwfL hlsl hdTy
        rw [List.append_nil, instLvlsCtx_policyPrefixContext] at h1
        have h2 := hasTyT_relocateN (Γ := Γ) h1
        exact ⟨instLevel ls u₀, ⟨h2⟩⟩
  · intro i D₂ hD₂
    rw [List.getElem?_map] at hD₂
    cases hdi : (piDomsOf m.mtype)[i]? with
    | none => rw [hdi] at hD₂; cases hD₂
    | some d =>
        rw [hdi] at hD₂
        injection hD₂ with hD₂_eq
        subst hD₂_eq
        obtain ⟨hi, hd_eq⟩ := List.getElem?_eq_some_iff.mp hdi
        subst hd_eq
        obtain ⟨u₀, ⟨hdTy⟩⟩ := hdoms i hi
        have h1 := hasTyT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW)
          hwfR hlsl' hdTy
        rw [List.append_nil, instLvlsCtx_policyPrefixContext] at h1
        have h2 := hasTyT_relocateN (Γ := Γ) h1
        exact ⟨instLevel ls' u₀, ⟨h2⟩⟩
  · intro i D₁ D₂ hD₁ hD₂
    rw [List.getElem?_map] at hD₁ hD₂
    cases hdi : (piDomsOf m.mtype)[i]? with
    | none => rw [hdi] at hD₁; cases hD₁
    | some d =>
        rw [hdi] at hD₁ hD₂
        injection hD₁ with hD₁_eq
        injection hD₂ with hD₂_eq
        subst hD₁_eq; subst hD₂_eq
        obtain ⟨hi, hd_eq⟩ := List.getElem?_eq_some_iff.mp hdi
        subst hd_eq
        obtain ⟨u₀, ⟨hdTy⟩⟩ := hdoms i hi
        have hc1 := convT_instantiateLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW)
          heqN hwfL hwfR hlsl hdTy
        rw [List.append_nil, instLvlsCtx_policyPrefixContext] at hc1
        have hc2 := convT_relocateN (Γ := Γ) hc1
        exact ⟨.of _ _ _ (instLevel ls u₀) hc2⟩

/-- **General `DomsRel` for Any Pair of Well-Typed Constant Spines `foldApps (.const r ls) xs` and
    `foldApps (.const r ls') ys` (`domsRel_of_typedSpines`):**
    Applies `NativeFamilyProjection.native_level_facts` (`RcicNativeFamilyProjection`) at arbitrary
    types `T₁, T₂ : Expr Nat` (no `.sort w` or saturation required!). -/
theorem domsRel_of_typedSpines (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls ls' : List Level} {xs ys : List (Expr Nat)} {T₁ T₂ : Expr Nat}
    (hty₁ : HasTyT E n Γ (foldApps (.const r ls) xs) T₁)
    (hty₂ : HasTyT E n Γ (foldApps (.const r ls') ys) T₂)
    (heqN : eqNList ls ls') :
    DomsRel E n Γ ((piDomsOf m.mtype).map (instantiateLevels ls))
      ((piDomsOf m.mtype).map (instantiateLevels ls')) := by
  obtain ⟨hlen, hbel⟩ := NativeFamilyProjection.native_level_facts hm hty₁
  obtain ⟨hlen', hbel'⟩ := NativeFamilyProjection.native_level_facts hm hty₂
  exact domsRel_of_levelFacts hW hΓ hm hlen hbel hlen' hbel' heqN

/-- **`PiRowField`-Free Symmetry of `ConvArgsT` Along `DomsRel` for Arbitrary Tail Expressions
    `T₁, T₂ : Expr Nat` (`convArgs_symm_domsRel_anyTail`):**
    Generalizes `convArgs_symm_domsRel` (`RcicNativeFamModel` §16) from sort tails `.sort u₁, .sort u₂`
    to **arbitrary** tail expressions `T₁, T₂ : Expr Nat` for any prefix `xs.length ≤ ds₁.length`,
    enabling unsaturated prefixes and constructor/recursor/definition/axiom telescopes! -/
theorem convArgs_symm_domsRel_anyTail (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {ds₁ ds₂ : List (Expr Nat)} (T₁ T₂ : Expr Nat)
    (hrel : DomsRel E n Γ ds₁ ds₂)
    {xs ys : List (Expr Nat)} (hbnd : xs.length ≤ ds₁.length)
    (hargs : ConvArgsT E n Γ (policyPi ds₁ T₁) xs ys) :
    ConvArgsT E n Γ (policyPi ds₂ T₂) ys xs := by
  induction xs generalizing ds₁ ds₂ T₁ T₂ ys with
  | nil =>
      generalize policyPi ds₁ T₁ = U at hargs
      cases hargs with
      | nil _ => exact .nil (policyPi ds₂ T₂)
  | cons x xs' ih =>
      cases ds₁ with
      | nil => nomatch hbnd
      | cons A₁ ds₁ =>
          cases ds₂ with
          | nil => cases hrel.1
          | cons A₂ ds₂ =>
              cases hargs with
              | cons _ _ _ y _ ys' hc hrest =>
                  rcases hc with ⟨hxy⟩
                  obtain ⟨_, _, ⟨hcA⟩⟩ := domsRel_head hrel
                  have hyx : ConvT E n Γ y x A₂ :=
                    convT_of_tyConv (.symm _ x y A₁ hxy) hcA
                  have hrel' : DomsRel E n Γ (instDomsT 0 x ds₁) (instDomsT 0 y ds₂) :=
                    domsRel_step hW hΓ hrel hxy
                  have hbnd' : xs'.length ≤ (instDomsT 0 x ds₁).length := by
                    rw [length_instDomsT]
                    exact Nat.le_of_succ_le_succ hbnd
                  have hinst₁ : instantiate0 x (policyPi ds₁ T₁) =
                      policyPi (instDomsT 0 x ds₁) (instantiate (0 + ds₁.length) (lift 0 ds₁.length x) T₁) := by
                    simp only [instantiate0, instantiate_policyPi]
                  have hinst₂ : instantiate0 y (policyPi ds₂ T₂) =
                      policyPi (instDomsT 0 y ds₂) (instantiate (0 + ds₂.length) (lift 0 ds₂.length y) T₂) := by
                    simp only [instantiate0, instantiate_policyPi]
                  rw [hinst₁] at hrest
                  have hstep := ih
                    (instantiate (0 + ds₁.length) (lift 0 ds₁.length x) T₁)
                    (instantiate (0 + ds₂.length) (lift 0 ds₂.length y) T₂)
                    hrel' hbnd' hrest
                  rw [← hinst₂] at hstep
                  exact .cons A₂ (policyPi ds₂ T₂) y x ys' xs' ⟨hyx⟩ hstep

/-- **`PiRowField`-Free Transitivity of `ConvArgsT` Along `DomsRel` for Arbitrary Tail Expressions
    `T₁, T₂ : Expr Nat` (`convArgs_trans_domsRel_anyTail`):**
    Generalizes `convArgs_trans_domsRel` (`RcicNativeFamModel` §16) from sort tails `.sort u₁, .sort u₂`
    to **arbitrary** tail expressions `T₁, T₂ : Expr Nat` for any prefix `xs.length ≤ ds₁.length`. -/
theorem convArgs_trans_domsRel_anyTail (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {ds₁ ds₂ : List (Expr Nat)} (T₁ T₂ : Expr Nat)
    (hrel : DomsRel E n Γ ds₁ ds₂)
    {xs ys zs : List (Expr Nat)} (hbnd : xs.length ≤ ds₁.length)
    (hargs₁ : ConvArgsT E n Γ (policyPi ds₁ T₁) xs ys)
    (hargs₂ : ConvArgsT E n Γ (policyPi ds₂ T₂) ys zs) :
    ConvArgsT E n Γ (policyPi ds₁ T₁) xs zs := by
  induction xs generalizing ds₁ ds₂ T₁ T₂ ys zs with
  | nil =>
      generalize policyPi ds₁ T₁ = U₁ at hargs₁
      generalize policyPi ds₂ T₂ = U₂ at hargs₂
      cases hargs₁ with
      | nil _ =>
          cases hargs₂ with
          | nil _ => exact .nil U₁
  | cons x xs' ih =>
      cases ds₁ with
      | nil => nomatch hbnd
      | cons A₁ ds₁ =>
          cases ds₂ with
          | nil => cases hrel.1
          | cons A₂ ds₂ =>
              cases hargs₁ with
              | cons _ _ _ y _ ys' hc₁ hrest₁ =>
                  cases hargs₂ with
                  | cons _ _ _ z _ zs' hc₂ hrest₂ =>
                      rcases hc₁ with ⟨hxy⟩
                      rcases hc₂ with ⟨hyz⟩
                      obtain ⟨_, _, ⟨hcA⟩⟩ := domsRel_head hrel
                      have hyz_A₁ : ConvT E n Γ y z A₁ :=
                        convT_of_tyConv hyz hcA.symmT
                      have hxz : ConvT E n Γ x z A₁ := .trans _ x y z A₁ hxy hyz_A₁
                      have hrel' : DomsRel E n Γ (instDomsT 0 x ds₁) (instDomsT 0 y ds₂) :=
                        domsRel_step hW hΓ hrel hxy
                      have hbnd' : xs'.length ≤ (instDomsT 0 x ds₁).length := by
                        rw [length_instDomsT]
                        exact Nat.le_of_succ_le_succ hbnd
                      have hinst₁ : instantiate0 x (policyPi ds₁ T₁) =
                          policyPi (instDomsT 0 x ds₁) (instantiate (0 + ds₁.length) (lift 0 ds₁.length x) T₁) := by
                        simp only [instantiate0, instantiate_policyPi]
                      have hinst₂ : instantiate0 y (policyPi ds₂ T₂) =
                          policyPi (instDomsT 0 y ds₂) (instantiate (0 + ds₂.length) (lift 0 ds₂.length y) T₂) := by
                        simp only [instantiate0, instantiate_policyPi]
                      rw [hinst₁] at hrest₁
                      rw [hinst₂] at hrest₂
                      have hstep := ih
                        (instantiate (0 + ds₁.length) (lift 0 ds₁.length x) T₁)
                        (instantiate (0 + ds₂.length) (lift 0 ds₂.length y) T₂)
                        hrel' hbnd' hrest₁ hrest₂
                      rw [← hinst₁] at hstep
                      exact .cons A₁ (policyPi ds₁ T₁) x z xs' zs' ⟨hxz⟩ hstep

/-- **All-Member / Unsaturated-Prefix `ConvArgsT` Symmetry from Level Facts Under `EnvWfT E` Alone
    (`convArgs_symm_member_of_levelFacts`):** -/
theorem convArgs_symm_member_of_levelFacts (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls ls' : List Level} {xs ys : List (Expr Nat)}
    (hlen : ls.length = m.arity) (hbel : levelsBounded n ls = true)
    (hlen' : ls'.length = m.arity) (hbel' : levelsBounded n ls' = true)
    (heqN : eqNList ls ls')
    (hbnd : xs.length ≤ (piDomsOf m.mtype).length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys) :
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) ys xs := by
  have hpi₁ := instantiateLevels_policyPi_piDomsOf_piTailOf ls m.mtype
  have hpi₂ := instantiateLevels_policyPi_piDomsOf_piTailOf ls' m.mtype
  rw [hpi₁] at hargs
  rw [hpi₂]
  have hbnd' : xs.length ≤ ((piDomsOf m.mtype).map (instantiateLevels ls)).length := by
    rwa [List.length_map]
  exact convArgs_symm_domsRel_anyTail hW hΓ
    (instantiateLevels ls (piTailOf m.mtype))
    (instantiateLevels ls' (piTailOf m.mtype))
    (domsRel_of_levelFacts hW hΓ hm hlen hbel hlen' hbel' heqN) hbnd' hargs

/-- **All-Member / Unsaturated-Prefix `ConvArgsT` Transitivity from Level Facts Under `EnvWfT E` Alone
    (`convArgs_trans_member_of_levelFacts`):** -/
theorem convArgs_trans_member_of_levelFacts (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls₁ ls₂ : List Level} {xs ys zs : List (Expr Nat)}
    (hlen₁ : ls₁.length = m.arity) (hbel₁ : levelsBounded n ls₁ = true)
    (hlen₂ : ls₂.length = m.arity) (hbel₂ : levelsBounded n ls₂ = true)
    (heqN : eqNList ls₁ ls₂)
    (hbnd : xs.length ≤ (piDomsOf m.mtype).length)
    (hargs₁ : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs ys)
    (hargs₂ : ConvArgsT E n Γ (instantiateLevels ls₂ m.mtype) ys zs) :
    ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs zs := by
  have hpi₁ := instantiateLevels_policyPi_piDomsOf_piTailOf ls₁ m.mtype
  have hpi₂ := instantiateLevels_policyPi_piDomsOf_piTailOf ls₂ m.mtype
  rw [hpi₁] at hargs₁ ⊢
  rw [hpi₂] at hargs₂
  have hbnd' : xs.length ≤ ((piDomsOf m.mtype).map (instantiateLevels ls₁)).length := by
    rwa [List.length_map]
  exact convArgs_trans_domsRel_anyTail hW hΓ
    (instantiateLevels ls₁ (piTailOf m.mtype))
    (instantiateLevels ls₂ (piTailOf m.mtype))
    (domsRel_of_levelFacts hW hΓ hm hlen₁ hbel₁ hlen₂ hbel₂ heqN) hbnd' hargs₁ hargs₂

/-- **All-Member / Unsaturated-Prefix `ConvArgsT` Symmetry for Typed Spines Under `EnvWfT E` Alone
    (`convArgs_symm_member_of_typedSpines`):**
    Applies to **any** admitted member `E.members r = some m` and **any** well-typed spines
    `HasTyT E n Γ (foldApps (.const r ls) xs) T₁` and `HasTyT E n Γ (foldApps (.const r ls') ys) T₂`
    (for any prefix `xs.length ≤ (piDomsOf m.mtype).length`, at any types `T₁, T₂`), with **zero**
    `PiRowField`! -/
theorem convArgs_symm_member_of_typedSpines (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls ls' : List Level} {xs ys : List (Expr Nat)} {T₁ T₂ : Expr Nat}
    (hty₁ : HasTyT E n Γ (foldApps (.const r ls) xs) T₁)
    (hty₂ : HasTyT E n Γ (foldApps (.const r ls') ys) T₂)
    (heqN : eqNList ls ls')
    (hbnd : xs.length ≤ (piDomsOf m.mtype).length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys) :
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) ys xs := by
  obtain ⟨hlen, hbel⟩ := NativeFamilyProjection.native_level_facts hm hty₁
  obtain ⟨hlen', hbel'⟩ := NativeFamilyProjection.native_level_facts hm hty₂
  exact convArgs_symm_member_of_levelFacts hW hΓ hm hlen hbel hlen' hbel' heqN hbnd hargs

/-- **All-Member / Unsaturated-Prefix `ConvArgsT` Transitivity for Typed Spines Under `EnvWfT E` Alone
    (`convArgs_trans_member_of_typedSpines`):** -/
theorem convArgs_trans_member_of_typedSpines (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls₁ ls₂ : List Level} {xs ys zs : List (Expr Nat)} {T₁ T₂ : Expr Nat}
    (hty₁ : HasTyT E n Γ (foldApps (.const r ls₁) xs) T₁)
    (hty₂ : HasTyT E n Γ (foldApps (.const r ls₂) ys) T₂)
    (heqN : eqNList ls₁ ls₂)
    (hbnd : xs.length ≤ (piDomsOf m.mtype).length)
    (hargs₁ : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs ys)
    (hargs₂ : ConvArgsT E n Γ (instantiateLevels ls₂ m.mtype) ys zs) :
    ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs zs := by
  obtain ⟨hlen₁, hbel₁⟩ := NativeFamilyProjection.native_level_facts hm hty₁
  obtain ⟨hlen₂, hbel₂⟩ := NativeFamilyProjection.native_level_facts hm hty₂
  exact convArgs_trans_member_of_levelFacts hW hΓ hm hlen₁ hbel₁ hlen₂ hbel₂ heqN hbnd hargs₁ hargs₂

/-- **All-Member / Unsaturated-Prefix `ConvArgsT` Symmetry Directly from `ConvT` of the Spines
    (`convArgs_symm_member_of_convSpines`):**
    Directly matches the `ConvT E n Γ (foldApps (.const r ls₁) args₁) (foldApps (.const r ls₂) args₂) A`
    premise of `#7673` Segment 10's `DataSpineS`! -/
theorem convArgs_symm_member_of_convSpines (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls ls' : List Level} {xs ys : List (Expr Nat)} {A : Expr Nat}
    (hconv : ConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') ys) A)
    (heqN : eqNList ls ls')
    (hbnd : xs.length ≤ (piDomsOf m.mtype).length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys) :
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) ys xs := by
  have hends := convEnds hW hΓ hconv
  exact convArgs_symm_member_of_typedSpines hW hΓ hm hends.1 hends.2.1 heqN hbnd hargs

/-- **All-Member / Unsaturated-Prefix `ConvArgsT` Transitivity Directly from `ConvT` of the Spines
    (`convArgs_trans_member_of_convSpines`):** -/
theorem convArgs_trans_member_of_convSpines (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls₁ ls₂ : List Level} {xs ys zs : List (Expr Nat)} {A : Expr Nat}
    (hconv₁ : ConvT E n Γ (foldApps (.const r ls₁) xs) (foldApps (.const r ls₂) ys) A)
    (heqN : eqNList ls₁ ls₂)
    (hbnd : xs.length ≤ (piDomsOf m.mtype).length)
    (hargs₁ : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs ys)
    (hargs₂ : ConvArgsT E n Γ (instantiateLevels ls₂ m.mtype) ys zs) :
    ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs zs := by
  have hends := convEnds hW hΓ hconv₁
  exact convArgs_trans_member_of_typedSpines hW hΓ hm hends.1 hends.2.1 heqN hbnd hargs₁ hargs₂

/-- Exact characterization of the diagonal `LRTypeFamINRKCanon E n Γ A A .sort`. -/
theorem lrTypeFamINRKCanon_diag_sort_iff {Γ : LCtx} (A : Expr Nat) :
    LRTypeFamINRKCanon E n Γ A A .sort ↔ ∃ u, WhRedRecKCanon E Γ A (.sort u) := by
  constructor
  · intro h
    cases h with
    | sort h₁ _ => exact ⟨_, h₁⟩
  · rintro ⟨u, hu⟩
    exact .sort hu hu

/-- Exact characterization of the diagonal `LRTypeFamINRKCanon E n Γ A A (.pi .bot [])`. -/
theorem lrTypeFamINRKCanon_diag_pi_bot_nil_iff {Γ : LCtx} (A : Expr Nat) :
    LRTypeFamINRKCanon E n Γ A A (.pi .bot []) ↔
      ∃ D B, WhRedRecKCanon E Γ A (.pi D B) ∧ Nonempty (CtxWfT E n (.assumption D :: Γ)) := by
  constructor
  · intro h
    cases h with
    | pi h₁ _ hΓ₁ _ _ _ _ => exact ⟨_, _, h₁, ⟨hΓ₁⟩⟩
  · rintro ⟨D, B, hpi, ⟨hΓ₁⟩⟩
    exact .pi hpi hpi hΓ₁ (.refl Γ D) (.refl (.assumption D :: Γ) B) (.bot _ _ _)
      (fun _ hs => (List.not_mem_nil _ hs).elim)

/-- Exact characterization of the diagonal `LRTypeFamINRKCanon E n Γ A A (.spine r cs)` at any
    `FamProbeCpt E (.spine r cs)` (`E.members r = some m`, `m.mclass = .inductiveM`). -/
theorem lrTypeFamINRKCanon_diag_famSpine_iff (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (cs : List CptI) (A : Expr Nat) :
    LRTypeFamINRKCanon E n Γ A A (.spine r cs) ↔
      ∃ ls xs w,
        WhRedRecKCanon E Γ A (foldApps (.const r ls) xs) ∧
        Nonempty (HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) ∧
        xs.length = (piDomsOf m.mtype).length ∧
        ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs := by
  constructor
  · intro h
    cases h with
    | @famSpine _ _ _ _ m' ls ls' xs xs' w w' _ hm' hind' h₁ _ hty hty' _ heqN hlen _ hargs =>
        have em : m' = m := Option.some.inj (hm'.symm.trans hm)
        subst em
        have hsymm := convArgs_symm_instMtype_of_envWfT hW hΓ hm hind hty hty' heqN hargs
        have hrefl := convArgs_trans_instMtype_of_envWfT hW hΓ hm hind hty hty' heqN hargs hsymm
        exact ⟨ls, xs, w, h₁, ⟨hty⟩, hlen, hrefl⟩
    | otherSpine hnot _ _ _ _ _ =>
        exact (hnot m hm hind).elim
  · rintro ⟨ls, xs, w, hred, ⟨hty⟩, hlen, hargs⟩
    exact .famSpine hm hind hred hred hty hty (.refl Γ _) (eqNList_refl ls) hlen hlen hargs

/-- **Weak-Head Adequacy of `ApproxDIKCanon E Γ A` at `FamProbeCpt E` (`WhFamApproxAdequateAt`):**
    States that every non-`.bot` `FamProbeCpt E` compact of `A` in `ApproxDIKCanon E Γ` is matched by
    a `WhRedRecKCanon E Γ` reduction of `A` to a sort, well-typed Π-domain, or saturated well-typed
    admitted `.inductiveM` family spine. -/
def WhFamApproxAdequateAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) : Prop :=
  (ApproxDIKCanon E Γ A .sort → ∃ u, WhRedRecKCanon E Γ A (.sort u)) ∧
  (ApproxDIKCanon E Γ A (.pi .bot []) →
    ∃ D B, WhRedRecKCanon E Γ A (.pi D B) ∧ Nonempty (CtxWfT E n (.assumption D :: Γ))) ∧
  (∀ {r : Nat} {m : CheckedMember} {cs : List CptI},
    E.members r = some m → m.mclass = .inductiveM →
     cs.length = (piDomsOf m.mtype).length → BotDemand cs →
    ApproxDIKCanon E Γ A (.spine r cs) →
    ∃ ls xs w,
      WhRedRecKCanon E Γ A (foldApps (.const r ls) xs) ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) ∧
      xs.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs)

/-- **Exact Diagonal Characterization of `LRTypeFamINBiProbeRKCanon E n Γ A A`
    (`lrTypeFamINBiProbeRKCanon_diag_iff`):**
    Under `EnvWfT E` and `CtxWfT E n Γ`, `LRTypeFamINBiProbeRKCanon E n Γ A A` holds if and only if
    `WhFamApproxAdequateAt E n Γ A` holds! -/
theorem lrTypeFamINBiProbeRKCanon_diag_iff (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (A : Expr Nat) :
    LRTypeFamINBiProbeRKCanon E n Γ A A ↔ WhFamApproxAdequateAt E n Γ A := by
  constructor
  · intro h
    refine ⟨fun hs => ?_, fun hpi => ?_, fun hm hind hlen hbd hsp => ?_⟩
    · exact (lrTypeFamINRKCanon_diag_sort_iff A).mp (h .sort .sort (Or.inl hs))
    · exact (lrTypeFamINRKCanon_diag_pi_bot_nil_iff A).mp
        (h (.pi .bot []) .pi_bot_nil (Or.inl hpi))
    · exact (lrTypeFamINRKCanon_diag_famSpine_iff hW hΓ hm hind _ A).mp
        (h (.spine _ _) (.famSpine hm hind hlen hbd) (Or.inl hsp))
  · rintro ⟨hsort, hpi, hsp⟩ c hc happrox
    have hA : ApproxDIKCanon E Γ A c := happrox.elim id id
    cases hc with
    | bot => exact .bot _ _ _
    | sort => exact (lrTypeFamINRKCanon_diag_sort_iff A).mpr (hsort hA)
    | pi_bot_nil => exact (lrTypeFamINRKCanon_diag_pi_bot_nil_iff A).mpr (hpi hA)
    | @famSpine r m cs hm hind hlen hbd =>
        exact (lrTypeFamINRKCanon_diag_famSpine_iff hW hΓ hm hind cs A).mpr
          (hsp hm hind hlen hbd hA)

/-- **Term-Level Weak-Head Adequacy of `ApproxDIKCanon E Γ e` at `T` (`WhFamTermApproxAdequateAt`):**
    At every `FamProbeCpt E` compact `c` of `e` in `ApproxDIKCanon E Γ e c`, `LRTermFamSemRKCanon E n Γ e e T c`
    holds (i.e., either `c = .bot`, `IsSemRigidPropRecKCanon E n Γ T`, or `T` weak-head reduces to a
    sort `.sort u` and `LRTypeFamINRKCanon E n Γ e e c` holds). -/
def WhFamTermApproxAdequateAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T : Expr Nat) : Prop :=
  ∀ c, FamProbeCpt E c → ApproxDIKCanon E Γ e c →
    LRTermFamSemRKCanon E n Γ e e T c

/-- **Exact Diagonal Characterization of `LRTermFamSemBiProbeRKCanon E n Γ e e T`
    (`lrTermFamSemBiProbeRKCanon_diag_iff`):**
    `LRTermFamSemBiProbeRKCanon E n Γ e e T` holds if and only if `WhFamTermApproxAdequateAt E n Γ e T`
    holds! -/
theorem lrTermFamSemBiProbeRKCanon_diag_iff {Γ : LCtx} (e T : Expr Nat) :
    LRTermFamSemBiProbeRKCanon E n Γ e e T ↔ WhFamTermApproxAdequateAt E n Γ e T :=
  ⟨fun h c hc he => h c hc (Or.inl he),
   fun h c hc happrox => h c hc (happrox.elim id id)⟩

/-- **Let-Binding Reduction for the Diagonal of `.app f a` in `LRTermFamSemBiProbeRKCanon`
    (`lrTermFamSemBiProbeRKCanon_app_diag_of_letBinding`):**
    Reduces the diagonal `LRTermFamSemBiProbeRKCanon E n Γ (.app f a) (.app f a) (instantiate0 a B)`
    to `LRTermFamSemRKCanon E n (.letBinding A a :: Γ) (.app (lift 0 1 f) (.bvar 0)) (.app (lift 0 1 f) (.bvar 0)) B c`! -/
theorem lrTermFamSemBiProbeRKCanon_app_diag_of_letBinding (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B f a : Expr Nat} (ha : HasTyT E n Γ a A)
    (hlet : ∀ c, FamProbeCpt E c → ApproxDIKCanon E Γ (.app f a) c →
      LRTermFamSemRKCanon E n (.letBinding A a :: Γ)
        (.app (lift 0 1 f) (.bvar 0)) (.app (lift 0 1 f) (.bvar 0)) B c) :
    LRTermFamSemBiProbeRKCanon E n Γ (.app f a) (.app f a) (instantiate0 a B) :=
  lrTermFamSemBiProbeRKCanon_app_fn_of_letBinding hW hΓ ha fun c hc happrox =>
    hlet c hc (happrox.elim id id)

/-- **Off-Diagonal `ConvT.app` (`f₁ a₁ ~ f₂ a₂`) from `.letBinding` Function-Step +
    0-Instantiation Argument Congruence (`lrTermFamSemBiProbeRKCanon_app_of_letDiag_and_subst0Congr`):**
    Combines `lrTermFamSemBiProbeRKCanon_app_fn_of_letBinding` (for `f₁ a₁ ~ f₂ a₁` via `.letBinding A a₁ :: Γ`)
    and 0-instantiation congruence on `(.app (lift 0 1 f₂) (.bvar 0))` (for `f₂ a₁ ~ f₂ a₂`) via
    `lrTermFamSemBiProbeRKCanon_app_of_fn_and_arg` under `EnvWfT E` and `CtxWfT E n Γ` alone! -/
theorem lrTermFamSemBiProbeRKCanon_app_of_letDiag_and_subst0Congr (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B f₁ f₂ a₁ a₂ : Expr Nat} (ha₁ : HasTyT E n Γ a₁ A)
    (hlet : ∀ c, FamProbeCpt E c →
      (ApproxDIKCanon E Γ (.app f₁ a₁) c ∨ ApproxDIKCanon E Γ (.app f₂ a₁) c) →
      LRTermFamSemRKCanon E n (.letBinding A a₁ :: Γ)
        (.app (lift 0 1 f₁) (.bvar 0)) (.app (lift 0 1 f₂) (.bvar 0)) B c)
    (hcong : LRTermFamSemBiProbeRKCanon E n Γ
      (instantiate0 a₁ (.app (lift 0 1 f₂) (.bvar 0)))
      (instantiate0 a₂ (.app (lift 0 1 f₂) (.bvar 0)))
      (instantiate0 a₁ B)) :
    LRTermFamSemBiProbeRKCanon E n Γ (.app f₁ a₁) (.app f₂ a₂) (instantiate0 a₁ B) := by
  have hfn : LRTermFamSemBiProbeRKCanon E n Γ (.app f₁ a₁) (.app f₂ a₁) (instantiate0 a₁ B) :=
    lrTermFamSemBiProbeRKCanon_app_fn_of_letBinding hW hΓ ha₁ hlet
  have heq₁ : instantiate0 a₁ (.app (lift 0 1 f₂) (.bvar 0)) = .app f₂ a₁ := by
    simp only [instantiate0, instantiate, ite_true, lift_zero,
      instantiate_lift_cancel 1 0 0 a₁ (by omega) (by omega), Nat.sub_self]
  have heq₂ : instantiate0 a₂ (.app (lift 0 1 f₂) (.bvar 0)) = .app f₂ a₂ := by
    simp only [instantiate0, instantiate, ite_true, lift_zero,
      instantiate_lift_cancel 1 0 0 a₂ (by omega) (by omega), Nat.sub_self]
  rw [heq₁, heq₂] at hcong
  exact lrTermFamSemBiProbeRKCanon_app_of_fn_and_arg hW hΓ hfn hcong


/-! ### §8 — Part A: Kernel Audit & Resolution of `#7673` Item 2.1 / 2.2 (`convArgsT_length_le_piDoms` Refutation on Polymorphic Axiom Members vs. `NonBvarTail` Sufficiency & `ConvArgsSymmS` / `ConvArgsTransS` Discharges); Part B: `NormalUniqueR`-Free Specified-Witness Family-Spine & Π Observation Transport (`FamObsTransport` / `FamObsEquiv` / `FamConvObsMotive` / `FamObsConvLinks`) -/

/-! #### §8 Part A — Polymorphic Axiom Refutation of Unguarded `convArgsT_length_le_piDoms` & `NonBvarTail` Sufficiency -/

/-- Domain sort level `.imax (.succ (.succ .zero)) (.succ .zero)` of `polyAxType`, chosen so that
    `polyAxArg0 = .pi (.sort (.succ .zero)) (.sort .zero)` has type `.sort polyAxDomSort` directly by
    `HasTyT.pi`. -/
def polyAxDomSort : Level := .imax (.succ (.succ .zero)) (.succ .zero)

/-- Polymorphic axiom type `Π (X : Sort polyAxDomSort), X`, whose syntactic Π-domains are
    `piDomsOf polyAxType = [.sort polyAxDomSort]` (length `1`) and whose non-Π tail is
    `piTailOf polyAxType = .bvar 0`. -/
def polyAxType : Expr Nat := .pi (.sort polyAxDomSort) (.bvar 0)

/-- Admitted `.axiomM` member at index `0` with `mtype = polyAxType` and `arity = 0`. -/
def polyAxMember : CheckedMember := ⟨.axiomM, 0, polyAxType, none⟩

/-- Environment extending `emptyEnv` with `polyAxMember` at `0`. -/
def polyAxEnv : ResolvedEnv := extendEnv emptyEnv 0 polyAxMember

noncomputable def hasTyT_polyAxType :
    HasTyT emptyEnv 0 [] polyAxType (.sort (.imax (.succ polyAxDomSort) polyAxDomSort)) :=
  .pi [] (.sort polyAxDomSort) (.succ polyAxDomSort) (.bvar 0) polyAxDomSort
    (.sort [] polyAxDomSort)
    (.bvar [.assumption (.sort polyAxDomSort)] 0 (.sort polyAxDomSort) rfl)

theorem lift_polyAxType : ∀ (k : Nat), lift k 1 polyAxType = polyAxType
  | 0 => rfl
  | _ + 1 => rfl

theorem exprLevelsBounded_polyAxType : exprLevelsBounded 0 polyAxType = true := rfl

/-- `polyAxEnv` is a kernel-admitted `EnvWfT` environment (`EnvWfT.axiom`). -/
noncomputable def envWfT_polyAxEnv : EnvWfT polyAxEnv :=
  .axiom emptyEnv 0 polyAxType (.imax (.succ polyAxDomSort) polyAxDomSort)
    .empty rfl hasTyT_polyAxType lift_polyAxType exprLevelsBounded_polyAxType

theorem polyAxEnv_members_zero : polyAxEnv.members 0 = some polyAxMember := rfl

theorem piDomsOf_polyAxType : piDomsOf polyAxType = [.sort polyAxDomSort] := rfl

theorem piTailOf_polyAxType : piTailOf polyAxType = .bvar 0 := rfl

/-- First argument `Π (x : Sort 1), Sort 0 : Sort polyAxDomSort` instantiating `.bvar 0` in
    `polyAxType` to a `.pi` expression. -/
def polyAxArg0 : Expr Nat := .pi (.sort (.succ .zero)) (.sort .zero)

/-- Length-2 argument list `[polyAxArg0, .sort .zero]` exceeding `(piDomsOf polyAxType).length = 1`. -/
def polyAxArgs : List (Expr Nat) := [polyAxArg0, .sort .zero]

noncomputable def hasTyT_polyAxArg0 (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ polyAxArg0 (.sort polyAxDomSort) :=
  .pi Γ (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero) (.succ .zero)
    (.sort Γ (.succ .zero)) (.sort (.assumption (.sort (.succ .zero)) :: Γ) .zero)

/-- `ConvArgsT polyAxEnv 0 [] (instantiateLevels [] polyAxMember.mtype) polyAxArgs polyAxArgs` holds
    even though `polyAxArgs.length = 2 > 1 = (piDomsOf polyAxMember.mtype).length`, because
    `instantiate0 polyAxArg0 (piTailOf polyAxType) = instantiate0 polyAxArg0 (.bvar 0) = polyAxArg0`
    turns the non-Π tail `.bvar 0` into a `.pi`! -/
theorem convArgsT_polyAxArgs :
    ConvArgsT polyAxEnv 0 [] (instantiateLevels [] polyAxMember.mtype) polyAxArgs polyAxArgs := by
  refine .cons (.sort polyAxDomSort) (.bvar 0) polyAxArg0 polyAxArg0
    [.sort .zero] [.sort .zero]
    ⟨.refl [] polyAxArg0 (.sort polyAxDomSort) (hasTyT_polyAxArg0 polyAxEnv 0 [])⟩ ?_
  exact .cons (.sort (.succ .zero)) (.sort .zero) (.sort .zero) (.sort .zero) [] []
    ⟨.refl [] (.sort .zero) (.sort (.succ .zero)) (.sort [] .zero)⟩
    (.nil (.sort .zero))

/-- **Refutation of `convArgsT_length_le_piDoms` on `polyAxEnv`
    (`not_convArgsT_length_le_piDoms_polyAxEnv`):**
    `polyAxArgs.length = 2` while `(piDomsOf polyAxMember.mtype).length = 1`. -/
theorem not_convArgsT_length_le_piDoms_polyAxEnv :
    ¬ (polyAxArgs.length ≤ (piDomsOf polyAxMember.mtype).length) := by
  decide

/-- **Kernel Refutation of All-Member Unguarded `convArgsT_length_le_piDoms`
    (`not_allMember_convArgsT_length_le_piDoms`):**
    Refutes the claim (#7673 comment `6271576104` item 2.2) that `ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys`
    implies `xs.length ≤ (piDomsOf m.mtype).length` for arbitrary admitted `CheckedMember`s in `EnvWfT E`. -/
theorem not_allMember_convArgsT_length_le_piDoms :
    ¬ (∀ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (m : CheckedMember)
        (ls : List Level) (xs ys : List (Expr Nat)),
        EnvWfT E → CtxWfT E n Γ → E.members r = some m →
        ls.length = m.arity → levelsBounded n ls = true →
        ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys →
        xs.length ≤ (piDomsOf m.mtype).length) := by
  intro hall
  exact not_convArgsT_length_le_piDoms_polyAxEnv
    (hall polyAxEnv 0 [] 0 polyAxMember [] polyAxArgs polyAxArgs
      envWfT_polyAxEnv .nil polyAxEnv_members_zero rfl rfl convArgsT_polyAxArgs)

/-- **Unguarded All-Member `ConvArgsSymmS` Entails Π-Domain Conversion Transport on `polyAxEnv`
    (`convT_piDom_of_unguarded_convArgsSymmS_polyAxEnv`):**
    Because `piTailOf polyAxMember.mtype = .bvar 0`, instantiating slot `0` with `.pi A₁ B₁` on the
    left and `.pi A₂ B₂` on the right exposes `A₁` as the slot-`1` domain on the left and `A₂` as the
    slot-`1` domain on the right. Thus an unguarded `ConvArgsSymmS` hypothesis (without
    `xs.length ≤ (piDomsOf m.mtype).length` or `NonBvarTail m.mtype`) transports `ConvT ... x y A₁`
    to `ConvT ... y x A₂` across `ConvT ... (.pi A₁ B₁) (.pi A₂ B₂) (.sort polyAxDomSort)`. -/
theorem convT_piDom_of_unguarded_convArgsSymmS_polyAxEnv
    (hSymm : ∀ {Γ : LCtx}, CtxWfT polyAxEnv n Γ →
      ∀ {r : Nat} {m : CheckedMember}, polyAxEnv.members r = some m →
      ∀ {ls ls' : List Level} {xs xs' : List (Expr Nat)},
        ls.length = m.arity → levelsBounded n ls = true → levelsBounded n ls' = true →
        eqNList ls ls' →
        ConvArgsT polyAxEnv n Γ (instantiateLevels ls m.mtype) xs xs' →
        ConvArgsT polyAxEnv n Γ (instantiateLevels ls' m.mtype) xs' xs)
    {Γ : LCtx} (hΓ : CtxWfT polyAxEnv n Γ)
    {A₁ B₁ A₂ B₂ x y : Expr Nat}
    (hcPi : ConvT polyAxEnv n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort polyAxDomSort))
    (hxy : ConvT polyAxEnv n Γ x y A₁) :
    Nonempty (ConvT polyAxEnv n Γ y x A₂) := by
  have hargs : ConvArgsT polyAxEnv n Γ (instantiateLevels [] polyAxMember.mtype)
      [.pi A₁ B₁, x] [.pi A₂ B₂, y] :=
    .cons (.sort polyAxDomSort) (.bvar 0) (.pi A₁ B₁) (.pi A₂ B₂) [x] [y] ⟨hcPi⟩
      (.cons A₁ B₁ x y [] [] ⟨hxy⟩ (.nil _))
  have hsymm := hSymm hΓ polyAxEnv_members_zero (ls := []) (ls' := []) rfl rfl rfl trivial hargs
  cases hsymm with
  | cons _ _ _ _ _ _ _ hs =>
      cases hs with
      | cons _ _ _ _ _ _ hyx _ => exact hyx

/-- Expressions that are neither `.bvar` nor `.pi` — preserved by `instantiateLevels` and `instantiate`. -/
def IsNonBvarNonPi : Expr Nat → Prop
  | .bvar _ => False
  | .pi _ _ => False
  | _ => True

/-- A type `T` has a non-variable Π-tail (`NonBvarTail T`) when `piTailOf T` is not `.bvar i` for any `i`. -/
def NonBvarTail (T : Expr Nat) : Prop :=
  ∀ i, piTailOf T ≠ .bvar i

theorem piTailOf_ne_pi : ∀ (T A B : Expr Nat), piTailOf T ≠ .pi A B
  | .pi _ B, A, C, h => piTailOf_ne_pi B A C h
  | .bvar _, _, _, h => Expr.noConfusion h
  | .sort _, _, _, h => Expr.noConfusion h
  | .const _ _, _, _, h => Expr.noConfusion h
  | .app _ _, _, _, h => Expr.noConfusion h
  | .lam _ _, _, _, h => Expr.noConfusion h
  | .letE _ _ _, _, _, h => Expr.noConfusion h
  | .lit _, _, _, h => Expr.noConfusion h

theorem isNonBvarNonPi_piTailOf_of_nonBvarTail {T : Expr Nat} (h : NonBvarTail T) :
    IsNonBvarNonPi (piTailOf T) := by
  cases he : piTailOf T with
  | bvar i => exact h i he
  | pi A B => exact piTailOf_ne_pi T A B he
  | sort _ => trivial
  | const _ _ => trivial
  | app _ _ => trivial
  | lam _ _ => trivial
  | letE _ _ _ => trivial
  | lit _ => trivial

theorem isNonBvarNonPi_instantiateLevels (ls : List Level) {e : Expr Nat}
    (h : IsNonBvarNonPi e) : IsNonBvarNonPi (instantiateLevels ls e) := by
  cases e <;> exact h

theorem isNonBvarNonPi_instantiate (k : Nat) (u : Expr Nat) {e : Expr Nat}
    (h : IsNonBvarNonPi e) : IsNonBvarNonPi (instantiate k u e) := by
  cases e with
  | bvar _ => exact h.elim
  | pi _ _ => exact h.elim
  | sort _ => trivial
  | const _ _ => trivial
  | app _ _ => trivial
  | lam _ _ => trivial
  | letE _ _ _ => trivial
  | lit _ => trivial

/-- Whenever `IsNonBvarNonPi U` holds, `ConvArgsT E n Γ (policyPi ds U) xs ys` forces
    `xs.length ≤ ds.length` because `U` (and every `instantiate` of `U`) is never a `.pi`. -/
theorem convArgsT_length_le_policyPi_of_isNonBvarNonPi :
    ∀ {xs : List (Expr Nat)} {ds : List (Expr Nat)} {U : Expr Nat} {ys : List (Expr Nat)},
      IsNonBvarNonPi U →
      ConvArgsT E n Γ (policyPi ds U) xs ys →
      xs.length ≤ ds.length
  | [], _, _, _, _, _ => Nat.zero_le _
  | f :: fs, [], U, ys, hU, h => by
      simp only [policyPi] at h
      generalize hEq : U = W at h
      cases h with
      | cons _ _ _ _ _ _ _ _ =>
          subst hEq
          exact hU.elim
  | f :: fs, A :: ds', U, ys, hU, h => by
      simp only [policyPi] at h
      cases h with
      | cons _ _ _ _ _ fs' _ hs =>
          have hinst : instantiate0 f (policyPi ds' U) =
              policyPi (instDomsT 0 f ds') (instantiate (0 + ds'.length) (lift 0 ds'.length f) U) := by
            simp only [instantiate0, instantiate_policyPi]
          rw [hinst] at hs
          have hle := convArgsT_length_le_policyPi_of_isNonBvarNonPi
            (isNonBvarNonPi_instantiate (0 + ds'.length) (lift 0 ds'.length f) hU) hs
          rw [length_instDomsT] at hle
          exact Nat.succ_le_succ hle

/-- **Sufficiency of `NonBvarTail T` for `convArgsT_length_le_piDoms`
    (`convArgsT_length_le_piDoms_of_nonBvarTail`):**
    Whenever `NonBvarTail T` holds (`∀ i, piTailOf T ≠ .bvar i`), any `ConvArgsT E n Γ (instantiateLevels ls T) xs ys`
    automatically satisfies `xs.length ≤ (piDomsOf T).length`! -/
theorem convArgsT_length_le_piDoms_of_nonBvarTail {T : Expr Nat} (hT : NonBvarTail T)
    {ls : List Level} {xs ys : List (Expr Nat)}
    (h : ConvArgsT E n Γ (instantiateLevels ls T) xs ys) :
    xs.length ≤ (piDomsOf T).length := by
  rw [instantiateLevels_policyPi_piDomsOf_piTailOf ls T] at h
  have hle := convArgsT_length_le_policyPi_of_isNonBvarNonPi
    (isNonBvarNonPi_instantiateLevels ls (isNonBvarNonPi_piTailOf_of_nonBvarTail hT)) h
  rwa [List.length_map] at hle

/-- Every arity (`isArity T = true`) has `piTailOf T = .sort (piBody T)` and therefore `NonBvarTail T`. -/
theorem nonBvarTail_of_isArity {T : Expr Nat} (har : isArity T = true) : NonBvarTail T := by
  intro i h
  rw [piTailOf_eq_piResult T, (isArity_piResult_sort T har).2] at h
  exact Expr.noConfusion h

/-- Every admitted `.inductiveM` member in `EnvWfT E` has `NonBvarTail m.mtype`. -/
theorem nonBvarTail_of_inductiveM (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) :
    NonBvarTail m.mtype := by
  intro i h
  rw [piTailOf_eq_piResult m.mtype, piResult_mtype_of_inductiveM hW hm hind] at h
  exact Expr.noConfusion h

theorem convArgsT_length_le_piDoms_of_isArity {T : Expr Nat} (har : isArity T = true)
    {ls : List Level} {xs ys : List (Expr Nat)}
    (h : ConvArgsT E n Γ (instantiateLevels ls T) xs ys) :
    xs.length ≤ (piDomsOf T).length :=
  convArgsT_length_le_piDoms_of_nonBvarTail (nonBvarTail_of_isArity har) h

theorem convArgsT_length_le_piDoms_of_inductiveM (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {xs ys : List (Expr Nat)}
    (h : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys) :
    xs.length ≤ (piDomsOf m.mtype).length :=
  convArgsT_length_le_piDoms_of_nonBvarTail (nonBvarTail_of_inductiveM hW hm hind) h

/-- **Unbounded `ConvArgsT` Symmetry for Any Member with `NonBvarTail m.mtype` Under `EnvWfT E` Alone
    (`convArgs_symm_of_nonBvarTail_levelFacts`):**
    No `xs.length ≤ (piDomsOf m.mtype).length` premise and zero `PiRowField`! -/
theorem convArgs_symm_of_nonBvarTail_levelFacts (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hnb : NonBvarTail m.mtype)
    {ls ls' : List Level} {xs ys : List (Expr Nat)}
    (hlen : ls.length = m.arity) (hbel : levelsBounded n ls = true)
    (hbel' : levelsBounded n ls' = true) (heqN : eqNList ls ls')
    (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys) :
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) ys xs := by
  have hlen' : ls'.length = m.arity := (eqNList_length ls ls' heqN).symm.trans hlen
  exact convArgs_symm_member_of_levelFacts hW hΓ hm hlen hbel hlen' hbel' heqN
    (convArgsT_length_le_piDoms_of_nonBvarTail hnb hargs) hargs

/-- **Unbounded `ConvArgsT` Transitivity for Any Member with `NonBvarTail m.mtype` Under `EnvWfT E` Alone
    (`convArgs_trans_of_nonBvarTail_levelFacts`):**
    No `xs.length ≤ (piDomsOf m.mtype).length` premise and zero `PiRowField`! -/
theorem convArgs_trans_of_nonBvarTail_levelFacts (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hnb : NonBvarTail m.mtype)
    {ls₁ ls₂ : List Level} {xs ys zs : List (Expr Nat)}
    (hlen₁ : ls₁.length = m.arity) (hbel₁ : levelsBounded n ls₁ = true)
    (hbel₂ : levelsBounded n ls₂ = true) (heqN : eqNList ls₁ ls₂)
    (hargs₁ : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs ys)
    (hargs₂ : ConvArgsT E n Γ (instantiateLevels ls₂ m.mtype) ys zs) :
    ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs zs := by
  have hlen₂ : ls₂.length = m.arity := (eqNList_length ls₁ ls₂ heqN).symm.trans hlen₁
  exact convArgs_trans_member_of_levelFacts hW hΓ hm hlen₁ hbel₁ hlen₂ hbel₂ heqN
    (convArgsT_length_le_piDoms_of_nonBvarTail hnb hargs₁) hargs₁ hargs₂


/-! #### §8 Part B — `NormalUniqueR`-Free Specified-Witness Family-Spine, Π, & Sort Observation Transport (`FamObsTransport` / `FamObsEquiv` / `FamConvObsMotive` / `FamObsConvLinks`) -/

/-- Specified-witness sort readback transport (`FamSortReadTransport`): preserves existence of a
    sort readback `RedR R Γ M (.sort u)`. -/
def FamSortReadTransport (R : Readback) (Γ : LCtx) (M N : Expr Nat) : Prop :=
  (∃ u, RedR R Γ M (.sort u)) → (∃ v, RedR R Γ N (.sort v))

/-- Specified-witness Π readback transport (`FamPiReadTransport`): transports every specified Π
    readback `RedR R Γ M (.pi A B)` with `CtxWfT E n (.assumption A :: Γ)` to a target Π readback
    `RedR R Γ N (.pi A' B')` with `TyConvT E n Γ A A'` and `TyConvT E n (.assumption A :: Γ) B B'`. -/
def FamPiReadTransport (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M N : Expr Nat) : Prop :=
  ∀ {A B : Expr Nat},
    RedR R Γ M (.pi A B) → CtxWfT E n (.assumption A :: Γ) →
    ∃ A' B' : Expr Nat,
      RedR R Γ N (.pi A' B') ∧
      Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B')

/-- **Specified-Witness Family-Spine Readback Transport (`FamSpineReadTransport`):**
    Transports every specified saturated well-typed admitted `.inductiveM` family-spine readback
    `RedR R Γ M (foldApps (.const r ls) xs)` (with `ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs`)
    to a target saturated well-typed family-spine readback `RedR R Γ N (foldApps (.const r ls') xs')`
    with `TyConvT`, `eqNList ls ls'`, and `ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs'`. -/
def FamSpineReadTransport (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M N : Expr Nat) : Prop :=
  ∀ {r : Nat} {m : CheckedMember} {ls : List Level} {xs : List (Expr Nat)} {w : Level},
    E.members r = some m → m.mclass = .inductiveM →
    RedR R Γ M (foldApps (.const r ls) xs) →
    HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w) →
    xs.length = (piDomsOf m.mtype).length →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs →
    ∃ (ls' : List Level) (xs' : List (Expr Nat)) (w' : Level),
      RedR R Γ N (foldApps (.const r ls') xs') ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w')) ∧
      Nonempty (TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) ∧
      eqNList ls ls' ∧
      xs'.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs'

/-- Combined specified-witness Sort + Π + Family-Spine observation transport (`FamObsTransport`). -/
def FamObsTransport (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M N : Expr Nat) : Prop :=
  FamSortReadTransport R Γ M N ∧
  FamPiReadTransport R E n Γ M N ∧
  FamSpineReadTransport R E n Γ M N

/-- Bidirectional specified-witness Sort + Π + Family-Spine observation equivalence (`FamObsEquiv`). -/
def FamObsEquiv (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M N : Expr Nat) : Prop :=
  FamObsTransport R E n Γ M N ∧ FamObsTransport R E n Γ N M

/-- Index-erased `ConvT` motive for specified-witness Sort + Π + Family-Spine observation equivalence. -/
def FamConvObsMotive (R : Readback) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {M N A : Expr Nat}
    (_hc : ConvT E n Γ M N A) : Prop :=
  FamObsEquiv R E n Γ M N

/-- Single-link `ConvT` obligation for specified-witness Sort + Π + Family-Spine observation equivalence. -/
def FamObsConvLinks (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M N : Expr Nat} {u : Level}
    (hc : ConvT E n Γ M N (.sort u)), FamConvObsMotive R hc

theorem famSpineReadTransport_refl (Γ : LCtx) (M : Expr Nat) :
    FamSpineReadTransport R E n Γ M M := by
  intro r m ls xs w _ _ hM hty hlen hargs
  exact ⟨ls, xs, w, hM, ⟨hty⟩, ⟨.refl Γ _⟩, eqNList_refl ls, hlen, hargs⟩

/-- **`NormalUniqueR`-Free and `PiRowField`-Free Transitivity of `FamSpineReadTransport`
    (`famSpineReadTransport_trans`):**
    Passes the exact middle family-spine witness `(ls₂, xs₂, w₂)` from `ht₁` into `ht₂` using
    `convArgs_symm_instMtype_of_envWfT` and `convArgs_trans_instMtype_of_envWfT` (`RcicNativeFamModel` §16) —
    requiring **only `EnvWfT E` and `CtxWfT E n Γ`, with ZERO `NormalUniqueR R`, ZERO `WhFamCohRecK`,
    and ZERO `PiRowField`**! -/
theorem famSpineReadTransport_trans (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N P : Expr Nat}
    (ht₁ : FamSpineReadTransport R E n Γ M N)
    (ht₂ : FamSpineReadTransport R E n Γ N P) :
    FamSpineReadTransport R E n Γ M P := by
  intro r m ls₁ xs₁ w₁ hm hind hM hty₁ hlen₁ hargs₁₁
  obtain ⟨ls₂, xs₂, w₂, hN, ⟨hty₂⟩, ⟨hconv₁₂⟩, heq₁₂, hlen₂, hargs₁₂⟩ :=
    ht₁ hm hind hM hty₁ hlen₁ hargs₁₁
  have hargs₂₁ : ConvArgsT E n Γ (instantiateLevels ls₂ m.mtype) xs₂ xs₁ :=
    convArgs_symm_instMtype_of_envWfT hW hΓ hm hind hty₁ hty₂ heq₁₂ hargs₁₂
  have hargs₂₂ : ConvArgsT E n Γ (instantiateLevels ls₂ m.mtype) xs₂ xs₂ :=
    convArgs_trans_instMtype_of_envWfT hW hΓ hm hind hty₂ hty₁ (eqNList_symm heq₁₂)
      hargs₂₁ hargs₁₂
  obtain ⟨ls₃, xs₃, w₃, hP, ⟨hty₃⟩, ⟨hconv₂₃⟩, heq₂₃, hlen₃, hargs₂₃⟩ :=
    ht₂ hm hind hN hty₂ hlen₂ hargs₂₂
  exact ⟨ls₃, xs₃, w₃, hP, ⟨hty₃⟩, ⟨.trans Γ _ _ _ hconv₁₂ hconv₂₃⟩,
    eqNList_trans heq₁₂ heq₂₃, hlen₃,
    convArgs_trans_instMtype_of_envWfT hW hΓ hm hind hty₁ hty₂ heq₁₂ hargs₁₂ hargs₂₃⟩

theorem famObsTransport_refl (Γ : LCtx) (M : Expr Nat) :
    FamObsTransport R E n Γ M M :=
  ⟨id,
   fun hM _ => ⟨_, _, hM, ⟨.refl _ _⟩, ⟨.refl _ _⟩⟩,
   famSpineReadTransport_refl Γ M⟩

/-- **`NormalUniqueR`-Free and `PiRowField`-Free Transitivity of `FamObsTransport`
    (`famObsTransport_trans`):** -/
theorem famObsTransport_trans (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N P : Expr Nat}
    (ht₁ : FamObsTransport R E n Γ M N)
    (ht₂ : FamObsTransport R E n Γ N P) :
    FamObsTransport R E n Γ M P := by
  refine ⟨fun hs => ht₂.1 (ht₁.1 hs), fun {A B} hM hΓA => ?_,
    famSpineReadTransport_trans hW hΓ ht₁.2.2 ht₂.2.2⟩
  obtain ⟨A', B', hN, ⟨hd₁⟩, ⟨hc₁⟩⟩ := ht₁.2.1 hM hΓA
  cases hΓA with
  | assumption _ _ u _ hA =>
      obtain ⟨u', hA'⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hd₁ hA
      have hΓA' : CtxWfT E n (.assumption A' :: Γ) := .assumption Γ A' u' hΓ hA'
      obtain ⟨A'', B'', hP, ⟨hd₂⟩, ⟨hc₂⟩⟩ := ht₂.2.1 hN hΓA'
      have hc₂' : TyConvT E n (.assumption A :: Γ) B' B'' :=
        tyConvT_assump_dom hW hΓ hd₁ hc₂
      exact ⟨A'', B'', hP, ⟨.trans Γ A A' A'' hd₁ hd₂⟩,
        ⟨.trans (.assumption A :: Γ) B B' B'' hc₁ hc₂'⟩⟩

theorem famObsEquiv_refl (Γ : LCtx) (M : Expr Nat) :
    FamObsEquiv R E n Γ M M :=
  ⟨famObsTransport_refl Γ M, famObsTransport_refl Γ M⟩

theorem famObsEquiv_symm {Γ : LCtx} {M N : Expr Nat}
    (h : FamObsEquiv R E n Γ M N) :
    FamObsEquiv R E n Γ N M :=
  ⟨h.2, h.1⟩

theorem famObsEquiv_trans (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N P : Expr Nat}
    (h₁ : FamObsEquiv R E n Γ M N)
    (h₂ : FamObsEquiv R E n Γ N P) :
    FamObsEquiv R E n Γ M P :=
  ⟨famObsTransport_trans hW hΓ h₁.1 h₂.1,
   famObsTransport_trans hW hΓ h₂.2 h₁.2⟩

/-- **Chaining `FamObsEquiv` Along Any `TyConvT E n Γ A B` Without `NormalUniqueR R`
    (`famObsEquiv_chain`):** -/
theorem famObsEquiv_chain (hW : EnvWfT E) (hlinks : FamObsConvLinks R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (hc : TyConvT E n Γ A B) :
    FamObsEquiv R E n Γ A B := by
  induction hc with
  | refl A => exact famObsEquiv_refl Γ A
  | of A B _ hc => exact hlinks hΓ hc
  | trans A B C _ _ ih₁ ih₂ => exact famObsEquiv_trans hW hΓ ih₁ ih₂

/-- Projecting `FamObsTransport` to `LRSCore` on any `FamProbeCpt E c`. -/
theorem lrSCore_of_famObsTransport (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N : Expr Nat} {u : Level} (ht : FamObsTransport R E n Γ M N)
    {c : CptI} (hpc : FamProbeCpt E c)
    (hMM : LRSCore R E n Γ M M (.sort u) c) :
    LRSCore R E n Γ M N (.sort u) c := by
  cases hpc with
  | bot => exact lrSCore_bot _ _ _ _
  | sort =>
      rw [LRSCore.eq_def] at hMM ⊢
      obtain ⟨hi, l, _, hM, _⟩ := hMM
      obtain ⟨v, hN⟩ := ht.1 ⟨l, hM⟩
      exact ⟨hi, l, v, hM, hN⟩
  | pi_bot_nil =>
      rw [LRSCore.eq_def] at hMM ⊢
      obtain ⟨hi, A, B, _, _, hM, _, ⟨hΓA⟩, _⟩ := hMM
      obtain ⟨A', B', hN, hdom, hcod⟩ := ht.2.1 hM hΓA
      exact ⟨hi, A, B, A', B', hM, hN, ⟨hΓA⟩, hdom, hcod,
        ⟨.zero, lrSCore_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩
  | @famSpine r m cs hm hind _ _ =>
      rw [LRSCore.eq_def] at hMM ⊢
      rcases hMM with ⟨hi, hsp⟩ | ⟨hns, _⟩
      · rcases hsp with ⟨m', ls₁, ls₂, xs₁, xs₂, w₁, w₂, hm', _, hM, _, ⟨hty₁⟩, ⟨hty₂⟩, _, heq, hlen₁, _, hargs⟩ | ⟨hnot, _⟩
        · have em : m = m' := Option.some.inj (hm.symm.trans hm')
          subst em
          have hargs₂₁ := convArgs_symm_instMtype_of_envWfT hW hΓ hm hind hty₁ hty₂ heq hargs
          have hargs₁₁ := convArgs_trans_instMtype_of_envWfT hW hΓ hm hind hty₁ hty₂ heq hargs hargs₂₁
          obtain ⟨ls', xs', w', hN, hty', hconv, heq', hlen', hargs'⟩ :=
            ht.2.2 hm hind hM hty₁ hlen₁ hargs₁₁
          exact Or.inl ⟨hi, Or.inl ⟨m, ls₁, ls', xs₁, xs', w₁, w', hm, hind, hM, hN,
            ⟨hty₁⟩, hty', hconv, heq', hlen₁, hlen', hargs'⟩⟩
        · exact (hnot m hm hind).elim
      · exact (hns u (.refl _)).elim

/-- Projecting `FamObsTransport` to `LRSCoreT` on any `FamProbeCptT E c`. -/
theorem lrSCoreT_of_famObsTransport (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N : Expr Nat} {u : Level} (hMN : TyConvT E n Γ M N)
    (ht : FamObsTransport R E n Γ M N)
    {c : CptT} (hpc : FamProbeCptT E c)
    (hMM : LRSCoreT R E n Γ M M (.sort u) c) :
    LRSCoreT R E n Γ M N (.sort u) c := by
  cases hpc with
  | bot => exact lrSCoreT_bot _ _ _ _
  | prop =>
      rw [lrSCoreT_prop_iff] at hMM ⊢
      obtain ⟨hi, l, _, hM, _⟩ := hMM
      obtain ⟨v, hN⟩ := ht.1 ⟨l, hM⟩
      exact ⟨hi, l, v, hM, hN⟩
  | sort =>
      rw [lrSCoreT_sort_iff] at hMM ⊢
      obtain ⟨hi, l, _, hM, _⟩ := hMM
      obtain ⟨v, hN⟩ := ht.1 ⟨l, hM⟩
      exact ⟨hi, l, v, hM, hN⟩
  | piBotNil =>
      rw [LRSCoreT.eq_def] at hMM ⊢
      obtain ⟨hi, A, B, _, _, hM, _, ⟨hΓA⟩, _⟩ := hMM
      obtain ⟨A', B', hN, hdom, hcod⟩ := ht.2.1 hM hΓA
      exact ⟨hi, A, B, A', B', hM, hN, ⟨hΓA⟩, hdom, hcod,
        ⟨.zero, lrSCoreT_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩
  | @spine r m args hm hind _ =>
      rw [lrSCoreT_spine_sort_iff] at hMM ⊢
      rcases hMM.2 with ⟨m', ls₁, ls₂, xs₁, xs₂, w₁, w₂, hm', _, hM, _, ⟨hty₁⟩, ⟨hty₂⟩, heq, hlen₁, _, hargs⟩ | ⟨hnot, _⟩
      · have em : m = m' := Option.some.inj (hm.symm.trans hm')
        subst em
        have hargs₂₁ := convArgs_symm_instMtype_of_envWfT hW hΓ hm hind hty₁ hty₂ heq hargs
        have hargs₁₁ := convArgs_trans_instMtype_of_envWfT hW hΓ hm hind hty₁ hty₂ heq hargs hargs₂₁
        obtain ⟨ls', xs', w', hN, hty', _, heq', hlen', hargs'⟩ :=
          ht.2.2 hm hind hM hty₁ hlen₁ hargs₁₁
        exact ⟨⟨hMN⟩, Or.inl ⟨m, ls₁, ls', xs₁, xs', w₁, w', hm, hind, hM, hN,
          ⟨hty₁⟩, hty', heq', hlen₁, hlen', hargs'⟩⟩
      · exact (hnot m hm hind).elim

/-- `FamObsConvLinks R E n` discharges `FamProbeLink R E n` (on `LRSCore`). -/
theorem famProbeLink_of_famObsConvLinks (hW : EnvWfT E) (hlinks : FamObsConvLinks R E n) :
    FamProbeLink R E n := by
  intro Γ hΓ A B _ hc c hpc hAA
  exact lrSCore_of_famObsTransport hW hΓ (hlinks hΓ hc).1 hpc hAA

/-- `FamObsConvLinks R E n` discharges `FamProbeLinkT R E n` (on `LRSCoreT`). -/
theorem famProbeLinkT_of_famObsConvLinks (hW : EnvWfT E) (hlinks : FamObsConvLinks R E n) :
    FamProbeLinkT R E n := by
  intro Γ hΓ A B u hc c hpc hAA
  exact lrSCoreT_of_famObsTransport hW hΓ (.of Γ A B u hc) (hlinks hΓ hc).1 hpc hAA

/-- `FamObsConvLinks R E n` discharges `PiProbeLinkT R E n` (`RcicNativePiCycleProbe`). -/
theorem piProbeLinkT_of_famObsConvLinks (hW : EnvWfT E) (hlinks : FamObsConvLinks R E n) :
    PiCycleAudit.PiProbeLinkT R E n := by
  intro Γ hΓ A B u hc hAA
  exact lrSCoreT_of_famObsTransport hW hΓ (.of Γ A B u hc) (hlinks hΓ hc).1 .piBotNil hAA

/-- **`NormalUniqueR`-Free `PiRowField E n` from `FamObsConvLinks R E n`
    (`piRowField_of_famObsConvLinks`):**
    Requires **only `ReadbackLaws E R` and `EnvWfT E`** — no `NormalUniqueR R`! -/
theorem piRowField_of_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hlinks : FamObsConvLinks R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    obtain ⟨u₁, _, hA, _, _⟩ := hasTyTInv_pi hPi rfl
    have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u₁ hΓ hA
    obtain ⟨A₂, B₂, hred, hdom, hcod⟩ :=
      (famObsEquiv_chain hW hlinks hΓ hc).1.2.1 (.refl _) hΓA
    have heq := redR_pi_eq hL hred
    injection heq with eA eB
    subst eA; subst eB
    exact ⟨hdom, hcod⟩

theorem not_tyConvT_pi_sort_of_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hlinks : FamObsConvLinks R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.pi A B) (.sort l)) : False := by
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · exact Expr.noConfusion heq
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    obtain ⟨u₁, _, hA, _, _⟩ := hasTyTInv_pi hPi rfl
    have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u₁ hΓ hA
    obtain ⟨_, _, hred, _, _⟩ := (famObsEquiv_chain hW hlinks hΓ hc).1.2.1 (.refl _) hΓA
    exact Expr.noConfusion (redR_sort_eq hL hred)

theorem not_tyConvT_sort_pi_of_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hlinks : FamObsConvLinks R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.sort l) (.pi A B)) : False := by
  obtain ⟨_, hred⟩ := (famObsEquiv_chain hW hlinks hΓ hc).1.1 ⟨l, .refl _⟩
  exact Expr.noConfusion (redR_pi_eq hL hred)

theorem famApp_saturated_of_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hlinks : FamObsConvLinks R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (_hind : m.mclass = .inductiveM)
    {doms : List (Expr Nat)} {u : Level}
    (hpi : instantiateLevels ls m.mtype = policyPi doms (.sort u))
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = doms.length := by
  have hprow : PiRowField E n := piRowField_of_famObsConvLinks hL hW hlinks
  rcases Nat.lt_trichotomy xs.length doms.length with hlt | heq | hgt
  · exfalso
    have hne : doms.drop xs.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hlt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hpi' : instantiateLevels ls m.mtype =
        policyPi (doms.take xs.length) (policyPi (doms.drop xs.length) (.sort u)) := by
      rw [← List.take_append_drop xs.length doms] at hpi
      rw [hpi, policyPi_append]
    have hlen' : (doms.take xs.length).length = xs.length := by
      rw [List.length_take]
      first
        | exact Nat.min_eq_right (Nat.le_of_lt hlt)
        | exact Nat.min_eq_left (Nat.le_of_lt hlt)
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi' xs hlen' hty
    rw [hrest] at hconv
    simp only [policyPi] at hconv
    rw [instPrefix_pi] at hconv
    exact not_tyConvT_pi_sort_of_famObsConvLinks hL hW hlinks hΓ hconv
  · exact heq
  · exfalso
    have hne : xs.drop doms.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hgt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hsplit : foldApps (.const r ls) xs =
        foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
      calc foldApps (.const r ls) xs
          = foldApps (.const r ls) (xs.take doms.length ++ xs.drop doms.length) := by
              rw [List.take_append_drop]
        _ = foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
            foldApps_append _ _ _
    obtain ⟨_, _, ⟨hf⟩⟩ := hasTyT_foldApps_prefix_pi
      (f := foldApps (.const r ls) (xs.take doms.length))
      (hsplit ▸ hty) hrest
    have hlen' : doms.length = (xs.take doms.length).length := by
      rw [List.length_take]
      first
        | exact (Nat.min_eq_right (Nat.le_of_lt hgt)).symm
        | exact (Nat.min_eq_left (Nat.le_of_lt hgt)).symm
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi
      (xs.take doms.length) hlen' hf
    rw [instPrefix_sort] at hconv
    exact not_tyConvT_sort_pi_of_famObsConvLinks hL hW hlinks hΓ hconv

theorem famApp_length_eq_piDomsOf_of_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hlinks : FamObsConvLinks R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = (piDomsOf m.mtype).length := by
  have hlen := famApp_saturated_of_famObsConvLinks hL hW hlinks hΓ hm hind
    (instMtype_policyPi_of_inductiveM hW hm hind ls) hty
  rwa [List.length_map] at hlen

/-- **`NormalUniqueR`-Free `FamAppRowLink E n` Directly from `FamObsConvLinks R E n`
    (`famAppRow_of_famObsConvLinks`):**
    Requires **only `ReadbackLaws E R` and `EnvWfT E`** — zero `NormalUniqueR R`, zero `WhFamCohRecK`,
    and zero `ReadbackModelInv`! -/
theorem famAppRow_of_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hlinks : FamObsConvLinks R E n) :
    FamAppRowLink E n := by
  intro Γ hΓ r m ls ls' xs xs' _ hm hind hty hc
  have hpi : PiRowField E n := piRowField_of_famObsConvLinks hL hW hlinks
  have hl : xs.length = (piDomsOf m.mtype).length :=
    famApp_length_eq_piDomsOf_of_famObsConvLinks hL hW hlinks hΓ hm hind hty
  have hargs₀ : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs :=
    convArgs_refl_instMtype hW hpi hΓ hm hind hl hty
  obtain ⟨ls₂, xs₂, _, hred, _, _, heqN, hlen₂, hargs⟩ :=
    (famObsEquiv_chain hW hlinks hΓ hc).1.2.2 hm hind (.refl _) hty hl hargs₀
  have heq := redR_famApp_eq hL hW hm hind hred
  obtain ⟨hconst, hxs⟩ := foldApps_const_inj heq
  injection hconst with _ hls
  subst hls; subst hxs
  exact ⟨heqN, hl.trans hlen₂.symm, hargs⟩

/-- **`NormalUniqueR`-Free `FamRelevantSlotConv E n` (#7525) Directly from `FamObsConvLinks R E n`
    (`famRelevantSlotConv_of_famObsConvLinks`):** -/
theorem famRelevantSlotConv_of_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hlinks : FamObsConvLinks R E n) :
    FamRelevantSlotConv E n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty hc
  have hrow := famAppRow_of_famObsConvLinks hL hW hlinks hΓ hm hind hty hc
  exact relevantSlotConv_of_convArgsT hW hm hind hrow.2.2

/-- **`NormalUniqueR`-Free `TypedRowsWf E n` Directly from `FamObsConvLinks R E n`
    (`typedRowsWf_of_allBelowScoped_famObsConvLinks`):** -/
theorem typedRowsWf_of_allBelowScoped_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlinks : FamObsConvLinks R E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_build hW hBel
  piRow := piRowField_of_famObsConvLinks hL hW hlinks
  famAppRow := famAppRow_of_famObsConvLinks hL hW hlinks

/-- Constructor closure of `FamConvObsMotive` for `ConvT.refl`. -/
theorem famConvObs_refl (Γ : LCtx) (M A : Expr Nat) (h : HasTyT E n Γ M A) :
    FamConvObsMotive R (.refl Γ M A h) :=
  famObsEquiv_refl Γ M

/-- Constructor closure of `FamConvObsMotive` for `ConvT.symm`. -/
theorem famConvObs_symm {Γ : LCtx} {M N A : Expr Nat}
    (hc : ConvT E n Γ M N A) (ih : FamConvObsMotive R hc) :
    FamConvObsMotive R (.symm Γ M N A hc) :=
  famObsEquiv_symm ih

/-- Constructor closure of `FamConvObsMotive` for `ConvT.trans` (under `EnvWfT E` and `CtxWfT E n Γ`
    alone — zero `NormalUniqueR R`!). -/
theorem famConvObs_trans (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N P A : Expr Nat} (hMN : ConvT E n Γ M N A) (hNP : ConvT E n Γ N P A)
    (ihMN : FamConvObsMotive R hMN) (ihNP : FamConvObsMotive R hNP) :
    FamConvObsMotive R (.trans Γ M N P A hMN hNP) :=
  famObsEquiv_trans hW hΓ ihMN ihNP

/-- Constructor closure of `FamConvObsMotive` for `ConvT.tyConv` (definitional from index erasure). -/
theorem famConvObs_tyConv {Γ : LCtx} {M N A A' : Expr Nat} {u : Level}
    (hc : ConvT E n Γ M N A) (hA : ConvT E n Γ A A' (.sort u))
    (ih : FamConvObsMotive R hc) :
    FamConvObsMotive R (.tyConv Γ M N A A' u hc hA) := ih

/-- Forward observation transport for syntactic sorts under `ReadbackLaws E R`. -/
theorem famObsTransport_sorts (hL : ReadbackLaws E R) (Γ : LCtx) (u v : Level) :
    FamObsTransport R E n Γ (.sort u) (.sort v) := by
  refine ⟨fun _ => ⟨v, .refl _⟩, fun h _ => ?_, fun _ _ h _ _ _ => ?_⟩
  · exact Expr.noConfusion (redR_sort_eq hL h)
  · exact (TypedModelAudit.foldApps_const_ne_sort _ _ (redR_sort_eq hL h)).elim

/-- Constructor closure of `FamConvObsMotive` for `ConvT.sorts`. -/
theorem famConvObs_sorts (hL : ReadbackLaws E R) (Γ : LCtx) (u v : Level) (heq : eqN u v) :
    FamConvObsMotive R (ConvT.sorts (E := E) (n := n) Γ u v heq) :=
  ⟨famObsTransport_sorts hL Γ u v, famObsTransport_sorts hL Γ v u⟩

/-- Forward observation transport for syntactic Π-types under `ReadbackLaws E R`. -/
theorem famObsTransport_pi (hL : ReadbackLaws E R) {Γ : LCtx}
    {A A' B B' : Expr Nat} (hA : TyConvT E n Γ A A')
    (hB : TyConvT E n (.assumption A :: Γ) B B') :
    FamObsTransport R E n Γ (.pi A B) (.pi A' B') := by
  refine ⟨fun ⟨_, h⟩ => Expr.noConfusion (redR_pi_eq hL h),
    fun h _ => ?_,
    fun _ _ h _ _ _ => (TypedModelAudit.foldApps_const_ne_pi _ _ _ (redR_pi_eq hL h)).elim⟩
  have heq := redR_pi_eq hL h
  injection heq with eA eB
  subst eA; subst eB
  exact ⟨A', B', .refl _, ⟨hA⟩, ⟨hB⟩⟩

/-- Constructor closure of `FamConvObsMotive` for `ConvT.pi`. -/
theorem famConvObs_pi (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    FamConvObsMotive R (.pi Γ A A' B B' u v hA hB) := by
  let hdom : TyConvT E n Γ A A' := .of _ _ _ _ hA
  let hcod : TyConvT E n (.assumption A :: Γ) B B' := .of _ _ _ _ hB
  exact ⟨famObsTransport_pi hL hdom hcod,
    famObsTransport_pi hL hdom.symmT
      (tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT)⟩

/-- Any pair of expressions `(M, N)` where every readback of `M` to a normal form is also a readback
    of `N` satisfies `FamObsTransport R E n Γ M N`. -/
theorem famObsTransport_of_readback_imp (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Γ : LCtx} {M N : Expr Nat}
    (himp : ∀ {V : Expr Nat}, NormalR R Γ V → RedR R Γ M V → RedR R Γ N V) :
    FamObsTransport R E n Γ M N := by
  refine ⟨fun ⟨u, hM⟩ => ⟨u, himp (fun _ hs => hL.sort_normal Γ u _ hs) hM⟩,
    fun hM _ => ⟨_, _, himp (fun _ hs => hL.pi_normal Γ _ _ _ hs) hM, ⟨.refl _ _⟩, ⟨.refl _ _⟩⟩,
    fun {r m ls xs w} hm hind hM hty hlen hargs =>
      ⟨ls, xs, w, himp (fun _ hs => hL.famApp_normal hW Γ hm hind _ _ _ hs) hM,
        ⟨hty⟩, ⟨.refl _ _⟩, eqNList_refl _, hlen, hargs⟩⟩

/-- Any one-step readback `hs : R Γ M N` under `ReadbackLaws E R`, `DetR R`, and `EnvWfT E`
    satisfies `FamObsEquiv R E n Γ M N`. -/
theorem famObsEquiv_of_stepR (hL : ReadbackLaws E R) (hdet : DetR R) (hW : EnvWfT E)
    {Γ : LCtx} {M N : Expr Nat} (hs : R Γ M N) :
    FamObsEquiv R E n Γ M N := by
  refine ⟨famObsTransport_of_readback_imp hL hW (fun hn hM => ?_),
    famObsTransport_of_readback_imp hL hW (fun _ hN => .step hs hN)⟩
  cases hM with
  | refl => exact (hn N hs).elim
  | step hs' hrest =>
      have e : _ = N := hdet Γ hs' hs
      subst e
      exact hrest

/-- Any multi-step readback `hr : RedR R Γ M N` under `ReadbackLaws E R`, `DetR R`, and `EnvWfT E`
    satisfies `FamObsEquiv R E n Γ M N`. -/
theorem famObsEquiv_of_redR (hL : ReadbackLaws E R) (hdet : DetR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N : Expr Nat} (hr : RedR R Γ M N) :
    FamObsEquiv R E n Γ M N := by
  induction hr with
  | refl M => exact famObsEquiv_refl Γ M
  | step hs _ ih => exact famObsEquiv_trans hW hΓ (famObsEquiv_of_stepR hL hdet hW hs) ih

/-- Constructor closure of `FamConvObsMotive` for `ConvT.beta` under `ReadbackLaws E R`, `DetR R`,
    and `EnvWfT E`. -/
theorem famConvObs_beta (hL : ReadbackLaws E R) (hdet : DetR R) (hW : EnvWfT E)
    {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A) :
    FamConvObsMotive R (.beta Γ A body arg B u hA hbody harg) :=
  famObsEquiv_of_stepR hL hdet hW (hL.beta Γ A body arg)

/-- **Saturated Admitted `.inductiveM` Family-Spine Congruence in `FamObsEquiv`
    (`famObsEquiv_famSpine_of_convArgsT`):**
    Under `ReadbackLaws E R` and `EnvWfT E` alone (zero `NormalUniqueR R` and zero `PiRowField`!),
    any two saturated well-typed admitted `.inductiveM` family spines related by `eqNList ls ls'`
    and `ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs'` satisfy `FamObsEquiv`. -/
theorem famObsEquiv_famSpine_of_convArgsT (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w w' : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (hty' : HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w'))
    (heqN : eqNList ls ls')
    (hlen : xs.length = (piDomsOf m.mtype).length)
    (hlen' : xs'.length = (piDomsOf m.mtype).length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs') :
    FamObsEquiv R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') := by
  obtain ⟨hlsl, hbel⟩ := NativeFamilyProjection.native_level_facts hm hty
  obtain ⟨_, hbel'⟩ := NativeFamilyProjection.native_level_facts hm hty'
  obtain ⟨hconv⟩ :=
    tyConvT_famApp_of_convArgsT hW hm hind hlsl hbel hbel' heqN hlen hargs
  have hargsSymm : ConvArgsT E n Γ (instantiateLevels ls' m.mtype) xs' xs :=
    convArgs_symm_instMtype_of_envWfT hW hΓ hm hind hty hty' heqN hargs
  refine ⟨⟨fun ⟨_, h⟩ => (TypedModelAudit.foldApps_const_ne_sort _ _ (redR_famApp_eq hL hW hm hind h).symm).elim,
    fun h _ => (TypedModelAudit.foldApps_const_ne_pi _ _ _ (redR_famApp_eq hL hW hm hind h).symm).elim,
    fun {r₀ m₀ ls₀ xs₀ w₀} hm₀ _ hM _ _ _ => ?_⟩,
    ⟨fun ⟨_, h⟩ => (TypedModelAudit.foldApps_const_ne_sort _ _ (redR_famApp_eq hL hW hm hind h).symm).elim,
    fun h _ => (TypedModelAudit.foldApps_const_ne_pi _ _ _ (redR_famApp_eq hL hW hm hind h).symm).elim,
    fun {r₀ m₀ ls₀ xs₀ w₀} hm₀ _ hN _ _ _ => ?_⟩⟩
  · have heq := redR_famApp_eq hL hW hm hind hM
    obtain ⟨hconst, hxs⟩ := foldApps_const_inj heq
    injection hconst with hr hls
    subst hr; subst hls; subst hxs
    have em : m₀ = m := Option.some.inj (hm₀.symm.trans hm)
    subst em
    exact ⟨ls', xs', w', .refl _, ⟨hty'⟩, ⟨hconv⟩, heqN, hlen', hargs⟩
  · have heq := redR_famApp_eq hL hW hm hind hN
    obtain ⟨hconst, hxs⟩ := foldApps_const_inj heq
    injection hconst with hr hls
    subst hr; subst hls; subst hxs
    have em : m₀ = m := Option.some.inj (hm₀.symm.trans hm)
    subst em
    exact ⟨ls, xs, w, .refl _, ⟨hty⟩, ⟨hconv.symmT⟩, eqNList_symm heqN, hlen, hargsSymm⟩

/-- Constructor closure of `FamConvObsMotive (WhStepRecKCanon E)` for `ConvT.zeta`. -/
theorem famConvObs_whStepRecKCanon_zeta (hW : EnvWfT E)
    {Γ : LCtx} {A v body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A)
    (hbody : HasTyT E n (.letBinding A v :: Γ) body B) :
    FamConvObsMotive (WhStepRecKCanon E) (.zeta Γ A v body B u hA hv hbody) :=
  famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW) hW
    (.zeta A v body)

/-- Constructor closure of `FamConvObsMotive (WhStepRecKCanon E)` for `ConvT.zetaLocal`. -/
theorem famConvObs_whStepRecKCanon_zetaLocal (hW : EnvWfT E)
    {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hlv : lookupValue Γ i = some v) (hlt : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A) :
    FamConvObsMotive (WhStepRecKCanon E) (.zetaLocal Γ i A v hlv hlt hv) :=
  famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW) hW
    (.zetaLocal hlv)

/-- Constructor closure of `FamConvObsMotive (WhStepRecKCanon E)` for `ConvT.delta`. -/
theorem famConvObs_whStepRecKCanon_delta (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)) :
    FamConvObsMotive (WhStepRecKCanon E) (.delta Γ r ls m b hres hbody htr hlen hwf hb) :=
  famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW) hW
    (.delta hres hbody)

/-- Observation equivalence in `FamObsEquiv (WhStepRecKCanon E)` for any `DerivedIotaU` step. -/
theorem famConvObs_whStepRecKCanon_iota (hW : EnvWfT E)
    {Γ : LCtx} {e rhs : Expr Nat} (hι : DerivedIotaU E e rhs) :
    FamObsEquiv (WhStepRecKCanon E) E n Γ e rhs :=
  famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW) hW
    (.iota hι)

/-- Constructor closure of `FamConvObsMotive (WhStepRecKCanon E)` for `ConvT.lit`. -/
theorem famConvObs_whStepRecKCanon_lit (hW : EnvWfT E)
    {Γ : LCtx} {t : Nat} {exp A : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : HasTyT E n Γ exp A) :
    FamConvObsMotive (WhStepRecKCanon E) (.lit Γ t exp A hlit hexp) := by
  cases hlit with
  | of =>
      exact famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW) hW
        (.lit t)

/-- Constructor closure of `FamConvObsMotive (WhStepRecKCanon E)` for `ConvT.lam` (both endpoints
    are weak-head normal `.lam` under `WhStepRecKCanon E`, so neither has a sort, Π, or family-spine
    readback). -/
theorem famConvObs_whStepRecKCanon_lam
    {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hb : ConvT E n (.assumption A :: Γ) b b' B) :
    FamConvObsMotive (WhStepRecKCanon E) (.lam Γ A A' b b' B u hA hb) := by
  have htr : ∀ (X Y : Expr Nat) (A₀ b₀ : Expr Nat),
      X = .lam A₀ b₀ → FamObsTransport (WhStepRecKCanon E) E n Γ X Y := by
    intro X Y A₀ b₀ hX
    subst hX
    refine ⟨fun ⟨_, h⟩ => ?_, fun h _ => ?_, fun _ _ h _ _ _ => ?_⟩
    · exact Expr.noConfusion (whRedRecKCanon_lam_eq (whRedRecKCanon_of_redR h))
    · exact Expr.noConfusion (whRedRecKCanon_lam_eq (whRedRecKCanon_of_redR h))
    · exact (foldApps_const_ne_lam _ (whRedRecKCanon_lam_eq (whRedRecKCanon_of_redR h))).elim
  exact ⟨htr _ _ A b rfl, htr _ _ A' b' rfl⟩

/-- Positive `W-K-OPEN` & `W-K-AND` verification in `FamObsEquiv (WhStepRecKCanon E)`:
    `trueVarSort`, `trueVarPi`, `trueVarFam`, and `mixAndRedex` all satisfy `FamObsEquiv`! -/
theorem famObsEquiv_whStepRecKCanon_trueVarSort (n : Nat) :
    FamObsEquiv (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx trueVarSort (.sort .zero) :=
  famObsEquiv_of_redR (readbackLaws_whStepRecKCanon trueEnvU) (detR_whStepRecKCanon trueEnvUWfT)
    trueEnvUWfT (trueVarCtx_wf n) (redR_of_whRedRecKCanon whRedRecKCanon_trueVarSort)

theorem famObsEquiv_whStepRecKCanon_trueVarPi (n : Nat) :
    FamObsEquiv (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarPi PiModelDeltaIotaAudit.idPiProp :=
  famObsEquiv_of_redR (readbackLaws_whStepRecKCanon trueEnvU) (detR_whStepRecKCanon trueEnvUWfT)
    trueEnvUWfT (trueVarCtx_wf n) (redR_of_whRedRecKCanon whRedRecKCanon_trueVarPi)

theorem famObsEquiv_whStepRecKCanon_trueVarFam (n : Nat) :
    FamObsEquiv (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx trueVarFam (.const 0 []) :=
  famObsEquiv_of_redR (readbackLaws_whStepRecKCanon trueEnvU) (detR_whStepRecKCanon trueEnvUWfT)
    trueEnvUWfT (trueVarCtx_wf n) (redR_of_whRedRecKCanon whRedRecKCanon_trueVarFam)

theorem famObsEquiv_whStepRecKCanon_mixAnd :
    FamObsEquiv (WhStepRecKCanon andEnvU) andEnvU 0 mixAndCtx mixAndRedex mixPi :=
  famObsEquiv_of_redR (readbackLaws_whStepRecKCanon andEnvU) (detR_whStepRecKCanon andEnvUWfT)
    andEnvUWfT Rcic.Domain.Model.PiInversion.mixAndCtx_wf
    (redR_of_whRedRecKCanon whRedRecKCanon_mixAndRedex)

theorem dt012_of_allBelowScoped_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlinks : FamObsConvLinks R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) :=
  DT012T_type_uniqueness_of_sortRow_piRow hW
    (sortRow_of_allBelowScoped_build hW hBel)
    (piRowField_of_famObsConvLinks hL hW hlinks) hΓ hA hB

theorem dt010_of_allBelowScoped_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlinks : FamObsConvLinks R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT010T_one_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_famObsConvLinks hL hW hBel hlinks) hΓ h hs

theorem dt011_of_allBelowScoped_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlinks : FamObsConvLinks R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Rcic.Declarative.Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  DT011T_multi_step_subject_reduction_rows hW
    (typedRowsWf_of_allBelowScoped_famObsConvLinks hL hW hBel hlinks) hΓ h hs

theorem dt019_of_allBelowScoped_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlinks : FamObsConvLinks R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) :=
  iotaPreserveT_rows hW
    (typedRowsWf_of_allBelowScoped_famObsConvLinks hL hW hBel hlinks) hΓ hd hlhs

theorem ia024_of_allBelowScoped_famObsConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlinks : FamObsConvLinks R E n) :
    IotaSRTN E n :=
  iotaSRTN_of_typedRowsWf hW
    (typedRowsWf_of_allBelowScoped_famObsConvLinks hL hW hBel hlinks)


/-! ### §9 — Part A: Whole-Spine `piTowerCpt` / `piTowerCptT` Alignment & All-Slot `W-FAMSPINE` Continuation Without Backward `ApproxT` Transport (Resolving `#7725` Audit Findings 1 & 2); Part B: Positive Resolution of `#7689` / `#7733`'s `eqEnvT` Convertible-Index K Obstruction (`eqCanonGapRedex`) and `pinLoopEnvT` Recursive-Singleton K Redex (`loopCanonRedex`) Under Deterministic `WhStepRecKCanon` -/

/-! #### §9 Part A — `piTowerCpt` / `piTowerCptT`, `TelescopeConvRel`, and Whole-Spine Alignment Without Backward `ApproxT` Transport -/

/-- Height-`k` `BotPiCpt` Π-tower compact over `CptI`:
    `piTowerCpt 0 = .pi .bot []`, `piTowerCpt (k + 1) = .pi .bot [([], piTowerCpt k)]`. -/
def piTowerCpt : Nat → CptI
  | 0 => .pi .bot []
  | k + 1 => .pi .bot [([], piTowerCpt k)]

/-- Height-`k` Π-tower compact over `CptT`:
    `piTowerCptT 0 = .pi .bot []`, `piTowerCptT (k + 1) = .pi .bot [([], piTowerCptT k)]`. -/
def piTowerCptT : Nat → CptT
  | 0 => .pi .bot []
  | k + 1 => .pi .bot [([], piTowerCptT k)]

/-- Every `piTowerCpt k` is a `BotPiCpt` compact (`RcicNativePiModelDeltaIota`). -/
theorem botPiCpt_piTowerCpt : ∀ k : Nat, BotPiCpt (piTowerCpt k)
  | 0 => botPiCpt_pi_bot_nil
  | k + 1 => botPiCpt_pi_nil_step .bot (botPiCpt_piTowerCpt k)

/-- Every `piTowerCpt k` is a `BotFamCpt E` compact. -/
theorem botFamCpt_piTowerCpt (E : ResolvedEnv) (k : Nat) : BotFamCpt E (piTowerCpt k) :=
  botFamCpt_of_botPiCpt (botPiCpt_piTowerCpt k)

/-- **Exact Equivalence Between `LRSCoreT` at `piTowerCptT k` and `LRSCore` at `piTowerCpt k`
    (`piTower_typed_iff`):**
    Because every domain compact in `piTowerCptT k` is `.bot` and every step demand list `s.1` is
    `[]` (making `∀ u ∈ s.1, CTyS E u .bot` and `∀ u ∈ s.1, LRSCore(T) ... u` vacuously true),
    `LRSCoreT R E n Γ M N A (piTowerCptT k)` is **logically equivalent** (`↔`) to
    `LRSCore R E n Γ M N A (piTowerCpt k)` for all `k : Nat`. -/
theorem piTower_typed_iff :
    ∀ (k : Nat) {Γ : LCtx} {M N A : Expr Nat},
      LRSCoreT R E n Γ M N A (piTowerCptT k) ↔ LRSCore R E n Γ M N A (piTowerCpt k)
  | 0, Γ, M, N, A => by
      simp only [piTowerCptT, piTowerCpt]
      rw [LRSCoreT.eq_def, LRSCore.eq_def]
      constructor
      · rintro ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod, _, _⟩
        exact ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod,
          ⟨.zero, lrSCore_bot _ _ _ _⟩,
          fun _ hs => (List.not_mem_nil _ hs).elim⟩
      · rintro ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod, _, _⟩
        exact ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod,
          ⟨.zero, lrSCoreT_bot _ _ _ _⟩,
          fun _ hs => (List.not_mem_nil _ hs).elim⟩
  | k + 1, Γ, M, N, A => by
      simp only [piTowerCptT, piTowerCpt]
      rw [LRSCoreT.eq_def, LRSCore.eq_def]
      constructor
      · rintro ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod, _, hrf⟩
        refine ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod,
          ⟨.zero, lrSCore_bot _ _ _ _⟩, ?_⟩
        intro s hs N₁ N₂ hN₁ hN₂ hcN _
        have es := List.mem_singleton.mp hs
        subst es
        obtain ⟨v, hv⟩ := hrf ([], piTowerCptT k) (List.mem_singleton.mpr rfl)
          (fun _ hu => (List.not_mem_nil _ hu).elim) N₁ N₂ hN₁ hN₂ hcN
          (fun _ hu => (List.not_mem_nil _ hu).elim)
        exact ⟨v, (piTower_typed_iff k).mp hv⟩
      · rintro ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod, _, hrf⟩
        refine ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod,
          ⟨.zero, lrSCoreT_bot _ _ _ _⟩, ?_⟩
        intro s hs _ N₁ N₂ hN₁ hN₂ hcN _
        have es := List.mem_singleton.mp hs
        subst es
        obtain ⟨v, hv⟩ := hrf ([], piTowerCpt k) (List.mem_singleton.mpr rfl)
          N₁ N₂ hN₁ hN₂ hcN (fun _ hu => (List.not_mem_nil _ hu).elim)
        exact ⟨v, (piTower_typed_iff k).mpr hv⟩

/-- Symmetry of `LRSCore` at `piTowerCpt k` from `EnvWfT E` and `CtxWfT E n Γ` alone (zero
    `PiRowField` or `ConvArgsSymmT`). -/
theorem piTower_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {k : Nat} {M N A : Expr Nat}
    (h : LRSCore R E n Γ M N A (piTowerCpt k)) :
    LRSCore R E n Γ N M A (piTowerCpt k) :=
  lrSCore_symm_botPiCpt hW hΓ (botPiCpt_piTowerCpt k) h

/-- Transitivity of `LRSCore` at `piTowerCpt k` from `ReadbackLaws E R`, `NormalUniqueR R`,
    `EnvWfT E`, and `CtxWfT E n Γ` alone. -/
theorem piTower_trans (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {k : Nat} {M N P A : Expr Nat}
    (h₁ : LRSCore R E n Γ M N A (piTowerCpt k))
    (h₂ : LRSCore R E n Γ N P A (piTowerCpt k)) :
    LRSCore R E n Γ M P A (piTowerCpt k) :=
  lrSCore_trans_botPiCpt hL hNU hW hΓ (botPiCpt_piTowerCpt k) h₁ h₂

/-- **Right-Diagonal Extraction at `piTowerCpt k` (`piTower_right_diagonal`):**
    Directly produces `LRSCore R E n Γ N N A (piTowerCpt k)` from
    `LRSCore R E n Γ M N A (piTowerCpt k)` via `piTower_symm` + `piTower_trans` — replacing the
    refuted backward `ApproxT` transport (`hinv : ReadbackModelInvT`) in `#7725`'s audit! -/
theorem piTower_right_diagonal (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {k : Nat} {M N A : Expr Nat}
    (h : LRSCore R E n Γ M N A (piTowerCpt k)) :
    LRSCore R E n Γ N N A (piTowerCpt k) :=
  piTower_trans hL hNU hW hΓ (piTower_symm hW hΓ h) h

/-- Symmetry of `LRSCoreT` at `piTowerCptT k` from `EnvWfT E` and `CtxWfT E n Γ` alone. -/
theorem piTower_symmT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {k : Nat} {M N A : Expr Nat}
    (h : LRSCoreT R E n Γ M N A (piTowerCptT k)) :
    LRSCoreT R E n Γ N M A (piTowerCptT k) :=
  (piTower_typed_iff k).mpr (piTower_symm hW hΓ ((piTower_typed_iff k).mp h))

/-- Transitivity of `LRSCoreT` at `piTowerCptT k` from `ReadbackLaws E R`, `NormalUniqueR R`,
    `EnvWfT E`, and `CtxWfT E n Γ` alone. -/
theorem piTower_transT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {k : Nat} {M N P A : Expr Nat}
    (h₁ : LRSCoreT R E n Γ M N A (piTowerCptT k))
    (h₂ : LRSCoreT R E n Γ N P A (piTowerCptT k)) :
    LRSCoreT R E n Γ M P A (piTowerCptT k) :=
  (piTower_typed_iff k).mpr
    (piTower_trans hL hNU hW hΓ ((piTower_typed_iff k).mp h₁) ((piTower_typed_iff k).mp h₂))

/-- Right-diagonal extraction for `LRSCoreT` at `piTowerCptT k`. -/
theorem piTower_right_diagonalT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {k : Nat} {M N A : Expr Nat}
    (h : LRSCoreT R E n Γ M N A (piTowerCptT k)) :
    LRSCoreT R E n Γ N N A (piTowerCptT k) :=
  piTower_transT hL hNU hW hΓ (piTower_symmT hW hΓ h) h

/-- Extract the top-level `.pi` readbacks and domain/codomain `TyConvT` from `LRSCore` at
    `piTowerCpt k` for any `k : Nat`. -/
theorem piTower_pi_read {Γ : LCtx} {k : Nat} {M N A : Expr Nat}
    (h : LRSCore R E n Γ M N A (piTowerCpt k)) :
    ∃ A₁ B₁ A₂ B₂ : Expr Nat,
      RedR R Γ M (.pi A₁ B₁) ∧ RedR R Γ N (.pi A₂ B₂) ∧
      Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
      Nonempty (TyConvT E n Γ A₁ A₂) ∧
      Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  cases k with
  | zero =>
      simp only [piTowerCpt] at h
      rw [LRSCore.eq_def] at h
      obtain ⟨_, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod, _, _⟩ := h
      exact ⟨A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod⟩
  | succ k =>
      simp only [piTowerCpt] at h
      rw [LRSCore.eq_def] at h
      obtain ⟨_, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod, _, _⟩ := h
      exact ⟨A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod⟩

/-- Extract `TyConvT E n Γ A₁ A₂` and `TyConvT E n (.assumption A₁ :: Γ) B₁ B₂` from
    `LRSCore R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCpt k)` at any `k : Nat`. -/
theorem piTower_pi_components (hL : ReadbackLaws E R) {Γ : LCtx} {k : Nat}
    {A₁ B₁ A₂ B₂ A : Expr Nat}
    (h : LRSCore R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCpt k)) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  obtain ⟨A₁', B₁', A₂', B₂', h1, h2, _, hdom, hcod⟩ := piTower_pi_read h
  have e₁ := redR_pi_eq hL h1
  have e₂ := redR_pi_eq hL h2
  injection e₁ with eA₁ eB₁
  injection e₂ with eA₂ eB₂
  subst eA₁; subst eB₁; subst eA₂; subst eB₂
  exact ⟨hdom, hcod⟩

/-- **Stepping Down `piTowerCpt (k + 1) → piTowerCpt k` Along Convertible Arguments
    (`piTower_step`):**
    Because `piTowerCpt (k + 1) = .pi .bot [([], piTowerCpt k)]` has empty argument demand list
    `[]`, applying the `.pi` clause to `x, y : A₁` with `ConvT E n Γ x y A₁` requires **zero**
    semantic relation on `x, y` and steps directly to
    `LRSCore R E n Γ (instantiate0 x B₁) (instantiate0 y B₂) (.sort v) (piTowerCpt k)`! -/
theorem piTower_step (hL : ReadbackLaws E R) {Γ : LCtx} {k : Nat}
    {A₁ B₁ A₂ B₂ x y A : Expr Nat}
    (h : LRSCore R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCpt (k + 1)))
    (hx : HasTyT E n Γ x A₁) (hy : HasTyT E n Γ y A₁)
    (hxy : ConvT E n Γ x y A₁) :
    ∃ v, LRSCore R E n Γ (instantiate0 x B₁) (instantiate0 y B₂) (.sort v) (piTowerCpt k) := by
  simp only [piTowerCpt] at h
  rw [LRSCore.eq_def] at h
  obtain ⟨_, A₁', B₁', A₂', B₂', h1, h2, _, _, _, _, hrf⟩ := h
  have e₁ := redR_pi_eq hL h1
  have e₂ := redR_pi_eq hL h2
  injection e₁ with eA₁ eB₁
  injection e₂ with eA₂ eB₂
  subst eA₁; subst eB₁; subst eA₂; subst eB₂
  exact hrf ([], piTowerCpt k) (List.mem_singleton.mpr rfl) x y hx hy ⟨hxy⟩
    (fun _ hu => (List.not_mem_nil _ hu).elim)

/-- Same-argument specialization of `piTower_step` (`y = x`, via `ConvT.refl Γ x A₁ hx`). -/
theorem piTower_step_same (hL : ReadbackLaws E R) {Γ : LCtx} {k : Nat}
    {A₁ B₁ A₂ B₂ x A : Expr Nat}
    (h : LRSCore R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCpt (k + 1)))
    (hx : HasTyT E n Γ x A₁) :
    ∃ v, LRSCore R E n Γ (instantiate0 x B₁) (instantiate0 x B₂) (.sort v) (piTowerCpt k) :=
  piTower_step hL h hx hx (.refl Γ x A₁ hx)

/-- `LRSCoreT` counterpart of `piTower_pi_components` at `piTowerCptT k`. -/
theorem piTower_pi_componentsT (hL : ReadbackLaws E R) {Γ : LCtx} {k : Nat}
    {A₁ B₁ A₂ B₂ A : Expr Nat}
    (h : LRSCoreT R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCptT k)) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :=
  piTower_pi_components hL ((piTower_typed_iff k).mp h)

/-- `LRSCoreT` counterpart of `piTower_step` at `piTowerCptT (k + 1) → piTowerCptT k`. -/
theorem piTower_stepT (hL : ReadbackLaws E R) {Γ : LCtx} {k : Nat}
    {A₁ B₁ A₂ B₂ x y A : Expr Nat}
    (h : LRSCoreT R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCptT (k + 1)))
    (hx : HasTyT E n Γ x A₁) (hy : HasTyT E n Γ y A₁)
    (hxy : ConvT E n Γ x y A₁) :
    ∃ v, LRSCoreT R E n Γ (instantiate0 x B₁) (instantiate0 y B₂) (.sort v) (piTowerCptT k) := by
  obtain ⟨v, hv⟩ := piTower_step hL ((piTower_typed_iff (k + 1)).mp h) hx hy hxy
  exact ⟨v, (piTower_typed_iff k).mpr hv⟩

/-- `LRSCoreT` counterpart of `piTower_step_same` at `piTowerCptT (k + 1) → piTowerCptT k`. -/
theorem piTower_step_sameT (hL : ReadbackLaws E R) {Γ : LCtx} {k : Nat}
    {A₁ B₁ A₂ B₂ x A : Expr Nat}
    (h : LRSCoreT R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCptT (k + 1)))
    (hx : HasTyT E n Γ x A₁) :
    ∃ v, LRSCoreT R E n Γ (instantiate0 x B₁) (instantiate0 x B₂) (.sort v) (piTowerCptT k) :=
  piTower_stepT hL h hx hx (.refl Γ x A₁ hx)

/-- Iterated tail instantiation along a telescope prefix `xs` and domain list `doms`. -/
def instTailPrefix : List (Expr Nat) → List (Expr Nat) → Expr Nat → Expr Nat
  | [], _, tail => tail
  | x :: xs, doms, tail =>
      match doms with
      | [] => tail
      | _ :: ds =>
          instTailPrefix xs (instDomsT 0 x ds)
            (instantiate (0 + ds.length) (lift 0 ds.length x) tail)

/-- General `instTelescope` on `policyPi doms tail` for any tail expression `tail : Expr Nat` and
    any prefix `xs.length ≤ doms.length`. -/
theorem instTelescope_policyPi :
    ∀ (xs doms : List (Expr Nat)) (tail : Expr Nat),
      xs.length ≤ doms.length →
      instTelescope (policyPi doms tail) xs =
        policyPi (instDomsPrefix xs doms) (instTailPrefix xs doms tail)
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => nomatch h
  | x :: xs, d :: doms, tail, h => by
      have hle : xs.length ≤ (instDomsT 0 x doms).length := by
        rw [length_instDomsT]
        exact Nat.le_of_succ_le_succ h
      simp only [policyPi, instTelescope_cons_pi, instantiate0,
        instantiate_policyPi, instDomsPrefix, instTailPrefix]
      exact instTelescope_policyPi xs (instDomsT 0 x doms)
        (instantiate (0 + doms.length) (lift 0 doms.length x) tail) hle

theorem instTelescope_policyPi_eq_of_length_eq (tail : Expr Nat)
    {xs doms : List (Expr Nat)} (hlen : xs.length = doms.length) :
    instTelescope (policyPi doms tail) xs = instTailPrefix xs doms tail := by
  rw [instTelescope_policyPi xs doms tail (Nat.le_of_eq hlen)]
  have hnil : instDomsPrefix xs doms = [] :=
    List.eq_nil_of_length_eq_zero (by rw [length_instDomsPrefix, hlen, Nat.sub_self])
  rw [hnil, policyPi]

theorem instTelescope_policyPi_eq_pi_of_lt (tail : Expr Nat)
    {xs doms : List (Expr Nat)} (hlt : xs.length < doms.length) :
    ∃ D B, instTelescope (policyPi doms tail) xs = .pi D B := by
  rw [instTelescope_policyPi xs doms tail (Nat.le_of_lt hlt)]
  have hpos : 0 < (instDomsPrefix xs doms).length := by
    rw [length_instDomsPrefix]; omega
  cases h : instDomsPrefix xs doms with
  | nil => rw [h] at hpos; exact (Nat.lt_irrefl 0 hpos).elim
  | cons D ds => exact ⟨D, policyPi ds (instTailPrefix xs doms tail), rfl⟩

/-- For **any** `CheckedMember` `m` and level list `ls`, if `xs.length < (piDomsOf m.mtype).length`
    then `instTelescope (instantiateLevels ls m.mtype) xs` is a syntactic `.pi D B`. -/
theorem instTelescope_member_eq_pi_of_lt (m : CheckedMember) (ls : List Level)
    {xs : List (Expr Nat)} (hlt : xs.length < (piDomsOf m.mtype).length) :
    ∃ D B, instTelescope (instantiateLevels ls m.mtype) xs = .pi D B := by
  rw [instantiateLevels_policyPi_piDomsOf_piTailOf ls m.mtype]
  exact instTelescope_policyPi_eq_pi_of_lt _ (by rw [List.length_map]; exact hlt)

/-- **Full Telescope Conversion Relation Including Tails (`TelescopeConvRel E n Γ ds₁ U₁ ds₂ U₂`):**
    Relates two telescopes `(ds₁, U₁)` and `(ds₂, U₂)` over `Γ` when `ds₁.length = ds₂.length`,
    every domain pair `(ds₁[i], ds₂[i])` is `ConvT`-convertible at a sort in the left prefix context
    `policyPrefixContext ds₁ i ++ Γ`, and the tails `U₁, U₂` are `ConvT`-convertible at a sort in
    `policyPrefixContext ds₁ ds₁.length ++ Γ`. -/
def TelescopeConvRel (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ds₁ : List (Expr Nat)) (U₁ : Expr Nat)
    (ds₂ : List (Expr Nat)) (U₂ : Expr Nat) : Prop :=
  ds₁.length = ds₂.length ∧
  (∀ i D₁ D₂, ds₁[i]? = some D₁ → ds₂[i]? = some D₂ →
    ∃ u, Nonempty (ConvT E n (policyPrefixContext ds₁ i ++ Γ) D₁ D₂ (.sort u))) ∧
  (∃ u, Nonempty (ConvT E n (policyPrefixContext ds₁ ds₁.length ++ Γ) U₁ U₂ (.sort u)))

/-- Extract the head domain conversion `ConvT E n Γ A₁ A₂ (.sort u₁)` from
    `TelescopeConvRel E n Γ (A₁ :: ds₁) U₁ (A₂ :: ds₂) U₂`. -/
theorem telescopeConvRel_head {Γ : LCtx} {A₁ A₂ U₁ U₂ : Expr Nat} {ds₁ ds₂ : List (Expr Nat)}
    (h : TelescopeConvRel E n Γ (A₁ :: ds₁) U₁ (A₂ :: ds₂) U₂) :
    ∃ u₁, Nonempty (ConvT E n Γ A₁ A₂ (.sort u₁)) :=
  h.2.1 0 A₁ A₂ (by simp) (by simp)

/-- Shift `TelescopeConvRel E n Γ (A₁ :: ds₁) U₁ (A₂ :: ds₂) U₂` into the extended context
    `.assumption A₁ :: Γ` on `(ds₁, U₁, ds₂, U₂)`. -/
theorem telescopeConvRel_cons_inv {Γ : LCtx} {A₁ A₂ U₁ U₂ : Expr Nat} {ds₁ ds₂ : List (Expr Nat)}
    (h : TelescopeConvRel E n Γ (A₁ :: ds₁) U₁ (A₂ :: ds₂) U₂) :
    TelescopeConvRel E n (.assumption A₁ :: Γ) ds₁ U₁ ds₂ U₂ := by
  refine ⟨Nat.succ.inj h.1, ?_, ?_⟩
  · intro i D₁ D₂ hD₁ hD₂
    obtain ⟨u, ⟨hc⟩⟩ := h.2.1 (i + 1) D₁ D₂ (by simp [hD₁]) (by simp [hD₂])
    rw [policyPrefixContext_cons_succ] at hc
    exact ⟨u, ⟨hc⟩⟩
  · obtain ⟨u, ⟨hc⟩⟩ := h.2.2
    change ConvT E n (policyPrefixContext (A₁ :: ds₁) (ds₁.length + 1) ++ Γ) U₁ U₂ (.sort u) at hc
    rw [policyPrefixContext_cons_succ] at hc
    exact ⟨u, ⟨hc⟩⟩

/-- Rebuild `ConvT E n Γ (policyPi ds₁ U₁) (policyPi ds₂ U₂) (.sort w)` from
    `TelescopeConvRel E n Γ ds₁ U₁ ds₂ U₂` by iterating `ConvT.pi` — with **zero** `PiRowField`! -/
theorem convT_policyPi_of_telescopeConvRel :
    ∀ {ds₁ ds₂ : List (Expr Nat)} {Γ : LCtx} {U₁ U₂ : Expr Nat},
      TelescopeConvRel E n Γ ds₁ U₁ ds₂ U₂ →
      ∃ w, Nonempty (ConvT E n Γ (policyPi ds₁ U₁) (policyPi ds₂ U₂) (.sort w))
  | [], ds₂, Γ, U₁, U₂, h => by
      have hnil : ds₂ = [] := List.eq_nil_of_length_eq_zero h.1.symm
      subst hnil
      simpa only [policyPi, List.length_nil, policyPrefixContext, List.take_zero,
        List.reverse_nil, List.map_nil, List.nil_append] using h.2.2
  | A₁ :: ds₁, [], _, _, _, h => nomatch h.1
  | A₁ :: ds₁, A₂ :: ds₂, Γ, U₁, U₂, h => by
      obtain ⟨u₁, ⟨hcA⟩⟩ := telescopeConvRel_head h
      obtain ⟨u₂, ⟨hcB⟩⟩ := convT_policyPi_of_telescopeConvRel (telescopeConvRel_cons_inv h)
      exact ⟨.imax u₁ u₂, ⟨.pi Γ A₁ A₂ (policyPi ds₁ U₁) (policyPi ds₂ U₂) u₁ u₂ hcA hcB⟩⟩

/-- Construct `CtxWfT E n (policyPrefixContext ds₁ j ++ Γ)` at every prefix `j ≤ ds₁.length` of
    `TelescopeConvRel E n Γ ds₁ U₁ ds₂ U₂`. -/
theorem ctxWfT_of_telescopeConvRel (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {ds₁ ds₂ : List (Expr Nat)} {U₁ U₂ : Expr Nat}
    (h : TelescopeConvRel E n Γ ds₁ U₁ ds₂ U₂) :
    ∀ (j : Nat), j ≤ ds₁.length → Nonempty (CtxWfT E n (policyPrefixContext ds₁ j ++ Γ))
  | 0, _ => ⟨by simpa only [policyPrefixContext, List.take_zero, List.reverse_nil,
      List.map_nil, List.nil_append] using hΓ⟩
  | j + 1, hj => by
      have hj₁ : j < ds₁.length := hj
      have hj₂ : j < ds₂.length := h.1 ▸ hj₁
      obtain ⟨hprev⟩ := ctxWfT_of_telescopeConvRel hW hΓ h j (Nat.le_of_lt hj₁)
      obtain ⟨u, ⟨hc⟩⟩ := h.2.1 j (ds₁[j]'hj₁) (ds₂[j]'hj₂)
        (List.getElem?_eq_getElem hj₁) (List.getElem?_eq_getElem hj₂)
      have hd : HasTyT E n (policyPrefixContext ds₁ j ++ Γ) (ds₁[j]'hj₁) (.sort u) :=
        (convEnds hW hprev hc).1
      rw [policyPrefixContext_succ ds₁ j hj₁, List.cons_append]
      exact ⟨.assumption _ _ u hprev hd⟩

/-- Two-leg substitution helper across `policyPrefixContext ds₁ j ++ (.assumption A₁ :: Γ)`:
    combines `convT_substS` (at `x`) and `hasTyT_subst_convS` (from `x` to `y` along
    `hxy : ConvT E n Γ x y A₁`) to transport `ConvT ... E₁ E₂ (.sort w)` to
    `ConvT ... (instantiate j (lift 0 j x) E₁) (instantiate j (lift 0 j y) E₂) (.sort w)`. -/
theorem convT_subst_prefix_assumption (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ x y E₁ E₂ : Expr Nat} {w : Level}
    (ds₁ : List (Expr Nat)) {j : Nat} (hj : j ≤ ds₁.length)
    (hΓ_pref : CtxWfT E n (policyPrefixContext ds₁ j ++ (.assumption A₁ :: Γ)))
    (hc : ConvT E n (policyPrefixContext ds₁ j ++ (.assumption A₁ :: Γ)) E₁ E₂ (.sort w))
    (hxy : ConvT E n Γ x y A₁) :
    Nonempty (ConvT E n (policyPrefixContext (instDomsT 0 x ds₁) j ++ Γ)
      (instantiate j (lift 0 j x) E₁) (instantiate j (lift 0 j y) E₂) (.sort w)) := by
  have hcl := envClosed_of_envWfT hW
  have hinst := envMembersSubstStable_of_envWfT hW
  have hx : HasTyT E n Γ x A₁ := (convEnds hW hΓ hxy).1
  have hE₂ : HasTyT E n (policyPrefixContext ds₁ j ++ (.assumption A₁ :: Γ)) E₂ (.sort w) :=
    (convEnds hW hΓ_pref hc).2.1
  have hhole := getElem?_policyPrefixContext_assumption ds₁ A₁ Γ j hj
  have hsub := substRemove_policyPrefixContext x Γ ds₁ A₁ j hj
  have hlen_inst : (policyPrefixContext (instDomsT 0 x ds₁) j).length = j :=
    policyPrefixContext_length (instDomsT 0 x ds₁) j (by rw [length_instDomsT]; exact hj)
  have hx_lift := hasTyTLiftPrefix hcl (policyPrefixContext (instDomsT 0 x ds₁) j) hx
  rw [hlen_inst, ← hsub] at hx_lift
  have hxy_lift := convTLiftPrefix hcl (policyPrefixContext (instDomsT 0 x ds₁) j) hxy
  rw [hlen_inst, ← hsub] at hxy_lift
  have hc_leg1 : ConvT E n (policyPrefixContext (instDomsT 0 x ds₁) j ++ Γ)
      (instantiate j (lift 0 j x) E₁) (instantiate j (lift 0 j x) E₂) (.sort w) := by
    have h0 := convT_substS hcl hinst x A₁ hc hhole hx_lift
    rwa [hsub] at h0
  have hc_leg2 : ConvT E n (policyPrefixContext (instDomsT 0 x ds₁) j ++ Γ)
      (instantiate j (lift 0 j x) E₂) (instantiate j (lift 0 j y) E₂) (.sort w) := by
    have h0 := hasTyT_subst_convS hcl hinst x y A₁ hE₂ hhole hx_lift hxy_lift
    rwa [hsub] at h0
  exact ⟨.trans _ _ _ _ _ hc_leg1 hc_leg2⟩

/-- **Stepping `TelescopeConvRel` Along `ConvT E n Γ x y A₁` Without `PiRowField`
    (`telescopeConvRel_step`):** -/
theorem telescopeConvRel_step (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ A₂ U₁ U₂ : Expr Nat} {ds₁ ds₂ : List (Expr Nat)}
    (hrel : TelescopeConvRel E n Γ (A₁ :: ds₁) U₁ (A₂ :: ds₂) U₂)
    {x y : Expr Nat} (hxy : ConvT E n Γ x y A₁) :
    TelescopeConvRel E n Γ
      (instDomsT 0 x ds₁) (instantiate (0 + ds₁.length) (lift 0 ds₁.length x) U₁)
      (instDomsT 0 y ds₂) (instantiate (0 + ds₂.length) (lift 0 ds₂.length y) U₂) := by
  obtain ⟨uA₁, ⟨hcA₁⟩⟩ := telescopeConvRel_head hrel
  have hA₁ : HasTyT E n Γ A₁ (.sort uA₁) := (convEnds hW hΓ hcA₁).1
  have hΓ_A₁ : CtxWfT E n (.assumption A₁ :: Γ) := .assumption Γ A₁ uA₁ hΓ hA₁
  have hshift := telescopeConvRel_cons_inv hrel
  have hlen₁₂ : ds₁.length = ds₂.length := hshift.1
  refine ⟨by rw [length_instDomsT, length_instDomsT, hlen₁₂], ?_, ?_⟩
  · intro j D₁' D₂' hD₁' hD₂'
    obtain ⟨hj_inst₁, hD₁_eq⟩ := List.getElem?_eq_some_iff.mp hD₁'
    obtain ⟨hj_inst₂, hD₂_eq⟩ := List.getElem?_eq_some_iff.mp hD₂'
    subst hD₁_eq; subst hD₂_eq
    have hj₁ : j < ds₁.length := by rw [← length_instDomsT 0 x ds₁]; exact hj_inst₁
    have hj₂ : j < ds₂.length := hlen₁₂ ▸ hj₁
    rw [getElem_instDomsT 0 x ds₁ j hj₁, getElem_instDomsT 0 y ds₂ j hj₂, Nat.zero_add]
    obtain ⟨w, ⟨hcj⟩⟩ := hshift.2.1 j (ds₁[j]'hj₁) (ds₂[j]'hj₂)
      (List.getElem?_eq_getElem hj₁) (List.getElem?_eq_getElem hj₂)
    obtain ⟨hΓ_pref⟩ := ctxWfT_of_telescopeConvRel hW hΓ_A₁ hshift j (Nat.le_of_lt hj₁)
    exact ⟨w, convT_subst_prefix_assumption hW hΓ ds₁ (Nat.le_of_lt hj₁) hΓ_pref hcj hxy⟩
  · obtain ⟨w, ⟨hcU⟩⟩ := hshift.2.2
    obtain ⟨hΓ_pref⟩ := ctxWfT_of_telescopeConvRel hW hΓ_A₁ hshift ds₁.length (Nat.le_refl _)
    have h0 := convT_subst_prefix_assumption hW hΓ ds₁ (Nat.le_refl _) hΓ_pref hcU hxy
    refine ⟨w, ?_⟩
    rwa [length_instDomsT, Nat.zero_add, Nat.zero_add, ← hlen₁₂]

/-- **Seeding `TelescopeConvRel` for Any Admitted Member `E.members r = some m`
    (`telescopeConvRel_of_levelFacts`):**
    Holds for **every** admitted `CheckedMember` `m` (`.inductiveM`, `.constructorM`, `.recursorM`,
    `.definitionM`, `.axiomM`, `.quotM`) under `EnvWfT E` alone! -/
theorem telescopeConvRel_of_levelFacts (hW : EnvWfT E) (Γ : LCtx)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls ls' : List Level}
    (hlsl : ls.length = m.arity) (hwfL : levelsBounded n ls = true)
    (_hlsl' : ls'.length = m.arity) (hwfR : levelsBounded n ls' = true)
    (heqN : eqNList ls ls') :
    TelescopeConvRel E n Γ
      ((piDomsOf m.mtype).map (instantiateLevels ls)) (instantiateLevels ls (piTailOf m.mtype))
      ((piDomsOf m.mtype).map (instantiateLevels ls')) (instantiateLevels ls' (piTailOf m.mtype)) := by
  obtain ⟨um, hmty⟩ := envWfT_mtypeSortTyped hW r m hm
  have hpol : m.mtype = policyPi (piDomsOf m.mtype) (piTailOf m.mtype) :=
    (policyPi_piDomsOf_piTailOf m.mtype).symm
  have hmtyPol : HasTyT E m.arity [] (policyPi (piDomsOf m.mtype) (piTailOf m.mtype)) (.sort um) :=
    hpol ▸ hmty
  obtain ⟨hdoms, u_tail, ⟨htail⟩⟩ := hasTyT_policyPi_inv (piDomsOf m.mtype) hmtyPol
  refine ⟨by simp, ?_, ?_⟩
  · intro i D₁ D₂ hD₁ hD₂
    rw [List.getElem?_map] at hD₁ hD₂
    cases hdi : (piDomsOf m.mtype)[i]? with
    | none => rw [hdi] at hD₁; cases hD₁
    | some d =>
        rw [hdi] at hD₁ hD₂
        injection hD₁ with e₁
        injection hD₂ with e₂
        subst e₁; subst e₂
        obtain ⟨hi, hd_eq⟩ := List.getElem?_eq_some_iff.mp hdi
        subst hd_eq
        obtain ⟨u₀, ⟨hdTy⟩⟩ := hdoms i hi
        have hc1 := convT_instantiateLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW)
          heqN hwfL hwfR hlsl hdTy
        rw [List.append_nil, instLvlsCtx_policyPrefixContext] at hc1
        exact ⟨instLevel ls u₀, ⟨convT_relocateN (Γ := Γ) hc1⟩⟩
  · have hc1 := convT_instantiateLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW)
      heqN hwfL hwfR hlsl htail
    rw [List.append_nil, instLvlsCtx_policyPrefixContext] at hc1
    have hc2 := convT_relocateN (Γ := Γ) hc1
    simpa only [List.length_map] using ⟨instLevel ls u_tail, ⟨hc2⟩⟩

/-- **Inhabiting `LRSCore` at `piTowerCpt k` for Any `TelescopeConvRel` Pair
    (`lrSCore_piTowerCpt_of_telescopeConvRel`):**
    For any `k` with `k + 1 ≤ ds₁.length`, `TelescopeConvRel E n Γ ds₁ U₁ ds₂ U₂` inhabits
    `LRSCore R E n Γ (policyPi ds₁ U₁) (policyPi ds₂ U₂) (.sort u) (piTowerCpt k)` under `EnvWfT E`
    and `CtxWfT E n Γ` **alone** (for **every** `R : Readback`)! -/
theorem lrSCore_piTowerCpt_of_telescopeConvRel (hW : EnvWfT E) :
    ∀ (k : Nat) {Γ : LCtx}, CtxWfT E n Γ →
      ∀ {ds₁ ds₂ : List (Expr Nat)} {U₁ U₂ : Expr Nat} (u : Level),
        TelescopeConvRel E n Γ ds₁ U₁ ds₂ U₂ →
        k + 1 ≤ ds₁.length →
        LRSCore R E n Γ (policyPi ds₁ U₁) (policyPi ds₂ U₂) (.sort u) (piTowerCpt k)
  | 0, Γ, hΓ, ds₁, ds₂, U₁, U₂, u, hrel, hle => by
      cases ds₁ with
      | nil => nomatch hle
      | cons A₁ ds₁ =>
          cases ds₂ with
          | nil => nomatch hrel.1
          | cons A₂ ds₂ =>
              simp only [piTowerCpt, policyPi]
              rw [LRSCore.eq_def]
              obtain ⟨u₁, ⟨hcA⟩⟩ := telescopeConvRel_head hrel
              have hA₁ : HasTyT E n Γ A₁ (.sort u₁) := (convEnds hW hΓ hcA).1
              obtain ⟨u₂, ⟨hcB⟩⟩ := convT_policyPi_of_telescopeConvRel (telescopeConvRel_cons_inv hrel)
              exact ⟨⟨u, .refl _⟩, A₁, policyPi ds₁ U₁, A₂, policyPi ds₂ U₂,
                .refl _, .refl _, ⟨.assumption Γ A₁ u₁ hΓ hA₁⟩,
                ⟨.of Γ A₁ A₂ u₁ hcA⟩, ⟨.of (.assumption A₁ :: Γ) _ _ u₂ hcB⟩,
                ⟨.zero, lrSCore_bot _ _ _ _⟩,
                fun _ hs => (List.not_mem_nil _ hs).elim⟩
  | k + 1, Γ, hΓ, ds₁, ds₂, U₁, U₂, u, hrel, hle => by
      cases ds₁ with
      | nil => nomatch hle
      | cons A₁ ds₁ =>
          cases ds₂ with
          | nil => nomatch hrel.1
          | cons A₂ ds₂ =>
              simp only [piTowerCpt, policyPi]
              rw [LRSCore.eq_def]
              obtain ⟨u₁, ⟨hcA⟩⟩ := telescopeConvRel_head hrel
              have hA₁ : HasTyT E n Γ A₁ (.sort u₁) := (convEnds hW hΓ hcA).1
              obtain ⟨u₂, ⟨hcB⟩⟩ := convT_policyPi_of_telescopeConvRel (telescopeConvRel_cons_inv hrel)
              refine ⟨⟨u, .refl _⟩, A₁, policyPi ds₁ U₁, A₂, policyPi ds₂ U₂,
                .refl _, .refl _, ⟨.assumption Γ A₁ u₁ hΓ hA₁⟩,
                ⟨.of Γ A₁ A₂ u₁ hcA⟩, ⟨.of (.assumption A₁ :: Γ) _ _ u₂ hcB⟩,
                ⟨.zero, lrSCore_bot _ _ _ _⟩, ?_⟩
              intro s hs N N' _ _ hcN _
              have es := List.mem_singleton.mp hs
              subst es
              obtain ⟨hcN⟩ := hcN
              have hstep := telescopeConvRel_step hW hΓ hrel hcN
              have hle' : k + 1 ≤ (instDomsT 0 N ds₁).length := by
                rw [length_instDomsT]
                exact Nat.le_of_succ_le_succ hle
              have ih := lrSCore_piTowerCpt_of_telescopeConvRel hW k hΓ .zero hstep hle'
              simp only [instantiate0, instantiate_policyPi]
              exact ⟨.zero, ih⟩

/-- `LRSCoreT` counterpart of `lrSCore_piTowerCpt_of_telescopeConvRel` at `piTowerCptT k`. -/
theorem lrSCoreT_piTowerCptT_of_telescopeConvRel (hW : EnvWfT E) (k : Nat)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {ds₁ ds₂ : List (Expr Nat)} {U₁ U₂ : Expr Nat} (u : Level)
    (hrel : TelescopeConvRel E n Γ ds₁ U₁ ds₂ U₂) (hle : k + 1 ≤ ds₁.length) :
    LRSCoreT R E n Γ (policyPi ds₁ U₁) (policyPi ds₂ U₂) (.sort u) (piTowerCptT k) :=
  (piTower_typed_iff k).mpr (lrSCore_piTowerCpt_of_telescopeConvRel hW k hΓ u hrel hle)

/-- **Seeding `LRSCore` at `piTowerCpt k` for Any Admitted Member's Declared Type
    (`lrSCore_piTowerCpt_member_of_levelFacts`):**
    For any member `E.members r = some m`, level lists `ls, ls'` with `eqNList ls ls'`, and
    `k + 1 ≤ (piDomsOf m.mtype).length`, inhabits
    `LRSCore R E n Γ (instantiateLevels ls m.mtype) (instantiateLevels ls' m.mtype) (.sort u) (piTowerCpt k)`
    under `EnvWfT E` and `CtxWfT E n Γ` alone! -/
theorem lrSCore_piTowerCpt_member_of_levelFacts (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls ls' : List Level}
    (hlsl : ls.length = m.arity) (hwfL : levelsBounded n ls = true)
    (hlsl' : ls'.length = m.arity) (hwfR : levelsBounded n ls' = true)
    (heqN : eqNList ls ls') {k : Nat} (hle : k + 1 ≤ (piDomsOf m.mtype).length) (u : Level) :
    LRSCore R E n Γ (instantiateLevels ls m.mtype) (instantiateLevels ls' m.mtype)
      (.sort u) (piTowerCpt k) := by
  rw [instantiateLevels_policyPi_piDomsOf_piTailOf ls m.mtype,
      instantiateLevels_policyPi_piDomsOf_piTailOf ls' m.mtype]
  exact lrSCore_piTowerCpt_of_telescopeConvRel hW k hΓ u
    (telescopeConvRel_of_levelFacts hW Γ hm hlsl hwfL hlsl' hwfR heqN)
    (by rw [List.length_map]; exact hle)

/-- Diagonal specialization (`ls' = ls`) of `lrSCore_piTowerCpt_member_of_levelFacts`. -/
theorem lrSCore_piTowerCpt_instMtype_diag (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls : List Level} (hlsl : ls.length = m.arity) (hwfL : levelsBounded n ls = true)
    {k : Nat} (hle : k + 1 ≤ (piDomsOf m.mtype).length) (u : Level) :
    LRSCore R E n Γ (instantiateLevels ls m.mtype) (instantiateLevels ls m.mtype)
      (.sort u) (piTowerCpt k) :=
  lrSCore_piTowerCpt_member_of_levelFacts hW hΓ hm hlsl hwfL hlsl hwfL (eqNList_refl ls) hle u

/-- `LRSCoreT` counterpart of `lrSCore_piTowerCpt_instMtype_diag` at `piTowerCptT k`. -/
theorem lrSCoreT_piTowerCptT_instMtype_diag (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls : List Level} (hlsl : ls.length = m.arity) (hwfL : levelsBounded n ls = true)
    {k : Nat} (hle : k + 1 ≤ (piDomsOf m.mtype).length) (u : Level) :
    LRSCoreT R E n Γ (instantiateLevels ls m.mtype) (instantiateLevels ls m.mtype)
      (.sort u) (piTowerCptT k) :=
  (piTower_typed_iff k).mpr (lrSCore_piTowerCpt_instMtype_diag hW hΓ hm hlsl hwfL hle u)

/-- Size-bounded chain of original `ConvT E n Γ A B (.sort u)` steps (`sizeOf hc < bound`),
    extracted directly from `HasTyT.conv` steps without synthesizing `TyConvT.trans` nodes. -/
inductive FamConvChainBelow (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (bound : Nat) :
    Expr Nat → Expr Nat → Prop
  | refl (A : Expr Nat) : FamConvChainBelow E n Γ bound A A
  | step {A B C : Expr Nat} {u : Level}
      (hc : ConvT E n Γ A B (.sort u)) (hsz : sizeOf hc < bound)
      (hrest : FamConvChainBelow E n Γ bound B C) :
      FamConvChainBelow E n Γ bound A C

theorem FamConvChainBelow.mono {Γ : LCtx} {b₁ b₂ : Nat} (hb : b₁ ≤ b₂)
    {A B : Expr Nat} (h : FamConvChainBelow E n Γ b₁ A B) :
    FamConvChainBelow E n Γ b₂ A B := by
  induction h with
  | refl A => exact .refl A
  | step hc hsz _ ih => exact .step hc (Nat.lt_of_lt_of_le hsz hb) ih

theorem FamConvChainBelow.append {Γ : LCtx} {bound : Nat} {A B C : Expr Nat}
    (h₁ : FamConvChainBelow E n Γ bound A B)
    (h₂ : FamConvChainBelow E n Γ bound B C) :
    FamConvChainBelow E n Γ bound A C := by
  induction h₁ with
  | refl _ => exact h₂
  | step hc hsz _ ih => exact .step hc hsz (ih h₂)

/-- Peel the `HasTyT.conv` wrapper chain from `d : HasTyT E n Γ (.const r ls) T`. -/
theorem famConvChainBelow_const {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) {ls : List Level} :
    ∀ {Γ : LCtx} {T : Expr Nat} (d : HasTyT E n Γ (.const r ls) T),
      FamConvChainBelow E n Γ (sizeOf d) (instantiateLevels ls m.mtype) T
  | _, _, .const _ _ _ m' hm' _ _ => by
      have em : m = m' := Option.some.inj (hm.symm.trans hm')
      subst em
      exact .refl _
  | _, _, .conv Γ₀ _ A B u d₀ hc => by
      have h0 : FamConvChainBelow E n Γ₀ (sizeOf (HasTyT.conv Γ₀ (.const r ls) A B u d₀ hc))
          (instantiateLevels ls m.mtype) A :=
        (famConvChainBelow_const hm d₀).mono (by simp_wf; omega)
      exact h0.append (.step hc (by simp_wf; omega) (.refl B))

/-- Peel the `HasTyT.conv` wrapper chain from `d : HasTyT E n Γ (.app f a) T`, returning the strict
    sub-derivation `df : HasTyT E n Γ f (.pi A B)` (`sizeOf df < sizeOf d`), the argument typing
    `Nonempty (HasTyT E n Γ a A)`, and the `FamConvChainBelow` chain from `instantiate0 a B` to `T`. -/
theorem famConvChainBelow_app {f a : Expr Nat} :
    ∀ {Γ : LCtx} {T : Expr Nat} (d : HasTyT E n Γ (.app f a) T),
      ∃ (A B : Expr Nat) (df : HasTyT E n Γ f (.pi A B)),
        sizeOf df < sizeOf d ∧
        Nonempty (HasTyT E n Γ a A) ∧
        FamConvChainBelow E n Γ (sizeOf d) (instantiate0 a B) T
  | _, _, .app _ _ _ A B df da =>
      ⟨A, B, df, by simp_wf; omega, ⟨da⟩, .refl (instantiate0 a B)⟩
  | _, _, .conv Γ₀ _ A' B' u d₀ hc => by
      obtain ⟨A, B, df, hsz, ha, hchain⟩ := famConvChainBelow_app d₀
      have hsz' : sizeOf df < sizeOf (HasTyT.conv Γ₀ (.app f a) A' B' u d₀ hc) :=
        Nat.lt_trans hsz (by simp_wf; omega)
      have h0 : FamConvChainBelow E n Γ₀ (sizeOf (HasTyT.conv Γ₀ (.app f a) A' B' u d₀ hc))
          (instantiate0 a B) A' :=
        hchain.mono (by simp_wf; omega)
      exact ⟨A, B, df, hsz', ha, h0.append (.step hc (by simp_wf; omega) (.refl B'))⟩

/-- **Diagonal-Seeded Single-Link Hypothesis on `piTowerCpt k` Below `bound`
    (`PiTowerLinkBelow R E n bound`):**
    States that for any single `hc : ConvT E n Γ A B (.sort u)` with `sizeOf hc < bound`, if `A` is
    already on the `piTowerCpt k` diagonal (`LRSCore R E n Γ A A (.sort u) (piTowerCpt k)`), then
    `LRSCore R E n Γ A B (.sort u) (piTowerCpt k)` holds.
    Requires **zero** `ApproxT` / `ApproxDI` hypothesis and **zero** `ReadbackModelInvT` (`hinv`)! -/
def PiTowerLinkBelow (R : Readback) (E : ResolvedEnv) (n : Nat) (bound : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A B : Expr Nat} {u : Level} (hc : ConvT E n Γ A B (.sort u)),
      sizeOf hc < bound →
      ∀ {k : Nat},
        LRSCore R E n Γ A A (.sort u) (piTowerCpt k) →
        LRSCore R E n Γ A B (.sort u) (piTowerCpt k)

/-- `LRSCoreT` counterpart of `PiTowerLinkBelow` at `piTowerCptT k`. -/
def PiTowerLinkBelowT (R : Readback) (E : ResolvedEnv) (n : Nat) (bound : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A B : Expr Nat} {u : Level} (hc : ConvT E n Γ A B (.sort u)),
      sizeOf hc < bound →
      ∀ {k : Nat},
        LRSCoreT R E n Γ A A (.sort u) (piTowerCptT k) →
        LRSCoreT R E n Γ A B (.sort u) (piTowerCptT k)

/-- `PiTowerLinkBelowT R E n bound` is logically equivalent (`↔`) to `PiTowerLinkBelow R E n bound`. -/
theorem piTowerLinkBelow_iff_typed {bound : Nat} :
    PiTowerLinkBelowT R E n bound ↔ PiTowerLinkBelow R E n bound := by
  constructor
  · intro hT Γ hΓ A B u hc hsz k hAA
    exact (piTower_typed_iff k).mp (hT hΓ hc hsz ((piTower_typed_iff k).mpr hAA))
  · intro hI Γ hΓ A B u hc hsz k hAA
    exact (piTower_typed_iff k).mpr (hI hΓ hc hsz ((piTower_typed_iff k).mp hAA))

theorem PiTowerLinkBelow.mono {b₁ b₂ : Nat} (hb : b₁ ≤ b₂)
    (h : PiTowerLinkBelow R E n b₂) : PiTowerLinkBelow R E n b₁ := by
  intro Γ hΓ A B u hc hsz k hAA
  exact h hΓ hc (Nat.lt_of_lt_of_le hsz hb) hAA

theorem PiTowerLinkBelowT.mono {b₁ b₂ : Nat} (hb : b₁ ≤ b₂)
    (h : PiTowerLinkBelowT R E n b₂) : PiTowerLinkBelowT R E n b₁ := by
  intro Γ hΓ A B u hc hsz k hAA
  exact h hΓ hc (Nat.lt_of_lt_of_le hsz hb) hAA

/-- **Walking Any `FamConvChainBelow` Chain at `piTowerCpt k` Without Backward `ApproxT` Transport
    (`piTower_chain`):**
    Directly resolves `#7725` Audit Finding 1 ("The backward-transport hypothesis has no witness"):
    instead of pulling `piTowerCptT k` back along `RedR R Γ B (.pi ...)` into `ApproxT` using the
    refuted `ReadbackModelInvT`, `piTower_right_diagonal` extracts the middle diagonal
    `LRSCore R E n Γ B B (.sort u') (piTowerCpt k)` directly from `hAB` via `piTower_symm` +
    `piTower_trans`! -/
theorem piTower_chain (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {bound : Nat}
    (hlink : PiTowerLinkBelow R E n bound)
    {A B : Expr Nat} (hchain : FamConvChainBelow E n Γ bound A B)
    {k : Nat} {u : Level}
    (hAA : LRSCore R E n Γ A A (.sort u) (piTowerCpt k)) :
    LRSCore R E n Γ A B (.sort u) (piTowerCpt k) := by
  induction hchain generalizing u with
  | refl _ => exact hAA
  | @step A₀ B₀ C₀ u' hc hsz _ ih =>
      have hAA' : LRSCore R E n Γ A₀ A₀ (.sort u') (piTowerCpt k) :=
        lrSCore_sort_index_irrel hL (piTowerCpt k) hAA
      have hAB' : LRSCore R E n Γ A₀ B₀ (.sort u') (piTowerCpt k) :=
        hlink hΓ hc hsz hAA'
      have hBB' : LRSCore R E n Γ B₀ B₀ (.sort u') (piTowerCpt k) :=
        piTower_right_diagonal hL hNU hW hΓ hAB'
      have hBC' : LRSCore R E n Γ B₀ C₀ (.sort u') (piTowerCpt k) :=
        ih hBB'
      exact lrSCore_sort_index_irrel hL (piTowerCpt k)
        (piTower_trans hL hNU hW hΓ hAB' hBC')

/-- `LRSCoreT` counterpart of `piTower_chain` at `piTowerCptT k`. -/
theorem piTower_chainT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {bound : Nat}
    (hlink : PiTowerLinkBelowT R E n bound)
    {A B : Expr Nat} (hchain : FamConvChainBelow E n Γ bound A B)
    {k : Nat} {u : Level}
    (hAA : LRSCoreT R E n Γ A A (.sort u) (piTowerCptT k)) :
    LRSCoreT R E n Γ A B (.sort u) (piTowerCptT k) :=
  (piTower_typed_iff k).mpr
    (piTower_chain hL hNU hW hΓ (piTowerLinkBelow_iff_typed.mp hlink) hchain
      ((piTower_typed_iff k).mp hAA))

/-- **Whole-Spine `piTowerCpt` Alignment Across All Prefix Lengths `xs` and Remaining Heights `k`
    (`wholeSpine_piTower_of_links`):**
    Directly resolves `#7725` Audit Finding 1 and Finding 2 ("Missing later-slot continuation"):
    for **any** admitted member `E.members r = some m`, **any** prefix `xs : List (Expr Nat)` and
    tower height `k : Nat` with `xs.length + k < (piDomsOf m.mtype).length`, and **any** typing
    derivation `d : HasTyT E n Γ (foldApps (.const r ls) xs) T`, relates the instantiated declared
    telescope `instTelescope (instantiateLevels ls m.mtype) xs` to `T` at `piTowerCpt k` using ONLY
    `PiTowerLinkBelow R E n (sizeOf d)` — with **zero** `ReadbackModelInvT`, **zero** `ApproxT`, and
    **zero** `PiRowField`! -/
theorem wholeSpine_piTower_of_links (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (ls : List Level)
    (xs : List (Expr Nat)) :
    ∀ {T : Expr Nat} (d : HasTyT E n Γ (foldApps (.const r ls) xs) T) {k : Nat},
      xs.length + k < (piDomsOf m.mtype).length →
      PiTowerLinkBelow R E n (sizeOf d) →
      ∃ u, LRSCore R E n Γ (instTelescope (instantiateLevels ls m.mtype) xs) T
        (.sort u) (piTowerCpt k) := by
  suffices hmain : ∀ (len : Nat) (xs : List (Expr Nat)), xs.length = len →
      ∀ {T : Expr Nat} (d : HasTyT E n Γ (foldApps (.const r ls) xs) T) {k : Nat},
        xs.length + k < (piDomsOf m.mtype).length →
        PiTowerLinkBelow R E n (sizeOf d) →
        ∃ u, LRSCore R E n Γ (instTelescope (instantiateLevels ls m.mtype) xs) T
          (.sort u) (piTowerCpt k) by
    intro T d k hlt hlink
    exact hmain xs.length xs rfl d hlt hlink
  intro len
  induction len with
  | zero =>
      intro xs hlen T d k hlt hlink
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hnil
      obtain ⟨hlsl, hwfL⟩ := NativeFamilyProjection.native_level_facts hm d
      have hle : k + 1 ≤ (piDomsOf m.mtype).length := by simp at hlt; omega
      have hseed := lrSCore_piTowerCpt_instMtype_diag (R := R) hW hΓ hm hlsl hwfL hle .zero
      have hchain := famConvChainBelow_const hm d
      exact ⟨.zero, piTower_chain hL hNU hW hΓ hlink hchain hseed⟩
  | succ m_len ih =>
      intro xs hlen T
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, a, rfl⟩
      · contradiction
      · have hpre_len : pre.length = m_len := by
          rw [List.length_append, List.length_singleton] at hlen
          omega
        rw [foldApps_snoc]
        intro d k hlt hlink
        obtain ⟨A, B, df, hsz, ⟨ha⟩, hchain⟩ := famConvChainBelow_app d
        have hlt_pre : pre.length + (k + 1) < (piDomsOf m.mtype).length := by
          rw [List.length_append, List.length_singleton] at hlt
          omega
        have hlink_pre : PiTowerLinkBelow R E n (sizeOf df) :=
          hlink.mono (Nat.le_of_lt hsz)
        obtain ⟨u₀, hLR_pre⟩ := ih pre hpre_len df hlt_pre hlink_pre
        have hpre_lt : pre.length < (piDomsOf m.mtype).length := by omega
        obtain ⟨D, B₀, hpi⟩ := instTelescope_member_eq_pi_of_lt m ls hpre_lt
        have hsnoc : instTelescope (instantiateLevels ls m.mtype) (pre ++ [a]) = instantiate0 a B₀ :=
          instTelescope_snoc_of_pi hpi a
        rw [hpi] at hLR_pre
        obtain ⟨⟨hDA⟩, _⟩ := piTower_pi_components hL hLR_pre
        have haD : HasTyT E n Γ a D := hasTyT_of_tyConvT ha hDA.symmT
        obtain ⟨v, hstep⟩ := piTower_step_same hL hLR_pre haD
        have hdiag_aB : LRSCore R E n Γ (instantiate0 a B) (instantiate0 a B) (.sort v) (piTowerCpt k) :=
          piTower_right_diagonal hL hNU hW hΓ hstep
        have hconv_T : LRSCore R E n Γ (instantiate0 a B) T (.sort v) (piTowerCpt k) :=
          piTower_chain hL hNU hW hΓ hlink hchain hdiag_aB
        rw [hsnoc]
        exact ⟨v, piTower_trans hL hNU hW hΓ hstep hconv_T⟩

/-- `LRSCoreT` counterpart of `wholeSpine_piTower_of_links` at `piTowerCptT k`. -/
theorem wholeSpine_piTower_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (ls : List Level)
    (xs : List (Expr Nat)) {T : Expr Nat}
    (d : HasTyT E n Γ (foldApps (.const r ls) xs) T) {k : Nat}
    (hlt : xs.length + k < (piDomsOf m.mtype).length)
    (hlink : PiTowerLinkBelowT R E n (sizeOf d)) :
    ∃ u, LRSCoreT R E n Γ (instTelescope (instantiateLevels ls m.mtype) xs) T
      (.sort u) (piTowerCptT k) := by
  obtain ⟨u, h⟩ := wholeSpine_piTower_of_links hL hNU hW hΓ hm ls xs d hlt
    (piTowerLinkBelow_iff_typed.mp hlink)
  exact ⟨u, (piTower_typed_iff k).mpr h⟩

/-- **All-Slot Node-to-Declared Domain Alignment (`wholeSpine_nodeDeclAlign_of_links`):**
    At any prefix `pre` with `pre.length < (piDomsOf m.mtype).length` and any sub-derivation
    `df : HasTyT E n Γ (foldApps (.const r ls) pre) (.pi A B)`, extracts the declared slot domain `D`
    and codomain `B₀` (`instTelescope (instantiateLevels ls m.mtype) pre = .pi D B₀`) together with
    `TyConvT E n Γ D A` and `TyConvT E n (.assumption D :: Γ) B₀ B` from
    `PiTowerLinkBelow R E n (sizeOf df)` alone! -/
theorem wholeSpine_nodeDeclAlign_of_links (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (ls : List Level)
    {pre : List (Expr Nat)} {A B : Expr Nat}
    (df : HasTyT E n Γ (foldApps (.const r ls) pre) (.pi A B))
    (hlt : pre.length < (piDomsOf m.mtype).length)
    (hlink : PiTowerLinkBelow R E n (sizeOf df)) :
    ∃ D B₀,
      instTelescope (instantiateLevels ls m.mtype) pre = .pi D B₀ ∧
      Nonempty (TyConvT E n Γ D A) ∧
      Nonempty (TyConvT E n (.assumption D :: Γ) B₀ B) := by
  obtain ⟨D, B₀, hpi⟩ := instTelescope_member_eq_pi_of_lt m ls hlt
  obtain ⟨_, hLR⟩ := wholeSpine_piTower_of_links hL hNU hW hΓ hm ls pre df (k := 0)
    (by omega) hlink
  rw [hpi] at hLR
  obtain ⟨hDA, hBB⟩ := piTower_pi_components hL hLR
  exact ⟨D, B₀, hpi, hDA, hBB⟩

/-- `LRSCoreT` counterpart of `wholeSpine_nodeDeclAlign_of_links`. -/
theorem wholeSpine_nodeDeclAlign_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (ls : List Level)
    {pre : List (Expr Nat)} {A B : Expr Nat}
    (df : HasTyT E n Γ (foldApps (.const r ls) pre) (.pi A B))
    (hlt : pre.length < (piDomsOf m.mtype).length)
    (hlink : PiTowerLinkBelowT R E n (sizeOf df)) :
    ∃ D B₀,
      instTelescope (instantiateLevels ls m.mtype) pre = .pi D B₀ ∧
      Nonempty (TyConvT E n Γ D A) ∧
      Nonempty (TyConvT E n (.assumption D :: Γ) B₀ B) :=
  wholeSpine_nodeDeclAlign_of_links hL hNU hW hΓ hm ls df hlt
    (piTowerLinkBelow_iff_typed.mp hlink)

/-- **Snoc-Step `ConvArgsT` Extension at Any Slot `pre.length < (piDomsOf m.mtype).length`
    (`wholeSpine_convArgsT_snoc_of_links`):**
    Given `ConvArgsT E n Γ (instantiateLevels ls m.mtype) pre pre'`, a typing derivation
    `df : HasTyT E n Γ (foldApps (.const r ls) pre) (.pi A B)`, and `hab : ConvT E n Γ a b A` at the
    application node's own domain `A`, aligns `A` with the declared instantiated domain `D` via
    `wholeSpine_nodeDeclAlign_of_links` and appends `(a, b)` via `convArgsT_snoc`! -/
theorem wholeSpine_convArgsT_snoc_of_links (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (ls : List Level)
    {pre pre' : List (Expr Nat)} {A B a b : Expr Nat}
    (df : HasTyT E n Γ (foldApps (.const r ls) pre) (.pi A B))
    (hlt : pre.length < (piDomsOf m.mtype).length)
    (hlink : PiTowerLinkBelow R E n (sizeOf df))
    (hpre : ConvArgsT E n Γ (instantiateLevels ls m.mtype) pre pre')
    (hab : ConvT E n Γ a b A) :
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) (pre ++ [a]) (pre' ++ [b]) := by
  obtain ⟨D, B₀, hpi, ⟨hDA⟩, _⟩ :=
    wholeSpine_nodeDeclAlign_of_links hL hNU hW hΓ hm ls df hlt hlink
  exact convArgsT_snoc hpre hpi (convT_of_tyConv hab hDA.symmT)

/-- `LRSCoreT` counterpart of `wholeSpine_convArgsT_snoc_of_links`. -/
theorem wholeSpine_convArgsT_snoc_of_linksT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (ls : List Level)
    {pre pre' : List (Expr Nat)} {A B a b : Expr Nat}
    (df : HasTyT E n Γ (foldApps (.const r ls) pre) (.pi A B))
    (hlt : pre.length < (piDomsOf m.mtype).length)
    (hlink : PiTowerLinkBelowT R E n (sizeOf df))
    (hpre : ConvArgsT E n Γ (instantiateLevels ls m.mtype) pre pre')
    (hab : ConvT E n Γ a b A) :
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) (pre ++ [a]) (pre' ++ [b]) :=
  wholeSpine_convArgsT_snoc_of_links hL hNU hW hΓ hm ls df hlt
    (piTowerLinkBelow_iff_typed.mp hlink) hpre hab


/-! #### §9 Part B — Positive Resolution of `#7689` / `#7733`'s `eqEnvT` Convertible-Index K Obstruction (`eqCanonGapRedex`) and `pinLoopEnvT` Recursive-Singleton K Redex (`loopCanonRedex`) Under Deterministic `WhStepRecKCanon` -/

/-- Non-syntactic convertible index `(λ x : α. x) a` under `[a : α, α : Sort 1]`. -/
def eqCanonGapIdx : Expr Nat := .app (.lam (.bvar 1) (.bvar 0)) (.bvar 0)

/-- The indexed equality type `Eq α a ((λ x : α. x) a)` under `[a : α, α : Sort 1]`. -/
def eqCanonGapEqTy : Expr Nat :=
  foldApps (.const 63 []) [.bvar 1, .bvar 0, eqCanonGapIdx]

/-- Context `[h : Eq α a ((λ x : α. x) a), a : α, α : Sort 1]` in `eqEnvT` (`RcicPinEqEraseWf`). -/
def eqCanonGapCtx : LCtx :=
  [.assumption eqCanonGapEqTy, .assumption (.bvar 0), .assumption (.sort (.succ .zero))]

/-- Motive `λ (b : α) (e : Eq α a b). Sort 1` in `eqCanonGapCtx`. -/
def eqCanonGapMot : Expr Nat :=
  .lam (.bvar 2)
    (.lam (foldApps (.const 63 []) [.bvar 3, .bvar 2, .bvar 0]) (.sort (.succ .zero)))

/-- **The Convertible-Index K Redex (`eqCanonGapRedex`):**
    `Eq.rec.{2} α a (λ b e. Sort 1) (Sort 0) ((λ x : α. x) a) h` in `eqCanonGapCtx` under `eqEnvT`.
    Whereas `#7689` (`WhStepCK`) and `#7733` get stuck on `eqCanonGapRedex` because their syntactic
    index-agreement guard `redexIdx w = resultIdxAt w ...` fails on `((λ x. x) a) ≠ a`, our landed
    deterministic `WhStepRecKCanon.pmajorCanon` (`RcicNativeFamModel` §16) has no syntactic
    index-agreement guard (because `iotaRhsOf w` depends only on `w.minor` and `w.fields`, not on the
    index arguments in `w.preMajor`) and reduces `eqCanonGapRedex` in **one step** to `.sort .zero`! -/
def eqCanonGapRedex : Expr Nat :=
  .app
    (foldApps (.const 65 [.succ (.succ .zero)])
      [.bvar 2, .bvar 1, eqCanonGapMot, .sort .zero,
       .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)])
    (.bvar 0)

/-- Canonical `IotaWitness eqEnvT` for `eqCanonGapRedex` (`ctorIdx = 0`, `fields = []`). -/
noncomputable def eqCanonGapW : IotaWitness eqEnvT where
  recRef := 65
  ctorRef := 64
  ls := [.succ (.succ .zero)]
  lsC := []
  recMember := eqRecT
  ctorMember := eqReflT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 2, .bvar 1, eqCanonGapMot, .sort .zero,
    .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]
  fields := []
  ctorParams := [.bvar 2, .bvar 1]
  kinds := []
  minor := .sort .zero
  hlen := rfl
  familyRef := 63
  famMember := eqFamT
  hfam := rfl
  hfamK := rfl
  nparams := 2
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort (.succ .zero), .bvar 0]
  ctorResult := foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 0]
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.sort (.succ .zero), .bvar 0, eqMotT, eqMinorT, .bvar 3,
    foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by decide
  hctorClosed := by decide
  hlsLen := rfl
  ctorAfterParams := foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1]
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- `eqCanonGapCtx` is a well-formed context in `eqEnvT`. -/
noncomputable def eqCanonGapCtx_wf (n : Nat) : CtxWfT eqEnvT n eqCanonGapCtx :=
  let Γ₀ : LCtx := []
  let Γ₁ : LCtx := [.assumption (.sort (.succ .zero))]
  let Γ₂ : LCtx := [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]
  have hΓ₁ : CtxWfT eqEnvT n Γ₁ :=
    .assumption Γ₀ (.sort (.succ .zero)) (.succ (.succ .zero)) .nil (.sort Γ₀ (.succ .zero))
  have hΓ₂ : CtxWfT eqEnvT n Γ₂ :=
    .assumption Γ₁ (.bvar 0) (.succ .zero) hΓ₁ (.bvar Γ₁ 0 (.sort (.succ .zero)) rfl)
  have hα : HasTyT eqEnvT n Γ₂ (.bvar 1) (.sort (.succ .zero)) :=
    .bvar Γ₂ 1 (.sort (.succ .zero)) rfl
  have ha : HasTyT eqEnvT n Γ₂ (.bvar 0) (.bvar 1) :=
    .bvar Γ₂ 0 (.bvar 1) rfl
  have hidx : HasTyT eqEnvT n Γ₂ eqCanonGapIdx (.bvar 1) :=
    .app Γ₂ (.lam (.bvar 1) (.bvar 0)) (.bvar 0) (.bvar 1) (.bvar 2)
      (.lam Γ₂ (.bvar 1) (.succ .zero) (.bvar 0) (.bvar 2) hα
        (.bvar (.assumption (.bvar 1) :: Γ₂) 0 (.bvar 2) rfl))
      ha
  have hEq : HasTyT eqEnvT n Γ₂ eqCanonGapEqTy (.sort .zero) :=
    .app Γ₂ _ eqCanonGapIdx (.bvar 1) (.sort .zero)
      (.app Γ₂ _ (.bvar 0) (.bvar 1) (.pi (.bvar 2) (.sort .zero))
        (.app Γ₂ (.const 63 []) (.bvar 1) (.sort (.succ .zero))
          (.pi (.bvar 0) (.pi (.bvar 1) (.sort .zero)))
          (.const Γ₂ 63 [] eqFamT rfl rfl rfl) hα)
        ha)
      hidx
  .assumption Γ₂ eqCanonGapEqTy .zero hΓ₂ hEq

/-- **One-Step `WhStepRecKCanon` Reduction of `eqCanonGapRedex` to `.sort .zero`
    (`whStepRecKCanon_eqCanonGapRedex`):** -/
theorem whStepRecKCanon_eqCanonGapRedex :
    WhStepRecKCanon eqEnvT eqCanonGapCtx eqCanonGapRedex (.sort .zero) :=
  .pmajorCanon eqCanonGapW 0 [] rfl rfl rfl rfl

theorem whRedRecKCanon_eqCanonGapRedex :
    WhRedRecKCanon eqEnvT eqCanonGapCtx eqCanonGapRedex (.sort .zero) :=
  .step whStepRecKCanon_eqCanonGapRedex (.refl (.sort .zero))

theorem redR_whStepRecKCanon_eqCanonGapRedex :
    RedR (WhStepRecKCanon eqEnvT) eqCanonGapCtx eqCanonGapRedex (.sort .zero) :=
  redR_of_whRedRecKCanon whRedRecKCanon_eqCanonGapRedex

/-- Exact two-sided `SemEqDIKCanon` equivalence of `eqCanonGapRedex` and `.sort .zero` in `eqEnvT`. -/
theorem semEqDIKCanon_eqCanonGapRedex :
    SemEqDIKCanon eqEnvT eqCanonGapCtx eqCanonGapRedex (.sort .zero) :=
  semEqDIKCanon_of_whRedRecKCanon pinEqGroupWfT whRedRecKCanon_eqCanonGapRedex

theorem approxDIKCanon_eqCanonGapRedex :
    ApproxDIKCanon eqEnvT eqCanonGapCtx eqCanonGapRedex .sort :=
  (semEqDIKCanon_eqCanonGapRedex .sort).mpr (approxDIKCanon_sort eqEnvT eqCanonGapCtx .zero)

/-- `eqCanonGapRedex` and `.sort .zero` inhabit `LRTypeFamINRKCanon` at `.sort`. -/
theorem lrTypeFamINRKCanon_eqCanonGap :
    LRTypeFamINRKCanon eqEnvT n eqCanonGapCtx eqCanonGapRedex (.sort .zero) .sort :=
  .sort whRedRecKCanon_eqCanonGapRedex (.refl (.sort .zero))

/-- `eqCanonGapRedex` and `.sort .zero` inhabit bidirectional `LRTypeFamINBiRKCanon` across all
    `BotFamCpt eqEnvT` compacts! -/
theorem lrTypeFamINBiRKCanon_eqCanonGap :
    LRTypeFamINBiRKCanon eqEnvT n eqCanonGapCtx eqCanonGapRedex (.sort .zero) := by
  have hdiag : LRTypeFamINBiRKCanon eqEnvT n eqCanonGapCtx (.sort .zero) (.sort .zero) := by
    intro c _ happrox
    cases happrox with
    | inl h =>
        cases PiModelDeltaIotaAudit.approxDI_sort_inv
          ((approxDIKCanon_sort_iff eqEnvT eqCanonGapCtx .zero c).mp h) with
        | inl hbot => subst hbot; exact .bot _ _ _
        | inr hsort => subst hsort; exact .sort (.refl _) (.refl _)
    | inr h =>
        cases PiModelDeltaIotaAudit.approxDI_sort_inv
          ((approxDIKCanon_sort_iff eqEnvT eqCanonGapCtx .zero c).mp h) with
        | inl hbot => subst hbot; exact .bot _ _ _
        | inr hsort => subst hsort; exact .sort (.refl _) (.refl _)
  exact lrTypeFamINBiRKCanon_whStepRecKCanon_left pinEqGroupWfT whStepRecKCanon_eqCanonGapRedex hdiag

/-- `eqCanonGapRedex` and `.sort .zero` inhabit bidirectional `LRTypeFamINBiProbeRKCanon` across all
    `FamProbeCpt eqEnvT` compacts! -/
theorem lrTypeFamINBiProbeRKCanon_eqCanonGap :
    LRTypeFamINBiProbeRKCanon eqEnvT n eqCanonGapCtx eqCanonGapRedex (.sort .zero) :=
  lrTypeFamINBiProbeRKCanon_of_lrTypeFamINBiRKCanon lrTypeFamINBiRKCanon_eqCanonGap

/-- `eqCanonGapRedex` and `.sort .zero` inhabit `LRTermFamSemBiProbeRKCanon` at `.sort u`! -/
theorem lrTermFamSemBiProbeRKCanon_eqCanonGap (u : Level) :
    LRTermFamSemBiProbeRKCanon eqEnvT n eqCanonGapCtx eqCanonGapRedex (.sort .zero) (.sort u) :=
  (lrTermFamSemBiProbeRKCanon_sort_iff eqCanonGapRedex (.sort .zero) u).mpr
    lrTypeFamINBiProbeRKCanon_eqCanonGap

/-- `eqCanonGapRedex` and `.sort .zero` inhabit `LRSCore (WhStepRecKCanon eqEnvT)` at `.sort`! -/
theorem lrSCore_whStepRecKCanon_eqCanonGap (u : Level) :
    LRSCore (WhStepRecKCanon eqEnvT) eqEnvT n eqCanonGapCtx
      eqCanonGapRedex (.sort .zero) (.sort u) .sort := by
  rw [LRSCore.eq_def]
  exact ⟨⟨u, .refl _⟩, .zero, .zero, redR_whStepRecKCanon_eqCanonGapRedex, .refl _⟩

theorem lrSCore_whStepRecKCanon_eqCanonGap_symm (u : Level) :
    LRSCore (WhStepRecKCanon eqEnvT) eqEnvT n eqCanonGapCtx
      (.sort .zero) eqCanonGapRedex (.sort u) .sort := by
  rw [LRSCore.eq_def]
  exact ⟨⟨u, .refl _⟩, .zero, .zero, .refl _, redR_whStepRecKCanon_eqCanonGapRedex⟩

/-- `eqCanonGapRedex` and `.sort .zero` inhabit `LRSCoreT (WhStepRecKCanon eqEnvT)` at `.prop` and
    `.sort`! -/
theorem lrSCoreT_whStepRecKCanon_eqCanonGap_prop (u : Level) :
    LRSCoreT (WhStepRecKCanon eqEnvT) eqEnvT n eqCanonGapCtx
      eqCanonGapRedex (.sort .zero) (.sort u) .prop := by
  rw [lrSCoreT_prop_iff]
  exact ⟨⟨u, .refl _⟩, .zero, .zero, redR_whStepRecKCanon_eqCanonGapRedex, .refl _⟩

theorem lrSCoreT_whStepRecKCanon_eqCanonGap_sort (u : Level) :
    LRSCoreT (WhStepRecKCanon eqEnvT) eqEnvT n eqCanonGapCtx
      eqCanonGapRedex (.sort .zero) (.sort u) .sort :=
  (lrSCoreT_prop_iff_sort _ _ _ _).mp (lrSCoreT_whStepRecKCanon_eqCanonGap_prop u)

/-- `eqCanonGapRedex` and `.sort .zero` inhabit `FamObsEquiv (WhStepRecKCanon eqEnvT)`! -/
theorem famObsEquiv_whStepRecKCanon_eqCanonGap :
    FamObsEquiv (WhStepRecKCanon eqEnvT) eqEnvT n eqCanonGapCtx eqCanonGapRedex (.sort .zero) :=
  famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon eqEnvT)
    (detR_whStepRecKCanon pinEqGroupWfT) pinEqGroupWfT whStepRecKCanon_eqCanonGapRedex

/-- Context `[h : Loop]` in `pinLoopEnvT` (`RcicPinLoopEraseWf`). -/
def loopCanonCtx : LCtx := [.assumption (.const 60 [])]

/-- Motive `λ _ : Loop. Sort 1` in `pinLoopEnvT`. -/
def loopCanonMot : Expr Nat := .lam (.const 60 []) (.sort (.succ .zero))

/-- Minor `λ (l : Loop) (ih : Sort 1). Sort 0` in `pinLoopEnvT`. -/
def loopCanonMin : Expr Nat :=
  .lam (.const 60 []) (.lam (.sort (.succ .zero)) (.sort .zero))

/-- **The Recursive-Singleton K Redex (`loopCanonRedex`):**
    `Loop.rec.{2} (λ _. Sort 1) (λ l ih. Sort 0) h` in `loopCanonCtx = [h : Loop]` under
    `pinLoopEnvT`. Because `Loop.mk : Loop → Loop` is a recursive singleton constructor
    (`kinds = [.directRec]`), `WhStepRecKCanon.pmajorCanon` instantiates the single recursive field
    with `famBotClosedExpr`, and two `beta` steps reduce the contractum to `.sort .zero` without
    unfolding the inner recursive call! -/
def loopCanonRedex : Expr Nat :=
  .app (foldApps (.const 62 [.succ (.succ .zero)]) [loopCanonMot, loopCanonMin]) (.bvar 0)

/-- Canonical `IotaWitness pinLoopEnvT` for `loopCanonRedex` (`ctorIdx = 0`,
    `fields = [famBotClosedExpr]`). -/
noncomputable def loopCanonW : IotaWitness pinLoopEnvT where
  recRef := 62
  ctorRef := 61
  ls := [.succ (.succ .zero)]
  lsC := []
  recMember := pinLoopRecT
  ctorMember := pinLoopMkT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [loopCanonMot, loopCanonMin]
  fields := [famBotClosedExpr]
  ctorParams := []
  kinds := [.directRec]
  minor := loopCanonMin
  hlen := rfl
  familyRef := 60
  famMember := pinLoopFamT
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.const 60 []]
  ctorResult := .const 60 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [loopMotT, loopMinorT, .const 60 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by decide
  hctorClosed := by decide
  hlsLen := rfl
  ctorAfterParams := .pi (.const 60 []) (.const 60 [])
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- `loopCanonRedex` reduces in three deterministic `WhStepRecKCanon` steps (`pmajorCanon` + two
    `beta` steps) to `.sort .zero` in `pinLoopEnvT`! -/
theorem whRedRecKCanon_loopCanonRedex :
    WhRedRecKCanon pinLoopEnvT loopCanonCtx loopCanonRedex (.sort .zero) := by
  have hs1 : WhStepRecKCanon pinLoopEnvT loopCanonCtx loopCanonRedex (iotaRhsOf loopCanonW) :=
    .pmajorCanon loopCanonW 0 [] rfl rfl rfl rfl
  have hs2 : WhStepRecKCanon pinLoopEnvT loopCanonCtx (iotaRhsOf loopCanonW)
      (.app (.lam (.sort (.succ .zero)) (.sort .zero))
        (.app (foldApps (.const 62 [.succ (.succ .zero)]) [loopCanonMot, loopCanonMin])
          famBotClosedExpr)) :=
    .appHead (.beta (.const 60 []) (.lam (.sort (.succ .zero)) (.sort .zero)) famBotClosedExpr)
  have hs3 : WhStepRecKCanon pinLoopEnvT loopCanonCtx
      (.app (.lam (.sort (.succ .zero)) (.sort .zero))
        (.app (foldApps (.const 62 [.succ (.succ .zero)]) [loopCanonMot, loopCanonMin])
          famBotClosedExpr))
      (.sort .zero) :=
    .beta (.sort (.succ .zero)) (.sort .zero)
      (.app (foldApps (.const 62 [.succ (.succ .zero)]) [loopCanonMot, loopCanonMin])
        famBotClosedExpr)
  exact .step hs1 (.step hs2 (.step hs3 (.refl (.sort .zero))))

theorem redR_whStepRecKCanon_loopCanonRedex :
    RedR (WhStepRecKCanon pinLoopEnvT) loopCanonCtx loopCanonRedex (.sort .zero) :=
  redR_of_whRedRecKCanon whRedRecKCanon_loopCanonRedex

/-- Exact two-sided `SemEqDIKCanon` equivalence of `loopCanonRedex` and `.sort .zero` in `pinLoopEnvT`. -/
theorem semEqDIKCanon_loopCanonRedex :
    SemEqDIKCanon pinLoopEnvT loopCanonCtx loopCanonRedex (.sort .zero) :=
  semEqDIKCanon_of_whRedRecKCanon pinLoopGroupRecWfT whRedRecKCanon_loopCanonRedex

/-- `loopCanonRedex` and `.sort .zero` inhabit `LRTypeFamINBiRKCanon` across all
    `BotFamCpt pinLoopEnvT` compacts! -/
theorem lrTypeFamINBiRKCanon_loopCanon :
    LRTypeFamINBiRKCanon pinLoopEnvT n loopCanonCtx loopCanonRedex (.sort .zero) := by
  have hdiag : LRTypeFamINBiRKCanon pinLoopEnvT n loopCanonCtx (.sort .zero) (.sort .zero) := by
    intro c _ happrox
    cases happrox with
    | inl h =>
        cases PiModelDeltaIotaAudit.approxDI_sort_inv
          ((approxDIKCanon_sort_iff pinLoopEnvT loopCanonCtx .zero c).mp h) with
        | inl hbot => subst hbot; exact .bot _ _ _
        | inr hsort => subst hsort; exact .sort (.refl _) (.refl _)
    | inr h =>
        cases PiModelDeltaIotaAudit.approxDI_sort_inv
          ((approxDIKCanon_sort_iff pinLoopEnvT loopCanonCtx .zero c).mp h) with
        | inl hbot => subst hbot; exact .bot _ _ _
        | inr hsort => subst hsort; exact .sort (.refl _) (.refl _)
  exact lrTypeFamINBiRKCanon_whRedRecKCanon_left pinLoopGroupRecWfT whRedRecKCanon_loopCanonRedex hdiag

/-- `loopCanonRedex` and `.sort .zero` inhabit `LRTypeFamINBiProbeRKCanon` across all
    `FamProbeCpt pinLoopEnvT` compacts! -/
theorem lrTypeFamINBiProbeRKCanon_loopCanon :
    LRTypeFamINBiProbeRKCanon pinLoopEnvT n loopCanonCtx loopCanonRedex (.sort .zero) :=
  lrTypeFamINBiProbeRKCanon_of_lrTypeFamINBiRKCanon lrTypeFamINBiRKCanon_loopCanon

/-- `loopCanonRedex` and `.sort .zero` inhabit `LRSCore (WhStepRecKCanon pinLoopEnvT)` at `.sort`! -/
theorem lrSCore_whStepRecKCanon_loopCanon (u : Level) :
    LRSCore (WhStepRecKCanon pinLoopEnvT) pinLoopEnvT n loopCanonCtx
      loopCanonRedex (.sort .zero) (.sort u) .sort := by
  rw [LRSCore.eq_def]
  exact ⟨⟨u, .refl _⟩, .zero, .zero, redR_whStepRecKCanon_loopCanonRedex, .refl _⟩

/-- `loopCanonRedex` and `.sort .zero` inhabit `LRSCoreT (WhStepRecKCanon pinLoopEnvT)` at `.prop`
    and `.sort`! -/
theorem lrSCoreT_whStepRecKCanon_loopCanon_prop (u : Level) :
    LRSCoreT (WhStepRecKCanon pinLoopEnvT) pinLoopEnvT n loopCanonCtx
      loopCanonRedex (.sort .zero) (.sort u) .prop := by
  rw [lrSCoreT_prop_iff]
  exact ⟨⟨u, .refl _⟩, .zero, .zero, redR_whStepRecKCanon_loopCanonRedex, .refl _⟩

theorem lrSCoreT_whStepRecKCanon_loopCanon_sort (u : Level) :
    LRSCoreT (WhStepRecKCanon pinLoopEnvT) pinLoopEnvT n loopCanonCtx
      loopCanonRedex (.sort .zero) (.sort u) .sort :=
  (lrSCoreT_prop_iff_sort _ _ _ _).mp (lrSCoreT_whStepRecKCanon_loopCanon_prop u)

/-- `loopCanonRedex` and `.sort .zero` inhabit `FamObsEquiv (WhStepRecKCanon pinLoopEnvT)`! -/
theorem famObsEquiv_whStepRecKCanon_loopCanon :
    FamObsEquiv (WhStepRecKCanon pinLoopEnvT) pinLoopEnvT n loopCanonCtx
      loopCanonRedex (.sort .zero) :=
  famObsEquiv_of_redR (readbackLaws_whStepRecKCanon pinLoopEnvT)
    (detR_whStepRecKCanon pinLoopGroupRecWfT) pinLoopGroupRecWfT
    (.assumption [] (.const 60 []) .zero .nil (.const [] 60 [] pinLoopFamT rfl rfl rfl))
    redR_whStepRecKCanon_loopCanonRedex


/-! ### §10 — Exact Bridge to `RcicNativePiProbe*`, Complete 18-Constructor `ConvT` Closure Audit
    for 3-Observation `FamConvObsMotive` at `WhStepRecKCanon` & `WhStepK`, and Positive Resolution
    of `RcicNativeTypedModelIotaSound`'s `Exists` Non-Proof-Field Witness `wEx` in `ApproxDI` /
    `WhStepRecKCanon` / `ApproxDIKCanon` -/

open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeComputationAudit
open Rcic.Declarative.NativeValleys.PiProbeConstantsAudit
open Rcic.Declarative.NativeValleys.PiProbeCongruenceAudit
open Rcic.Declarative.NativeValleys.PiProbeKObstructionAudit
open Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit

/-! #### §10 Part A — Exact Factorization of 3-Observation `FamObsTransport` / `FamObsEquiv` /
    `FamConvObsMotive` / `FamObsConvLinks` into `RcicNativePiProbeAlgebra`'s `ProbeTransportT` /
    `ProbeEquivT` / `ConvProbeMotiveT` / `ProbeConvLinksT` + `FamSpineEquiv`, and Unconditional
    Closure of `ConvT.consts` (Including Non-Vacuous 0-Arity `.inductiveM` Family Spines) -/

/-- `FamSortReadTransport` is definitionally `RcicNativePiProbeAlgebra.SortReadTransportT`. -/
theorem famSortReadTransport_eq_sortReadTransportT (R : Readback) (Γ : LCtx) (M N : Expr Nat) :
    FamSortReadTransport R Γ M N = SortReadTransportT R Γ M N := rfl

/-- `FamPiReadTransport` is definitionally `RcicNativePiProbeAlgebra.PiReadTransportT`. -/
theorem famPiReadTransport_eq_piReadTransportT (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (M N : Expr Nat) :
    FamPiReadTransport R E n Γ M N = PiReadTransportT R E n Γ M N := rfl

/-- **Exact Factorization of `FamObsTransport` (`famObsTransport_iff_probeTransportT_and_famSpine`):**
    The 3-observation transport `FamObsTransport` is equivalent to `RcicNativePiProbeAlgebra`'s
    2-observation `ProbeTransportT` (Sort + Π) plus `FamSpineReadTransport`. -/
theorem famObsTransport_iff_probeTransportT_and_famSpine {Γ : LCtx} {M N : Expr Nat} :
    FamObsTransport R E n Γ M N ↔
      ProbeTransportT R E n Γ M N ∧ FamSpineReadTransport R E n Γ M N :=
  ⟨fun ⟨hs, hp, hf⟩ => ⟨⟨hs, hp⟩, hf⟩, fun ⟨⟨hs, hp⟩, hf⟩ => ⟨hs, hp, hf⟩⟩

/-- Bidirectional specified-witness `.inductiveM` family-spine readback equivalence (`FamSpineEquiv`). -/
def FamSpineEquiv (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M N : Expr Nat) : Prop :=
  FamSpineReadTransport R E n Γ M N ∧ FamSpineReadTransport R E n Γ N M

theorem famSpineEquiv_refl (Γ : LCtx) (M : Expr Nat) :
    FamSpineEquiv R E n Γ M M :=
  ⟨famSpineReadTransport_refl Γ M, famSpineReadTransport_refl Γ M⟩

theorem famSpineEquiv_symm {Γ : LCtx} {M N : Expr Nat}
    (h : FamSpineEquiv R E n Γ M N) :
    FamSpineEquiv R E n Γ N M :=
  ⟨h.2, h.1⟩

theorem famSpineEquiv_trans (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N P : Expr Nat}
    (h₁ : FamSpineEquiv R E n Γ M N)
    (h₂ : FamSpineEquiv R E n Γ N P) :
    FamSpineEquiv R E n Γ M P :=
  ⟨famSpineReadTransport_trans hW hΓ h₁.1 h₂.1,
   famSpineReadTransport_trans hW hΓ h₂.2 h₁.2⟩

/-- **Exact Factorization of `FamObsEquiv` (`famObsEquiv_iff_probeEquivT_and_famSpineEquiv`):**
    The 3-observation equivalence `FamObsEquiv` is equivalent to `RcicNativePiProbeAlgebra`'s
    `ProbeEquivT` plus `FamSpineEquiv`. -/
theorem famObsEquiv_iff_probeEquivT_and_famSpineEquiv {Γ : LCtx} {M N : Expr Nat} :
    FamObsEquiv R E n Γ M N ↔
      ProbeEquivT R E n Γ M N ∧ FamSpineEquiv R E n Γ M N :=
  ⟨fun ⟨⟨hs₁, hp₁, hf₁⟩, ⟨hs₂, hp₂, hf₂⟩⟩ => ⟨⟨⟨hs₁, hp₁⟩, ⟨hs₂, hp₂⟩⟩, ⟨hf₁, hf₂⟩⟩,
   fun ⟨⟨⟨hs₁, hp₁⟩, ⟨hs₂, hp₂⟩⟩, ⟨hf₁, hf₂⟩⟩ => ⟨⟨hs₁, hp₁, hf₁⟩, ⟨hs₂, hp₂, hf₂⟩⟩⟩

/-- **Exact Factorization of `FamConvObsMotive`
    (`famConvObsMotive_iff_convProbeMotiveT_and_famSpineEquiv`):** -/
theorem famConvObsMotive_iff_convProbeMotiveT_and_famSpineEquiv {Γ : LCtx} {M N A : Expr Nat}
    (hc : ConvT E n Γ M N A) :
    FamConvObsMotive R hc ↔
      ConvProbeMotiveT R hc ∧ FamSpineEquiv R E n Γ M N :=
  famObsEquiv_iff_probeEquivT_and_famSpineEquiv

/-- Single-link `ConvT` obligation for bidirectional specified-witness `.inductiveM` family-spine
    readback transport (`FamSpineConvLinks`). -/
def FamSpineConvLinks (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M N : Expr Nat} {u : Level},
    ConvT E n Γ M N (.sort u) → FamSpineEquiv R E n Γ M N

/-- Projecting `FamObsConvLinks R E n` to `RcicNativePiProbeAlgebra.ProbeConvLinksT R E n`. -/
theorem probeConvLinksT_of_famObsConvLinks (hlinks : FamObsConvLinks R E n) :
    ProbeConvLinksT R E n := by
  intro Γ hΓ M N u hc
  exact ((famConvObsMotive_iff_convProbeMotiveT_and_famSpineEquiv hc).mp (hlinks hΓ hc)).1

/-- Projecting `FamObsConvLinks R E n` to `FamSpineConvLinks R E n`. -/
theorem famSpineConvLinks_of_famObsConvLinks (hlinks : FamObsConvLinks R E n) :
    FamSpineConvLinks R E n := by
  intro Γ hΓ M N u hc
  exact ((famConvObsMotive_iff_convProbeMotiveT_and_famSpineEquiv hc).mp (hlinks hΓ hc)).2

/-- **Exact Factorization of `FamObsConvLinks`
    (`famObsConvLinks_iff_probeConvLinksT_and_famSpineConvLinks`):** -/
theorem famObsConvLinks_iff_probeConvLinksT_and_famSpineConvLinks :
    FamObsConvLinks R E n ↔ ProbeConvLinksT R E n ∧ FamSpineConvLinks R E n := by
  refine ⟨fun h => ⟨probeConvLinksT_of_famObsConvLinks h, famSpineConvLinks_of_famObsConvLinks h⟩, ?_⟩
  intro ⟨hp, hf⟩ Γ hΓ M N u hc
  exact (famConvObsMotive_iff_convProbeMotiveT_and_famSpineEquiv hc).mpr ⟨hp hΓ hc, hf hΓ hc⟩

/-- **`NormalUniqueR`-Free `FamAppRowLink E n` from `ProbeConvLinksT` + `FamSpineConvLinks`
    (`famAppRow_of_probeConvLinksT_and_famSpineConvLinks`):** -/
theorem famAppRow_of_probeConvLinksT_and_famSpineConvLinks (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (hp : ProbeConvLinksT R E n) (hf : FamSpineConvLinks R E n) :
    FamAppRowLink E n :=
  famAppRow_of_famObsConvLinks hL hW
    (famObsConvLinks_iff_probeConvLinksT_and_famSpineConvLinks.mpr ⟨hp, hf⟩)

/-- **`NormalUniqueR`-Free `FamRelevantSlotConv E n` (#7525) from `ProbeConvLinksT` + `FamSpineConvLinks`
    (`famRelevantSlotConv_of_probeConvLinksT_and_famSpineConvLinks`):** -/
theorem famRelevantSlotConv_of_probeConvLinksT_and_famSpineConvLinks (hL : ReadbackLaws E R)
    (hW : EnvWfT E) (hp : ProbeConvLinksT R E n) (hf : FamSpineConvLinks R E n) :
    FamRelevantSlotConv E n :=
  famRelevantSlotConv_of_famObsConvLinks hL hW
    (famObsConvLinks_iff_probeConvLinksT_and_famSpineConvLinks.mpr ⟨hp, hf⟩)

/-- **`NormalUniqueR`-Free `TypedRowsWf E n` from `ProbeConvLinksT` + `FamSpineConvLinks`
    (`typedRowsWf_of_allBelowScoped_probeConvLinksT_and_famSpineConvLinks`):** -/
theorem typedRowsWf_of_allBelowScoped_probeConvLinksT_and_famSpineConvLinks
    (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hp : ProbeConvLinksT R E n) (hf : FamSpineConvLinks R E n) :
    TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_famObsConvLinks hL hW hBel
    (famObsConvLinks_iff_probeConvLinksT_and_famSpineConvLinks.mpr ⟨hp, hf⟩)

/-- For any 0-arity admitted `.inductiveM` member (`(piDomsOf m.mtype).length = 0`),
    `instantiateLevels ls m.mtype = .sort (instLevel ls (inductiveSortLevel hW hm hind))`. -/
theorem instantiateLevels_mtype_of_inductiveM_zeroArity (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hzero : (piDomsOf m.mtype).length = 0) (ls : List Level) :
    instantiateLevels ls m.mtype =
      .sort (instLevel ls (inductiveSortLevel hW hm hind)) := by
  have hpi := instMtype_policyPi_of_inductiveM hW hm hind ls
  have hnil : piDomsOf m.mtype = [] := by
    cases h : piDomsOf m.mtype with
    | nil => rfl
    | cons _ _ => rw [h] at hzero; exact Nat.noConfusion hzero
  rw [hnil, List.map_nil, policyPi] at hpi
  exact hpi

/-- **Forward 3-Observation Transport for Bodyless Constants (`famObsTransport_consts_opaque`):**
    Unlike `ProbeTransportT` (where bodyless constants are vacuous because they have neither Sort
    nor Π readbacks), in `FamObsTransport` a 0-arity `.inductiveM` constant
    (`.const r ls = foldApps (.const r ls) []`) **is** a saturated family spine!
    Whenever `.const r ls` is normal in `R`, `ConvT.consts`'s level premises
    (`ls.length = m.arity`, `levelsBounded n ls = true`, `levelsBounded n ls' = true`, `eqNList ls ls'`)
    preserve `FamSpineReadTransport` unconditionally under `EnvWfT E` alone! -/
theorem famObsTransport_consts_opaque (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls ls' : List Level}
    (hlen : ls.length = m.arity) (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (hnorm : NormalR R Γ (.const r ls)) :
    FamObsTransport R E n Γ (.const r ls) (.const r ls') := by
  refine ⟨fun ⟨u, hred⟩ => Expr.noConfusion (redR_of_normal hnorm hred),
    fun hred _ => Expr.noConfusion (redR_of_normal hnorm hred),
    fun {r₀ m₀ ls₀ xs₀ w₀} hm₀ hind₀ hred _ hlen₀ _ => ?_⟩
  have heq_sp : foldApps (.const r₀ ls₀) xs₀ = foldApps (.const r ls) [] :=
    redR_of_normal hnorm hred
  obtain ⟨hconst, hxs⟩ := foldApps_const_inj heq_sp
  injection hconst with hr hls_eq
  subst hr; subst hls_eq; subst hxs
  have em : m₀ = m := Option.some.inj (hm₀.symm.trans hm)
  subst em
  have hzero : (piDomsOf m₀.mtype).length = 0 := hlen₀.symm
  have hlen' : ls'.length = m₀.arity := (eqNList_length ls₀ ls' heq).symm.trans hlen
  have hinst : instantiateLevels ls₀ m₀.mtype =
      .sort (instLevel ls₀ (inductiveSortLevel hW hm₀ hind₀)) :=
    instantiateLevels_mtype_of_inductiveM_zeroArity hW hm₀ hind₀ hzero ls₀
  have hinst' : instantiateLevels ls' m₀.mtype =
      .sort (instLevel ls' (inductiveSortLevel hW hm₀ hind₀)) :=
    instantiateLevels_mtype_of_inductiveM_zeroArity hW hm₀ hind₀ hzero ls'
  have hty' : HasTyT E n Γ (foldApps (.const r₀ ls') [])
      (.sort (instLevel ls' (inductiveSortLevel hW hm₀ hind₀))) := by
    simpa only [foldApps, hinst'] using HasTyT.const Γ r₀ ls' m₀ hm₀ hlen' hls'
  have hconv : ConvT E n Γ (foldApps (.const r₀ ls₀) []) (foldApps (.const r₀ ls') [])
      (.sort (instLevel ls₀ (inductiveSortLevel hW hm₀ hind₀))) := by
    simpa only [foldApps, hinst] using ConvT.consts Γ r₀ ls₀ ls' m₀ hm₀ hlen hls hls' heq
  exact ⟨ls', [], instLevel ls' (inductiveSortLevel hW hm₀ hind₀), .refl _,
    ⟨hty'⟩, ⟨.of Γ _ _ _ hconv⟩, heq, hlen₀, .nil _⟩

/-- Bidirectional 3-observation equivalence for bodyless constants under `EnvWfT E` alone. -/
theorem famObsEquiv_consts_opaque (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    {ls ls' : List Level}
    (hlen : ls.length = m.arity) (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (hnorm : NormalR R Γ (.const r ls))
    (hnorm' : NormalR R Γ (.const r ls')) :
    FamObsEquiv R E n Γ (.const r ls) (.const r ls') := by
  have hlen' : ls'.length = m.arity := (eqNList_length ls ls' heq).symm.trans hlen
  exact ⟨famObsTransport_consts_opaque hW hm hlen hls hls' heq hnorm,
    famObsTransport_consts_opaque hW hm hlen' hls' hls (eqNList_symm heq) hnorm'⟩

/-- Bidirectional 3-observation equivalence for constants with a stored body under `ReadbackLaws E R`,
    `DetR R`, and `EnvWfT E`: both `.const r ls` and `.const r ls'` step deterministically to the
    same level-free `body` (`instantiateLevels_stored_body`). -/
theorem famObsEquiv_consts_body_of_detR (hL : ReadbackLaws E R) (hdet : DetR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {body : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some body) {ls ls' : List Level}
    (hs₁ : R Γ (.const r ls) (instantiateLevels ls body))
    (hs₂ : R Γ (.const r ls') (instantiateLevels ls' body)) :
    FamObsEquiv R E n Γ (.const r ls) (.const r ls') := by
  have hs₁' : R Γ (.const r ls) body := by
    rwa [instantiateLevels_stored_body hW hm hb ls] at hs₁
  have hs₂' : R Γ (.const r ls') body := by
    rwa [instantiateLevels_stored_body hW hm hb ls'] at hs₂
  exact famObsEquiv_trans hW hΓ
    (famObsEquiv_of_stepR hL hdet hW hs₁')
    (famObsEquiv_symm (famObsEquiv_of_stepR hL hdet hW hs₂'))

/-- **Unconditional `ConvT.consts` Closure in `FamConvObsMotive (WhStepRecKCanon E)`
    (`famConvObs_whStepRecKCanon_consts`):**
    Closes constructor #14 (`ConvT.consts`) for the 3-observation motive `FamConvObsMotive (WhStepRecKCanon E)`
    under `EnvWfT E` and `CtxWfT E n Γ` alone! -/
theorem famConvObs_whStepRecKCanon_consts (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} (hm : E.members r = some m)
    (hlen : ls.length = m.arity) (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (heq : eqNList ls ls') :
    FamConvObsMotive (WhStepRecKCanon E)
      (.consts Γ r ls ls' m hm hlen hls hls' heq) := by
  cases hb : m.body with
  | none =>
      exact famObsEquiv_consts_opaque hW hm hlen hls hls' heq
        (fun _ hs => whStepRecKCanon_const_opaque_false hm hb ls hs)
        (fun _ hs => whStepRecKCanon_const_opaque_false hm hb ls' hs)
  | some body =>
      exact famObsEquiv_consts_body_of_detR (readbackLaws_whStepRecKCanon E)
        (detR_whStepRecKCanon hW) hW hΓ hm hb (.delta hm hb) (.delta hm hb)

/-- Bidirectional 3-observation equivalence for constants with a stored body under `WhStepK E n`
    and `EnvWfT E` alone (`redR_consts_body_iff`). -/
theorem famObsEquiv_whStepK_consts_body (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} {body : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some body) (ls ls' : List Level) :
    FamObsEquiv (WhStepK E n) E n Γ (.const r ls) (.const r ls') :=
  ⟨famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hM => (redR_consts_body_iff hW hm hb ls ls' hX).mp hM),
   famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hN => (redR_consts_body_iff hW hm hb ls ls' hX).mpr hN)⟩

/-- **Unconditional `ConvT.consts` Closure in `FamConvObsMotive (WhStepK E n)`
    (`famConvObs_whStepK_consts`):**
    Closes `ConvT.consts` for the 3-observation motive at `WhStepK E n` under `EnvWfT E` alone! -/
theorem famConvObs_whStepK_consts (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} (hm : E.members r = some m)
    (hlen : ls.length = m.arity) (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (heq : eqNList ls ls') :
    FamConvObsMotive (WhStepK E n)
      (.consts Γ r ls ls' m hm hlen hls hls' heq) := by
  cases hb : m.body with
  | none =>
      exact famObsEquiv_consts_opaque hW hm hlen hls hls' heq
        (normalR_const_opaque hm hb ls) (normalR_const_opaque hm hb ls')
  | some body =>
      exact famObsEquiv_whStepK_consts_body hW hm hb ls ls'

/-- Concrete `ConvT.consts` derivation on the 0-arity `.inductiveM` family `True` (`r = 0`) in
    admitted `trueEnvU`. -/
noncomputable def constsFam_trueEnvU_conversion :
    ConvT trueEnvU 0 [] (.const 0 []) (.const 0 []) (.sort .zero) :=
  .consts [] 0 [] [] trueFamMember rfl rfl rfl rfl (eqNList_refl [])

/-- **Non-Vacuity of `ConvT.consts` on a 0-Arity `.inductiveM` Family Spine
    (`constsFam_trueEnvU_nonvacuity`):**
    Exhibits an admitted environment (`trueEnvU`), a well-typed 0-arity `.inductiveM` constant
    `True = .const 0 [] = foldApps (.const 0 []) []`, an **active saturated family-spine observation**
    (`RedR ... (.const 0 []) (foldApps (.const 0 []) [])`, `[].length = (piDomsOf trueFamMember.mtype).length`,
    `ConvArgsT trueEnvU 0 [] (instantiateLevels [] trueFamMember.mtype) [] []`), and full
    3-observation `FamConvObsMotive` satisfaction at both `WhStepRecKCanon trueEnvU` and
    `WhStepK trueEnvU 0`! -/
theorem constsFam_trueEnvU_nonvacuity :
    Nonempty (EnvWfT trueEnvU) ∧
    Nonempty (HasTyT trueEnvU 0 [] (foldApps (.const 0 []) []) (.sort .zero)) ∧
    RedR (WhStepRecKCanon trueEnvU) [] (.const 0 []) (foldApps (.const 0 []) []) ∧
    RedR (WhStepK trueEnvU 0) [] (.const 0 []) (foldApps (.const 0 []) []) ∧
    (([] : List (Expr Nat)).length = (piDomsOf trueFamMember.mtype).length) ∧
    ConvArgsT trueEnvU 0 [] (instantiateLevels [] trueFamMember.mtype) [] [] ∧
    FamConvObsMotive (WhStepRecKCanon trueEnvU) constsFam_trueEnvU_conversion ∧
    FamConvObsMotive (WhStepK trueEnvU 0) constsFam_trueEnvU_conversion :=
  ⟨⟨trueEnvUWfT⟩,
   ⟨.const [] 0 [] trueFamMember rfl rfl rfl⟩,
   .refl _,
   .refl _,
   rfl,
   .nil _,
   famConvObs_whStepRecKCanon_consts trueEnvUWfT .nil (r := 0) (ls := []) (ls' := []) (m := trueFamMember) rfl rfl rfl rfl (eqNList_refl []),
   famConvObs_whStepK_consts trueEnvUWfT (r := 0) (ls := []) (ls' := []) (m := trueFamMember) rfl rfl rfl rfl (eqNList_refl [])⟩

/-- Constructor closure of `FamConvObsMotive (WhStepK E n)` for `ConvT.beta` (`redR_beta_iff`). -/
theorem famConvObs_whStepK_beta (hW : EnvWfT E) {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (harg : HasTyT E n Γ arg A) :
    FamConvObsMotive (WhStepK E n) (.beta Γ A body arg B u hA hbody harg) :=
  ⟨famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hM => (redR_beta_iff hW hX).mp hM),
   famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hN => (redR_beta_iff hW hX).mpr hN)⟩

/-- Constructor closure of `FamConvObsMotive (WhStepK E n)` for `ConvT.zeta` (`redR_zeta_iff`). -/
theorem famConvObs_whStepK_zeta (hW : EnvWfT E) {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hbody : HasTyT E n (.letBinding A value :: Γ) body B) :
    FamConvObsMotive (WhStepK E n) (.zeta Γ A value body B u hA hv hbody) :=
  ⟨famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hM => (redR_zeta_iff hW hX).mp hM),
   famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hN => (redR_zeta_iff hW hX).mpr hN)⟩

/-- Constructor closure of `FamConvObsMotive (WhStepK E n)` for `ConvT.zetaLocal` (`redR_zetaLocal_iff`). -/
theorem famConvObs_whStepK_zetaLocal (hW : EnvWfT E) {Γ : LCtx} {i : Nat} {A value : Expr Nat}
    (hv : lookupValue Γ i = some value) (hA : lookupType Γ i = some A)
    (hty : HasTyT E n Γ value A) :
    FamConvObsMotive (WhStepK E n) (.zetaLocal Γ i A value hv hA hty) :=
  ⟨famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hM => (redR_zetaLocal_iff hW hv hX).mp hM),
   famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hN => (redR_zetaLocal_iff hW hv hX).mpr hN)⟩

/-- Constructor closure of `FamConvObsMotive (WhStepK E n)` for `ConvT.delta` (`redR_delta_iff`). -/
theorem famConvObs_whStepK_delta (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {body : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some body)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hty : HasTyT E n Γ (instantiateLevels ls body) (instantiateLevels ls m.mtype)) :
    FamConvObsMotive (WhStepK E n) (.delta Γ r ls m body hm hb htr hlen hwf hty) :=
  ⟨famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hM => (redR_delta_iff hW hm hb hX).mp hM),
   famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hN => (redR_delta_iff hW hm hb hX).mpr hN)⟩

/-- Constructor closure of `FamConvObsMotive (WhStepK E n)` for `ConvT.lit` (`redR_literalExpansion_iff`). -/
theorem famConvObs_whStepK_lit (hW : EnvWfT E) {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hexp : LiteralExpansion t exp) (hty : HasTyT E n Γ exp T) :
    FamConvObsMotive (WhStepK E n) (.lit Γ t exp T hexp hty) :=
  ⟨famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hM => (redR_literalExpansion_iff hW hexp hX).mp hM),
   famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
     (fun hX hN => (redR_literalExpansion_iff hW hexp hX).mpr hN)⟩

/-- Constructor closure of `FamConvObsMotive (WhStepK E n)` for `ConvT.lam`. -/
theorem famConvObs_whStepK_lam {Γ : LCtx} {A A' body body' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) body body' B) :
    FamConvObsMotive (WhStepK E n) (.lam Γ A A' body body' B u hA hB) := by
  have htrans (X Y X' Y' : Expr Nat) :
      FamObsTransport (WhStepK E n) E n Γ (.lam X Y) (.lam X' Y') :=
    ⟨fun ⟨u, h⟩ => (not_redR_lam_sort u h).elim,
     fun h _ => (not_redR_lam_pi _ _ h).elim,
     fun _ _ h _ _ _ => (F8EtaK.foldApps_const_ne_lam_any (redR_lam_eq h)).elim⟩
  exact ⟨htrans A body A' body', htrans A' body' A body⟩

/-- Reverse 3-observation transport for native `DerivedIota` under `WhStepK E n`
    (`famObsTransport_whStepK_native_iota_reverse`). -/
theorem famObsTransport_whStepK_native_iota_reverse (hW : EnvWfT E) {Γ : LCtx}
    {lhs rhs : Expr Nat} (hI : DerivedIota E lhs rhs) :
    FamObsTransport (WhStepK E n) E n Γ rhs lhs :=
  famObsTransport_of_readback_imp (readbackLaws_whStepK E n) hW
    (fun _ hread => .step (whStepK_of_native_iota hI) hread)

/-- Forward 3-observation port for a selected native `DerivedIota` step (`FamNativeIotaForwardAt`). -/
def FamNativeIotaForwardAt (R : Readback) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs T : Expr Nat} (_hI : DerivedIota E lhs rhs)
    (_hlhs : HasTyT E n Γ lhs T) (_hrhs : HasTyT E n Γ rhs T) : Prop :=
  FamObsTransport R E n Γ lhs rhs

/-- At `WhStepK E n`, `FamConvObsMotive` on `ConvT.iota` is equivalent to `FamNativeIotaForwardAt`
    because the reverse arm is unconditionally closed by `famObsTransport_whStepK_native_iota_reverse`. -/
theorem famConvObs_whStepK_iota_iff_forward (hW : EnvWfT E) {Γ : LCtx}
    {lhs rhs T : Expr Nat} (hI : DerivedIota E lhs rhs)
    (hlhs : HasTyT E n Γ lhs T) (hrhs : HasTyT E n Γ rhs T) :
    FamConvObsMotive (WhStepK E n) (.iota Γ lhs rhs T hI hlhs hrhs) ↔
      FamNativeIotaForwardAt (WhStepK E n) hI hlhs hrhs :=
  ⟨fun h => h.1, fun h => ⟨h, famObsTransport_whStepK_native_iota_reverse hW hI⟩⟩

/-- **Unconditional Discharge of `FamNativeIotaForwardAt (WhStepRecKCanon E)`
    (`famNativeIotaForwardAt_whStepRecKCanon`):**
    Unlike `WhStepK E n` (where `NativeIotaForwardAtT` is open because `WhStepK` is non-deterministic),
    at the canonical deterministic K-readback `WhStepRecKCanon E`, `detR_whStepRecKCanon hW`
    discharges `FamNativeIotaForwardAt (WhStepRecKCanon E)` **unconditionally** for every native
    `DerivedIota E lhs rhs` under `EnvWfT E` alone! -/
theorem famNativeIotaForwardAt_whStepRecKCanon (hW : EnvWfT E) {Γ : LCtx}
    {lhs rhs T : Expr Nat} (hI : DerivedIota E lhs rhs)
    (hlhs : HasTyT E n Γ lhs T) (hrhs : HasTyT E n Γ rhs T) :
    FamNativeIotaForwardAt (WhStepRecKCanon E) hI hlhs hrhs :=
  (famConvObs_whStepRecKCanon_iota hW (derivedIotaU_ofDerivedIota hI)).1


/-! #### §10 Part B — The Remaining 4 `ConvT` Constructors (`eta`, `irr`, `app`, `letE`) for 3-Observation
    `FamConvObsMotive`, Step-by-Step Family-Spine Application, 3-Head Model Boundary (`TypingLemmaT` +
    `FamTypedProbeRealizationT`), and Complete 18-Constructor Packager at `WhStepRecKCanon E` -/

/-- Pointwise 3-head exclusion at `f`: excludes Sort readbacks, well-formed-domain Π readbacks, and
    saturated well-typed admitted `.inductiveM` family-spine readbacks. -/
def FamFunctionNoTypeProbeAt (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (f : Expr Nat) : Prop :=
  (∀ u, ¬ RedR R Γ f (.sort u)) ∧
  (∀ A B, RedR R Γ f (.pi A B) → CtxWfT E n (.assumption A :: Γ) → False) ∧
  (∀ r m ls xs w,
    E.members r = some m → m.mclass = .inductiveM →
    RedR R Γ f (foldApps (.const r ls) xs) →
    HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w) →
    xs.length = (piDomsOf m.mtype).length →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs → False)

/-- Global 3-head exclusion at function-typed expressions `HasTyT E n Γ f (.pi A B)`. -/
def FamFunctionNoTypeProbe (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f A B : Expr Nat},
    HasTyT E n Γ f (.pi A B) → FamFunctionNoTypeProbeAt R E n Γ f

/-- Global 3-head exclusion at proof-typed expressions `HasTyT E n Γ p P` (`HasTyT E n Γ P (.sort .zero)`). -/
def FamPropNoTypeProbe (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {P p : Expr Nat},
    HasTyT E n Γ P (.sort .zero) → HasTyT E n Γ p P →
    FamFunctionNoTypeProbeAt R E n Γ p

/-- Projecting `FamFunctionNoTypeProbeAt` to `RcicNativePiProbeComputation.FunctionNoTypeProbeAtT`. -/
theorem functionNoTypeProbeAtT_of_fam {Γ : LCtx} {f : Expr Nat}
    (h : FamFunctionNoTypeProbeAt R E n Γ f) :
    FunctionNoTypeProbeAtT R E n Γ f :=
  ⟨h.1, h.2.1⟩

/-- Every syntactic lambda `.lam A body` satisfies `FamFunctionNoTypeProbeAt (WhStepRecKCanon E)`
    unconditionally in every context `Γ`. -/
theorem famFunctionNoTypeProbeAt_whStepRecKCanon_lam {Γ : LCtx} (A body : Expr Nat) :
    FamFunctionNoTypeProbeAt (WhStepRecKCanon E) E n Γ (.lam A body) :=
  ⟨fun _ h => Expr.noConfusion (whRedRecKCanon_lam_eq (whRedRecKCanon_of_redR h)),
   fun _ _ h _ => Expr.noConfusion (whRedRecKCanon_lam_eq (whRedRecKCanon_of_redR h)),
   fun _ _ _ _ _ _ _ h _ _ _ =>
     F8EtaK.foldApps_const_ne_lam_any (whRedRecKCanon_lam_eq (whRedRecKCanon_of_redR h))⟩

/-- Every syntactic lambda `.lam A body` satisfies `FamFunctionNoTypeProbeAt (WhStepK E n)`
    unconditionally in every context `Γ`. -/
theorem famFunctionNoTypeProbeAt_whStepK_lam {Γ : LCtx} (A body : Expr Nat) :
    FamFunctionNoTypeProbeAt (WhStepK E n) E n Γ (.lam A body) :=
  ⟨not_redR_lam_sort,
   fun A' B' h _ => not_redR_lam_pi A' B' h,
   fun _ _ _ _ _ _ _ h _ _ _ => F8EtaK.foldApps_const_ne_lam_any (redR_lam_eq h)⟩

/-- Any source `M` satisfying `FamFunctionNoTypeProbeAt R E n Γ M` vacuously satisfies
    `FamObsTransport R E n Γ M N` to every target `N`. -/
theorem famObsTransport_of_famFunctionNoTypeProbeAt {Γ : LCtx} {M N : Expr Nat}
    (hno : FamFunctionNoTypeProbeAt R E n Γ M) :
    FamObsTransport R E n Γ M N :=
  ⟨fun ⟨u, h⟩ => (hno.1 u h).elim,
   fun h hΓA => (hno.2.1 _ _ h hΓA).elim,
   fun hm hind h hty hlen hargs => (hno.2.2 _ _ _ _ _ hm hind h hty hlen hargs).elim⟩

/-- **Exact Characterization of `ConvT.eta` in `FamObsEquiv (WhStepRecKCanon E)`
    (`famObsEquiv_whStepRecKCanon_eta_iff_famFunctionNoTypeProbeAt`):** -/
theorem famObsEquiv_whStepRecKCanon_eta_iff_famFunctionNoTypeProbeAt {Γ : LCtx} (A f : Expr Nat) :
    FamObsEquiv (WhStepRecKCanon E) E n Γ
        (.lam A (.app (lift 0 1 f) (.bvar 0))) f ↔
      FamFunctionNoTypeProbeAt (WhStepRecKCanon E) E n Γ f := by
  have hlam := famFunctionNoTypeProbeAt_whStepRecKCanon_lam (E := E) (n := n) (Γ := Γ)
    A (.app (lift 0 1 f) (.bvar 0))
  constructor
  · intro h
    refine ⟨fun u hr => ?_, fun C D hr hΓC => ?_,
      fun r m ls xs w hm hind hr hty hlen hargs => ?_⟩
    · obtain ⟨v, hred⟩ := h.2.1 ⟨u, hr⟩
      exact hlam.1 v hred
    · obtain ⟨C', D', hred, _, _⟩ := h.2.2.1 hr hΓC
      exact hlam.2.1 C' D' hred (by
        exfalso
        exact Expr.noConfusion (whRedRecKCanon_lam_eq (whRedRecKCanon_of_redR hred)))
    · obtain ⟨ls', xs', w', hred, _, _, _, _, _⟩ := h.2.2.2 hm hind hr hty hlen hargs
      exact F8EtaK.foldApps_const_ne_lam_any
        (whRedRecKCanon_lam_eq (whRedRecKCanon_of_redR hred))
  · intro hno
    exact ⟨famObsTransport_of_famFunctionNoTypeProbeAt hlam,
      famObsTransport_of_famFunctionNoTypeProbeAt hno⟩

/-- Constructor closure of `FamConvObsMotive (WhStepRecKCanon E)` for `ConvT.eta` from
    `FamFunctionNoTypeProbe (WhStepRecKCanon E) E n`. -/
theorem famConvObs_whStepRecKCanon_eta_of_functionNoTypeProbe
    (hno : FamFunctionNoTypeProbe (WhStepRecKCanon E) E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) :
    FamConvObsMotive (WhStepRecKCanon E) (.eta Γ f A B hf) :=
  (famObsEquiv_whStepRecKCanon_eta_iff_famFunctionNoTypeProbeAt A f).mpr (hno hΓ hf)

/-- Constructor closure of `FamConvObsMotive R` for `ConvT.irr` from local 3-head exclusions. -/
theorem famConvObs_irr_of_local_exclusions {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hnoP : FamFunctionNoTypeProbeAt R E n Γ p)
    (hnoQ : FamFunctionNoTypeProbeAt R E n Γ q) :
    FamConvObsMotive R (.irr Γ P p q hP hp hq) :=
  ⟨famObsTransport_of_famFunctionNoTypeProbeAt hnoP,
   famObsTransport_of_famFunctionNoTypeProbeAt hnoQ⟩

/-- Constructor closure of `FamConvObsMotive R` for `ConvT.irr` from `FamPropNoTypeProbe R E n`. -/
theorem famConvObs_irr_of_famPropNoTypeProbe (hno : FamPropNoTypeProbe R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    FamConvObsMotive R (.irr Γ P p q hP hp hq) :=
  famConvObs_irr_of_local_exclusions hP hp hq (hno hΓ hP hp) (hno hΓ hP hq)

/-- **3-Head Pointwise Realization in `ApproxT E (ctxEnvT E Γ)` (`FamProbeRealizedAtT`):**
    Extends `RcicNativePiProbeModelBoundary.ProbeRealizedAtT` with the 3rd type head: any
    observed saturated well-typed `.inductiveM` family spine `foldApps (.const r ls) xs` realizes
    `.spine r (botVecT xs)` in `ApproxT E (ctxEnvT E Γ)`. -/
def FamProbeRealizedAtT (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (M : Expr Nat) : Prop :=
  ProbeRealizedAtT R E n Γ M ∧
  ∀ r m ls xs w,
    E.members r = some m → m.mclass = .inductiveM →
    RedR R Γ M (foldApps (.const r ls) xs) →
    HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w) →
    xs.length = (piDomsOf m.mtype).length →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs →
    ApproxT E (ctxEnvT E Γ) M (.spine r (botVecT xs))

/-- Global 3-head realization over native typed expressions in well-formed contexts. -/
def FamTypedProbeRealizationT (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M I : Expr Nat},
    HasTyT E n Γ M I → FamProbeRealizedAtT R E n Γ M

/-- A Π-type `ElT E ρ (.pi A B)` has no `.spine r args` element compact (`not_elT_pi_spine`). -/
theorem not_elT_pi_spine {ρ : EnvT} {A B : Expr Nat} (r : Nat) (args : List CptT) :
    ¬ ElT E ρ (.pi A B) (.spine r args) := by
  intro h
  rcases elT_pi_element_shape h with h0 | ⟨g, hg⟩
  · exact CptT.noConfusion h0
  · exact CptT.noConfusion hg

/-- **Saturated 3-Head Type-Probe Compact Fragment (`FamSatProbeCptT E`):**
    Refines `FamProbeCptT E` by requiring `.spine r args` to be a **saturated** `.inductiveM`
    spine (`args.length = (piDomsOf m.mtype).length`). Every probe compact observed by
    `FamTypedProbeRealizationT`, `FamFunctionNoTypeProbe`, `FamPropNoTypeProbe`, and
    `famObsTransport_of_lrSCoreSL_probes` lies in `FamSatProbeCptT E`
    (`.bot`, `sortCode u`, `.pi .bot []`, and `.spine r (botVecT xs)` with
    `xs.length = (piDomsOf m.mtype).length`), while `FamSatProbeCptT E` excludes all `.lam g`
    compacts, all unsaturated `.inductiveM` spines (`args.length < (piDomsOf m.mtype).length`),
    and all `.constructorM`/`.axiomM` spines! -/
inductive FamSatProbeCptT (E : ResolvedEnv) : CptT → Prop
  | bot : FamSatProbeCptT E .bot
  | prop : FamSatProbeCptT E .prop
  | sort : FamSatProbeCptT E .sort
  | piBotNil : FamSatProbeCptT E (.pi .bot [])
  | spine {r : Nat} {m : CheckedMember} {args : List CptT}
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
      (hlen : args.length = (piDomsOf m.mtype).length)
      (hbd : BotDemandT args) : FamSatProbeCptT E (.spine r args)

theorem famSatProbeCptT_to_famProbeCptT {c : CptT} (h : FamSatProbeCptT E c) :
    FamProbeCptT E c := by
  cases h with
  | bot => exact .bot
  | prop => exact .prop
  | sort => exact .sort
  | piBotNil => exact .piBotNil
  | spine hm hind _ hbd => exact .spine hm hind hbd

theorem famSatProbeCptT_sortCode (l : Level) : FamSatProbeCptT E (sortCode l) := by
  rcases sortCode_prop_or_sort l with h | h <;> (rw [h]; constructor)

theorem famSatProbeCptT_spine_botVecT {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {xs : List (Expr Nat)} (hlen : xs.length = (piDomsOf m.mtype).length) :
    FamSatProbeCptT E (.spine r (botVecT xs)) :=
  .spine hm hind (by rw [botVecT_length, hlen]) (botDemandT_botVecT xs)

/-- **Probe-Restricted Typing Realization Lemma (`FamProbeTypingLemmaT E n`):**
    Restricts `TypingLemmaT E n`'s term-evaluation clause to the saturated 3-head type-probe
    fragment `FamSatProbeCptT E u` together with the sort-zero proposition-ideal clause
    `HasTyT E n Γ P (.sort .zero) → ApproxT E (ctxEnvT E Γ) P a → IsPropCT E a`.
    Unlike unrestricted `TypingLemmaT E n` (which is refuted on every environment with an
    indexed/parameterized `.inductiveM` family by `not_typingLemmaT_of_inductiveM_posArity` and
    on every environment by `not_typingLemmaT_all` in §12 Part A), `FamProbeTypingLemmaT E n`
    excludes all `.lam g`, unsaturated `.inductiveM` spine, and `.constructorM`/`.axiomM` spine
    compacts and holds unconditionally across all 6 canonical RCIC expression families (§12 Part A),
    while sufficing directly for `famFunctionNoTypeProbe_of_typing_realization`,
    `famPropNoTypeProbe_of_typing_realization`, and `FamProbeAdapterInputsRKCanon`! -/
def FamProbeTypingLemmaT (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a A : Expr Nat}, HasTyT E n Γ a A →
    ∀ u, FamSatProbeCptT E u → ApproxT E (ctxEnvT E Γ) a u → ElT E (ctxEnvT E Γ) A u) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {P : Expr Nat}, HasTyT E n Γ P (.sort .zero) →
    ∀ a, ApproxT E (ctxEnvT E Γ) P a → IsPropCT E a)

theorem famProbeTypingLemmaT_of_typingLemmaT (hty : TypingLemmaT E n) :
    FamProbeTypingLemmaT E n :=
  ⟨fun {_} hΓ {_ _} ha u _ hap => hty hΓ ha u hap,
   fun {Γ} hΓ {_} hP a hap => by
     rcases (elT_sort_zero_iff E (ctxEnvT E Γ) a).mp (hty hΓ hP a hap) with rfl | h
     · exact .bot
     · exact h⟩

/-- **`FamProbeTypingLemmaT E n` + `FamTypedProbeRealizationT R E n` Implies `FamFunctionNoTypeProbe R E n`
    (`famFunctionNoTypeProbe_of_typing_realization`):** -/
theorem famFunctionNoTypeProbe_of_typing_realization
    (hty : FamProbeTypingLemmaT E n) (hreal : FamTypedProbeRealizationT R E n) :
    FamFunctionNoTypeProbe R E n := by
  intro Γ hΓ f A B hf
  have hr := hreal hΓ hf
  refine ⟨fun u hu => not_elT_pi_sortCode u
      (hty.1 hΓ hf _ (famSatProbeCptT_sortCode u) (hr.1.1 u hu)),
    fun C D hread hΓC => not_elT_pi_piProbe
      (hty.1 hΓ hf _ .piBotNil (hr.1.2 C D hread hΓC)),
    fun r m ls xs w hm hind hread hty_sp hlen hargs =>
      not_elT_pi_spine r (botVecT xs)
        (hty.1 hΓ hf _ (famSatProbeCptT_spine_botVecT hm hind hlen)
          (hr.2 r m ls xs w hm hind hread hty_sp hlen hargs))⟩

/-- **`FamProbeTypingLemmaT E n` + `FamTypedProbeRealizationT R E n` Implies `FamPropNoTypeProbe R E n`
    (`famPropNoTypeProbe_of_typing_realization`):** -/
theorem famPropNoTypeProbe_of_typing_realization
    (hty : FamProbeTypingLemmaT E n) (hreal : FamTypedProbeRealizationT R E n) :
    FamPropNoTypeProbe R E n := by
  intro Γ hΓ P p hP hp
  have hprop : ∀ a, ApproxT E (ctxEnvT E Γ) P a → IsPropCT E a :=
    fun a ha => hty.2 hΓ hP a ha
  have hbot : ∀ c, FamSatProbeCptT E c → ApproxT E (ctxEnvT E Γ) p c → c = .bot :=
    fun c hc hap => elT_bot_of_propIdeal hprop (hty.1 hΓ hp c hc hap)
  have hr := hreal hΓ hp
  refine ⟨fun u hu => sortCode_ne_bot u
      (hbot _ (famSatProbeCptT_sortCode u) (hr.1.1 u hu)),
    fun A B hread hΓA => CptT.noConfusion
      (hbot _ .piBotNil (hr.1.2 A B hread hΓA)),
    fun r m ls xs w hm hind hread hty_sp hlen hargs =>
      CptT.noConfusion
        (hbot _ (famSatProbeCptT_spine_botVecT hm hind hlen)
          (hr.2 r m ls xs w hm hind hread hty_sp hlen hargs))⟩

/-- Local 3-head realization witness for `.sort u` at any `R` satisfying `ReadbackLaws E R`. -/
theorem famProbeRealizedAt_sort (hL : ReadbackLaws E R) (Γ : LCtx) (u : Level) :
    FamProbeRealizedAtT R E n Γ (.sort u) := by
  refine ⟨⟨fun v hread => ?_, fun _ _ hread _ =>
      (Expr.noConfusion (redR_sort_eq hL hread) : False).elim⟩,
    fun _ _ _ _ _ _ _ hread _ _ _ =>
      (TypedModelAudit.foldApps_const_ne_sort _ _ (redR_sort_eq hL hread)).elim⟩
  have heq := Expr.sort.inj (redR_sort_eq hL hread)
  subst v
  exact .sort _ _

/-- Local 3-head realization witness for `.pi A B` at any `R` satisfying `ReadbackLaws E R`. -/
theorem famProbeRealizedAt_pi (hL : ReadbackLaws E R) (Γ : LCtx) (A B : Expr Nat) :
    FamProbeRealizedAtT R E n Γ (.pi A B) :=
  ⟨⟨fun _ hread => (Expr.noConfusion (redR_pi_eq hL hread) : False).elim,
    fun _ _ _ _ => approxT_pi_bot_nil _ _ _ _⟩,
   fun _ _ _ _ _ _ _ hread _ _ _ =>
     (TypedModelAudit.foldApps_const_ne_pi _ _ _ (redR_pi_eq hL hread)).elim⟩

/-- Local 3-head realization witness for any admitted `.inductiveM` family spine
    `foldApps (.const r ls) xs` at any `R` satisfying `ReadbackLaws E R`. -/
theorem famProbeRealizedAt_famApp (hL : ReadbackLaws E R) (hW : EnvWfT E) (Γ : LCtx)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (ls : List Level) (xs : List (Expr Nat)) :
    FamProbeRealizedAtT R E n Γ (foldApps (.const r ls) xs) := by
  refine ⟨⟨fun _ hread =>
      (TypedModelAudit.foldApps_const_ne_sort _ _
        (redR_famApp_eq hL hW hm hind hread).symm).elim,
    fun _ _ hread _ =>
      (TypedModelAudit.foldApps_const_ne_pi _ _ _
        (redR_famApp_eq hL hW hm hind hread).symm).elim⟩,
    fun r' m' ls' xs' _ _ _ hread _ _ _ => ?_⟩
  have heq := redR_famApp_eq hL hW hm hind hread
  obtain ⟨hconst, hxs⟩ := foldApps_const_inj heq
  injection hconst with hr _
  subst hr; subst hxs
  exact approxT_famApp_botVecT hW (ctxEnvT E Γ) hm hind ls xs'

/-- Contextual head-action port for `ConvT.app` in the 3-observation motive `FamObsEquiv`. -/
def FamAppHeadAction (R : Readback) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g A B : Expr Nat} (_hf : ConvT E n Γ f g (.pi A B)) : Prop :=
  ∀ {a : Expr Nat}, HasTyT E n Γ a A →
    FamObsEquiv R E n Γ (.app f a) (.app g a)

/-- Contextual argument-action port for `ConvT.app` in the 3-observation motive `FamObsEquiv`. -/
def FamAppArgAction (R : Readback) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {g A B : Expr Nat} (_hg : HasTyT E n Γ g (.pi A B)) : Prop :=
  ∀ {a b : Expr Nat}, ConvT E n Γ a b A →
    FamObsEquiv R E n Γ (.app g a) (.app g b)

/-- **`NormalUniqueR`-Free `ConvT.app` Composition from `FamAppHeadAction` + `FamAppArgAction`
    (`famConvObs_app_of_actions`):** -/
theorem famConvObs_app_of_actions (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B : Expr Nat}
    (hf : ConvT E n Γ f g (.pi A B)) (ha : ConvT E n Γ a b A)
    (hhead : FamAppHeadAction R hf)
    (harg : FamAppArgAction R (convEnds hW hΓ hf).2.1) :
    FamConvObsMotive R (.app Γ f g a b A B hf ha) :=
  famObsEquiv_trans hW hΓ (hhead (convEnds hW hΓ ha).1) (harg ha)

/-- Endpoint replacement for `FamObsEquiv` (`famObsEquiv_iff_of_ends`). -/
theorem famObsEquiv_iff_of_ends (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N M' N' : Expr Nat}
    (hM : FamObsEquiv R E n Γ M M') (hN : FamObsEquiv R E n Γ N N') :
    FamObsEquiv R E n Γ M N ↔ FamObsEquiv R E n Γ M' N' :=
  ⟨fun h => famObsEquiv_trans hW hΓ (famObsEquiv_symm hM) (famObsEquiv_trans hW hΓ h hN),
   fun h => famObsEquiv_trans hW hΓ hM (famObsEquiv_trans hW hΓ h (famObsEquiv_symm hN))⟩

/-- At `WhStepRecKCanon E`, `FamObsEquiv` on two syntactic-lambda β-redexes is equivalent to
    `FamObsEquiv` on their instantiated bodies (`famObsEquiv_whStepRecKCanon_app_lam_iff_subst`). -/
theorem famObsEquiv_whStepRecKCanon_app_lam_iff_subst (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (D D' body body' a b : Expr Nat) :
    FamObsEquiv (WhStepRecKCanon E) E n Γ
        (.app (.lam D body) a) (.app (.lam D' body') b) ↔
      FamObsEquiv (WhStepRecKCanon E) E n Γ
        (instantiate0 a body) (instantiate0 b body') :=
  famObsEquiv_iff_of_ends hW hΓ
    (famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW) hW
      (.beta D body a))
    (famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW) hW
      (.beta D' body' b))

/-- At `WhStepRecKCanon E`, `FamObsEquiv` on two `letE` expressions is equivalent to `FamObsEquiv`
    on their instantiated bodies (`famObsEquiv_whStepRecKCanon_letE_iff_subst`). -/
theorem famObsEquiv_whStepRecKCanon_letE_iff_subst (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (A A' value value' body body' : Expr Nat) :
    FamObsEquiv (WhStepRecKCanon E) E n Γ
        (.letE A value body) (.letE A' value' body') ↔
      FamObsEquiv (WhStepRecKCanon E) E n Γ
        (instantiate0 value body) (instantiate0 value' body') :=
  famObsEquiv_iff_of_ends hW hΓ
    (famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW) hW
      (.zeta A value body))
    (famObsEquiv_of_stepR (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW) hW
      (.zeta A' value' body'))

/-- Localized mixed-substitution edges for the 3-observation motive `FamObsEquiv`
    (`FamMixedSubstEdges`). -/
def FamMixedSubstEdges (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (value value' body body' : Expr Nat) : Prop :=
  FamObsEquiv R E n Γ (instantiate0 value body) (instantiate0 value body') ∧
  FamObsEquiv R E n Γ (instantiate0 value body') (instantiate0 value' body')

theorem famObsEquiv_subst_of_edges (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {value value' body body' : Expr Nat}
    (h : FamMixedSubstEdges R E n Γ value value' body body') :
    FamObsEquiv R E n Γ (instantiate0 value body) (instantiate0 value' body') :=
  famObsEquiv_trans hW hΓ h.1 h.2

theorem famConvObs_whStepRecKCanon_app_lam_of_mixedSubst (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {D D' body body' a b A B : Expr Nat}
    (hf : ConvT E n Γ (.lam D body) (.lam D' body') (.pi A B))
    (ha : ConvT E n Γ a b A)
    (hsubst : FamMixedSubstEdges (WhStepRecKCanon E) E n Γ a b body body') :
    FamConvObsMotive (WhStepRecKCanon E)
      (.app Γ (.lam D body) (.lam D' body') a b A B hf ha) :=
  (famObsEquiv_whStepRecKCanon_app_lam_iff_subst hW hΓ D D' body body' a b).mpr
    (famObsEquiv_subst_of_edges hW hΓ hsubst)

theorem famConvObs_whStepRecKCanon_letE_of_mixedSubst (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' value value' body body' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ value value' A)
    (hb : ConvT E n (.letBinding A value :: Γ) body body' B)
    (hsubst : FamMixedSubstEdges (WhStepRecKCanon E) E n Γ value value' body body') :
    FamConvObsMotive (WhStepRecKCanon E)
      (.letE Γ A A' value value' body body' B u hA hv hb) :=
  (famObsEquiv_whStepRecKCanon_letE_iff_subst hW hΓ A A' value value' body body').mpr
    (famObsEquiv_subst_of_edges hW hΓ hsubst)

theorem famMixedSubstEdges_refl (Γ : LCtx) (value body : Expr Nat) :
    FamMixedSubstEdges R E n Γ value value body body :=
  ⟨famObsEquiv_refl Γ _, famObsEquiv_refl Γ _⟩

theorem famMixedSubstEdges_lift {Γ : LCtx} {M N : Expr Nat}
    (hMN : FamObsEquiv R E n Γ M N) (value value' : Expr Nat) :
    FamMixedSubstEdges R E n Γ value value' (lift 0 1 M) (lift 0 1 N) := by
  have hcancel (v X : Expr Nat) : instantiate0 v (lift 0 1 X) = X := by
    simpa only [instantiate0, Nat.sub_self, lift_zero] using
      (instantiate_lift_cancel 1 0 0 v (Nat.le_refl 0) (by decide) X)
  exact ⟨by simpa only [hcancel] using hMN, by simpa only [hcancel] using famObsEquiv_refl Γ N⟩

theorem famAppHeadAction_refl {Γ : LCtx} {f A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) :
    FamAppHeadAction R (.refl Γ f (.pi A B) hf) :=
  fun _ => famObsEquiv_refl Γ _

theorem famAppArgAction_whStepRecKCanon_lam_lift (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {D M A B : Expr Nat}
    (hf : HasTyT E n Γ (.lam D (lift 0 1 M)) (.pi A B)) :
    FamAppArgAction (WhStepRecKCanon E) hf := by
  intro a b _
  apply (famObsEquiv_whStepRecKCanon_app_lam_iff_subst hW hΓ D D (lift 0 1 M) (lift 0 1 M) a b).mpr
  exact famObsEquiv_subst_of_edges hW hΓ (famMixedSubstEdges_lift (famObsEquiv_refl Γ M) a b)

/-- **Unconditional `FamObsEquiv` on Partial Admitted `.inductiveM` Spines
    (`famObsEquiv_famSpine_partial`):**
    Under `ReadbackLaws E R` and `EnvWfT E`, any two non-saturated `.inductiveM` spines
    (`xs.length ≠ (piDomsOf m.mtype).length` and `xs'.length ≠ (piDomsOf m'.mtype).length`) are
    normal and have no Sort, Π, or *saturated* family-spine readbacks, so they satisfy
    `FamObsEquiv R E n Γ` unconditionally! -/
theorem famObsEquiv_famSpine_partial (hL : ReadbackLaws E R) (hW : EnvWfT E) {Γ : LCtx}
    {r r' : Nat} {m m' : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hm' : E.members r' = some m') (hind' : m'.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    (hne : xs.length ≠ (piDomsOf m.mtype).length)
    (hne' : xs'.length ≠ (piDomsOf m'.mtype).length) :
    FamObsEquiv R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r' ls') xs') := by
  have hno {r₁ : Nat} {m₁ : CheckedMember} (hm₁ : E.members r₁ = some m₁)
      (hind₁ : m₁.mclass = .inductiveM) (ls₁ : List Level) {xs₁ : List (Expr Nat)}
      (hne₁ : xs₁.length ≠ (piDomsOf m₁.mtype).length) :
      FamFunctionNoTypeProbeAt R E n Γ (foldApps (.const r₁ ls₁) xs₁) := by
    refine ⟨fun _ h => TypedModelAudit.foldApps_const_ne_sort _ _ (redR_famApp_eq hL hW hm₁ hind₁ h).symm,
      fun _ _ h _ => TypedModelAudit.foldApps_const_ne_pi _ _ _ (redR_famApp_eq hL hW hm₁ hind₁ h).symm,
      fun r₀ m₀ ls₀ xs₀ _ hm₀ _ h _ hlen₀ _ => ?_⟩
    have heq := redR_famApp_eq hL hW hm₁ hind₁ h
    obtain ⟨hconst, hxs⟩ := foldApps_const_inj heq
    injection hconst with hr _
    subst hr; subst hxs
    have em : m₀ = m₁ := Option.some.inj (hm₀.symm.trans hm₁)
    subst em
    exact hne₁ hlen₀
  exact ⟨famObsTransport_of_famFunctionNoTypeProbeAt (hno hm hind ls hne),
    famObsTransport_of_famFunctionNoTypeProbeAt (hno hm' hind' ls' hne')⟩

/-- **Step-by-Step `ConvT.app` on Partial `.inductiveM` Spines in `FamObsEquiv`
    (`famObsEquiv_famSpine_step_app_partial`):** -/
theorem famObsEquiv_famSpine_step_app_partial (hL : ReadbackLaws E R) (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {x x' : Expr Nat}
    (hlt : (xs ++ [x]).length < (piDomsOf m.mtype).length)
    (hlen : (xs' ++ [x']).length = (xs ++ [x]).length) :
    FamObsEquiv R E n Γ
      (.app (foldApps (.const r ls) xs) x)
      (.app (foldApps (.const r ls') xs') x') := by
  have h := famObsEquiv_famSpine_partial (R := R) (E := E) (n := n) (Γ := Γ)
    (ls := ls) (ls' := ls') hL hW hm hind hm hind
    (Nat.ne_of_lt hlt) (hlen ▸ Nat.ne_of_lt hlt)
  simpa only [foldApps_snoc] using h

/-- **Step-by-Step `ConvT.app` Reaching a Saturated `.inductiveM` Spine in `FamObsEquiv`
    (`famObsEquiv_famSpine_step_app_saturated`):**
    Appending `a, a'` with `ConvT E n Γ a a' A` where `instTelescope (instantiateLevels ls m.mtype) xs = .pi A B`
    produces `FamObsEquiv R E n Γ (.app (foldApps (.const r ls) xs) a) (.app (foldApps (.const r ls') xs') a')`
    under `ReadbackLaws E R` and `EnvWfT E` alone (with **zero** `NormalUniqueR R` and **zero** `PiRowField`)! -/
theorem famObsEquiv_famSpine_step_app_saturated (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    {A B a a' : Expr Nat} {w w' : Level}
    (heqN : eqNList ls ls')
    (hpre : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs')
    (hpi : instTelescope (instantiateLevels ls m.mtype) xs = .pi A B)
    (ha : ConvT E n Γ a a' A)
    (hlen : (xs ++ [a]).length = (piDomsOf m.mtype).length)
    (hty : HasTyT E n Γ (.app (foldApps (.const r ls) xs) a) (.sort w))
    (hty' : HasTyT E n Γ (.app (foldApps (.const r ls') xs') a') (.sort w')) :
    FamObsEquiv R E n Γ
      (.app (foldApps (.const r ls) xs) a)
      (.app (foldApps (.const r ls') xs') a') := by
  have hty_sp : HasTyT E n Γ (foldApps (.const r ls) (xs ++ [a])) (.sort w) := by
    simpa only [foldApps_snoc] using hty
  have hty_sp' : HasTyT E n Γ (foldApps (.const r ls') (xs' ++ [a'])) (.sort w') := by
    simpa only [foldApps_snoc] using hty'
  have hlen_xs : xs.length = xs'.length := convArgsT_length_eq hpre
  have hlen' : (xs' ++ [a']).length = (piDomsOf m.mtype).length := by
    simp only [List.length_append, List.length_singleton] at hlen ⊢
    omega
  have hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) (xs ++ [a]) (xs' ++ [a']) :=
    convArgsT_snoc hpre hpi ha
  simpa only [foldApps_snoc] using
    famObsEquiv_famSpine_of_convArgsT hL hW hΓ hm hind hty_sp hty_sp' heqN hlen hlen' hargs

private theorem famConvObs_whStepRecKCanon_of_four_ports_aux (hW : EnvWfT E)
    (hApp : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f g a b A B : Expr Nat}
      (hf : ConvT E n Γ f g (.pi A B)) (ha : ConvT E n Γ a b A),
      FamConvObsMotive (WhStepRecKCanon E) hf →
      FamConvObsMotive (WhStepRecKCanon E) ha →
      FamConvObsMotive (WhStepRecKCanon E) (.app Γ f g a b A B hf ha))
    (hLetE : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' v v' b b' B : Expr Nat} {u : Level}
      (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ v v' A)
      (hb : ConvT E n (.letBinding A v :: Γ) b b' B),
      FamConvObsMotive (WhStepRecKCanon E) hA →
      FamConvObsMotive (WhStepRecKCanon E) hv →
      FamConvObsMotive (WhStepRecKCanon E) hb →
      FamConvObsMotive (WhStepRecKCanon E) (.letE Γ A A' v v' b b' B u hA hv hb))
    (hEta : FamFunctionNoTypeProbe (WhStepRecKCanon E) E n)
    (hIrr : FamPropNoTypeProbe (WhStepRecKCanon E) E n) :
    {Γ : LCtx} → {M N A : Expr Nat} → (hc : ConvT E n Γ M N A) →
      CtxWfT E n Γ → FamConvObsMotive (WhStepRecKCanon E) hc
  | _, _, _, _, .refl Γ M A h, _ => famConvObs_refl Γ M A h
  | _, _, _, _, .symm _ _ _ _ hc, hΓ =>
      famConvObs_symm hc
        (famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr hc hΓ)
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂, hΓ =>
      famConvObs_trans hW hΓ h₁ h₂
        (famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr h₁ hΓ)
        (famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr h₂ hΓ)
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg, _ =>
      famConvObs_beta (readbackLaws_whStepRecKCanon E) (detR_whStepRecKCanon hW)
        hW hA hbody harg
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hbody, _ =>
      famConvObs_whStepRecKCanon_zeta hW hA hv hbody
  | _, _, _, _, .zetaLocal _ _ _ _ hv hA hty, _ =>
      famConvObs_whStepRecKCanon_zetaLocal hW hv hA hty
  | _, _, _, _, .delta _ _ _ _ _ hm hb htr hlen hwf hty, _ =>
      famConvObs_whStepRecKCanon_delta hW hm hb htr hlen hwf hty
  | _, _, _, _, .iota _ _ _ _ hI _ _, _ =>
      famConvObs_whStepRecKCanon_iota hW (derivedIotaU_ofDerivedIota hI)
  | _, _, _, _, .lit _ _ _ _ hexp hty, _ =>
      famConvObs_whStepRecKCanon_lit hW hexp hty
  | _, _, _, _, .app _ _ _ _ _ _ _ hf ha, hΓ =>
      hApp hΓ hf ha
        (famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr hf hΓ)
        (famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr ha hΓ)
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hB, _ =>
      famConvObs_whStepRecKCanon_lam hA hB
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, hΓ =>
      famConvObs_pi (readbackLaws_whStepRecKCanon E) hW hΓ hA hB
  | _, _, _, _, .letE Γ A _ v _ _ _ _ _ hA hv hb, hΓ =>
      have hAu := (convEnds hW hΓ hA).1
      have hvu := (convEnds hW hΓ hv).1
      have hΓv : CtxWfT E n (.letBinding A v :: Γ) := .letBinding Γ A _ v hΓ hAu hvu
      hLetE hΓ hA hv hb
        (famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr hA hΓ)
        (famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr hv hΓ)
        (famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr hb hΓv)
  | _, _, _, _, .sorts Γ u v heq, _ =>
      famConvObs_sorts (readbackLaws_whStepRecKCanon E) Γ u v heq
  | _, _, _, _, .consts _ _ _ _ _ hm hlen hls hls' heq, hΓ =>
      famConvObs_whStepRecKCanon_consts hW hΓ hm hlen hls hls' heq
  | _, _, _, _, .eta _ _ _ _ hf, hΓ =>
      famConvObs_whStepRecKCanon_eta_of_functionNoTypeProbe hEta hΓ hf
  | _, _, _, _, .irr _ _ _ _ hP hp hq, hΓ =>
      famConvObs_irr_of_famPropNoTypeProbe hIrr hΓ hP hp hq
  | _, _, _, _, .tyConv _ _ _ _ _ _ hc hA, hΓ =>
      famConvObs_tyConv hc hA
        (famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr hc hΓ)

/-- **Complete 18-Constructor `ConvT` Closure Packager for `FamConvObsMotive (WhStepRecKCanon E)`
    (`famObsConvLinks_whStepRecKCanon_of_four_ports`):**
    At `WhStepRecKCanon E`, **14 of the 18** native `ConvT` constructors (`refl`, `symm`, `trans`,
    `tyConv`, `sorts`, `pi`, `beta`, `zeta`, `zetaLocal`, `delta`, `iota`, `lit`, `lam`, `consts`)
    are **unconditionally closed** under `EnvWfT E` alone (including both forward and reverse `iota`
    via `detR_whStepRecKCanon`). Supplying the remaining 4 constructor ports (`app`, `letE`, `eta`,
    `irr`) immediately yields `FamObsConvLinks (WhStepRecKCanon E) E n` (and hence `PiRowField E n`,
    `FamAppRowLink E n`, `FamRelevantSlotConv E n`, and `TypedRowsWf E n`)! -/
theorem famObsConvLinks_whStepRecKCanon_of_four_ports (hW : EnvWfT E)
    (hApp : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f g a b A B : Expr Nat}
      (hf : ConvT E n Γ f g (.pi A B)) (ha : ConvT E n Γ a b A),
      FamConvObsMotive (WhStepRecKCanon E) hf →
      FamConvObsMotive (WhStepRecKCanon E) ha →
      FamConvObsMotive (WhStepRecKCanon E) (.app Γ f g a b A B hf ha))
    (hLetE : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' v v' b b' B : Expr Nat} {u : Level}
      (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ v v' A)
      (hb : ConvT E n (.letBinding A v :: Γ) b b' B),
      FamConvObsMotive (WhStepRecKCanon E) hA →
      FamConvObsMotive (WhStepRecKCanon E) hv →
      FamConvObsMotive (WhStepRecKCanon E) hb →
      FamConvObsMotive (WhStepRecKCanon E) (.letE Γ A A' v v' b b' B u hA hv hb))
    (hEta : FamFunctionNoTypeProbe (WhStepRecKCanon E) E n)
    (hIrr : FamPropNoTypeProbe (WhStepRecKCanon E) E n) :
    FamObsConvLinks (WhStepRecKCanon E) E n := by
  intro Γ hΓ M N u hc
  exact famConvObs_whStepRecKCanon_of_four_ports_aux hW hApp hLetE hEta hIrr hc hΓ


/-! #### §10 Part C — Positive Resolution of `RcicNativeTypedModelIotaSound`'s `Exists` Non-Proof-Field
    Witness `wEx` (`not_iotaSoundT_ex`) in `ApproxDI exEnv`, `WhStepRecKCanon exEnv`, `ApproxDIKCanon exEnv`,
    and `SemEqDIKCanon exEnv` -/

/-- **Unconditional `SemEqDI` Soundness on `RcicNativeTypedModelIotaSound.wEx` (`semEqDI_wEx`):**
    While `IotaSoundT exEnv` is refuted in `ApproxT` (`not_iotaSoundT_ex`) because `ApproxT.recursorProp`
    erases the non-proof witness field `w` of `Ex α p` to `[]`, `ApproxDI exEnv` satisfies
    `SemEqDI exEnv ρ (iotaLhsOfS wEx) (iotaRhsOfS wEx)` **unconditionally** for every environment
    `ρ : EnvI` (`approxDI_iotaS wEx ρ`)! -/
theorem semEqDI_wEx (ρ : EnvI) :
    SemEqDI exEnv ρ (iotaLhsOfS wEx) (iotaRhsOfS wEx) :=
  approxDI_iotaS wEx ρ

/-- `RigidConst exEnv 0` holds for the axiom `N : Sort 1` (`exAxMember`) in `exEnv`. -/
theorem rigidConst_exEnv_zero : RigidConst exEnv 0 := by
  intro m hm
  rw [exEnv_mem0] at hm
  obtain rfl := Option.some.inj hm
  exact ⟨Or.inl rfl, by decide⟩

/-- `ApproxDI exEnv ρ exFieldVal (.spine 0 [])` holds in every environment `ρ : EnvI`. -/
theorem approxDI_exFieldVal (ρ : EnvI) :
    ApproxDI exEnv ρ exFieldVal (.spine 0 []) :=
  .const ρ 0 [] rigidConst_exEnv_zero

/-- The contractum `iotaRhsOfS wEx = .app (.app exMinorArg exFieldVal) exFieldVal` has compact
    `.spine 0 []` in `ApproxDI exEnv ρ` for every `ρ : EnvI`. -/
theorem approxDI_exRhs (ρ : EnvI) :
    ApproxDI exEnv ρ (iotaRhsOfS wEx) (.spine 0 []) := by
  rw [wEx_rhs]
  refine .app (g := [([], .spine 0 [])]) (s := ([], .spine 0 [])) ?_
    (List.mem_singleton.mpr rfl) (fun _ hu => (List.not_mem_nil _ hu).elim)
  refine .app (g := [([.spine 0 []], .lam [([], .spine 0 [])])])
    (s := ([.spine 0 []], .lam [([], .spine 0 [])])) ?_
    (List.mem_singleton.mpr rfl)
    (fun u hu => by
      rw [List.mem_singleton] at hu
      subst hu
      exact approxDI_exFieldVal ρ)
  refine .lam (fun s hs => ?_)
  rw [List.mem_singleton] at hs
  subst hs
  refine .lam (fun t ht => ?_)
  rw [List.mem_singleton] at ht
  subst ht
  exact .bvar (List.mem_singleton.mpr rfl)

/-- **Positive Resolution of `not_approxT_exLhs` in `ApproxDI exEnv` (`approxDI_exLhs`):**
    Unlike `ApproxT` (`not_approxT_exLhs : ¬ ApproxT exEnv EnvT.bot (iotaLhsOfS wEx) (.spine 0 [])`),
    in `ApproxDI exEnv` the recursor source `iotaLhsOfS wEx` **does** have compact `.spine 0 []` in
    every environment `ρ : EnvI` (including `EnvI.bot` and `ctxEnvDI exEnv Γ`)! -/
theorem approxDI_exLhs (ρ : EnvI) :
    ApproxDI exEnv ρ (iotaLhsOfS wEx) (.spine 0 []) :=
  (semEqDI_wEx ρ (.spine 0 [])).mpr (approxDI_exRhs ρ)

/-- One-step `WhStepRecKCanon exEnv` reduction of `iotaLhsOfS wEx` to `iotaRhsOfS wEx`. -/
theorem whStepRecKCanon_wEx (Γ : LCtx) :
    WhStepRecKCanon exEnv Γ (iotaLhsOfS wEx) (iotaRhsOfS wEx) :=
  .iota (.ofUS wEx)

/-- Two-step `WhStepRecKCanon exEnv` β-reduction of `iotaRhsOfS wEx` to `exFieldVal = .const 0 []`. -/
theorem whRedRecKCanon_wEx_rhs_to_fieldVal (Γ : LCtx) :
    WhRedRecKCanon exEnv Γ (iotaRhsOfS wEx) exFieldVal := by
  rw [wEx_rhs]
  have hs1 : WhStepRecKCanon exEnv Γ
      (.app (.app exMinorArg exFieldVal) exFieldVal)
      (.app (.lam (.sort .zero) exFieldVal) exFieldVal) :=
    .appHead (.beta (.sort (.succ .zero)) (.lam (.sort .zero) (.bvar 1)) exFieldVal)
  have hs2 : WhStepRecKCanon exEnv Γ
      (.app (.lam (.sort .zero) exFieldVal) exFieldVal)
      exFieldVal :=
    .beta (.sort .zero) exFieldVal exFieldVal
  exact .step hs1 (.step hs2 (.refl exFieldVal))

/-- **3-Step `WhStepRecKCanon exEnv` Reduction of `iotaLhsOfS wEx` to `exFieldVal = .const 0 []`
    (`whRedRecKCanon_wEx_to_fieldVal`):** -/
theorem whRedRecKCanon_wEx_to_fieldVal (Γ : LCtx) :
    WhRedRecKCanon exEnv Γ (iotaLhsOfS wEx) exFieldVal :=
  .step (whStepRecKCanon_wEx Γ) (whRedRecKCanon_wEx_rhs_to_fieldVal Γ)

/-- Both `iotaLhsOfS wEx` and `iotaRhsOfS wEx` have compact `.spine 0 []` in `ApproxDIKCanon exEnv Γ`
    for every context `Γ : LCtx`! -/
theorem approxDIKCanon_exLhs (Γ : LCtx) :
    ApproxDIKCanon exEnv Γ (iotaLhsOfS wEx) (.spine 0 []) :=
  approxDIKCanon_of_approxDI (approxDI_exLhs (ctxEnvDI exEnv Γ))

theorem approxDIKCanon_exRhs (Γ : LCtx) :
    ApproxDIKCanon exEnv Γ (iotaRhsOfS wEx) (.spine 0 []) :=
  approxDIKCanon_of_approxDI (approxDI_exRhs (ctxEnvDI exEnv Γ))

/-- Even in `ApproxT exEnv`, when projected through `ElT` at any proposition type `P` (such as
    `Ex α p = foldApps (.const 1 []) [α, p]`), every element compact `c` of `P` is `.bot`,
    so `ElT exEnv ρ (foldApps (.const 1 []) [α, p])` agrees on both sides! -/
theorem elT_exEnv_famApp_bot (ρ : EnvT) (α p : Expr Nat) {c : CptT}
    (h : ElT exEnv ρ (foldApps (.const 1 []) [α, p]) c) : c = .bot := by
  have hrig : RigidConst exEnv 1 := by
    intro m hm
    rw [exEnv_mem1] at hm
    obtain rfl := Option.some.inj hm
    exact ⟨Or.inl rfl, by decide⟩
  refine elT_bot_of_propIdeal (fun u hu => ?_) h
  have hinv := approxT_foldApps_const_inductiveM_inv_aux (E := exEnv) (ρ := ρ) (r := 1) (pre := [])
    [α, p] (fun hd => (approxT_rigid_const_inv hrig hd).elim Or.inl (fun e => Or.inr ⟨[], e, .nil⟩)) hu
  rcases hinv with rfl | ⟨_, rfl, _⟩
  · exact .bot
  · exact .spine exEnv_mem1 rfl


/-! ### §11 — Level-Fact-Strengthened Unified Spine Relation `SpineClauseSL` / `LRSCoreSL` / `LRSSL`
    Resolving `#7673` Items 2.1–2.2 & §8 Part A, Unconditional `typedPERSL_of_envWfT`,
    3-Observation Typed-Relation Bridge & Spine-Growth Application / Substitution Adapters,
    and End-to-End 18-Constructor `WhStepRecKCanon` Assembly -/

/-! #### §11 Part A — `SpineClauseSL` / `LRSCoreSL` / `LRSSL` Over `CptT`, Automatic Sort-Typing & `TyConvT` Recovery (`hasTyT_famApp_both_of_levelFacts_convArgsT`), Exact Equivalence on `FamProbeCptT`, and Unconditional 5-Part Mutual PER (`typedPERSL_of_envWfT`) Under `EnvWfT E` Alone -/

/-- **Automatic Recovery of Right Saturation, Both Sort Typings, and `TyConvT` for Any Saturated
    Admitted `.inductiveM` Spine from Level Facts and `ConvArgsT`
    (`hasTyT_famApp_both_of_levelFacts_convArgsT`):**
    Under `EnvWfT E` and `CtxWfT E n Γ`, whenever `E.members r = some m` with `m.mclass = .inductiveM`,
    `ls₁.length = m.arity`, `levelsBounded n ls₁ = true`, `levelsBounded n ls₂ = true`, `eqNList ls₁ ls₂`,
    `xs₁.length = (piDomsOf m.mtype).length`, and `ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs₁ xs₂`,
    a single call to `convT_famApp_of_convArgsT` + `convEnds` yields:
    1. `xs₂.length = (piDomsOf m.mtype).length`,
    2. both sort typings `HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.sort w₁)` and
       `HasTyT E n Γ (foldApps (.const r ls₂) xs₂) (.sort w₂)`, and
    3. `Nonempty (TyConvT E n Γ (foldApps (.const r ls₁) xs₁) (foldApps (.const r ls₂) xs₂))`! -/
theorem hasTyT_famApp_both_of_levelFacts_convArgsT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls₁ ls₂ : List Level} {xs₁ xs₂ : List (Expr Nat)}
    (hlen : ls₁.length = m.arity) (hbel₁ : levelsBounded n ls₁ = true)
    (hbel₂ : levelsBounded n ls₂ = true) (heqN : eqNList ls₁ ls₂)
    (hxs₁ : xs₁.length = (piDomsOf m.mtype).length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs₁ xs₂) :
    xs₂.length = (piDomsOf m.mtype).length ∧
    (∃ w₁ w₂,
      Nonempty (HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.sort w₁)) ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls₂) xs₂) (.sort w₂))) ∧
    Nonempty (TyConvT E n Γ (foldApps (.const r ls₁) xs₁) (foldApps (.const r ls₂) xs₂)) := by
  have hxs₂ : xs₂.length = (piDomsOf m.mtype).length :=
    (convArgsT_length_eq hargs).symm.trans hxs₁
  obtain ⟨hc⟩ := convT_famApp_of_convArgsT hW hm hind hlen hbel₁ hbel₂ heqN hxs₁ hargs
  obtain ⟨hty₁, hty₂, _⟩ := convEnds hW hΓ hc
  exact ⟨hxs₂, ⟨_, _, ⟨hty₁⟩, ⟨hty₂⟩⟩, ⟨.of Γ _ _ _ hc⟩⟩

/-- **Level-Fact-Strengthened Unified Spine Clause Over `CptT` (`SpineClauseSL`):**
    Directly resolves `#7673#issuecomment-6271576104` Items 2.1 & 2.2 together with §8 Part A's
    `not_allMember_convArgsT_length_le_piDoms` obstruction:
    - Incorporates `ls₁.length = m.arity ∧ levelsBounded n ls₁ = true ∧ levelsBounded n ls₂ = true`
      (Item 2.1) and `xs₁.length ≤ (piDomsOf m.mtype).length` (automatic for every `NonBvarTail m.mtype`
      member and in particular every `.inductiveM` member by `convArgsT_length_le_piDoms_of_inductiveM`,
      avoiding the polymorphic-axiom counterexample `polyAxEnv`).
    - Consequently, `SpineClauseSL` is symmetric and transitive at **every** ambient index `A : Expr Nat`
      under `EnvWfT E` and `CtxWfT E n Γ` alone (`spineClauseSL_symm`, `spineClauseSL_trans`) — with
      **zero** external `ConvArgsSymmS` / `ConvArgsTransS` / `PiRowField` premises! -/
def SpineClauseSL (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (M M' A : Expr Nat) (r : Nat) (args : List CptT) : Prop :=
  ((Nonempty (TyConvT E n Γ M M') ∧ ((∃ l, RedR R Γ A (.sort l)) ∨ Nonempty (ConvT E n Γ M M' A))) ∨
    ((∀ l, ¬ RedR R Γ A (.sort l)) ∧ Nonempty (ConvT E n Γ M M' A))) ∧
  ((∃ (m : CheckedMember) (ls₁ ls₂ : List Level) (xs₁ xs₂ : List (Expr Nat)),
      E.members r = some m ∧
      ls₁.length = m.arity ∧
      levelsBounded n ls₁ = true ∧
      levelsBounded n ls₂ = true ∧
      xs₁.length ≤ (piDomsOf m.mtype).length ∧
      RedR R Γ M (foldApps (.const r ls₁) xs₁) ∧
      RedR R Γ M' (foldApps (.const r ls₂) xs₂) ∧
      NormalR R Γ (foldApps (.const r ls₁) xs₁) ∧
      NormalR R Γ (foldApps (.const r ls₂) xs₂) ∧
      eqNList ls₁ ls₂ ∧
      args.length ≤ xs₁.length ∧
      args.length ≤ xs₂.length ∧
      ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs₁ xs₂) ∨
    ((∀ m, E.members r = some m → False) ∧
      ∃ (ls₁ ls₂ : List Level) (xs₁ xs₂ : List (Expr Nat)),
        RedR R Γ M (foldApps (.const r ls₁) xs₁) ∧
        RedR R Γ M' (foldApps (.const r ls₂) xs₂) ∧
        NormalR R Γ (foldApps (.const r ls₁) xs₁) ∧
        NormalR R Γ (foldApps (.const r ls₂) xs₂) ∧
        args.length ≤ xs₁.length ∧
        args.length ≤ xs₂.length))

/-- Constructor for `SpineClauseSL` at any member with `NonBvarTail m.mtype` (in particular any
    `.inductiveM` member by `nonBvarTail_of_inductiveM`): `xs₁.length ≤ (piDomsOf m.mtype).length`
    is derived automatically from `ConvArgsT` via `convArgsT_length_le_piDoms_of_nonBvarTail`. -/
theorem spineClauseSL_of_nonBvarTail {Γ : LCtx} {M M' A : Expr Nat} {r : Nat} {args : List CptT}
    {m : CheckedMember} {ls₁ ls₂ : List Level} {xs₁ xs₂ : List (Expr Nat)}
    (hidx : (Nonempty (TyConvT E n Γ M M') ∧
        ((∃ l, RedR R Γ A (.sort l)) ∨ Nonempty (ConvT E n Γ M M' A))) ∨
      ((∀ l, ¬ RedR R Γ A (.sort l)) ∧ Nonempty (ConvT E n Γ M M' A)))
    (hm : E.members r = some m) (hnb : NonBvarTail m.mtype)
    (hlen₁ : ls₁.length = m.arity)
    (hbel₁ : levelsBounded n ls₁ = true) (hbel₂ : levelsBounded n ls₂ = true)
    (h1 : RedR R Γ M (foldApps (.const r ls₁) xs₁))
    (h2 : RedR R Γ M' (foldApps (.const r ls₂) xs₂))
    (hn1 : NormalR R Γ (foldApps (.const r ls₁) xs₁))
    (hn2 : NormalR R Γ (foldApps (.const r ls₂) xs₂))
    (heqN : eqNList ls₁ ls₂)
    (ha1 : args.length ≤ xs₁.length) (ha2 : args.length ≤ xs₂.length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs₁ xs₂) :
    SpineClauseSL R E n Γ M M' A r args :=
  ⟨hidx, Or.inl ⟨m, ls₁, ls₂, xs₁, xs₂, hm, hlen₁, hbel₁, hbel₂,
    convArgsT_length_le_piDoms_of_nonBvarTail hnb hargs,
    h1, h2, hn1, hn2, heqN, ha1, ha2, hargs⟩⟩

/-- **Symmetry of `SpineClauseSL` at Every Ambient Index `A : Expr Nat` Under `EnvWfT E` Alone
    (`spineClauseSL_symm`):** -/
theorem spineClauseSL_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A : Expr Nat} {r : Nat} {args : List CptT}
    (h : SpineClauseSL R E n Γ M M' A r args) :
    SpineClauseSL R E n Γ M' M A r args := by
  refine ⟨?_, ?_⟩
  · rcases h.1 with ⟨⟨htyc⟩, hsub⟩ | ⟨hns, ⟨hconv⟩⟩
    · rcases hsub with hsort | hne
      · exact Or.inl ⟨⟨htyc.symmT⟩, Or.inl hsort⟩
      · obtain ⟨hconv⟩ := hne
        exact Or.inl ⟨⟨htyc.symmT⟩, Or.inr ⟨.symm _ _ _ _ hconv⟩⟩
    · exact Or.inr ⟨hns, ⟨.symm _ _ _ _ hconv⟩⟩
  · rcases h.2 with ⟨m, ls₁, ls₂, xs₁, xs₂, hm, hlen₁, hbel₁, hbel₂, hbnd₁,
        h1, h2, hn1, hn2, heqN, ha1, ha2, hargs⟩ |
      ⟨hnone, ls₁, ls₂, xs₁, xs₂, h1, h2, hn1, hn2, ha1, ha2⟩
    · have hlen₂ : ls₂.length = m.arity := (eqNList_length ls₁ ls₂ heqN).symm.trans hlen₁
      have hbnd₂ : xs₂.length ≤ (piDomsOf m.mtype).length :=
        (convArgsT_length_eq hargs) ▸ hbnd₁
      exact Or.inl ⟨m, ls₂, ls₁, xs₂, xs₁, hm, hlen₂, hbel₂, hbel₁, hbnd₂,
        h2, h1, hn2, hn1, eqNList_symm'' heqN, ha2, ha1,
        convArgs_symm_member_of_levelFacts hW hΓ hm hlen₁ hbel₁ hlen₂ hbel₂ heqN hbnd₁ hargs⟩
    · exact Or.inr ⟨hnone, ls₂, ls₁, xs₂, xs₁, h2, h1, hn2, hn1, ha2, ha1⟩

/-- **Transitivity of `SpineClauseSL` at Every Ambient Index `A : Expr Nat` Under `NormalUniqueR R`
    and `EnvWfT E` Alone (`spineClauseSL_trans`):** -/
theorem spineClauseSL_trans (hNU : NormalUniqueR R) (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' M'' A : Expr Nat} {r : Nat} {args : List CptT}
    (h₁ : SpineClauseSL R E n Γ M M' A r args)
    (h₂ : SpineClauseSL R E n Γ M' M'' A r args) :
    SpineClauseSL R E n Γ M M'' A r args := by
  refine ⟨?_, ?_⟩
  · rcases h₁.1 with ⟨⟨ht₁⟩, hs₁⟩ | ⟨hns, ⟨hc₁⟩⟩
    · rcases h₂.1 with ⟨⟨ht₂⟩, hs₂⟩ | ⟨hns, ⟨hc₂⟩⟩
      · rcases hs₁ with hsort | hne₁
        · exact Or.inl ⟨⟨.trans _ _ _ _ ht₁ ht₂⟩, Or.inl hsort⟩
        · obtain ⟨hc₁⟩ := hne₁
          rcases hs₂ with hsort | hne₂
          · exact Or.inl ⟨⟨.trans _ _ _ _ ht₁ ht₂⟩, Or.inl hsort⟩
          · obtain ⟨hc₂⟩ := hne₂
            exact Or.inl ⟨⟨.trans _ _ _ _ ht₁ ht₂⟩, Or.inr ⟨.trans _ _ _ _ _ hc₁ hc₂⟩⟩
      · rcases hs₁ with ⟨l, hl⟩ | hne₁
        · exact (hns l hl).elim
        · obtain ⟨hc₁⟩ := hne₁
          exact Or.inr ⟨hns, ⟨.trans _ _ _ _ _ hc₁ hc₂⟩⟩
    · rcases h₂.1 with ⟨_, hs₂⟩ | ⟨_, ⟨hc₂⟩⟩
      · rcases hs₂ with ⟨l, hl⟩ | hne₂
        · exact (hns l hl).elim
        · obtain ⟨hc₂⟩ := hne₂
          exact Or.inr ⟨hns, ⟨.trans _ _ _ _ _ hc₁ hc₂⟩⟩
      · exact Or.inr ⟨hns, ⟨.trans _ _ _ _ _ hc₁ hc₂⟩⟩
  · rcases h₁.2 with ⟨m, ls₁, ls₂, xs₁, xs₂, hm, hlen₁, hbel₁, hbel₂, hbnd₁,
        h1, h2, hn1, hn2, heqN, ha1, _, hargs⟩ |
      ⟨hnone, ls₁, ls₂, xs₁, xs₂, h1, h2, hn1, hn2, ha1, _⟩
    · rcases h₂.2 with ⟨m', ls₂', ls₃, xs₂', xs₃, hm', _, _, hbel₃, _,
          h2', h3, hn2', hn3, heqN', _, ha3, hargs'⟩ | ⟨hnone, _⟩
      · have em : m = m' := Option.some.inj (hm.symm.trans hm')
        subst em
        have e := hNU Γ h2 hn2 h2' hn2'
        obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
        injection hconst with _ hls
        subst hls; subst hxs
        have hlen₂ : ls₂.length = m.arity := (eqNList_length ls₁ ls₂ heqN).symm.trans hlen₁
        exact Or.inl ⟨m, ls₁, ls₃, xs₁, xs₃, hm, hlen₁, hbel₁, hbel₃, hbnd₁,
          h1, h3, hn1, hn3, eqNList_trans'' heqN heqN', ha1, ha3,
          convArgs_trans_member_of_levelFacts hW hΓ hm hlen₁ hbel₁ hlen₂ hbel₂ heqN hbnd₁ hargs hargs'⟩
      · exact (hnone m hm).elim
    · rcases h₂.2 with ⟨m, _, _, _, _, hm, _⟩ |
        ⟨_, ls₂', ls₃, xs₂', xs₃, h2', h3, hn2', hn3, _, ha3⟩
      · exact (hnone m hm).elim
      · have e := hNU Γ h2 hn2 h2' hn2'
        obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
        injection hconst with _ hls
        subst hls; subst hxs
        exact Or.inr ⟨hnone, ls₁, ls₃, xs₁, xs₃, h1, h3, hn1, hn3, ha1, ha3⟩

/-- Terms related by `SpineClauseSL` have normal constant-headed reducts and therefore never read
    back to a sort (`spineClauseSL_not_sort`). -/
theorem spineClauseSL_not_sort (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {M M' A : Expr Nat} {r : Nat} {args : List CptT}
    (h : SpineClauseSL R E n Γ M M' A r args) :
    (∀ l, ¬ RedR R Γ M (.sort l)) ∧ (∀ l, ¬ RedR R Γ M' (.sort l)) := by
  rcases h.2 with ⟨_, _, _, xs₁, xs₂, _, _, _, _, _, h1, h2, hn1, hn2, _⟩ |
    ⟨_, _, _, xs₁, xs₂, h1, h2, hn1, hn2, _⟩
  · exact ⟨not_redR_sort_of_normal hL hNU h1 hn1 (TypedModelAudit.foldApps_const_ne_sort xs₁),
      not_redR_sort_of_normal hL hNU h2 hn2 (TypedModelAudit.foldApps_const_ne_sort xs₂)⟩
  · exact ⟨not_redR_sort_of_normal hL hNU h1 hn1 (TypedModelAudit.foldApps_const_ne_sort xs₁),
      not_redR_sort_of_normal hL hNU h2 hn2 (TypedModelAudit.foldApps_const_ne_sort xs₂)⟩

/-- **The Level-Fact-Strengthened Logical Relation Over `CptT` (`LRSCoreSL`):**
    Replaces `LRSCoreT`'s `.spine r args` clause with `SpineClauseSL R E n Γ M M' A r args`. -/
def LRSCoreSL (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) :
    CptT → Prop
  | .bot => True
  | .prop => SortClauseT R Γ M M' A
  | .sort => SortClauseT R Γ M M' A
  | .pi a f => (∃ l, RedR R Γ A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ : Expr Nat, RedR R Γ M (.pi A₁ B₁) ∧ RedR R Γ M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        (∃ u₁, LRSCoreSL R E n Γ A₁ A₂ (.sort u₁) a) ∧
        ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) →
          ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCoreSL R E n Γ N N' A₁ u) →
          ∃ v, LRSCoreSL R E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort v) s.2
  | .lam g =>
      ∃ A₁ B₁ : Expr Nat, RedR R Γ A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCoreSL R E n Γ N N' A₁ u) →
          LRSCoreSL R E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
  | .spine r args => SpineClauseSL R E n Γ M M' A r args
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfT_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₃ := sizeOfT_snd_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfT_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₃ := sizeOfT_snd_lt s
       omega)

/-- Top-level proposition-collapsed counterpart of `LRSCoreSL` (`LRSSL`). -/
def LRSSL (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (M M' A : Expr Nat) (c : CptT) : Prop :=
  IsPropTyR R E n Γ A ∨ LRSCoreSL R E n Γ M M' A c

theorem lrSCoreSL_bot (Γ : LCtx) (M M' A : Expr Nat) : LRSCoreSL R E n Γ M M' A .bot := by
  rw [LRSCoreSL.eq_def]; trivial

theorem lrSCoreSL_prop_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreSL R E n Γ M M' A .prop ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreSL.eq_def]

theorem lrSCoreSL_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreSL R E n Γ M M' A .sort ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreSL.eq_def]

theorem lrSCoreSL_prop_iff_sort (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreSL R E n Γ M M' A .prop ↔ LRSCoreSL R E n Γ M M' A .sort :=
  (lrSCoreSL_prop_iff Γ M M' A).trans (lrSCoreSL_sort_iff Γ M M' A).symm

theorem lrSCoreSL_sortCode_iff {Γ : LCtx} {M M' A : Expr Nat} (l : Level) :
    LRSCoreSL R E n Γ M M' A (sortCode l) ↔ SortClauseT R Γ M M' A := by
  rcases sortCode_prop_or_sort l with h | h
  · rw [h, lrSCoreSL_prop_iff]
  · rw [h, lrSCoreSL_sort_iff]

theorem lrSCoreSL_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptT) :
    LRSCoreSL R E n Γ M M' A (.spine r args) ↔ SpineClauseSL R E n Γ M M' A r args := by
  rw [LRSCoreSL.eq_def]

/-- Sort-index irrelevance for `LRSCoreSL` (`lrSCoreSL_sortIdx_irrel`). -/
theorem lrSCoreSL_sortIdx_irrel (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {N N' A A' : Expr Nat} (hA : ∃ l, RedR R Γ A (.sort l)) (hA' : ∃ l, RedR R Γ A' (.sort l)) :
    (c : CptT) → LRSCoreSL R E n Γ N N' A c → LRSCoreSL R E n Γ N N' A' c
  | .bot, _ => lrSCoreSL_bot _ _ _ _
  | .prop, h => by
      rw [lrSCoreSL_prop_iff] at h
      rw [lrSCoreSL_prop_iff]
      exact ⟨hA', h.2⟩
  | .sort, h => by
      rw [lrSCoreSL_sort_iff] at h
      rw [lrSCoreSL_sort_iff]
      exact ⟨hA', h.2⟩
  | .pi a f, h => by
      rw [LRSCoreSL.eq_def] at h
      rw [LRSCoreSL.eq_def]
      exact ⟨hA', h.2⟩
  | .lam g, h => by
      rw [LRSCoreSL.eq_def] at h
      obtain ⟨A₁, B₁, hr, _⟩ := h
      obtain ⟨l, hl⟩ := hA
      exact (not_redR_pi_of_redR_sort hL hNU hl A₁ B₁ hr).elim
  | .spine r args, h => by
      rw [lrSCoreSL_spine_iff] at h ⊢
      rcases h.1 with ⟨htyc, _⟩ | ⟨hns, _⟩
      · exact ⟨Or.inl ⟨htyc, Or.inl hA'⟩, h.2⟩
      · obtain ⟨l, hl⟩ := hA
        exact (hns l hl).elim

/-- At `.pi .bot []`, `LRSCoreSL` is identically equivalent to `LRSCoreT` (`piProbeSL_iff_lrSCoreT`). -/
theorem piProbeSL_iff_lrSCoreT {Γ : LCtx} {M N A : Expr Nat} :
    LRSCoreSL R E n Γ M N A (.pi .bot []) ↔
      LRSCoreT R E n Γ M N A (.pi .bot []) := by
  rw [LRSCoreSL.eq_def, LRSCoreT.eq_def]
  constructor
  · rintro ⟨hA, A₁, B₁, A₂, B₂, hM, hN, hΓ, hdom, hcod, ⟨u, _⟩, _⟩
    exact ⟨hA, A₁, B₁, A₂, B₂, hM, hN, hΓ, hdom, hcod,
      ⟨u, lrSCoreT_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩
  · rintro ⟨hA, A₁, B₁, A₂, B₂, hM, hN, hΓ, hdom, hcod, ⟨u, _⟩, _⟩
    exact ⟨hA, A₁, B₁, A₂, B₂, hM, hN, hΓ, hdom, hcod,
      ⟨u, lrSCoreSL_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- At `.pi .bot []`, `LRSCoreSL` is identically equivalent to `LRSCore` (`piProbeSL_iff_lrSCore`). -/
theorem piProbeSL_iff_lrSCore {Γ : LCtx} {M N A : Expr Nat} :
    LRSCoreSL R E n Γ M N A (.pi .bot []) ↔
      LRSCore R E n Γ M N A (.pi .bot []) :=
  piProbeSL_iff_lrSCoreT.trans piProbe_typed_iff

/-- **Exact Equivalence of `LRSCoreSL` and `LRSCoreT` at Every Saturated `.inductiveM` Spine Probe
    (`famProbeSL_iff_lrSCoreT`):**
    For any admitted `.inductiveM` head `E.members r = some m`, `m.mclass = .inductiveM`, any demand list
    `args : List CptT` with `args.length = (piDomsOf m.mtype).length` (in particular `args = botVecT xs`),
    and any sort index `A` with `∃ l, RedR R Γ A (.sort l)`, `LRSCoreSL` and `LRSCoreT` are **logically
    equivalent (`↔`)** under `ReadbackLaws E R`, `EnvWfT E`, and `CtxWfT E n Γ`! -/
theorem famProbeSL_iff_lrSCoreT (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {args : List CptT} (hargs_len : args.length = (piDomsOf m.mtype).length)
    {M N A : Expr Nat} (hA : ∃ l, RedR R Γ A (.sort l)) :
    LRSCoreSL R E n Γ M N A (.spine r args) ↔
      LRSCoreT R E n Γ M N A (.spine r args) := by
  rw [lrSCoreSL_spine_iff, LRSCoreT.eq_def]
  constructor
  · intro h
    have htyc : Nonempty (TyConvT E n Γ M N) := by
      rcases h.1 with ⟨htyc, _⟩ | ⟨hns, _⟩
      · exact htyc
      · obtain ⟨l, hl⟩ := hA
        exact (hns l hl).elim
    rcases h.2 with ⟨m', ls₁, ls₂, xs₁, xs₂, hm', hlen₁, hbel₁, hbel₂, hbnd₁,
        h1, h2, _, _, heqN, ha1, _, hargs⟩ | ⟨hnone, _⟩
    · have em : m = m' := Option.some.inj (hm.symm.trans hm')
      subst em
      have hxs₁ : xs₁.length = (piDomsOf m.mtype).length :=
        Nat.le_antisymm hbnd₁ (hargs_len ▸ ha1)
      obtain ⟨hxs₂, ⟨w₁, w₂, hty₁, hty₂⟩, _⟩ :=
        hasTyT_famApp_both_of_levelFacts_convArgsT hW hΓ hm hind hlen₁ hbel₁ hbel₂ heqN hxs₁ hargs
      exact Or.inl ⟨hA, htyc, Or.inl ⟨m, ls₁, ls₂, xs₁, xs₂, w₁, w₂, hm, hind,
        h1, h2, hty₁, hty₂, heqN, hxs₁, hxs₂, hargs⟩⟩
    · exact (hnone m hm).elim
  · rintro (⟨_, htyc, hT⟩ | ⟨hns, _⟩)
    · rcases hT with ⟨m', ls₁, ls₂, xs₁, xs₂, _, _, hm', _, h1, h2,
          ⟨hty₁⟩, ⟨hty₂⟩, heqN, hxs₁, hxs₂, hargs⟩ | ⟨hnot, _⟩
      · have em : m = m' := Option.some.inj (hm.symm.trans hm')
        subst em
        obtain ⟨hlen₁, hbel₁⟩ := NativeFamilyProjection.native_level_facts hm hty₁
        obtain ⟨_, hbel₂⟩ := NativeFamilyProjection.native_level_facts hm hty₂
        exact ⟨Or.inl ⟨htyc, Or.inl hA⟩,
          Or.inl ⟨m, ls₁, ls₂, xs₁, xs₂, hm, hlen₁, hbel₁, hbel₂, Nat.le_of_eq hxs₁,
            h1, h2,
            fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs,
            fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs,
            heqN, by omega, by omega, hargs⟩⟩
      · exact (hnot m hm hind).elim
    · obtain ⟨l, hl⟩ := hA
      exact (hns l hl).elim

/-- **Symmetry of `LRSCoreSL` on All `FamProbeCptT E` Compacts at ANY Index `I : Expr Nat`
    (`lrSCoreSL_famProbe_symm`):**
    Holds under `EnvWfT E` and `CtxWfT E n Γ` alone — at **every** index `I : Expr Nat` (whether `I`
    is a sort, a Π-type, or an arbitrary instantiated type)! -/
theorem lrSCoreSL_famProbe_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {c : CptT} (hc : FamProbeCptT E c) {M N I : Expr Nat}
    (h : LRSCoreSL R E n Γ M N I c) :
    LRSCoreSL R E n Γ N M I c := by
  cases hc with
  | bot => exact lrSCoreSL_bot _ _ _ _
  | prop =>
      rw [lrSCoreSL_prop_iff] at h ⊢
      obtain ⟨hI, u, u', h1, h2⟩ := h
      exact ⟨hI, u', u, h2, h1⟩
  | sort =>
      rw [lrSCoreSL_sort_iff] at h ⊢
      obtain ⟨hI, u, u', h1, h2⟩ := h
      exact ⟨hI, u', u, h2, h1⟩
  | piBotNil =>
      exact piProbeSL_iff_lrSCore.mpr
        (lrSCore_symm_botPiCpt hW hΓ botPiCpt_pi_bot_nil (piProbeSL_iff_lrSCore.mp h))
  | spine =>
      rw [lrSCoreSL_spine_iff] at h ⊢
      exact spineClauseSL_symm hW hΓ h

/-- **Transitivity of `LRSCoreSL` on All `FamProbeCptT E` Compacts at ANY Index `I : Expr Nat`
    (`lrSCoreSL_famProbe_trans`):** -/
theorem lrSCoreSL_famProbe_trans (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {c : CptT} (hc : FamProbeCptT E c) {M N P I : Expr Nat}
    (h₁ : LRSCoreSL R E n Γ M N I c) (h₂ : LRSCoreSL R E n Γ N P I c) :
    LRSCoreSL R E n Γ M P I c := by
  cases hc with
  | bot => exact lrSCoreSL_bot _ _ _ _
  | prop =>
      rw [lrSCoreSL_prop_iff] at h₁ h₂ ⊢
      obtain ⟨hI, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hI, u, u'', h1, h3⟩
  | sort =>
      rw [lrSCoreSL_sort_iff] at h₁ h₂ ⊢
      obtain ⟨hI, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hI, u, u'', h1, h3⟩
  | piBotNil =>
      exact piProbeSL_iff_lrSCore.mpr
        (lrSCore_trans_botPiCpt hL hNU hW hΓ botPiCpt_pi_bot_nil
          (piProbeSL_iff_lrSCore.mp h₁) (piProbeSL_iff_lrSCore.mp h₂))
  | spine =>
      rw [lrSCoreSL_spine_iff] at h₁ h₂ ⊢
      exact spineClauseSL_trans hNU hW hΓ h₁ h₂

/-- The 5 statements of the `LRSCoreSL` mutual PER package. -/
def IrrelAtSL (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ : Expr Nat} {w : Level},
    LRSCoreSL R E n Γ A₁ A₂ (.sort w) a → CTyS E u a →
    ∀ {N N' : Expr Nat}, LRSCoreSL R E n Γ N N' A₁ u → LRSCoreSL R E n Γ N N' A₂ u

def SymmTmAtSL (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreSL R E n Γ A A (.sort w) a → CTyS E u a →
    ∀ {N N' : Expr Nat}, LRSCoreSL R E n Γ N N' A u → LRSCoreSL R E n Γ N' N A u

def TransTmAtSL (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreSL R E n Γ A A (.sort w) a → CTyS E u a →
    ∀ {N N' N'' : Expr Nat}, LRSCoreSL R E n Γ N N' A u → LRSCoreSL R E n Γ N' N'' A u →
      LRSCoreSL R E n Γ N N'' A u

def SymmTyAtSL (R : Readback) (E : ResolvedEnv) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ : Expr Nat} {w : Level},
    LRSCoreSL R E n Γ A₁ A₂ (.sort w) c → LRSCoreSL R E n Γ A₂ A₁ (.sort w) c

def TransTyAtSL (R : Readback) (E : ResolvedEnv) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ A₃ : Expr Nat} {w : Level},
    LRSCoreSL R E n Γ A₁ A₂ (.sort w) c → LRSCoreSL R E n Γ A₂ A₃ (.sort w) c →
      LRSCoreSL R E n Γ A₁ A₃ (.sort w) c

/-- `SymmTyAtSL c` from the package below `c`, under `EnvWfT E` alone (zero `ConvArgsSymmS`). -/
theorem symmTy_stepSL (hL : ReadbackLaws E R) (hW : EnvWfT E) (c : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAtSL R E n c' ∧ TransTyAtSL R E n c')
    (ihP : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      IrrelAtSL R E n a u ∧ SymmTmAtSL R E n a u ∧ TransTmAtSL R E n a u) :
    SymmTyAtSL R E n c := by
  intro Γ hΓ A₁ A₂ w h
  cases c with
  | bot => exact lrSCoreSL_bot _ _ _ _
  | prop =>
      rw [lrSCoreSL_prop_iff] at h ⊢
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | sort =>
      rw [lrSCoreSL_sort_iff] at h ⊢
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | lam g =>
      rw [LRSCoreSL.eq_def] at h
      obtain ⟨_, _, hr, _⟩ := h
      exact Expr.noConfusion (redR_sort_eq hL hr)
  | spine r args =>
      rw [lrSCoreSL_spine_iff] at h ⊢
      exact spineClauseSL_symm hW hΓ h
  | pi a f =>
      rw [LRSCoreSL.eq_def] at h ⊢
      obtain ⟨hA, A₁', B₁', A₂', B₂', h1, h2, ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩, ⟨u₁, hra⟩, hrf⟩ := h
      obtain ⟨hsa, hta⟩ := ihQ a (sizeOf_dom_lt_pi a f)
      have hra' : LRSCoreSL R E n Γ A₂' A₁' (.sort u₁) a := hsa hΓ hra
      have hself₂ : LRSCoreSL R E n Γ A₂' A₂' (.sort u₁) a := hta hΓ hra' hra
      cases hΓ₁ with
      | assumption _ _ u _ hA₁ =>
          obtain ⟨v, hA₂⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hdom hA₁
          refine ⟨hA, A₂', B₂', A₁', B₁', h2, h1, ⟨.assumption Γ A₂' v hΓ hA₂⟩, ⟨hdom.symmT⟩,
            ⟨tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT⟩, ⟨u₁, hra'⟩, ?_⟩
          intro s hs hty N N' hN hN' hcN hrel
          obtain ⟨hcN⟩ := hcN
          have hN₁ : HasTyT E n Γ N A₁' := hasTyT_of_tyConvT hN hdom.symmT
          have hN'₁ : HasTyT E n Γ N' A₁' := hasTyT_of_tyConvT hN' hdom.symmT
          have hc₁ : ConvT E n Γ N' N A₁' := convT_of_tyConv (.symm _ _ _ _ hcN) hdom.symmT
          have hrel₁ : ∀ u ∈ s.1, LRSCoreSL R E n Γ N' N A₁' u := fun u hu => by
            have hlt : sizeOf a + sizeOf u < sizeOf (CptT.pi a f) := by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega
            exact (ihP a u hlt).1 hΓ hra' (hty u hu)
              ((ihP a u hlt).2.1 hΓ hself₂ (hty u hu) (hrel u hu))
          obtain ⟨v', hv'⟩ := hrf s hs hty N' N hN'₁ hN₁ ⟨hc₁⟩ hrel₁
          exact ⟨v', (ihQ s.2 (sizeOf_out_lt_pi hs)).1 hΓ hv'⟩

/-- `TransTyAtSL c` from the package below `c`, under `EnvWfT E` alone (zero `ConvArgsTransS`). -/
theorem transTy_stepSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (c : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAtSL R E n c' ∧ TransTyAtSL R E n c')
    (ihP : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      IrrelAtSL R E n a u ∧ SymmTmAtSL R E n a u ∧ TransTmAtSL R E n a u) :
    TransTyAtSL R E n c := by
  intro Γ hΓ A₁ A₂ A₃ w h₁ h₂
  cases c with
  | bot => exact lrSCoreSL_bot _ _ _ _
  | prop =>
      rw [lrSCoreSL_prop_iff] at h₁ h₂ ⊢
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hA, u, u'', h1, h3⟩
  | sort =>
      rw [lrSCoreSL_sort_iff] at h₁ h₂ ⊢
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hA, u, u'', h1, h3⟩
  | lam g =>
      rw [LRSCoreSL.eq_def] at h₁
      obtain ⟨_, _, hr, _⟩ := h₁
      exact Expr.noConfusion (redR_sort_eq hL hr)
  | spine r args =>
      rw [lrSCoreSL_spine_iff] at h₁ h₂ ⊢
      exact spineClauseSL_trans hNU hW hΓ h₁ h₂
  | pi a f =>
      rw [LRSCoreSL.eq_def] at h₁ h₂ ⊢
      obtain ⟨hA, A₁', B₁', A₂', B₂', h1, h2, ⟨hΓ₁⟩, ⟨hdom₁⟩, ⟨hcod₁⟩, ⟨u₁, hra₁⟩, hrf₁⟩ := h₁
      obtain ⟨_, A₂'', B₂'', A₃', B₃', h2', h3, _, ⟨hdom₂⟩, ⟨hcod₂⟩, ⟨u₂, hra₂⟩, hrf₂⟩ := h₂
      obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU h2 h2'
      subst eA; subst eB
      obtain ⟨hsa, hta⟩ := ihQ a (sizeOf_dom_lt_pi a f)
      have hra₂' : LRSCoreSL R E n Γ A₂' A₃' (.sort u₁) a :=
        lrSCoreSL_sortIdx_irrel hL hNU ⟨_, .refl _⟩ ⟨_, .refl _⟩ a hra₂
      have hself₁ : LRSCoreSL R E n Γ A₁' A₁' (.sort u₁) a := hta hΓ hra₁ (hsa hΓ hra₁)
      refine ⟨hA, A₁', B₁', A₃', B₃', h1, h3, ⟨hΓ₁⟩, ⟨TyConvT.trans _ _ _ _ hdom₁ hdom₂⟩,
        ⟨TyConvT.trans _ _ _ _ hcod₁ (tyConvT_assump_dom hW hΓ hdom₁ hcod₂)⟩,
        ⟨u₁, hta hΓ hra₁ hra₂'⟩, ?_⟩
      intro s hs hty N N' hN hN' hcN hrel
      obtain ⟨hcN⟩ := hcN
      have hrelNN : ∀ u ∈ s.1, LRSCoreSL R E n Γ N N A₁' u := fun u hu => by
        have hlt : sizeOf a + sizeOf u < sizeOf (CptT.pi a f) := by
          have h₁ := List.sizeOf_lt_of_mem hs
          have h₂ := List.sizeOf_lt_of_mem hu
          have h₃ := sizeOfT_fst_lt s
          simp; omega
        exact (ihP a u hlt).2.2 hΓ hself₁ (hty u hu) (hrel u hu)
          ((ihP a u hlt).2.1 hΓ hself₁ (hty u hu) (hrel u hu))
      obtain ⟨v, hv⟩ := hrf₁ s hs hty N N hN hN ⟨.refl _ _ _ hN⟩ hrelNN
      have hN₂ : HasTyT E n Γ N A₂' := hasTyT_of_tyConvT hN hdom₁
      have hN'₂ : HasTyT E n Γ N' A₂' := hasTyT_of_tyConvT hN' hdom₁
      have hrel₂ : ∀ u ∈ s.1, LRSCoreSL R E n Γ N N' A₂' u := fun u hu => by
        have hlt : sizeOf a + sizeOf u < sizeOf (CptT.pi a f) := by
          have h₁ := List.sizeOf_lt_of_mem hs
          have h₂ := List.sizeOf_lt_of_mem hu
          have h₃ := sizeOfT_fst_lt s
          simp; omega
        exact (ihP a u hlt).1 hΓ hra₁ (hty u hu) (hrel u hu)
      obtain ⟨v', hv'⟩ := hrf₂ s hs hty N N' hN₂ hN'₂ ⟨convT_of_tyConv hcN hdom₁⟩ hrel₂
      exact ⟨v, (ihQ s.2 (sizeOf_out_lt_pi hs)).2 hΓ hv
        (lrSCoreSL_sortIdx_irrel hL hNU ⟨_, .refl _⟩ ⟨_, .refl _⟩ s.2 hv')⟩

/-- At a spine-coded type index `LRSCoreSL R E n Γ A A₂ (.sort w) (.spine r' args')`, neither `A` nor
    `A₂` reads back to a sort, and `Nonempty (TyConvT E n Γ A A₂)` holds. -/
theorem lrSCoreSL_spine_data_of_tyIdx (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {A A₂ : Expr Nat} {w : Level} {r' : Nat} {args' : List CptT}
    (h : LRSCoreSL R E n Γ A A₂ (.sort w) (.spine r' args')) :
    (∀ l, ¬ RedR R Γ A (.sort l)) ∧ (∀ l, ¬ RedR R Γ A₂ (.sort l)) ∧
      Nonempty (TyConvT E n Γ A A₂) := by
  rw [lrSCoreSL_spine_iff] at h
  obtain ⟨hns₁, hns₂⟩ := spineClauseSL_not_sort hL hNU h
  rcases h.1 with ⟨htyc, _⟩ | ⟨hns, _⟩
  · exact ⟨hns₁, hns₂, htyc⟩
  · exact (hns w (.refl _)).elim

/-- `IrrelAtSL a u` from the package below. -/
theorem irrel_stepSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtSL R E n c' ∧ TransTyAtSL R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAtSL R E n a' u' ∧ SymmTmAtSL R E n a' u' ∧ TransTmAtSL R E n a' u') :
    IrrelAtSL R E n a u := by
  intro Γ hΓ A₁ A₂ w hAA hu N N' h
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreSL_bot _ _ _ _
  | prop =>
      rw [lrSCoreSL_prop_iff] at hAA
      obtain ⟨_, l₁, l₂, h1, h2⟩ := hAA
      exact lrSCoreSL_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨_, h2⟩ u h
  | sort =>
      rw [lrSCoreSL_sort_iff] at hAA
      obtain ⟨_, l₁, l₂, h1, h2⟩ := hAA
      exact lrSCoreSL_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨_, h2⟩ u h
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreSL_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreSL_bot _ _ _ _
      · obtain ⟨hns₁, hns₂, ⟨hc₁₂⟩⟩ := lrSCoreSL_spine_data_of_tyIdx hL hNU hAA
        rw [lrSCoreSL_spine_iff] at h ⊢
        refine ⟨?_, h.2⟩
        rcases h.1 with ⟨_, hsub⟩ | ⟨_, ⟨hconv⟩⟩
        · rcases hsub with ⟨l, hl⟩ | hne
          · exact (hns₁ l hl).elim
          · obtain ⟨hconv⟩ := hne
            exact Or.inr ⟨hns₂, ⟨convT_of_tyConv hconv hc₁₂⟩⟩
        · exact Or.inr ⟨hns₂, ⟨convT_of_tyConv hconv hc₁₂⟩⟩
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreSL_bot _ _ _ _
      · rw [LRSCoreSL.eq_def] at h
        obtain ⟨A₁₁, B₁₁, hr₁, ⟨hΓ₁₁⟩, hclause⟩ := h
        rw [LRSCoreSL.eq_def] at hAA
        obtain ⟨_, A₁₁', B₁₁', A₂₁, B₂₁, hr₁', hr₂, _, ⟨hdomT⟩, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr₁ hr₁'
        subst eA; subst eB
        have hlt_a' : sizeOf a' < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
          have := sizeOf_dom_lt_pi a' g; omega
        obtain ⟨hsa, hta⟩ := ihQ a' hlt_a'
        have hra' : LRSCoreSL R E n Γ A₂₁ A₁₁ (.sort u₁) a' := hsa hΓ hra
        have hself₁ : LRSCoreSL R E n Γ A₁₁ A₁₁ (.sort u₁) a' := hta hΓ hra hra'
        rw [LRSCoreSL.eq_def]
        cases hΓ₁₁ with
        | assumption _ _ u₀ _ hA₁₁ =>
            obtain ⟨v₀, hA₂₁⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hdomT hA₁₁
            refine ⟨A₂₁, B₂₁, hr₂, ⟨.assumption Γ A₂₁ v₀ hΓ hA₂₁⟩, ?_⟩
            intro s hs M M' hM hM' hcM hrel
            obtain ⟨hcM⟩ := hcM
            have hM₁ : HasTyT E n Γ M A₁₁ := hasTyT_of_tyConvT hM hdomT.symmT
            have hM'₁ : HasTyT E n Γ M' A₁₁ := hasTyT_of_tyConvT hM' hdomT.symmT
            have hc₁ : ConvT E n Γ M M' A₁₁ := convT_of_tyConv hcM hdomT.symmT
            have hltP : ∀ v ∈ s.1,
                sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
              fun v hv => by
                have := sizeOf_dom_lt_pi a' g
                have := sizeOf_dem_lt_lam hs hv
                omega
            have hrel₁ : ∀ v ∈ s.1, LRSCoreSL R E n Γ M M' A₁₁ v := fun v hv =>
              (ihP a' v (hltP v hv)).1 hΓ hra' (hdom s hs v hv) (hrel v hv)
            have hcore := hclause s hs M M' hM₁ hM'₁ ⟨hc₁⟩ hrel₁
            rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
            · rw [h0]; exact lrSCoreSL_bot _ _ _ _
            · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
              have hrelMM : ∀ v ∈ t.1, LRSCoreSL R E n Γ M M A₁₁ v := fun v hv =>
                (ihP a' v (hltP v (hcomp v hv))).2.2 hΓ hself₁ (htyt v hv) (hrel₁ v (hcomp v hv))
                  ((ihP a' v (hltP v (hcomp v hv))).2.1 hΓ hself₁ (htyt v hv) (hrel₁ v (hcomp v hv)))
              obtain ⟨v₁, hv₁⟩ := hrf t ht htyt M M hM₁ hM₁ ⟨.refl _ _ _ hM₁⟩ hrelMM
              have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
                have := sizeOf_out_lt_pi (a := a') ht
                have := sizeOf_out_lt_lam hs
                omega
              exact (ihP t.2 s.2 hlt_t).1 hΓ hv₁ (hcod s hs t ht hcomp) hcore

/-- `SymmTmAtSL a u` from the package below. -/
theorem symmTm_stepSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtSL R E n c' ∧ TransTyAtSL R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAtSL R E n a' u' ∧ SymmTmAtSL R E n a' u' ∧ TransTmAtSL R E n a' u') :
    SymmTmAtSL R E n a u := by
  intro Γ hΓ A w hAA hu N N' h
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreSL_bot _ _ _ _
  | prop =>
      rw [lrSCoreSL_prop_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.prop + sizeOf u := by
        have := CptT.sizeOf_pos CptT.prop; omega
      have h' := lrSCoreSL_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h
      exact lrSCoreSL_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).1 hΓ h')
  | sort =>
      rw [lrSCoreSL_sort_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.sort + sizeOf u := by
        have := CptT.sizeOf_pos CptT.sort; omega
      have h' := lrSCoreSL_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h
      exact lrSCoreSL_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).1 hΓ h')
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreSL_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreSL_bot _ _ _ _
      · rw [lrSCoreSL_spine_iff] at h ⊢
        exact spineClauseSL_symm hW hΓ h
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreSL_bot _ _ _ _
      · rw [LRSCoreSL.eq_def] at h
        obtain ⟨A₁, B₁, hr, ⟨hΓ₁⟩, hclause⟩ := h
        rw [LRSCoreSL.eq_def] at hAA
        obtain ⟨_, A₁', B₁', A₁'', B₁'', hr', hr'', _, _, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr''
        subst eA; subst eB
        have hltP : ∀ {s : List CptT × CptT}, s ∈ f → ∀ v ∈ s.1,
            sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
          fun {s} hs v hv => by
            have := sizeOf_dom_lt_pi a' g
            have := sizeOf_dem_lt_lam hs hv
            omega
        rw [LRSCoreSL.eq_def]
        refine ⟨A₁, B₁, hr, ⟨hΓ₁⟩, ?_⟩
        intro s hs M M' hM hM' hcM hrel
        obtain ⟨hcM⟩ := hcM
        have hrel' : ∀ v ∈ s.1, LRSCoreSL R E n Γ M' M A₁ v := fun v hv =>
          (ihP a' v (hltP hs v hv)).2.1 hΓ hra (hdom s hs v hv) (hrel v hv)
        have hcore := hclause s hs M' M hM' hM ⟨.symm _ _ _ _ hcM⟩ hrel'
        rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
        · rw [h0]; exact lrSCoreSL_bot _ _ _ _
        · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
          have hrelM'M : ∀ v ∈ t.1, LRSCoreSL R E n Γ M' M A₁ v := fun v hv => hrel' v (hcomp v hv)
          have hrelMM : ∀ v ∈ t.1, LRSCoreSL R E n Γ M M A₁ v := fun v hv =>
            (ihP a' v (hltP hs v (hcomp v hv))).2.2 hΓ hra (htyt v hv) (hrel v (hcomp v hv))
              (hrelM'M v hv)
          obtain ⟨v₁, hv₁⟩ := hrf t ht htyt M' M hM' hM ⟨.symm _ _ _ _ hcM⟩ hrelM'M
          obtain ⟨v₂, hv₂⟩ := hrf t ht htyt M M hM hM ⟨.refl _ _ _ hM⟩ hrelMM
          have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
            have := sizeOf_out_lt_pi (a := a') ht
            have := sizeOf_out_lt_lam hs
            omega
          have hmoved := (ihP t.2 s.2 hlt_t).1 hΓ hv₁ (hcod s hs t ht hcomp) hcore
          exact (ihP t.2 s.2 hlt_t).2.1 hΓ hv₂ (hcod s hs t ht hcomp) hmoved

/-- `TransTmAtSL a u` from the package below. -/
theorem transTm_stepSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtSL R E n c' ∧ TransTyAtSL R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAtSL R E n a' u' ∧ SymmTmAtSL R E n a' u' ∧ TransTmAtSL R E n a' u') :
    TransTmAtSL R E n a u := by
  intro Γ hΓ A w hAA hu N N' N'' h₁ h₂
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreSL_bot _ _ _ _
  | prop =>
      rw [lrSCoreSL_prop_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.prop + sizeOf u := by
        have := CptT.sizeOf_pos CptT.prop; omega
      have h₁' := lrSCoreSL_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₁
      have h₂' := lrSCoreSL_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₂
      exact lrSCoreSL_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).2 hΓ h₁' h₂')
  | sort =>
      rw [lrSCoreSL_sort_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.sort + sizeOf u := by
        have := CptT.sizeOf_pos CptT.sort; omega
      have h₁' := lrSCoreSL_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₁
      have h₂' := lrSCoreSL_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₂
      exact lrSCoreSL_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).2 hΓ h₁' h₂')
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreSL_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreSL_bot _ _ _ _
      · rw [lrSCoreSL_spine_iff] at h₁ h₂ ⊢
        exact spineClauseSL_trans hNU hW hΓ h₁ h₂
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreSL_bot _ _ _ _
      · rw [LRSCoreSL.eq_def] at h₁ h₂
        obtain ⟨A₁, B₁, hr, ⟨hΓ₁⟩, hcl₁⟩ := h₁
        obtain ⟨A₁', B₁', hr', _, hcl₂⟩ := h₂
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        rw [LRSCoreSL.eq_def] at hAA
        obtain ⟨_, A₁', B₁', A₁'', B₁'', hr', hr'', _, _, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr''
        subst eA; subst eB
        have hltP : ∀ {s : List CptT × CptT}, s ∈ f → ∀ v ∈ s.1,
            sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
          fun {s} hs v hv => by
            have := sizeOf_dom_lt_pi a' g
            have := sizeOf_dem_lt_lam hs hv
            omega
        rw [LRSCoreSL.eq_def]
        refine ⟨A₁, B₁, hr, ⟨hΓ₁⟩, ?_⟩
        intro s hs M M' hM hM' hcM hrel
        obtain ⟨hcM⟩ := hcM
        have hrelMM : ∀ v ∈ s.1, LRSCoreSL R E n Γ M M A₁ v := fun v hv =>
          (ihP a' v (hltP hs v hv)).2.2 hΓ hra (hdom s hs v hv) (hrel v hv)
            ((ihP a' v (hltP hs v hv)).2.1 hΓ hra (hdom s hs v hv) (hrel v hv))
        have hc₁ := hcl₁ s hs M M hM hM ⟨.refl _ _ _ hM⟩ hrelMM
        have hc₂ := hcl₂ s hs M M' hM hM' ⟨hcM⟩ hrel
        rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
        · rw [h0]; exact lrSCoreSL_bot _ _ _ _
        · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
          obtain ⟨v₂, hv₂⟩ := hrf t ht htyt M M hM hM ⟨.refl _ _ _ hM⟩
            (fun v hv => hrelMM v (hcomp v hv))
          have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
            have := sizeOf_out_lt_pi (a := a') ht
            have := sizeOf_out_lt_lam hs
            omega
          exact (ihP t.2 s.2 hlt_t).2.2 hΓ hv₂ (hcod s hs t ht hcomp) hc₁ hc₂

/-- **Unconditional 5-Part Mutual PER for `LRSCoreSL` Under `EnvWfT E` Alone (`typedPERSL_of_envWfT`):**
    Discharges `#7673#issuecomment-6271576104` Items 2.1 & 2.2: proves `SymmTyAtSL`, `TransTyAtSL`,
    `IrrelAtSL`, `SymmTmAtSL`, and `TransTmAtSL` across all `CptT` compacts under `ReadbackLaws E R`,
    `NormalUniqueR R`, and `EnvWfT E` **alone** (zero `ConvArgsSymmS`, zero `ConvArgsTransS`, zero
    `PiRowField`)! -/
theorem typedPERSL_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) :
    ∀ k : Nat,
      (∀ c : CptT, sizeOf c ≤ k → SymmTyAtSL R E n c ∧ TransTyAtSL R E n c) ∧
      (∀ a u : CptT, sizeOf a + sizeOf u ≤ k →
        IrrelAtSL R E n a u ∧ SymmTmAtSL R E n a u ∧ TransTmAtSL R E n a u) := by
  intro k
  induction k with
  | zero =>
      refine ⟨fun c hc => ?_, fun a u hau => ?_⟩
      · exact absurd hc (Nat.not_le_of_gt (CptT.sizeOf_pos c))
      · exact absurd hau (Nat.not_le_of_gt (Nat.add_pos_left (CptT.sizeOf_pos a) _))
  | succ k ih =>
      refine ⟨fun c hc => ?_, fun a u hau => ?_⟩
      · by_cases hk : sizeOf c ≤ k
        · exact ih.1 c hk
        · have ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAtSL R E n c' ∧ TransTyAtSL R E n c' :=
            fun c' _ => ih.1 c' (by omega)
          have ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf c →
              IrrelAtSL R E n a' u' ∧ SymmTmAtSL R E n a' u' ∧ TransTmAtSL R E n a' u' :=
            fun a' u' _ => ih.2 a' u' (by omega)
          exact ⟨symmTy_stepSL hL hW c ihQ ihP, transTy_stepSL hL hNU hW c ihQ ihP⟩
      · by_cases hk : sizeOf a + sizeOf u ≤ k
        · exact ih.2 a u hk
        · have ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u →
              SymmTyAtSL R E n c' ∧ TransTyAtSL R E n c' :=
            fun c' _ => ih.1 c' (by omega)
          have ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
              IrrelAtSL R E n a' u' ∧ SymmTmAtSL R E n a' u' ∧ TransTmAtSL R E n a' u' :=
            fun a' u' _ => ih.2 a' u' (by omega)
          exact ⟨irrel_stepSL hL hNU hW a u ihQ ihP, symmTm_stepSL hL hNU hW a u ihQ ihP,
            transTm_stepSL hL hNU hW a u ihQ ihP⟩

theorem lrSCoreSL_irrel_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSL R E n Γ A₁ A₂ (.sort w) a) (hu : CTyS E u a) {N N' : Expr Nat}
    (h : LRSCoreSL R E n Γ N N' A₁ u) : LRSCoreSL R E n Γ N N' A₂ u :=
  ((typedPERSL_of_envWfT hL hNU hW _).2 a u (Nat.le_refl _)).1 hΓ hAA hu h

theorem lrSCoreSL_symm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {w : Level} {c : CptT}
    (h : LRSCoreSL R E n Γ A₁ A₂ (.sort w) c) :
    LRSCoreSL R E n Γ A₂ A₁ (.sort w) c :=
  ((typedPERSL_of_envWfT hL hNU hW _).1 c (Nat.le_refl _)).1 hΓ h

theorem lrSCoreSL_trans_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ A₃ : Expr Nat} {w : Level} {c : CptT}
    (h₁ : LRSCoreSL R E n Γ A₁ A₂ (.sort w) c) (h₂ : LRSCoreSL R E n Γ A₂ A₃ (.sort w) c) :
    LRSCoreSL R E n Γ A₁ A₃ (.sort w) c :=
  ((typedPERSL_of_envWfT hL hNU hW _).1 c (Nat.le_refl _)).2 hΓ h₁ h₂

theorem lrSCoreSL_symm_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSL R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' : Expr Nat} (h : LRSCoreSL R E n Γ N N' A u) :
    LRSCoreSL R E n Γ N' N A u :=
  ((typedPERSL_of_envWfT hL hNU hW _).2 a u (Nat.le_refl _)).2.1 hΓ hAA hu h

theorem lrSCoreSL_trans_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSL R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' N'' : Expr Nat} (h₁ : LRSCoreSL R E n Γ N N' A u) (h₂ : LRSCoreSL R E n Γ N' N'' A u) :
    LRSCoreSL R E n Γ N N'' A u :=
  ((typedPERSL_of_envWfT hL hNU hW _).2 a u (Nat.le_refl _)).2.2 hΓ hAA hu h₁ h₂

theorem lrSSL_symm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {w : Level} {c : CptT}
    (h : LRSSL R E n Γ A₁ A₂ (.sort w) c) :
    LRSSL R E n Γ A₂ A₁ (.sort w) c := by
  rcases h with hP | h
  · exact Or.inl hP
  · exact Or.inr (lrSCoreSL_symm_of_envWfT hL hNU hW hΓ h)

theorem lrSSL_trans_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ A₃ : Expr Nat} {w : Level} {c : CptT}
    (h₁ : LRSSL R E n Γ A₁ A₂ (.sort w) c) (h₂ : LRSSL R E n Γ A₂ A₃ (.sort w) c) :
    LRSSL R E n Γ A₁ A₃ (.sort w) c := by
  rcases h₁ with hP | h₁
  · exact Or.inl hP
  · rcases h₂ with hP | h₂
    · exact Or.inl hP
    · exact Or.inr (lrSCoreSL_trans_of_envWfT hL hNU hW hΓ h₁ h₂)

theorem lrSSL_symm_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSL R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' : Expr Nat} (h : LRSSL R E n Γ N N' A u) :
    LRSSL R E n Γ N' N A u := by
  rcases h with hP | h
  · exact Or.inl hP
  · exact Or.inr (lrSCoreSL_symm_tm_of_envWfT hL hNU hW hΓ hAA hu h)

theorem lrSSL_trans_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSL R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' N'' : Expr Nat} (h₁ : LRSSL R E n Γ N N' A u) (h₂ : LRSSL R E n Γ N' N'' A u) :
    LRSSL R E n Γ N N'' A u := by
  rcases h₁ with hP | h₁
  · exact Or.inl hP
  · rcases h₂ with hP | h₂
    · exact Or.inl hP
    · exact Or.inr (lrSCoreSL_trans_tm_of_envWfT hL hNU hW hΓ hAA hu h₁ h₂)


/-! #### §11 Part B — 3-Observation Bridge (`famObsTransport_of_lrSCoreSL_probes`, `famObsEquiv_of_lrSCoreSL_probes`) at ANY Ambient Index `I`, Unified Application Demand Lemmas (`lrSCoreSL_app_of_lambda_demand`, `lrSCoreSL_app_of_famSpine_step`, `lrSCoreSL_app_of_approxT_famProbe`, `famObsEquiv_app_of_lrSCoreSL`), and Related-Substitution `letE` Adapters (`FamModelProbeAtSubst`, `famObsEquiv_of_substRelation_lrSCoreSL`, `famMixedSubstEdges_of_lrSCoreSL`) -/

/-- **Sort Readback Extraction from `LRSCoreSL` at Any Index `I` (`sortRead_of_lrSCoreSL_left`):** -/
theorem sortRead_of_lrSCoreSL_left {Γ : LCtx} {M N I : Expr Nat} {u : Level}
    (h : LRSCoreSL R E n Γ M N I (sortCode u)) :
    ∃ v, RedR R Γ N (.sort v) := by
  obtain ⟨_, _, v, _, hN⟩ := (lrSCoreSL_sortCode_iff u).mp h
  exact ⟨v, hN⟩

/-- **Π Readback Extraction from `LRSCoreSL` at Any Index `I` (`piRead_of_lrSCoreSL_left`):** -/
theorem piRead_of_lrSCoreSL_left (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {M N I A B : Expr Nat}
    (hread : RedR R Γ M (.pi A B))
    (h : LRSCoreSL R E n Γ M N I (.pi .bot [])) :
    ∃ A' B' : Expr Nat,
      RedR R Γ N (.pi A' B') ∧
      Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  rw [LRSCoreSL.eq_def] at h
  obtain ⟨_, A₁, B₁, A₂, B₂, h1, h2, _, hdom, hcod, _⟩ := h
  obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hread h1
  subst eA; subst eB
  exact ⟨A₂, B₂, h2, hdom, hcod⟩

/-- **Π Readback Extraction from `LRSCoreT` at Any Index `I` (`piRead_of_lrSCoreT_left`):** -/
theorem piRead_of_lrSCoreT_left (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {M N I A B : Expr Nat}
    (hread : RedR R Γ M (.pi A B))
    (h : LRSCoreT R E n Γ M N I (.pi .bot [])) :
    ∃ A' B' : Expr Nat,
      RedR R Γ N (.pi A' B') ∧
      Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  piRead_of_lrSCoreSL_left hL hNU hread (piProbeSL_iff_lrSCoreT.mpr h)

/-- **Family-Spine Readback Extraction from `LRSCoreSL` at ANY Ambient Index `I : Expr Nat`
    (`famSpineRead_of_lrSCoreSL_left`):**
    Because `SpineClauseSL` carries the level facts (`ls₁.length = m.arity`, `levelsBounded n ls₁ = true`,
    `levelsBounded n ls₂ = true`) and `xs₁.length ≤ (piDomsOf m.mtype).length` at **every** index `I`,
    evaluating `LRSCoreSL R E n Γ M N I (.spine r (botVecT xs))` when `xs.length = (piDomsOf m.mtype).length`
    recovers `xs₂.length = (piDomsOf m.mtype).length`, both sort typings, AND `TyConvT` via
    `hasTyT_famApp_both_of_levelFacts_convArgsT` — **without** requiring `∃ l, RedR R Γ I (.sort l)`! -/
theorem famSpineRead_of_lrSCoreSL_left (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N I : Expr Nat} {r : Nat} {m : CheckedMember} {ls : List Level} {xs : List (Expr Nat)}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hread : RedR R Γ M (foldApps (.const r ls) xs))
    (hlen : xs.length = (piDomsOf m.mtype).length)
    (h : LRSCoreSL R E n Γ M N I (.spine r (botVecT xs))) :
    ∃ (ls' : List Level) (xs' : List (Expr Nat)) (w' : Level),
      RedR R Γ N (foldApps (.const r ls') xs') ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w')) ∧
      Nonempty (TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) ∧
      eqNList ls ls' ∧
      xs'.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  rw [lrSCoreSL_spine_iff] at h
  rcases h.2 with ⟨m', ls₁, ls₂, xs₁, xs₂, hm', hlen₁, hbel₁, hbel₂, _,
      h1, h2, hn1, _, heqN, _, _, hargs⟩ | ⟨hnone, _⟩
  · have em : m' = m := Option.some.inj (hm'.symm.trans hm)
    subst em
    have e := hNU Γ hread (fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs) h1 hn1
    obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
    injection hconst with _ hls
    subst hls; subst hxs
    obtain ⟨hxs₂, ⟨_, w₂, _, hty₂⟩, htyc⟩ :=
      hasTyT_famApp_both_of_levelFacts_convArgsT hW hΓ hm hind hlen₁ hbel₁ hbel₂ heqN hlen hargs
    exact ⟨ls₂, xs₂, w₂, h2, hty₂, htyc, heqN, hxs₂, hargs⟩
  · exact (hnone m hm).elim

/-- **Family-Spine Readback Extraction from `LRSCoreT` at a Sort Index `I` (`famSpineRead_of_lrSCoreT_sort`):** -/
theorem famSpineRead_of_lrSCoreT_sort (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N I : Expr Nat} (hI : ∃ l, RedR R Γ I (.sort l))
    {r : Nat} {m : CheckedMember} {ls : List Level} {xs : List (Expr Nat)}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hread : RedR R Γ M (foldApps (.const r ls) xs))
    (hlen : xs.length = (piDomsOf m.mtype).length)
    (h : LRSCoreT R E n Γ M N I (.spine r (botVecT xs))) :
    ∃ (ls' : List Level) (xs' : List (Expr Nat)) (w' : Level),
      RedR R Γ N (foldApps (.const r ls') xs') ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w')) ∧
      Nonempty (TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) ∧
      eqNList ls ls' ∧
      xs'.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  have hlen_bot : (botVecT xs).length = (piDomsOf m.mtype).length := by
    rw [botVecT_length, hlen]
  exact famSpineRead_of_lrSCoreSL_left hL hNU hW hΓ hm hind hread hlen
    ((famProbeSL_iff_lrSCoreT hL hW hΓ hm hind hlen_bot hI).mpr h)

/-- **3-Observation Transport Bridge from `LRSCoreSL` at ANY Ambient Index `I : Expr Nat`
    (`famObsTransport_of_lrSCoreSL_probes`):**
    Extends `#7733`'s 2-observation `probeTransportT_of_lrSCoreS_probes` to all 3 type heads
    (Sort + Π + `.inductiveM` family spines) at **any** ambient index `I : Expr Nat`! -/
theorem famObsTransport_of_lrSCoreSL_probes (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N I : Expr Nat}
    (hreal : FamProbeRealizedAtT R E n Γ M)
    (hrel : ∀ c, FamProbeCptT E c → ApproxT E (ctxEnvT E Γ) M c → LRSCoreSL R E n Γ M N I c) :
    FamObsTransport R E n Γ M N := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hread⟩
    exact sortRead_of_lrSCoreSL_left
      (hrel (sortCode u) (famProbeCptT_sortCode u) (hreal.1.1 u hread))
  · intro A B hread hΓA
    exact piRead_of_lrSCoreSL_left hL hNU hread
      (hrel (.pi .bot []) .piBotNil (hreal.1.2 A B hread hΓA))
  · intro r m ls xs w hm hind hread hty hlen hargs
    exact famSpineRead_of_lrSCoreSL_left hL hNU hW hΓ hm hind hread hlen
      (hrel (.spine r (botVecT xs)) (famProbeCptT_spine_botVecT hm hind xs)
        (hreal.2 r m ls xs w hm hind hread hty hlen hargs))

/-- **3-Observation Equivalence Bridge from `LRSCoreSL` at ANY Ambient Index `I : Expr Nat`
    (`famObsEquiv_of_lrSCoreSL_probes`):**
    Uses `lrSCoreSL_famProbe_symm` to obtain both directions of `FamObsEquiv R E n Γ M N` from a
    single forward `LRSCoreSL R E n Γ M N I c` hypothesis on `FamProbeCptT E c` at **any** index `I`! -/
theorem famObsEquiv_of_lrSCoreSL_probes (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N I : Expr Nat}
    (hrealM : FamProbeRealizedAtT R E n Γ M)
    (hrealN : FamProbeRealizedAtT R E n Γ N)
    (hrel : ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) M c ∨ ApproxT E (ctxEnvT E Γ) N c) →
      LRSCoreSL R E n Γ M N I c) :
    FamObsEquiv R E n Γ M N :=
  ⟨famObsTransport_of_lrSCoreSL_probes hL hNU hW hΓ hrealM
      (fun c hc hM => hrel c hc (Or.inl hM)),
   famObsTransport_of_lrSCoreSL_probes hL hNU hW hΓ hrealN
      (fun c hc hN => lrSCoreSL_famProbe_symm hW hΓ hc (hrel c hc (Or.inr hN)))⟩

/-- **3-Observation Transport Bridge from `LRSCoreT` at a Sort Index `I`
    (`famObsTransport_of_lrSCoreT_probes`):** -/
theorem famObsTransport_of_lrSCoreT_probes (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N I : Expr Nat}
    (hI : ∃ l, RedR R Γ I (.sort l))
    (hreal : FamProbeRealizedAtT R E n Γ M)
    (hrel : ∀ c, FamProbeCptT E c → ApproxT E (ctxEnvT E Γ) M c → LRSCoreT R E n Γ M N I c) :
    FamObsTransport R E n Γ M N := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hread⟩
    have h := hrel (sortCode u) (famProbeCptT_sortCode u) (hreal.1.1 u hread)
    obtain ⟨_, _, v, _, hN⟩ := (lrSCoreT_sort_iff Γ M N I).mp
      ((lrSCoreT_sortCode_iff (Or.inr rfl) u).mp h)
    exact ⟨v, hN⟩
  · intro A B hread hΓA
    exact piRead_of_lrSCoreT_left hL hNU hread
      (hrel (.pi .bot []) .piBotNil (hreal.1.2 A B hread hΓA))
  · intro r m ls xs w hm hind hread hty hlen hargs
    exact famSpineRead_of_lrSCoreT_sort hL hNU hW hΓ hI hm hind hread hlen
      (hrel (.spine r (botVecT xs)) (famProbeCptT_spine_botVecT hm hind xs)
        (hreal.2 r m ls xs w hm hind hread hty hlen hargs))

/-- **Lambda-Demand Application Step for `LRSCoreSL` (`lrSCoreSL_app_of_lambda_demand`):**
    Handles the `ApproxT.app` branch (`f` approximated at `.lam g` with step `s ∈ g`) for **every**
    output compact `s.2 : CptT` — including `.spine r args`! -/
theorem lrSCoreSL_app_of_lambda_demand (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B : Expr Nat} {graph : List (List CptT × CptT)} {s : List CptT × CptT}
    (_hc_fg : ConvT E n Γ f g (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hfg : LRSCoreSL R E n Γ f g (.pi A B) (.lam graph))
    (hs : s ∈ graph)
    (hab : ∀ u ∈ s.1, LRSCoreSL R E n Γ a b A u) :
    LRSCoreSL R E n Γ (.app f a) (.app g b) (instantiate0 a B) s.2 := by
  rw [LRSCoreSL.eq_def] at hfg
  obtain ⟨A₁, B₁, hr, _, hclause⟩ := hfg
  obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU (.refl (.pi A B)) hr
  subst eA; subst eB
  obtain ⟨ha_ty, hb_ty, _⟩ := convEnds hW hΓ hc_ab
  exact hclause s hs a b ha_ty hb_ty ⟨hc_ab⟩ hab

/-- `LRSCoreT` counterpart of `lrSCoreSL_app_of_lambda_demand`. -/
theorem lrSCoreT_app_of_lambda_demand (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B : Expr Nat} {graph : List (List CptT × CptT)} {s : List CptT × CptT}
    (_hc_fg : ConvT E n Γ f g (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hfg : LRSCoreT R E n Γ f g (.pi A B) (.lam graph))
    (hs : s ∈ graph)
    (hab : ∀ u ∈ s.1, LRSCoreT R E n Γ a b A u) :
    LRSCoreT R E n Γ (.app f a) (.app g b) (instantiate0 a B) s.2 := by
  rw [LRSCoreT.eq_def] at hfg
  obtain ⟨A₁, B₁, hr, _, hclause⟩ := hfg
  obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU (.refl (.pi A B)) hr
  subst eA; subst eB
  obtain ⟨ha_ty, hb_ty, _⟩ := convEnds hW hΓ hc_ab
  exact hclause s hs a b ha_ty hb_ty ⟨hc_ab⟩ hab

/-- **Strict Prefix Length `xs₁.length + 1 < (piDomsOf m.mtype).length` Refutes Sort Readback of
    `instantiate0 a B` (`not_redR_sort_of_wholeSpine_lt`):**
    Uses `wholeSpine_piTower_of_links` at `k = 1` + `piTower_step_same` + `piTower_pi_read` to show
    that when `xs₁.length + 1 < (piDomsOf m.mtype).length`, `instantiate0 a B` reads back to a
    `.pi` and therefore cannot read back to any `.sort l`! -/
theorem not_redR_sort_of_wholeSpine_lt (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) {ls₁ : List Level}
    {xs₁ : List (Expr Nat)} {A B a : Expr Nat}
    (df_sp : HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.pi A B))
    (ha : HasTyT E n Γ a A)
    (hlt1 : xs₁.length + 1 < (piDomsOf m.mtype).length)
    (hlink : PiTowerLinkBelow R E n (sizeOf df_sp)) :
    ∀ l, ¬ RedR R Γ (instantiate0 a B) (.sort l) := by
  obtain ⟨D, B₀, hpi⟩ := instTelescope_member_eq_pi_of_lt m ls₁ (xs := xs₁) (by omega)
  obtain ⟨u₀, hLR⟩ := wholeSpine_piTower_of_links hL hNU hW hΓ hm ls₁ xs₁ df_sp (k := 1) hlt1 hlink
  rw [hpi] at hLR
  obtain ⟨⟨hDA⟩, _⟩ := piTower_pi_components hL hLR
  have ha_D : HasTyT E n Γ a D := hasTyT_of_tyConvT ha hDA.symmT
  obtain ⟨_, hstep⟩ := piTower_step_same hL hLR ha_D
  obtain ⟨_, _, A₂', B₂', _, hred_pi, _⟩ := piTower_pi_read hstep
  intro l hred_sort
  exact not_redR_pi_of_redR_sort hL hNU hred_sort A₂' B₂' hred_pi

/-- **Spine-Growth Application Step for `LRSCoreSL` on Admitted `.inductiveM` Family Spines
    (`lrSCoreSL_app_of_famSpine_step`):**
    Handles the `ApproxT.appSpine` branch (`f` approximated at `.spine r args` stepping to
    `.spine r (args ++ [u])`) across **every** prefix length `xs₁.length < (piDomsOf m.mtype).length`
    (both unsaturated `xs₁.length + 1 < (piDomsOf m.mtype).length` via `not_redR_sort_of_wholeSpine_lt`
    and saturated `xs₁.length + 1 = (piDomsOf m.mtype).length` via `wholeSpine_nodeDeclAlign_of_links`
    + `tyConvT_subst0_of_envWfT`)! -/
theorem lrSCoreSL_app_of_famSpine_step (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {f g a b A B : Expr Nat} {args : List CptT} (u : CptT)
    (hc_fg : ConvT E n Γ f g (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hf_sp : LRSCoreSL R E n Γ f g (.pi A B) (.spine r args))
    (hsp_ty : ∀ ls₁ xs₁, RedR R Γ f (foldApps (.const r ls₁) xs₁) →
      ∃ df_sp : HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.pi A B),
        xs₁.length < (piDomsOf m.mtype).length ∧
        PiTowerLinkBelow R E n (sizeOf df_sp)) :
    LRSCoreSL R E n Γ (.app f a) (.app g b) (instantiate0 a B) (.spine r (args ++ [u])) := by
  rw [lrSCoreSL_spine_iff] at hf_sp ⊢
  rcases hf_sp.2 with ⟨m', ls₁, ls₂, xs₁, xs₂, hm', hlen₁, hbel₁, hbel₂, _,
      hred₁, hred₂, _, _, heqN, ha1, ha2, hargs⟩ | ⟨hnone, _⟩
  · have em : m = m' := Option.some.inj (hm.symm.trans hm')
    subst em
    obtain ⟨df_sp, hlt, hlink⟩ := hsp_ty ls₁ xs₁ hred₁
    obtain ⟨ha_ty, _, _⟩ := convEnds hW hΓ hc_ab
    have hc_app : ConvT E n Γ (.app f a) (.app g b) (instantiate0 a B) :=
      .app Γ f g a b A B hc_fg hc_ab
    have hargs_snoc : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) (xs₁ ++ [a]) (xs₂ ++ [b]) :=
      wholeSpine_convArgsT_snoc_of_links hL hNU hW hΓ hm ls₁ df_sp hlt hlink hargs hc_ab
    have hbnd_snoc : (xs₁ ++ [a]).length ≤ (piDomsOf m.mtype).length := by
      simp only [List.length_append, List.length_singleton]; exact hlt
    have hred_fa : RedR R Γ (.app f a) (foldApps (.const r ls₁) (xs₁ ++ [a])) := by
      rw [foldApps_snoc]; exact redR_appHead hL hred₁
    have hred_gb : RedR R Γ (.app g b) (foldApps (.const r ls₂) (xs₂ ++ [b])) := by
      rw [foldApps_snoc]; exact redR_appHead hL hred₂
    have hn_fa : NormalR R Γ (foldApps (.const r ls₁) (xs₁ ++ [a])) :=
      fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs
    have hn_gb : NormalR R Γ (foldApps (.const r ls₂) (xs₂ ++ [b])) :=
      fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs
    have ha1_snoc : (args ++ [u]).length ≤ (xs₁ ++ [a]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    have ha2_snoc : (args ++ [u]).length ≤ (xs₂ ++ [b]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    refine ⟨?_, Or.inl ⟨m, ls₁, ls₂, xs₁ ++ [a], xs₂ ++ [b], hm, hlen₁, hbel₁, hbel₂, hbnd_snoc,
      hred_fa, hred_gb, hn_fa, hn_gb, heqN, ha1_snoc, ha2_snoc, hargs_snoc⟩⟩
    rcases Nat.lt_or_eq_of_le hbnd_snoc with hlt_sat | hlen_sat
    · have hlt1 : xs₁.length + 1 < (piDomsOf m.mtype).length := by
        simpa only [List.length_append, List.length_singleton] using hlt_sat
      exact Or.inr ⟨not_redR_sort_of_wholeSpine_lt hL hNU hW hΓ hm df_sp ha_ty hlt1 hlink,
        ⟨hc_app⟩⟩
    · obtain ⟨D, B₀, hpi, ⟨hDA⟩, ⟨hBB⟩⟩ :=
        wholeSpine_nodeDeclAlign_of_links hL hNU hW hΓ hm ls₁ df_sp hlt hlink
      have ha_D : HasTyT E n Γ a D := hasTyT_of_tyConvT ha_ty hDA.symmT
      have hB_conv : TyConvT E n Γ (instantiate0 a B₀) (instantiate0 a B) :=
        tyConvT_subst0_of_envWfT hW ha_D hBB
      have hB₀_sort : instantiate0 a B₀ =
          .sort (instLevel ls₁ (inductiveSortLevel hW hm hind)) := by
        rw [← instTelescope_snoc_of_pi hpi a,
            instTelescope_instMtype_eq_sort hW hm hind ls₁ hlen_sat]
      rw [hB₀_sort] at hB_conv
      have hc_sort : ConvT E n Γ (.app f a) (.app g b)
          (.sort (instLevel ls₁ (inductiveSortLevel hW hm hind))) :=
        convT_of_tyConv hc_app hB_conv.symmT
      exact Or.inl ⟨⟨.of Γ _ _ _ hc_sort⟩, Or.inr ⟨hc_app⟩⟩
  · exact (hnone m hm).elim

/-- **Syntactic-Spine Specialization of `lrSCoreSL_app_of_famSpine_step`
    (`lrSCoreSL_app_of_famSpine_syntactic`):**
    When `f = foldApps (.const r ls) xs`, `df_sp : HasTyT E n Γ (foldApps (.const r ls) xs) (.pi A B)`
    is immediately `(convEnds hW hΓ hc_fg).1`! -/
theorem lrSCoreSL_app_of_famSpine_syntactic (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {xs : List (Expr Nat)} {g a b A B : Expr Nat} {args : List CptT} (u : CptT)
    (hc_fg : ConvT E n Γ (foldApps (.const r ls) xs) g (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hlt : xs.length < (piDomsOf m.mtype).length)
    (hlink : PiTowerLinkBelow R E n (sizeOf (convEnds hW hΓ hc_fg).1))
    (hf_sp : LRSCoreSL R E n Γ (foldApps (.const r ls) xs) g (.pi A B) (.spine r args)) :
    LRSCoreSL R E n Γ (.app (foldApps (.const r ls) xs) a) (.app g b)
      (instantiate0 a B) (.spine r (args ++ [u])) := by
  refine lrSCoreSL_app_of_famSpine_step hL hNU hW hΓ hm hind u hc_fg hc_ab hf_sp ?_
  intro ls₁ xs₁ hred
  have e := redR_famApp_eq hL hW hm hind hred
  obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
  injection hconst with _ hls
  subst hls; subst hxs
  exact ⟨(convEnds hW hΓ hc_fg).1, hlt, hlink⟩

/-- **Unified `ApproxT` Application Demand Theorem Across All `FamProbeCptT E` Compacts
    (`lrSCoreSL_app_of_approxT_famProbe`):**
    Removes `#7733`'s `hns : ∀ r args, c ≠ .spine r args` restriction (`RcicNativePiProbeRelApp`):
    for **every** `c` in `FamProbeCptT E` (including `.spine r args`), `ApproxT E (ctxEnvT E Γ) (.app f a) c`
    steps to `LRSCoreSL R E n Γ (.app f a) (.app g b) (instantiate0 a B) c` by dispatching
    `ApproxT.app` through `lrSCoreSL_app_of_lambda_demand` and `ApproxT.appSpine` through
    `lrSCoreSL_app_of_famSpine_step`! -/
theorem lrSCoreSL_app_of_approxT_famProbe (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B : Expr Nat} {c : CptT}
    (hc_fg : ConvT E n Γ f g (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hc : FamProbeCptT E c)
    (happrox : ApproxT E (ctxEnvT E Γ) (.app f a) c)
    (hf : ∀ d, ApproxT E (ctxEnvT E Γ) f d → LRSCoreSL R E n Γ f g (.pi A B) d)
    (ha : ∀ u, ApproxT E (ctxEnvT E Γ) a u → LRSCoreSL R E n Γ a b A u)
    (hsp_ty : ∀ r m ls₁ xs₁,
      E.members r = some m → m.mclass = .inductiveM →
      RedR R Γ f (foldApps (.const r ls₁) xs₁) →
      ∃ df_sp : HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.pi A B),
        xs₁.length < (piDomsOf m.mtype).length ∧
        PiTowerLinkBelow R E n (sizeOf df_sp)) :
    LRSCoreSL R E n Γ (.app f a) (.app g b) (instantiate0 a B) c := by
  cases hc with
  | bot => exact lrSCoreSL_bot _ _ _ _
  | prop =>
      rcases approxT_app_inv happrox with hbot | ⟨graph, s, heq_s, hfg, hs, hax⟩ | ⟨_, _, _, heq, _, _⟩
      · exact CptT.noConfusion hbot
      · rw [heq_s]
        exact lrSCoreSL_app_of_lambda_demand hL hNU hW hΓ hc_fg hc_ab
          (hf (.lam graph) hfg) hs (fun u hu => ha u (hax u hu))
      · exact CptT.noConfusion heq
  | sort =>
      rcases approxT_app_inv happrox with hbot | ⟨graph, s, heq_s, hfg, hs, hax⟩ | ⟨_, _, _, heq, _, _⟩
      · exact CptT.noConfusion hbot
      · rw [heq_s]
        exact lrSCoreSL_app_of_lambda_demand hL hNU hW hΓ hc_fg hc_ab
          (hf (.lam graph) hfg) hs (fun u hu => ha u (hax u hu))
      · exact CptT.noConfusion heq
  | piBotNil =>
      rcases approxT_app_inv happrox with hbot | ⟨graph, s, heq_s, hfg, hs, hax⟩ | ⟨_, _, _, heq, _, _⟩
      · exact CptT.noConfusion hbot
      · rw [heq_s]
        exact lrSCoreSL_app_of_lambda_demand hL hNU hW hΓ hc_fg hc_ab
          (hf (.lam graph) hfg) hs (fun u hu => ha u (hax u hu))
      · exact CptT.noConfusion heq
  | @spine r m args hm hind _ =>
      rcases approxT_app_inv happrox with hbot | ⟨graph, s, heq_s, hfg, hs, hax⟩ |
        ⟨r', args₀, u₀, heq, hfs, _⟩
      · exact CptT.noConfusion hbot
      · rw [heq_s]
        exact lrSCoreSL_app_of_lambda_demand hL hNU hW hΓ hc_fg hc_ab
          (hf (.lam graph) hfg) hs (fun u hu => ha u (hax u hu))
      · injection heq with hr hargs_eq
        subst hr; subst hargs_eq
        exact lrSCoreSL_app_of_famSpine_step hL hNU hW hΓ hm hind u₀ hc_fg hc_ab
          (hf (.spine r args₀) hfs) (fun ls₁ xs₁ hred => hsp_ty r m ls₁ xs₁ hm hind hred)

/-- **3-Observation `FamObsEquiv` Application Closure from `LRSCoreSL`
    (`famObsEquiv_app_of_lrSCoreSL`):** -/
theorem famObsEquiv_app_of_lrSCoreSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B : Expr Nat}
    (_hc_fg : ConvT E n Γ f g (.pi A B))
    (_hc_ab : ConvT E n Γ a b A)
    (hreal_fa : FamProbeRealizedAtT R E n Γ (.app f a))
    (hreal_gb : FamProbeRealizedAtT R E n Γ (.app g b))
    (hrel : ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) (.app f a) c ∨ ApproxT E (ctxEnvT E Γ) (.app g b) c) →
      LRSCoreSL R E n Γ (.app f a) (.app g b) (instantiate0 a B) c) :
    FamObsEquiv R E n Γ (.app f a) (.app g b) :=
  famObsEquiv_of_lrSCoreSL_probes hL hNU hW hΓ hreal_fa hreal_gb hrel

/-- **3-Observation `FamAppHeadAction` Adapter from `LRSCoreSL` (`famAppHeadAction_of_lrSCoreSL`):** -/
theorem famAppHeadAction_of_lrSCoreSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g A B : Expr Nat} (hc_fg : ConvT E n Γ f g (.pi A B))
    (hreal : ∀ {a : Expr Nat}, HasTyT E n Γ a A →
      FamProbeRealizedAtT R E n Γ (.app f a) ∧ FamProbeRealizedAtT R E n Γ (.app g a))
    (hrel : ∀ {a : Expr Nat}, HasTyT E n Γ a A → ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) (.app f a) c ∨ ApproxT E (ctxEnvT E Γ) (.app g a) c) →
      LRSCoreSL R E n Γ (.app f a) (.app g a) (instantiate0 a B) c) :
    FamAppHeadAction R hc_fg := by
  intro a ha
  exact famObsEquiv_app_of_lrSCoreSL hL hNU hW hΓ hc_fg (.refl Γ a A ha)
    (hreal ha).1 (hreal ha).2 (hrel ha)

/-- **3-Observation `FamAppArgAction` Adapter from `LRSCoreSL` (`famAppArgAction_of_lrSCoreSL`):** -/
theorem famAppArgAction_of_lrSCoreSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {g A B : Expr Nat} (hg : HasTyT E n Γ g (.pi A B))
    (hreal : ∀ {a b : Expr Nat}, ConvT E n Γ a b A →
      FamProbeRealizedAtT R E n Γ (.app g a) ∧ FamProbeRealizedAtT R E n Γ (.app g b))
    (hrel : ∀ {a b : Expr Nat}, ConvT E n Γ a b A → ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) (.app g a) c ∨ ApproxT E (ctxEnvT E Γ) (.app g b) c) →
      LRSCoreSL R E n Γ (.app g a) (.app g b) (instantiate0 a B) c) :
    FamAppArgAction R hg := by
  intro a b hab
  exact famObsEquiv_app_of_lrSCoreSL hL hNU hW hΓ (.refl Γ g (.pi A B) hg) hab
    (hreal hab).1 (hreal hab).2 (hrel hab)

/-- **3-Observation Substituted-Endpoint Realization Package (`FamModelProbeAtSubst`):**
    Extends `#7733`'s `ModelProbeAtSubst` (`RcicNativePiProbeRelSubst`) to all 3 type heads
    (Sort + Π + `.inductiveM` family spines) via `FamProbeRealizedAtT`. -/
def FamModelProbeAtSubst (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (σ₁ σ₂ : Expr Nat → Expr Nat) (M N : Expr Nat) : Prop :=
  FamProbeRealizedAtT R E n Γ (σ₁ M) ∧
  FamProbeRealizedAtT R E n Γ (σ₂ N)

/-- Identity-substitution specialization of `FamModelProbeAtSubst` (`famModelProbeAtSubst_id_of_realized`). -/
theorem famModelProbeAtSubst_id_of_realized {Γ : LCtx} {M N : Expr Nat}
    (hM : FamProbeRealizedAtT R E n Γ M) (hN : FamProbeRealizedAtT R E n Γ N) :
    FamModelProbeAtSubst R E n Γ (fun X => X) (fun X => X) M N :=
  ⟨hM, hN⟩

/-- **3-Observation Substituted-Endpoint Equivalence from `LRSCoreSL` at ANY Ambient Index `I`
    (`famObsEquiv_of_substRelation_lrSCoreSL`):**
    Extends `#7733`'s `probeEquivT_of_substRelation` to all 3 type heads and to **any** ambient
    index `I : Expr Nat` (such as `I = instantiate0 value B` for `letE`), using `lrSCoreSL_famProbe_symm`
    for the reverse direction without requiring `I = .sort w`! -/
theorem famObsEquiv_of_substRelation_lrSCoreSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {σ₁ σ₂ : Expr Nat → Expr Nat} {M N I : Expr Nat}
    (hprobe : FamModelProbeAtSubst R E n Γ σ₁ σ₂ M N)
    (hrel : ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) (σ₁ M) c ∨ ApproxT E (ctxEnvT E Γ) (σ₂ N) c) →
      LRSCoreSL R E n Γ (σ₁ M) (σ₂ N) I c) :
    FamObsEquiv R E n Γ (σ₁ M) (σ₂ N) :=
  famObsEquiv_of_lrSCoreSL_probes hL hNU hW hΓ hprobe.1 hprobe.2 hrel

/-- **Body-at-Same-Value Edge (`instantiate0 value body ~ instantiate0 value body'`) from `LRSCoreSL`
    (`famBodyAtValue_of_lrSCoreSL`):** -/
theorem famBodyAtValue_of_lrSCoreSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {value body body' I : Expr Nat}
    (hprobe : FamModelProbeAtSubst R E n Γ (instantiate0 value) (instantiate0 value) body body')
    (hrel : ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) (instantiate0 value body) c ∨
        ApproxT E (ctxEnvT E Γ) (instantiate0 value body') c) →
      LRSCoreSL R E n Γ (instantiate0 value body) (instantiate0 value body') I c) :
    FamObsEquiv R E n Γ (instantiate0 value body) (instantiate0 value body') :=
  famObsEquiv_of_lrSCoreSL_probes hL hNU hW hΓ hprobe.1 hprobe.2 hrel

/-- **Value-in-Same-Body Edge (`instantiate0 value body' ~ instantiate0 value' body'`) from `LRSCoreSL`
    (`famValueInBody_of_lrSCoreSL`):** -/
theorem famValueInBody_of_lrSCoreSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {value value' body' I : Expr Nat}
    (hprobe : FamModelProbeAtSubst R E n Γ (instantiate0 value) (instantiate0 value') body' body')
    (hrel : ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) (instantiate0 value body') c ∨
        ApproxT E (ctxEnvT E Γ) (instantiate0 value' body') c) →
      LRSCoreSL R E n Γ (instantiate0 value body') (instantiate0 value' body') I c) :
    FamObsEquiv R E n Γ (instantiate0 value body') (instantiate0 value' body') :=
  famObsEquiv_of_lrSCoreSL_probes hL hNU hW hΓ hprobe.1 hprobe.2 hrel

/-- **Mixed-Substitution Edges (`FamMixedSubstEdges`) from `LRSCoreSL`
    (`famMixedSubstEdges_of_lrSCoreSL`):** -/
theorem famMixedSubstEdges_of_lrSCoreSL (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {value value' body body' I₁ I₂ : Expr Nat}
    (hprobe₁ : FamModelProbeAtSubst R E n Γ (instantiate0 value) (instantiate0 value) body body')
    (hrel₁ : ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) (instantiate0 value body) c ∨
        ApproxT E (ctxEnvT E Γ) (instantiate0 value body') c) →
      LRSCoreSL R E n Γ (instantiate0 value body) (instantiate0 value body') I₁ c)
    (hprobe₂ : FamModelProbeAtSubst R E n Γ (instantiate0 value) (instantiate0 value') body' body')
    (hrel₂ : ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) (instantiate0 value body') c ∨
        ApproxT E (ctxEnvT E Γ) (instantiate0 value' body') c) →
      LRSCoreSL R E n Γ (instantiate0 value body') (instantiate0 value' body') I₂ c) :
    FamMixedSubstEdges R E n Γ value value' body body' :=
  ⟨famBodyAtValue_of_lrSCoreSL hL hNU hW hΓ hprobe₁ hrel₁,
   famValueInBody_of_lrSCoreSL hL hNU hW hΓ hprobe₂ hrel₂⟩


/-! #### §11 Part C — End-to-End 18-Constructor `WhStepRecKCanon` Adapter Assembly (`FamProbeAdapterInputsRKCanon`, `famObsConvLinks_whStepRecKCanon_of_adapterInputs`) and Positive Non-Vacuity Witnesses in `eqEnvT`, `pinLoopEnvT`, `trueEnvU`, and `andEnvU` -/

/-- **Bundled Remaining-4-Port Adapter Inputs for `FamConvObsMotive (WhStepRecKCanon E)`
    (`FamProbeAdapterInputsRKCanon`):**
    Combines:
    1. `FamProbeTypingLemmaT E n` + `FamTypedProbeRealizationT (WhStepRecKCanon E) E n` (which together
       discharge `ConvT.eta` and `ConvT.irr` via `famFunctionNoTypeProbe_of_typing_realization` and
       `famPropNoTypeProbe_of_typing_realization`),
    2. `FamAppHeadAction` + `FamAppArgAction` for `ConvT.app`, and
    3. `FamMixedSubstEdges` for `ConvT.letE`
    with the 14 unconditionally proved `ConvT` constructors at `WhStepRecKCanon E`! -/
def FamProbeAdapterInputsRKCanon (E : ResolvedEnv) (n : Nat) : Prop :=
  FamProbeTypingLemmaT E n ∧
  FamTypedProbeRealizationT (WhStepRecKCanon E) E n ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f g A B : Expr Nat}
    (hf : ConvT E n Γ f g (.pi A B)),
    FamConvObsMotive (WhStepRecKCanon E) hf →
    FamAppHeadAction (WhStepRecKCanon E) hf) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {g A B : Expr Nat}
    (hg : HasTyT E n Γ g (.pi A B)),
    FamAppArgAction (WhStepRecKCanon E) hg) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ v v' A)
    (hb : ConvT E n (.letBinding A v :: Γ) b b' B),
    FamConvObsMotive (WhStepRecKCanon E) hA →
    FamConvObsMotive (WhStepRecKCanon E) hv →
    FamConvObsMotive (WhStepRecKCanon E) hb →
    FamMixedSubstEdges (WhStepRecKCanon E) E n Γ v v' b b')

/-- **All-18-Constructor `FamObsConvLinks (WhStepRecKCanon E) E n` from `FamProbeAdapterInputsRKCanon`
    (`famObsConvLinks_whStepRecKCanon_of_adapterInputs`):** -/
theorem famObsConvLinks_whStepRecKCanon_of_adapterInputs (hW : EnvWfT E)
    (hadapt : FamProbeAdapterInputsRKCanon E n) :
    FamObsConvLinks (WhStepRecKCanon E) E n := by
  obtain ⟨hty, hreal, hhead, harg, hlet⟩ := hadapt
  refine famObsConvLinks_whStepRecKCanon_of_four_ports hW ?_ ?_
    (famFunctionNoTypeProbe_of_typing_realization hty hreal)
    (famPropNoTypeProbe_of_typing_realization hty hreal)
  · intro Γ hΓ f g a b A B hf ha ihf _
    exact famConvObs_app_of_actions hW hΓ hf ha (hhead hΓ hf ihf) (harg hΓ (convEnds hW hΓ hf).2.1)
  · intro Γ hΓ A A' v v' b b' B u hA hv hb ihA ihv ihb
    exact famConvObs_whStepRecKCanon_letE_of_mixedSubst hW hΓ hA hv hb
      (hlet hΓ hA hv hb ihA ihv ihb)

/-- **`PiRowField E n` from `FamProbeAdapterInputsRKCanon E n` (`piRowField_of_whStepRecKCanon_adapterInputs`):** -/
theorem piRowField_of_whStepRecKCanon_adapterInputs (hW : EnvWfT E)
    (hadapt : FamProbeAdapterInputsRKCanon E n) :
    PiRowField E n :=
  piRowField_of_famObsConvLinks (readbackLaws_whStepRecKCanon E) hW
    (famObsConvLinks_whStepRecKCanon_of_adapterInputs hW hadapt)

/-- **`FamAppRowLink E n` from `FamProbeAdapterInputsRKCanon E n` (`famAppRow_of_whStepRecKCanon_adapterInputs`):** -/
theorem famAppRow_of_whStepRecKCanon_adapterInputs (hW : EnvWfT E)
    (hadapt : FamProbeAdapterInputsRKCanon E n) :
    FamAppRowLink E n :=
  famAppRow_of_famObsConvLinks (readbackLaws_whStepRecKCanon E) hW
    (famObsConvLinks_whStepRecKCanon_of_adapterInputs hW hadapt)

/-- **`FamRelevantSlotConv E n` from `FamProbeAdapterInputsRKCanon E n`
    (`famRelevantSlotConv_of_whStepRecKCanon_adapterInputs`):** -/
theorem famRelevantSlotConv_of_whStepRecKCanon_adapterInputs (hW : EnvWfT E)
    (hadapt : FamProbeAdapterInputsRKCanon E n) :
    FamRelevantSlotConv E n :=
  famRelevantSlotConv_of_famObsConvLinks (readbackLaws_whStepRecKCanon E) hW
    (famObsConvLinks_whStepRecKCanon_of_adapterInputs hW hadapt)

/-- **`TypedRowsWf E n` from `AllBelowScoped` + `FamProbeAdapterInputsRKCanon E n`
    (`typedRowsWf_of_allBelowScoped_whStepRecKCanon_adapterInputs`):** -/
theorem typedRowsWf_of_allBelowScoped_whStepRecKCanon_adapterInputs (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hadapt : FamProbeAdapterInputsRKCanon E n) :
    TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_famObsConvLinks (readbackLaws_whStepRecKCanon E) hW hBel
    (famObsConvLinks_whStepRecKCanon_of_adapterInputs hW hadapt)

/-- Concrete `LRSCoreSL (WhStepRecKCanon trueEnvU)` witness on `trueVarSort` at `.sort`. -/
theorem lrSCoreSL_whStepRecKCanon_trueVarSort (n : Nat) :
    LRSCoreSL (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarSort (.sort .zero) (.sort (.succ .zero)) .sort := by
  rw [lrSCoreSL_sort_iff]
  exact ⟨⟨_, .refl _⟩, _, _, redR_of_whRedRecKCanon whRedRecKCanon_trueVarSort, .refl _⟩

/-- Concrete `LRSCoreSL (WhStepRecKCanon trueEnvU)` witness on `trueVarPi` at `.pi .bot []`. -/
theorem lrSCoreSL_whStepRecKCanon_trueVarPi (n : Nat) :
    LRSCoreSL (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarPi PiModelDeltaIotaAudit.idPiProp (.sort (.succ .zero)) (.pi .bot []) :=
  piProbeSL_iff_lrSCore.mpr (lrSCore_whStepRecKCanon_trueVarPi n)

/-- Concrete `LRSCoreSL (WhStepRecKCanon trueEnvU)` witness on `trueVarFam` at `.spine 0 []`. -/
theorem lrSCoreSL_whStepRecKCanon_trueVarFam (n : Nat) :
    LRSCoreSL (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarFam (.const 0 []) (.sort .zero) (.spine 0 []) := by
  rw [lrSCoreSL_spine_iff]
  have hm0 : trueEnvU.members 0 = some trueFamMember := rfl
  have h1 : RedR (WhStepRecKCanon trueEnvU) trueVarCtx trueVarFam (foldApps (.const 0 []) []) :=
    redR_of_whRedRecKCanon whRedRecKCanon_trueVarFam
  exact ⟨Or.inl ⟨⟨.of trueVarCtx trueVarFam (.const 0 []) .zero (convT_trueVarFam n)⟩,
      Or.inl ⟨_, .refl _⟩⟩,
    Or.inl ⟨trueFamMember, [], [], [], [], hm0, rfl, rfl, rfl, Nat.zero_le _,
      h1, .refl _,
      fun _ hs => whStepRecKCanon_famApp_false trueEnvUWfT hm0 rfl hs,
      fun _ hs => whStepRecKCanon_famApp_false trueEnvUWfT hm0 rfl hs,
      trivial, Nat.le_refl 0, Nat.le_refl 0, .nil _⟩⟩

/-- Concrete `LRSCoreSL (WhStepRecKCanon andEnvU)` witness on `mixAndRedex` at `.pi .bot []`. -/
theorem lrSCoreSL_whStepRecKCanon_mixAnd :
    LRSCoreSL (WhStepRecKCanon andEnvU) andEnvU 0 mixAndCtx
      mixAndRedex mixPi (.sort (.succ .zero)) (.pi .bot []) :=
  piProbeSL_iff_lrSCore.mpr lrSCore_whStepRecKCanon_mixAnd

/-- Concrete `LRSCoreSL (WhStepRecKCanon eqEnvT)` witness on `#7733`'s `eqCanonGapRedex` at `.sort`. -/
theorem lrSCoreSL_whStepRecKCanon_eqCanonGap_sort :
    LRSCoreSL (WhStepRecKCanon eqEnvT) eqEnvT 0 eqCanonGapCtx
      eqCanonGapRedex (.sort .zero) (.sort (.succ .zero)) .sort := by
  rw [lrSCoreSL_sort_iff]
  exact ⟨⟨_, .refl _⟩, .zero, .zero, redR_whStepRecKCanon_eqCanonGapRedex, .refl _⟩

/-- Concrete `LRSCoreSL (WhStepRecKCanon pinLoopEnvT)` witness on `loopCanonRedex` at `.sort`. -/
theorem lrSCoreSL_whStepRecKCanon_loopCanon_sort :
    LRSCoreSL (WhStepRecKCanon pinLoopEnvT) pinLoopEnvT 0 loopCanonCtx
      loopCanonRedex (.sort .zero) (.sort (.succ .zero)) .sort := by
  rw [lrSCoreSL_sort_iff]
  exact ⟨⟨_, .refl _⟩, .zero, .zero, redR_whStepRecKCanon_loopCanonRedex, .refl _⟩


/-! ### §12 — Refutation of Unrestricted `TypingLemmaT` vs. Saturated-Probe `FamProbeTypingLemmaT`,
    Type-Discipline-Guarded `SpineClauseSLT` / `LRSCoreSLT` / `LRSSLT` Resolving `#7726`/`#7731`'s
    Escape Obstruction, and Semantic Non-Sort Proposition Classifier `IsSemNoSortPropRecKCanon` /
    `LRTermFamNoSortRKCanon` -/

/-! #### §12 Part A — Family-Side & Universal Refutations of Unrestricted `TypingLemmaT E n` vs. Unconditional Satisfaction of `FamProbeTypingLemmaT`'s Probe-Typing Clause Across All 6 Canonical Families -/

/-- `levelsBounded n (List.replicate k Level.zero) = true` for all `n, k : Nat`. -/
theorem famLevelsBounded_replicate_zero (n k : Nat) :
    levelsBounded n (List.replicate k Level.zero) = true := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate, levelsBounded, ih]; rfl

/-- Any `.inductiveM` member with `m.body = none` is a `RigidConst E r` (with **zero** `EnvWfT E`). -/
theorem rigidConst_of_inductiveM_noBody {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hbody : m.body = none) :
    RigidConst E r := by
  intro m' hm'
  have em : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst em
  refine ⟨Or.inl hbody, fun hrec => ?_⟩
  rw [hind] at hrec
  exact MemberClass.noConfusion hrec

/-- **Family-Head Refutation of Unrestricted `TypingLemmaT E n` Without `EnvWfT E`
    (`not_typingLemmaT_of_inductiveM_noBody_posArity`):**
    In **any** environment `E` containing an indexed or parameterized `.inductiveM` family `r`
    (`0 < (piDomsOf m.mtype).length` and `m.body = none`), the unapplied family head
    `.const r (List.replicate m.arity .zero)` has type `instantiateLevels ls m.mtype = .pi D B`
    and has compact `.spine r []` in `ApproxT E (ctxEnvT E [])`, whereas `¬ ElT E (ctxEnvT E []) (.pi D B) (.spine r [])`
    by `not_elT_pi_spine`! -/
theorem not_typingLemmaT_of_inductiveM_noBody_posArity {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hbody : m.body = none)
    (hpos : 0 < (piDomsOf m.mtype).length) (n : Nat) :
    ¬ TypingLemmaT E n := by
  intro hty
  let ls := List.replicate m.arity Level.zero
  have hconst : HasTyT E n [] (.const r ls) (instantiateLevels ls m.mtype) :=
    .const [] r ls m hm (List.length_replicate _ _) (famLevelsBounded_replicate_zero n m.arity)
  obtain ⟨D, B, hpi⟩ := instTelescope_member_eq_pi_of_lt m ls (xs := []) hpos
  change instantiateLevels ls m.mtype = .pi D B at hpi
  rw [hpi] at hconst
  have hap : ApproxT E (ctxEnvT E []) (.const r ls) (.spine r []) :=
    .const (ctxEnvT E []) r ls (rigidConst_of_inductiveM_noBody hm hind hbody)
      (not_propCtorT_of_inductiveM hm hind)
  exact not_elT_pi_spine r [] (hty .nil hconst (.spine r []) hap)

/-- **Family-Head Refutation of Unrestricted `TypingLemmaT E n` Under `EnvWfT E`
    (`not_typingLemmaT_of_inductiveM_posArity`):**
    Under `EnvWfT E`, `m.body = none` holds automatically for every `.inductiveM` member, so
    every environment with an indexed/parameterized `.inductiveM` family (`0 < (piDomsOf m.mtype).length`)
    refutes unrestricted `TypingLemmaT E n`! -/
theorem not_typingLemmaT_of_inductiveM_posArity (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hpos : 0 < (piDomsOf m.mtype).length) (n : Nat) :
    ¬ TypingLemmaT E n := by
  intro hty
  let ls := List.replicate m.arity Level.zero
  have hconst : HasTyT E n [] (.const r ls) (instantiateLevels ls m.mtype) :=
    .const [] r ls m hm (List.length_replicate _ _) (famLevelsBounded_replicate_zero n m.arity)
  obtain ⟨D, B, hpi⟩ := instTelescope_member_eq_pi_of_lt m ls (xs := []) hpos
  change instantiateLevels ls m.mtype = .pi D B at hpi
  rw [hpi] at hconst
  have hap : ApproxT E (ctxEnvT E []) (.const r ls) (.spine r []) :=
    approxT_const_inductiveM hW (ctxEnvT E []) hm hind ls
  exact not_elT_pi_spine r [] (hty .nil hconst (.spine r []) hap)

/-- Unrestricted `TypingLemmaT andEnvU n` is false for every `n : Nat` (`not_typingLemmaT_andEnvU`). -/
theorem not_typingLemmaT_andEnvU (n : Nat) : ¬ TypingLemmaT andEnvU n :=
  not_typingLemmaT_of_inductiveM_noBody_posArity (r := 0) (m := andFamMember) rfl rfl rfl (by decide) n

/-- Unrestricted `TypingLemmaT exEnv n` is false for every `n : Nat` (`not_typingLemmaT_exEnv`). -/
theorem not_typingLemmaT_exEnv (n : Nat) : ¬ TypingLemmaT exEnv n :=
  not_typingLemmaT_of_inductiveM_noBody_posArity exEnv_mem1 rfl rfl (by decide) n

/-- Unrestricted `TypingLemmaT eqEnvT n` is false for every `n : Nat` (`not_typingLemmaT_eqEnvT`). -/
theorem not_typingLemmaT_eqEnvT (n : Nat) : ¬ TypingLemmaT eqEnvT n :=
  not_typingLemmaT_of_inductiveM_noBody_posArity (r := 63) (m := eqFamT) rfl rfl rfl (by decide) n

/-- Closed polymorphic constant-Prop function `λ (α : Type 0) (x : α), Prop` (`famCexIdLam`). -/
def famCexIdLam : Expr Nat :=
  .lam (.sort (.succ .zero)) (.lam (.bvar 0) (.sort .zero))

/-- Closed polymorphic Π-type `∀ (α : Type 0), α → Type 0` (`famCexIdPi`). -/
def famCexIdPi : Expr Nat :=
  .pi (.sort (.succ .zero)) (.pi (.bvar 0) (.sort (.succ .zero)))

/-- Two-step `.lam` compact `CptT.lam [([], .lam [([], .prop)]), ([.sort], .lam [([.prop], .prop)])]`
    on `famCexIdLam`: step 1 demands `[]` from `α` and `[]` from `x`; step 2 demands `[.sort]` from
    `α` and `[.prop]` from `x`. -/
def famCexIdLamCpt : CptT :=
  .lam [([], .lam [([], .prop)]), ([.sort], .lam [([.prop], .prop)])]

/-- `HasTyT E n [] famCexIdLam famCexIdPi` holds in **every** environment `E` and level bound `n`. -/
def hasTyT_famCexIdLam (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] famCexIdLam famCexIdPi :=
  .lam [] (.sort (.succ .zero)) (.succ (.succ .zero))
    (.lam (.bvar 0) (.sort .zero)) (.pi (.bvar 0) (.sort (.succ .zero)))
    (.sort [] (.succ .zero))
    (.lam [.assumption (.sort (.succ .zero))] (.bvar 0) (.succ .zero)
      (.sort .zero) (.sort (.succ .zero))
      (.bvar [.assumption (.sort (.succ .zero))] 0 (.sort (.succ .zero)) rfl)
      (.sort [.assumption (.bvar 0), .assumption (.sort (.succ .zero))] .zero))

/-- `ApproxT E ρ famCexIdLam famCexIdLamCpt` holds in **every** `E` and `ρ`. -/
theorem approxT_famCexIdLam_cpt (E : ResolvedEnv) (ρ : EnvT) :
    ApproxT E ρ famCexIdLam famCexIdLamCpt := by
  have hsc1 : sortCode (.succ .zero) = .sort := rfl
  refine .lam (a := .sort) (hsc1 ▸ .sort ρ (.succ .zero)) ?_
    ⟨([], .lam [([], .prop)]), List.Mem.head _, fun h => CptT.noConfusion h⟩ ?_
  · intro s hs u hu
    rcases List.mem_cons.mp hs with rfl | hs₂
    · exact (List.not_mem_nil u hu).elim
    · rcases List.mem_singleton.mp hs₂ with rfl
      rcases List.mem_singleton.mp hu with rfl
      rw [CTyS]; exact Or.inr .sort
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs₂
    · refine .lam (a := .bot) (.bot _ (.bvar 0)) ?_
        ⟨([], .prop), List.Mem.head _, fun h => CptT.noConfusion h⟩ ?_
      · intro s' hs' u hu
        rcases List.mem_singleton.mp hs' with rfl
        exact (List.not_mem_nil u hu).elim
      · intro s' hs'
        rcases List.mem_singleton.mp hs' with rfl
        exact sortCode_zero ▸ .sort _ .zero
    · rcases List.mem_singleton.mp hs₂ with rfl
      refine .lam (a := .sort) (.bvar (List.Mem.head [])) ?_
        ⟨([.prop], .prop), List.Mem.head _, fun h => CptT.noConfusion h⟩ ?_
      · intro s' hs' u hu
        rcases List.mem_singleton.mp hs' with rfl
        rcases List.mem_singleton.mp hu with rfl
        rw [CTyS]; exact Or.inr .prop
      · intro s' hs'
        rcases List.mem_singleton.mp hs' with rfl
        exact sortCode_zero ▸ .sort _ .zero

/-- `famCexIdLamCpt` is **never** in `ElT E ρ famCexIdPi` (`not_elT_famCexIdPi_cpt`):
    coverage on step 1 `([], .lam [([], .prop)])` forces any covering step `t ∈ f` of `famCexIdPi`
    to have `t.1 = []`, so `.bvar 0` in the inner domain of `.pi (.bvar 0) (.sort (.succ .zero))`
    evaluates only to `.bot`; since `t.1 = [] ⊆ [.sort]`, `t` is also compatible with step 2
    `([.sort], .lam [([.prop], .prop)])`, forcing `CTyS E .prop .bot`, contradiction! -/
theorem not_elT_famCexIdPi_cpt (E : ResolvedEnv) (ρ : EnvT) :
    ¬ ElT E ρ famCexIdPi famCexIdLamCpt := by
  rintro ⟨a, hap, hcty⟩
  rcases approxT_pi_inv hap with rfl | ⟨b, f, rfl, _, hf⟩
  · exact CptT.noConfusion (ctyS_bot_inv hcty)
  · rcases ctyS_pi_inv hcty with hbot | ⟨g, heq, _, _, hcod, hcov⟩
    · exact CptT.noConfusion hbot
    · injection heq with hg
      subst hg
      have hs₁ : (([], .lam [([], .prop)]) : List CptT × CptT) ∈
          [([], .lam [([], .prop)]), ([.sort], .lam [([.prop], .prop)])] :=
        List.Mem.head _
      have hs₂ : (([.sort], .lam [([.prop], .prop)]) : List CptT × CptT) ∈
          [([], .lam [([], .prop)]), ([.sort], .lam [([.prop], .prop)])] :=
        List.Mem.tail _ (List.Mem.head _)
      rcases hcov ([], .lam [([], .prop)]) hs₁ with h0 | ⟨t, ht, hcomp₁⟩
      · exact CptT.noConfusion h0
      · have hcomp₂ : ∀ v ∈ t.1, v ∈ ([CptT.sort] : List CptT) :=
          fun v hv => (List.not_mem_nil v (hcomp₁ v hv)).elim
        have hcty_inner : CTyS E (.lam [([.prop], .prop)]) t.2 :=
          hcod ([.sort], .lam [([.prop], .prop)]) hs₂ t ht hcomp₂
        rcases approxT_pi_inv (hf t ht).2 with hbot_t2 | ⟨d, g', ht2_eq, hd, _⟩
        · rw [hbot_t2] at hcty_inner
          exact CptT.noConfusion (ctyS_bot_inv hcty_inner)
        · rw [ht2_eq] at hcty_inner
          have hd_bot : d = .bot := by
            rcases approxT_bvar_inv hd with rfl | hmem
            · rfl
            · exact (List.not_mem_nil d (hcomp₁ d hmem)).elim
          subst hd_bot
          rcases ctyS_pi_inv hcty_inner with hbot | ⟨_, heq', _, hdom', _, _⟩
          · exact CptT.noConfusion hbot
          · injection heq' with hg'
            subst hg'
            have hprop_bot : CTyS E .prop .bot :=
              hdom' ([.prop], .prop) (List.Mem.head []) .prop (List.Mem.head [])
            exact CptT.noConfusion (ctyS_bot_inv hprop_bot)

/-- **Universal Refutation of Unrestricted `TypingLemmaT E n` (`not_typingLemmaT_all`):**
    Unrestricted `TypingLemmaT E n` is false for **every** `E : ResolvedEnv` and **every** `n : Nat`! -/
theorem not_typingLemmaT_all (E : ResolvedEnv) (n : Nat) :
    ¬ TypingLemmaT E n :=
  fun hty => not_elT_famCexIdPi_cpt E (ctxEnvT E [])
    (hty .nil (hasTyT_famCexIdLam E n) famCexIdLamCpt (approxT_famCexIdLam_cpt E (ctxEnvT E [])))

/-- No `.lam g` compact lies in `FamProbeCptT E` (`not_famProbeCptT_lam`). -/
theorem not_famProbeCptT_lam (g : List (List CptT × CptT)) :
    ¬ FamProbeCptT E (.lam g) := fun h => by cases h

/-- No `.lam g` compact lies in `FamSatProbeCptT E` (`not_famSatProbeCptT_lam`). -/
theorem not_famSatProbeCptT_lam (g : List (List CptT × CptT)) :
    ¬ FamSatProbeCptT E (.lam g) := fun h => by cases h

/-- No `.spine r args` with `args.length ≠ (piDomsOf m.mtype).length` lies in `FamSatProbeCptT E`
    (`not_famSatProbeCptT_spine_of_length_ne`). -/
theorem not_famSatProbeCptT_spine_of_length_ne {r : Nat} {m : CheckedMember} {args : List CptT}
    (hm : E.members r = some m) (hne : args.length ≠ (piDomsOf m.mtype).length) :
    ¬ FamSatProbeCptT E (.spine r args) := by
  intro h
  cases h with
  | @spine _ m' _ hm' _ hlen _ =>
      have em : m' = m := Option.some.inj (hm'.symm.trans hm)
      subst em
      exact hne hlen

/-- No `.spine r args` for a non-`.inductiveM` member lies in `FamProbeCptT E`
    (`not_famProbeCptT_spine_of_not_inductiveM`). -/
theorem not_famProbeCptT_spine_of_not_inductiveM {r : Nat} {m : CheckedMember} {args : List CptT}
    (hm : E.members r = some m) (hnot : m.mclass ≠ .inductiveM) :
    ¬ FamProbeCptT E (.spine r args) := by
  intro h
  cases h with
  | @spine _ m' _ hm' hind _ =>
      have em : m' = m := Option.some.inj (hm'.symm.trans hm)
      subst em
      exact hnot hind

/-- No `.spine r args` for a non-`.inductiveM` member lies in `FamSatProbeCptT E`
    (`not_famSatProbeCptT_spine_of_not_inductiveM`). -/
theorem not_famSatProbeCptT_spine_of_not_inductiveM {r : Nat} {m : CheckedMember} {args : List CptT}
    (hm : E.members r = some m) (hnot : m.mclass ≠ .inductiveM) :
    ¬ FamSatProbeCptT E (.spine r args) :=
  fun h => not_famProbeCptT_spine_of_not_inductiveM hm hnot (famSatProbeCptT_to_famProbeCptT h)

/-- On `FamProbeCptT E u`, `ElT E ρ (.pi A B) u` holds **if and only if** `u = .bot`
    (`elT_pi_iff_eq_bot_of_famProbeCptT`). -/
theorem elT_pi_iff_eq_bot_of_famProbeCptT {ρ : EnvT} {A B : Expr Nat} {u : CptT}
    (hu : FamProbeCptT E u) :
    ElT E ρ (.pi A B) u ↔ u = .bot := by
  constructor
  · intro h
    rcases elT_pi_element_shape h with rfl | ⟨_, rfl⟩
    · rfl
    · cases hu
  · rintro rfl
    exact elT_bot E ρ (.pi A B)

/-- `.pi .bot []` is in `IsPropCT E` (`isPropCT_pi_bot_nil`). -/
theorem isPropCT_pi_bot_nil : IsPropCT E (.pi .bot []) :=
  .pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim)

/-- `.pi .bot []` is a `TyCodeCT` (`tyCodeCT_pi_bot_nil`). -/
theorem tyCodeCT_pi_bot_nil : TyCodeCT (.pi .bot []) :=
  .pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim)

/-- `CTyS E (.pi .bot []) (sortCode w)` holds for every universe level `w : Level`
    (`ctyS_pi_bot_nil_sortCode`). -/
theorem ctyS_pi_bot_nil_sortCode (w : Level) : CTyS E (.pi .bot []) (sortCode w) := by
  rcases sortCode_prop_or_sort w with h | h <;> rw [h]
  · rw [CTyS]; exact Or.inr isPropCT_pi_bot_nil
  · rw [CTyS]; exact Or.inr tyCodeCT_pi_bot_nil

/-- `.pi .bot []` lies in `ElT E ρ (.sort w)` for every `ρ : EnvT` and `w : Level`
    (`elT_sort_pi_bot_nil`). -/
theorem elT_sort_pi_bot_nil (ρ : EnvT) (w : Level) :
    ElT E ρ (.sort w) (.pi .bot []) :=
  ⟨sortCode w, .sort ρ w, ctyS_pi_bot_nil_sortCode w⟩

/-- **Canonical Family 1 (`famProbeTyping_at_sort`):**
    Every compact `u` of `.sort l` in `ApproxT E ρ (.sort l) u` lies in `ElT E ρ (.sort (.succ l))`
    (the exact type assigned by `HasTyT.sort Γ l`). -/
theorem famProbeTyping_at_sort (ρ : EnvT) (l : Level) {u : CptT}
    (hap : ApproxT E ρ (.sort l) u) :
    ElT E ρ (.sort (.succ l)) u := by
  have hw : ¬ eqN (.succ l) .zero := by
    intro h
    have h0 : eval (fun _ => some 0) (.succ l) = some 0 := h (fun _ => some 0)
    simp only [eval] at h0
    cases hev : eval (fun _ => some 0) l <;> rw [hev] at h0 <;> simp only [Option.map] at h0
    · exact Option.noConfusion h0
    · exact Nat.noConfusion (Option.some.inj h0)
  rcases approxT_sort_inv hap with rfl | rfl
  · exact elT_bot E ρ (.sort (.succ l))
  · refine (elT_sort_iff E ρ hw (sortCode l)).mpr (Or.inr ?_)
    rcases sortCode_prop_or_sort l with h | h <;> rw [h]
    · exact .prop
    · exact .sort

/-- **Canonical Family 2 (`famProbeTyping_at_pi`):**
    Every probe compact `u` (`FamProbeCptT E u`) of `.pi A B` in `ApproxT E ρ (.pi A B) u`
    lies in `ElT E ρ (.sort w)` (avoiding `TypingLemmaT`'s multi-step `.pi a f` failure!). -/
theorem famProbeTyping_at_pi (ρ : EnvT) (A B : Expr Nat) (w : Level) {u : CptT}
    (hu : FamProbeCptT E u) (hap : ApproxT E ρ (.pi A B) u) :
    ElT E ρ (.sort w) u := by
  rcases approxT_pi_famProbeCptT hu hap with rfl | rfl
  · exact elT_bot E ρ (.sort w)
  · exact elT_sort_pi_bot_nil ρ w

/-- **Canonical Family 3 (`famProbeTyping_at_lam`):**
    Every probe compact `u` (`FamProbeCptT E u`) of `.lam A b` in `ApproxT E ρ (.lam A b) u`
    is `.bot` and therefore lies in `ElT E ρ T u` for **every** type `T` (completely avoiding
    `not_typingLemmaT_all`!). -/
theorem famProbeTyping_at_lam (ρ : EnvT) (A b T : Expr Nat) {u : CptT}
    (hu : FamProbeCptT E u) (hap : ApproxT E ρ (.lam A b) u) :
    ElT E ρ T u := by
  rcases approxT_lam_inv hap with rfl | ⟨_, _, rfl, _, _⟩
  · exact elT_bot E ρ T
  · cases hu

/-- **Canonical Family 4 (`famProbeTyping_at_famApp_unsaturated`):**
    For any unsaturated `.inductiveM` family spine `foldApps (.const r ls) xs` with
    `xs.length < (piDomsOf m.mtype).length`, every saturated-probe compact `u` (`FamSatProbeCptT E u`)
    in `ApproxT E ρ (foldApps (.const r ls) xs) u` is `.bot` and therefore lies in `ElT E ρ T u` for
    **every** type `T` (completely avoiding `not_typingLemmaT_of_inductiveM_posArity`!). -/
theorem famProbeTyping_at_famApp_unsaturated (hW : EnvWfT E) (ρ : EnvT)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (ls : List Level) {xs : List (Expr Nat)} (hlt : xs.length < (piDomsOf m.mtype).length)
    (T : Expr Nat) {u : CptT} (hu : FamSatProbeCptT E u)
    (hap : ApproxT E ρ (foldApps (.const r ls) xs) u) :
    ElT E ρ T u := by
  rcases approxT_foldApps_const_inductiveM_inv hW hm hind ls xs hap with rfl | ⟨us, rfl, hus⟩
  · exact elT_bot E ρ T
  · have hlen_us : us.length = xs.length := (approxTArgs_length hus).symm
    exact (not_famSatProbeCptT_spine_of_length_ne hm (by omega) hu).elim

/-- **Canonical Family 5 (`famProbeTyping_at_famApp_allArity`):**
    For **every** prefix length `xs.length ≤ (piDomsOf m.mtype).length` (both unsaturated and
    saturated!), every `FamSatProbeCptT E u` compact of `foldApps (.const r ls) xs` lies in
    `ElT E ρ (instTelescope (instantiateLevels ls m.mtype) xs) u` whenever the family is either a
    proposition family (`piBody m.mtype = .sort .zero`) or instantiated at a non-zero sort level
    (`¬ eqN (instLevel ls (inductiveSortLevel hW hm hind)) .zero`)! -/
theorem famProbeTyping_at_famApp_allArity (hW : EnvWfT E) (ρ : EnvT)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (ls : List Level)
    (hsort : piBody m.mtype = .sort .zero ∨ ¬ eqN (instLevel ls (inductiveSortLevel hW hm hind)) .zero)
    {xs : List (Expr Nat)} (hle : xs.length ≤ (piDomsOf m.mtype).length)
    {u : CptT} (hu : FamSatProbeCptT E u)
    (hap : ApproxT E ρ (foldApps (.const r ls) xs) u) :
    ElT E ρ (instTelescope (instantiateLevels ls m.mtype) xs) u := by
  rcases Nat.lt_or_eq_of_le hle with hlt | hlen
  · exact famProbeTyping_at_famApp_unsaturated hW ρ hm hind ls hlt _ hu hap
  · rw [instTelescope_instMtype_eq_sort hW hm hind ls hlen]
    rcases hsort with hprop | hnz
    · exact typingLemma_at_famApp_prop hW hm hind hprop ls xs _ hap
    · exact typingLemma_at_famApp_nonprop hW hm hind ls xs hnz hap

/-- **Canonical Family 6a (`famProbeTyping_at_nonInductive_rigidSpine`):**
    For any rigid constant `r` (`RigidConst E r`) with `E.members r = some m` and
    `m.mclass ≠ .inductiveM` (i.e. `.constructorM`, `.axiomM`, or `.quotM`), every `FamProbeCptT E u`
    compact of `foldApps (.const r ls) xs` is `.bot` and lies in `ElT E ρ T u` for **every** type `T`! -/
theorem famProbeTyping_at_nonInductive_rigidSpine {ρ : EnvT} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hrig : RigidConst E r) (hnot : m.mclass ≠ .inductiveM)
    (ls : List Level) (xs : List (Expr Nat)) (T : Expr Nat) {u : CptT}
    (hu : FamProbeCptT E u) (hap : ApproxT E ρ (foldApps (.const r ls) xs) u) :
    ElT E ρ T u := by
  have hinv := approxT_foldApps_const_inductiveM_inv_aux (E := E) (ρ := ρ) (r := r) (pre := [])
    xs (fun hd => (approxT_rigid_const_inv hrig hd).elim Or.inl (fun e => Or.inr ⟨[], e, .nil⟩)) hap
  rcases hinv with rfl | ⟨us, rfl, _⟩
  · exact elT_bot E ρ T
  · exact (not_famProbeCptT_spine_of_not_inductiveM hm hnot hu).elim

/-- **Canonical Family 6b (`famProbeTyping_at_bvarSpine_of_lookupValue_none`):**
    For any assumption-variable spine `foldApps (.bvar i) xs` (`lookupValue Γ i = none`), every
    compact `u` in `ApproxT E (ctxEnvT E Γ) (foldApps (.bvar i) xs) u` is `.bot` and lies in
    `ElT E (ctxEnvT E Γ) T u` for **every** type `T`! -/
theorem famProbeTyping_at_bvarSpine_of_lookupValue_none {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) (xs : List (Expr Nat)) (T : Expr Nat) {u : CptT}
    (hap : ApproxT E (ctxEnvT E Γ) (foldApps (.bvar i) xs) u) :
    ElT E (ctxEnvT E Γ) T u := by
  have hbot : u = .bot :=
    approxT_ctxEnvT_foldApps_bvar_of_lookupValue_none hnone xs
      (approxT_ctxEnvT_bvar_of_lookupValue_none hnone) hap
  subst hbot
  exact elT_bot E (ctxEnvT E Γ) T


/-! #### §12 Part B — Type-Discipline-Guarded Spine Relation `SpineClauseSLT` / `LRSCoreSLT` / `LRSSLT` Resolving `#7726`/`#7731`'s Escape Obstruction, Unconditional 5-Way Mutual PER (`typedPERSLT_of_envWfT`), and Π-Index Probe Collapse (`lrSCoreSLT_satProbe_at_pi_iff_eq_bot`) -/

/-- A term with a normal non-Π readback does not read back to a Π (`not_redR_pi_of_normal`). -/
theorem not_redR_pi_of_normal (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {A X : Expr Nat} (hX : RedR R Γ A X) (hXn : NormalR R Γ X) (hXp : ∀ D B, X ≠ .pi D B) :
    ∀ D B, ¬ RedR R Γ A (.pi D B) :=
  fun D B h => hXp D B (hNU Γ hX hXn h (fun _ hs => hL.pi_normal _ _ _ _ hs))

/-- Terms related by `SpineClauseSL` have normal constant-headed reducts and therefore never read
    back to a Π (`spineClauseSL_not_pi`). -/
theorem spineClauseSL_not_pi (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {M M' A : Expr Nat} {r : Nat} {args : List CptT}
    (h : SpineClauseSL R E n Γ M M' A r args) :
    (∀ D B, ¬ RedR R Γ M (.pi D B)) ∧ (∀ D B, ¬ RedR R Γ M' (.pi D B)) := by
  rcases h.2 with ⟨_, _, _, xs₁, xs₂, _, _, _, _, _, h1, h2, hn1, hn2, _⟩ |
    ⟨_, _, _, xs₁, xs₂, h1, h2, hn1, hn2, _⟩
  · exact ⟨not_redR_pi_of_normal hL hNU h1 hn1 (TypedModelAudit.foldApps_const_ne_pi xs₁),
      not_redR_pi_of_normal hL hNU h2 hn2 (TypedModelAudit.foldApps_const_ne_pi xs₂)⟩
  · exact ⟨not_redR_pi_of_normal hL hNU h1 hn1 (TypedModelAudit.foldApps_const_ne_pi xs₁),
      not_redR_pi_of_normal hL hNU h2 hn2 (TypedModelAudit.foldApps_const_ne_pi xs₂)⟩

/-- **Type-Discipline-Guarded Unified Spine Clause Over `CptT` (`SpineClauseSLT`):**
    Strengthens `SpineClauseSL R E n Γ M M' A r args` with the Π-index guard
    `((∃ D B, RedR R Γ A (.pi D B)) → ∃ m, E.members r = some m ∧ m.mclass = .inductiveM ∧ args.length < (piDomsOf m.mtype).length)`.
    - Directly resolves `#7726`/`#7731`'s `cexEnvP` / `badPiCpt` escape obstruction: at any Π-index
      `RedR R Γ A (.pi D B)`, `.axiomM` and `.constructorM` spines (`m.mclass ≠ .inductiveM`) and
      saturated `.inductiveM` spines (`args.length = (piDomsOf m.mtype).length`) are **excluded**,
      while unsaturated `.inductiveM` prefixes (`args.length < (piDomsOf m.mtype).length`) needed
      for `ApproxT.appSpine` growth are **retained**.
    - Because the Π-index guard depends only on `A, r, args` (not `M, M'`) and because any `A₂`
      related at a spine type compact `.spine r' args'` satisfies `∀ D B, ¬ RedR R Γ A₂ (.pi D B)`
      by `spineClauseSL_not_pi`, `SpineClauseSLT` / `LRSCoreSLT` satisfies the full 5-part mutual
      PER (`typedPERSLT_of_envWfT`) under `ReadbackLaws E R`, `NormalUniqueR R`, and `EnvWfT E`
      **alone**! -/
def SpineClauseSLT (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (M M' A : Expr Nat) (r : Nat) (args : List CptT) : Prop :=
  SpineClauseSL R E n Γ M M' A r args ∧
  ((∃ D B, RedR R Γ A (.pi D B)) →
    ∃ m : CheckedMember,
      E.members r = some m ∧ m.mclass = .inductiveM ∧ args.length < (piDomsOf m.mtype).length)

/-- Symmetry of `SpineClauseSLT` at every ambient index `A : Expr Nat` under `EnvWfT E` alone
    (`spineClauseSLT_symm`). -/
theorem spineClauseSLT_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A : Expr Nat} {r : Nat} {args : List CptT}
    (h : SpineClauseSLT R E n Γ M M' A r args) :
    SpineClauseSLT R E n Γ M' M A r args :=
  ⟨spineClauseSL_symm hW hΓ h.1, h.2⟩

/-- Transitivity of `SpineClauseSLT` at every ambient index `A : Expr Nat` under `NormalUniqueR R`
    and `EnvWfT E` alone (`spineClauseSLT_trans`). -/
theorem spineClauseSLT_trans (hNU : NormalUniqueR R) (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' M'' A : Expr Nat} {r : Nat} {args : List CptT}
    (h₁ : SpineClauseSLT R E n Γ M M' A r args)
    (h₂ : SpineClauseSLT R E n Γ M' M'' A r args) :
    SpineClauseSLT R E n Γ M M'' A r args :=
  ⟨spineClauseSL_trans hNU hW hΓ h₁.1 h₂.1, h₁.2⟩

/-- At any index `A` that does not read back to a Π, `SpineClauseSLT` is equivalent (`↔`) to
    `SpineClauseSL` (`spineClauseSLT_iff_spineClauseSL_of_not_pi`). -/
theorem spineClauseSLT_iff_spineClauseSL_of_not_pi {Γ : LCtx} {M M' A : Expr Nat}
    (hnp : ∀ D B, ¬ RedR R Γ A (.pi D B)) (r : Nat) (args : List CptT) :
    SpineClauseSLT R E n Γ M M' A r args ↔ SpineClauseSL R E n Γ M M' A r args :=
  ⟨fun h => h.1, fun h => ⟨h, fun ⟨D, B, hpi⟩ => (hnp D B hpi).elim⟩⟩

/-- At any sort index `A` (`∃ l, RedR R Γ A (.sort l)`), `SpineClauseSLT` is equivalent (`↔`) to
    `SpineClauseSL` (`spineClauseSLT_iff_spineClauseSL_of_sort`). -/
theorem spineClauseSLT_iff_spineClauseSL_of_sort (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {M M' A : Expr Nat} (hA : ∃ l, RedR R Γ A (.sort l)) (r : Nat) (args : List CptT) :
    SpineClauseSLT R E n Γ M M' A r args ↔ SpineClauseSL R E n Γ M M' A r args :=
  spineClauseSLT_iff_spineClauseSL_of_not_pi
    (fun D B => let ⟨_, hl⟩ := hA; not_redR_pi_of_redR_sort hL hNU hl D B) r args

/-- **Type-Discipline-Guarded Logical Relation Over `CptT` (`LRSCoreSLT`):**
    Replaces `LRSCoreSL`'s `.spine r args` clause with `SpineClauseSLT R E n Γ M M' A r args`. -/
def LRSCoreSLT (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) :
    CptT → Prop
  | .bot => True
  | .prop => SortClauseT R Γ M M' A
  | .sort => SortClauseT R Γ M M' A
  | .pi a f => (∃ l, RedR R Γ A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ : Expr Nat, RedR R Γ M (.pi A₁ B₁) ∧ RedR R Γ M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        (∃ u₁, LRSCoreSLT R E n Γ A₁ A₂ (.sort u₁) a) ∧
        ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) →
          ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCoreSLT R E n Γ N N' A₁ u) →
          ∃ v, LRSCoreSLT R E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort v) s.2
  | .lam g =>
      ∃ A₁ B₁ : Expr Nat, RedR R Γ A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCoreSLT R E n Γ N N' A₁ u) →
          LRSCoreSLT R E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
  | .spine r args => SpineClauseSLT R E n Γ M M' A r args
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfT_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₃ := sizeOfT_snd_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfT_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₃ := sizeOfT_snd_lt s
       omega)

/-- Top-level proposition-collapsed counterpart of `LRSCoreSLT` (`LRSSLT`). -/
def LRSSLT (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (M M' A : Expr Nat) (c : CptT) : Prop :=
  IsPropTyR R E n Γ A ∨ LRSCoreSLT R E n Γ M M' A c

theorem lrSCoreSLT_bot (Γ : LCtx) (M M' A : Expr Nat) : LRSCoreSLT R E n Γ M M' A .bot := by
  rw [LRSCoreSLT.eq_def]; trivial

theorem lrSCoreSLT_prop_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreSLT R E n Γ M M' A .prop ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreSLT.eq_def]

theorem lrSCoreSLT_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreSLT R E n Γ M M' A .sort ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreSLT.eq_def]

theorem lrSCoreSLT_sortCode_iff {Γ : LCtx} {M M' A : Expr Nat} (l : Level) :
    LRSCoreSLT R E n Γ M M' A (sortCode l) ↔ SortClauseT R Γ M M' A := by
  rcases sortCode_prop_or_sort l with h | h
  · rw [h, lrSCoreSLT_prop_iff]
  · rw [h, lrSCoreSLT_sort_iff]

theorem lrSCoreSLT_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptT) :
    LRSCoreSLT R E n Γ M M' A (.spine r args) ↔ SpineClauseSLT R E n Γ M M' A r args := by
  rw [LRSCoreSLT.eq_def]

/-- Sort-index irrelevance for `LRSCoreSLT` (`lrSCoreSLT_sortIdx_irrel`). -/
theorem lrSCoreSLT_sortIdx_irrel (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {N N' A A' : Expr Nat} (hA : ∃ l, RedR R Γ A (.sort l)) (hA' : ∃ l, RedR R Γ A' (.sort l)) :
    (c : CptT) → LRSCoreSLT R E n Γ N N' A c → LRSCoreSLT R E n Γ N N' A' c
  | .bot, _ => lrSCoreSLT_bot _ _ _ _
  | .prop, h => by
      rw [lrSCoreSLT_prop_iff] at h
      rw [lrSCoreSLT_prop_iff]
      exact ⟨hA', h.2⟩
  | .sort, h => by
      rw [lrSCoreSLT_sort_iff] at h
      rw [lrSCoreSLT_sort_iff]
      exact ⟨hA', h.2⟩
  | .pi a f, h => by
      rw [LRSCoreSLT.eq_def] at h
      rw [LRSCoreSLT.eq_def]
      exact ⟨hA', h.2⟩
  | .lam g, h => by
      rw [LRSCoreSLT.eq_def] at h
      obtain ⟨A₁, B₁, hr, _⟩ := h
      obtain ⟨l, hl⟩ := hA
      exact (not_redR_pi_of_redR_sort hL hNU hl A₁ B₁ hr).elim
  | .spine r args, h => by
      rw [lrSCoreSLT_spine_iff, spineClauseSLT_iff_spineClauseSL_of_sort hL hNU hA] at h
      rw [lrSCoreSLT_spine_iff, spineClauseSLT_iff_spineClauseSL_of_sort hL hNU hA']
      rw [← lrSCoreSL_spine_iff] at h ⊢
      exact lrSCoreSL_sortIdx_irrel hL hNU hA hA' (.spine r args) h

/-- At `.pi .bot []`, `LRSCoreSLT` is identically equivalent to `LRSCoreSL` (`piProbeSLT_iff_lrSCoreSL`). -/
theorem piProbeSLT_iff_lrSCoreSL {Γ : LCtx} {M N A : Expr Nat} :
    LRSCoreSLT R E n Γ M N A (.pi .bot []) ↔
      LRSCoreSL R E n Γ M N A (.pi .bot []) := by
  rw [LRSCoreSLT.eq_def, LRSCoreSL.eq_def]
  constructor
  · rintro ⟨hA, A₁, B₁, A₂, B₂, hM, hN, hΓ, hdom, hcod, ⟨u, _⟩, _⟩
    exact ⟨hA, A₁, B₁, A₂, B₂, hM, hN, hΓ, hdom, hcod,
      ⟨u, lrSCoreSL_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩
  · rintro ⟨hA, A₁, B₁, A₂, B₂, hM, hN, hΓ, hdom, hcod, ⟨u, _⟩, _⟩
    exact ⟨hA, A₁, B₁, A₂, B₂, hM, hN, hΓ, hdom, hcod,
      ⟨u, lrSCoreSLT_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- At `.pi .bot []`, `LRSCoreSLT` is identically equivalent to `LRSCore` (`piProbeSLT_iff_lrSCore`). -/
theorem piProbeSLT_iff_lrSCore {Γ : LCtx} {M N A : Expr Nat} :
    LRSCoreSLT R E n Γ M N A (.pi .bot []) ↔
      LRSCore R E n Γ M N A (.pi .bot []) :=
  piProbeSLT_iff_lrSCoreSL.trans piProbeSL_iff_lrSCore

/-- At any index `A` with `∀ D B, ¬ RedR R Γ A (.pi D B)`, `LRSCoreSLT` and `LRSCoreSL` are
    logically equivalent (`↔`) on **every** `FamProbeCptT E c` (`famProbeSLT_iff_lrSCoreSL_of_not_pi`). -/
theorem famProbeSLT_iff_lrSCoreSL_of_not_pi {Γ : LCtx} {M N A : Expr Nat}
    (hnp : ∀ D B, ¬ RedR R Γ A (.pi D B)) {c : CptT} (hc : FamProbeCptT E c) :
    LRSCoreSLT R E n Γ M N A c ↔ LRSCoreSL R E n Γ M N A c := by
  cases hc with
  | bot => exact ⟨fun _ => lrSCoreSL_bot _ _ _ _, fun _ => lrSCoreSLT_bot _ _ _ _⟩
  | prop => rw [lrSCoreSLT_prop_iff, lrSCoreSL_prop_iff]
  | sort => rw [lrSCoreSLT_sort_iff, lrSCoreSL_sort_iff]
  | piBotNil => exact piProbeSLT_iff_lrSCoreSL
  | spine =>
      rw [lrSCoreSLT_spine_iff, lrSCoreSL_spine_iff]
      exact spineClauseSLT_iff_spineClauseSL_of_not_pi hnp _ _

/-- At any sort index `A` (`∃ l, RedR R Γ A (.sort l)`), `LRSCoreSLT` and `LRSCoreSL` are
    logically equivalent (`↔`) on **every** `FamProbeCptT E c` (`famProbeSLT_iff_lrSCoreSL_of_sort`). -/
theorem famProbeSLT_iff_lrSCoreSL_of_sort (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {M N A : Expr Nat} (hA : ∃ l, RedR R Γ A (.sort l))
    {c : CptT} (hc : FamProbeCptT E c) :
    LRSCoreSLT R E n Γ M N A c ↔ LRSCoreSL R E n Γ M N A c :=
  famProbeSLT_iff_lrSCoreSL_of_not_pi
    (fun D B => let ⟨_, hl⟩ := hA; not_redR_pi_of_redR_sort hL hNU hl D B) hc

/-- Symmetry of `LRSCoreSLT` on all `FamProbeCptT E` compacts at any index `I : Expr Nat`
    (`lrSCoreSLT_famProbe_symm`). -/
theorem lrSCoreSLT_famProbe_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {c : CptT} (hc : FamProbeCptT E c) {M N I : Expr Nat}
    (h : LRSCoreSLT R E n Γ M N I c) :
    LRSCoreSLT R E n Γ N M I c := by
  cases hc with
  | bot => exact lrSCoreSLT_bot _ _ _ _
  | prop =>
      rw [lrSCoreSLT_prop_iff] at h ⊢
      obtain ⟨hI, u, u', h1, h2⟩ := h
      exact ⟨hI, u', u, h2, h1⟩
  | sort =>
      rw [lrSCoreSLT_sort_iff] at h ⊢
      obtain ⟨hI, u, u', h1, h2⟩ := h
      exact ⟨hI, u', u, h2, h1⟩
  | piBotNil =>
      exact piProbeSLT_iff_lrSCoreSL.mpr
        (lrSCoreSL_famProbe_symm hW hΓ .piBotNil (piProbeSLT_iff_lrSCoreSL.mp h))
  | spine =>
      rw [lrSCoreSLT_spine_iff] at h ⊢
      exact spineClauseSLT_symm hW hΓ h

/-- Transitivity of `LRSCoreSLT` on all `FamProbeCptT E` compacts at any index `I : Expr Nat`
    (`lrSCoreSLT_famProbe_trans`). -/
theorem lrSCoreSLT_famProbe_trans (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {c : CptT} (hc : FamProbeCptT E c) {M N P I : Expr Nat}
    (h₁ : LRSCoreSLT R E n Γ M N I c) (h₂ : LRSCoreSLT R E n Γ N P I c) :
    LRSCoreSLT R E n Γ M P I c := by
  cases hc with
  | bot => exact lrSCoreSLT_bot _ _ _ _
  | prop =>
      rw [lrSCoreSLT_prop_iff] at h₁ h₂ ⊢
      obtain ⟨hI, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hI, u, u'', h1, h3⟩
  | sort =>
      rw [lrSCoreSLT_sort_iff] at h₁ h₂ ⊢
      obtain ⟨hI, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hI, u, u'', h1, h3⟩
  | piBotNil =>
      exact piProbeSLT_iff_lrSCoreSL.mpr
        (lrSCoreSL_famProbe_trans hL hNU hW hΓ .piBotNil
          (piProbeSLT_iff_lrSCoreSL.mp h₁) (piProbeSLT_iff_lrSCoreSL.mp h₂))
  | spine =>
      rw [lrSCoreSLT_spine_iff] at h₁ h₂ ⊢
      exact spineClauseSLT_trans hNU hW hΓ h₁ h₂

/-- **Refutation of Non-Inductive Spines (`.axiomM` / `.constructorM`) at Π-Indices in `LRSCoreSLT`
    (`not_lrSCoreSLT_nonInductive_at_pi`):**
    Directly blocks `#7726`/`#7731`'s `cexEnvP` / `badPiCpt` escape: for any member `r` with
    `m.mclass ≠ .inductiveM` (in particular any `.axiomM` or `.constructorM`), `.spine r args`
    is **never** inhabited in `LRSCoreSLT R E n Γ M M' A` when `RedR R Γ A (.pi D B)`! -/
theorem not_lrSCoreSLT_nonInductive_at_pi {Γ : LCtx} {M M' A D B : Expr Nat}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hnot : m.mclass ≠ .inductiveM)
    (hpi : RedR R Γ A (.pi D B)) (args : List CptT) :
    ¬ LRSCoreSLT R E n Γ M M' A (.spine r args) := by
  rw [lrSCoreSLT_spine_iff]
  rintro ⟨_, hguard⟩
  obtain ⟨m', hm', hind, _⟩ := hguard ⟨D, B, hpi⟩
  have em : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst em
  exact hnot hind

/-- **Refutation of Saturated Spines at Π-Indices in `LRSCoreSLT` (`not_lrSCoreSLT_satSpine_at_pi`):** -/
theorem not_lrSCoreSLT_satSpine_at_pi {Γ : LCtx} {M M' A D B : Expr Nat}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    (hpi : RedR R Γ A (.pi D B)) {args : List CptT}
    (hsat : (piDomsOf m.mtype).length ≤ args.length) :
    ¬ LRSCoreSLT R E n Γ M M' A (.spine r args) := by
  rw [lrSCoreSLT_spine_iff]
  rintro ⟨_, hguard⟩
  obtain ⟨m', hm', _, hlt⟩ := hguard ⟨D, B, hpi⟩
  have em : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst em
  exact Nat.not_lt_of_ge hsat hlt

/-- **Exact Π-Index Probe Collapse on `FamSatProbeCptT E` (`lrSCoreSLT_satProbe_at_pi_iff_eq_bot`):**
    At any Π-index `A` (`RedR R Γ A (.pi D B)`), a saturated type probe compact `c`
    (`FamSatProbeCptT E c`) satisfies `LRSCoreSLT R E n Γ M M' A c` **if and only if** `c = .bot`! -/
theorem lrSCoreSLT_satProbe_at_pi_iff_eq_bot (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {M M' A D B : Expr Nat} (hpi : RedR R Γ A (.pi D B))
    {c : CptT} (hc : FamSatProbeCptT E c) :
    LRSCoreSLT R E n Γ M M' A c ↔ c = .bot := by
  constructor
  · intro h
    cases hc with
    | bot => rfl
    | prop =>
        rw [lrSCoreSLT_prop_iff] at h
        obtain ⟨⟨l, hl⟩, _⟩ := h
        exact (not_redR_pi_of_redR_sort hL hNU hl D B hpi).elim
    | sort =>
        rw [lrSCoreSLT_sort_iff] at h
        obtain ⟨⟨l, hl⟩, _⟩ := h
        exact (not_redR_pi_of_redR_sort hL hNU hl D B hpi).elim
    | piBotNil =>
        rw [LRSCoreSLT.eq_def] at h
        obtain ⟨⟨l, hl⟩, _⟩ := h
        exact (not_redR_pi_of_redR_sort hL hNU hl D B hpi).elim
    | spine hm _ hlen _ =>
        exact (not_lrSCoreSLT_satSpine_at_pi hm hpi (Nat.le_of_eq hlen.symm) h).elim
  · rintro rfl
    exact lrSCoreSLT_bot _ _ _ _

/-- The 5 statements of the `LRSCoreSLT` mutual PER package. -/
def IrrelAtSLT (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ : Expr Nat} {w : Level},
    LRSCoreSLT R E n Γ A₁ A₂ (.sort w) a → CTyS E u a →
    ∀ {N N' : Expr Nat}, LRSCoreSLT R E n Γ N N' A₁ u → LRSCoreSLT R E n Γ N N' A₂ u

def SymmTmAtSLT (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreSLT R E n Γ A A (.sort w) a → CTyS E u a →
    ∀ {N N' : Expr Nat}, LRSCoreSLT R E n Γ N N' A u → LRSCoreSLT R E n Γ N' N A u

def TransTmAtSLT (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreSLT R E n Γ A A (.sort w) a → CTyS E u a →
    ∀ {N N' N'' : Expr Nat}, LRSCoreSLT R E n Γ N N' A u → LRSCoreSLT R E n Γ N' N'' A u →
      LRSCoreSLT R E n Γ N N'' A u

def SymmTyAtSLT (R : Readback) (E : ResolvedEnv) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ : Expr Nat} {w : Level},
    LRSCoreSLT R E n Γ A₁ A₂ (.sort w) c → LRSCoreSLT R E n Γ A₂ A₁ (.sort w) c

def TransTyAtSLT (R : Readback) (E : ResolvedEnv) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ A₃ : Expr Nat} {w : Level},
    LRSCoreSLT R E n Γ A₁ A₂ (.sort w) c → LRSCoreSLT R E n Γ A₂ A₃ (.sort w) c →
      LRSCoreSLT R E n Γ A₁ A₃ (.sort w) c

/-- `SymmTyAtSLT c` from the package below `c`, under `EnvWfT E` alone. -/
theorem symmTy_stepSLT (hL : ReadbackLaws E R) (hW : EnvWfT E) (c : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAtSLT R E n c' ∧ TransTyAtSLT R E n c')
    (ihP : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      IrrelAtSLT R E n a u ∧ SymmTmAtSLT R E n a u ∧ TransTmAtSLT R E n a u) :
    SymmTyAtSLT R E n c := by
  intro Γ hΓ A₁ A₂ w h
  cases c with
  | bot => exact lrSCoreSLT_bot _ _ _ _
  | prop =>
      rw [lrSCoreSLT_prop_iff] at h ⊢
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | sort =>
      rw [lrSCoreSLT_sort_iff] at h ⊢
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | lam g =>
      rw [LRSCoreSLT.eq_def] at h
      obtain ⟨_, _, hr, _⟩ := h
      exact Expr.noConfusion (redR_sort_eq hL hr)
  | spine r args =>
      rw [lrSCoreSLT_spine_iff] at h ⊢
      exact spineClauseSLT_symm hW hΓ h
  | pi a f =>
      rw [LRSCoreSLT.eq_def] at h ⊢
      obtain ⟨hA, A₁', B₁', A₂', B₂', h1, h2, ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩, ⟨u₁, hra⟩, hrf⟩ := h
      obtain ⟨hsa, hta⟩ := ihQ a (sizeOf_dom_lt_pi a f)
      have hra' : LRSCoreSLT R E n Γ A₂' A₁' (.sort u₁) a := hsa hΓ hra
      have hself₂ : LRSCoreSLT R E n Γ A₂' A₂' (.sort u₁) a := hta hΓ hra' hra
      cases hΓ₁ with
      | assumption _ _ u _ hA₁ =>
          obtain ⟨v, hA₂⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hdom hA₁
          refine ⟨hA, A₂', B₂', A₁', B₁', h2, h1, ⟨.assumption Γ A₂' v hΓ hA₂⟩, ⟨hdom.symmT⟩,
            ⟨tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT⟩, ⟨u₁, hra'⟩, ?_⟩
          intro s hs hty N N' hN hN' hcN hrel
          obtain ⟨hcN⟩ := hcN
          have hN₁ : HasTyT E n Γ N A₁' := hasTyT_of_tyConvT hN hdom.symmT
          have hN'₁ : HasTyT E n Γ N' A₁' := hasTyT_of_tyConvT hN' hdom.symmT
          have hc₁ : ConvT E n Γ N' N A₁' := convT_of_tyConv (.symm _ _ _ _ hcN) hdom.symmT
          have hrel₁ : ∀ u ∈ s.1, LRSCoreSLT R E n Γ N' N A₁' u := fun u hu => by
            have hlt : sizeOf a + sizeOf u < sizeOf (CptT.pi a f) := by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega
            exact (ihP a u hlt).1 hΓ hra' (hty u hu)
              ((ihP a u hlt).2.1 hΓ hself₂ (hty u hu) (hrel u hu))
          obtain ⟨v', hv'⟩ := hrf s hs hty N' N hN'₁ hN₁ ⟨hc₁⟩ hrel₁
          exact ⟨v', (ihQ s.2 (sizeOf_out_lt_pi hs)).1 hΓ hv'⟩

/-- `TransTyAtSLT c` from the package below `c`, under `EnvWfT E` alone. -/
theorem transTy_stepSLT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (c : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAtSLT R E n c' ∧ TransTyAtSLT R E n c')
    (ihP : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      IrrelAtSLT R E n a u ∧ SymmTmAtSLT R E n a u ∧ TransTmAtSLT R E n a u) :
    TransTyAtSLT R E n c := by
  intro Γ hΓ A₁ A₂ A₃ w h₁ h₂
  cases c with
  | bot => exact lrSCoreSLT_bot _ _ _ _
  | prop =>
      rw [lrSCoreSLT_prop_iff] at h₁ h₂ ⊢
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hA, u, u'', h1, h3⟩
  | sort =>
      rw [lrSCoreSLT_sort_iff] at h₁ h₂ ⊢
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hA, u, u'', h1, h3⟩
  | lam g =>
      rw [LRSCoreSLT.eq_def] at h₁
      obtain ⟨_, _, hr, _⟩ := h₁
      exact Expr.noConfusion (redR_sort_eq hL hr)
  | spine r args =>
      rw [lrSCoreSLT_spine_iff] at h₁ h₂ ⊢
      exact spineClauseSLT_trans hNU hW hΓ h₁ h₂
  | pi a f =>
      rw [LRSCoreSLT.eq_def] at h₁ h₂ ⊢
      obtain ⟨hA, A₁', B₁', A₂', B₂', h1, h2, ⟨hΓ₁⟩, ⟨hdom₁⟩, ⟨hcod₁⟩, ⟨u₁, hra₁⟩, hrf₁⟩ := h₁
      obtain ⟨_, A₂'', B₂'', A₃', B₃', h2', h3, _, ⟨hdom₂⟩, ⟨hcod₂⟩, ⟨u₂, hra₂⟩, hrf₂⟩ := h₂
      obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU h2 h2'
      subst eA; subst eB
      obtain ⟨hsa, hta⟩ := ihQ a (sizeOf_dom_lt_pi a f)
      have hra₂' : LRSCoreSLT R E n Γ A₂' A₃' (.sort u₁) a :=
        lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, .refl _⟩ ⟨_, .refl _⟩ a hra₂
      have hself₁ : LRSCoreSLT R E n Γ A₁' A₁' (.sort u₁) a := hta hΓ hra₁ (hsa hΓ hra₁)
      refine ⟨hA, A₁', B₁', A₃', B₃', h1, h3, ⟨hΓ₁⟩, ⟨TyConvT.trans _ _ _ _ hdom₁ hdom₂⟩,
        ⟨TyConvT.trans _ _ _ _ hcod₁ (tyConvT_assump_dom hW hΓ hdom₁ hcod₂)⟩,
        ⟨u₁, hta hΓ hra₁ hra₂'⟩, ?_⟩
      intro s hs hty N N' hN hN' hcN hrel
      obtain ⟨hcN⟩ := hcN
      have hrelNN : ∀ u ∈ s.1, LRSCoreSLT R E n Γ N N A₁' u := fun u hu => by
        have hlt : sizeOf a + sizeOf u < sizeOf (CptT.pi a f) := by
          have h₁ := List.sizeOf_lt_of_mem hs
          have h₂ := List.sizeOf_lt_of_mem hu
          have h₃ := sizeOfT_fst_lt s
          simp; omega
        exact (ihP a u hlt).2.2 hΓ hself₁ (hty u hu) (hrel u hu)
          ((ihP a u hlt).2.1 hΓ hself₁ (hty u hu) (hrel u hu))
      obtain ⟨v, hv⟩ := hrf₁ s hs hty N N hN hN ⟨.refl _ _ _ hN⟩ hrelNN
      have hN₂ : HasTyT E n Γ N A₂' := hasTyT_of_tyConvT hN hdom₁
      have hN'₂ : HasTyT E n Γ N' A₂' := hasTyT_of_tyConvT hN' hdom₁
      have hrel₂ : ∀ u ∈ s.1, LRSCoreSLT R E n Γ N N' A₂' u := fun u hu => by
        have hlt : sizeOf a + sizeOf u < sizeOf (CptT.pi a f) := by
          have h₁ := List.sizeOf_lt_of_mem hs
          have h₂ := List.sizeOf_lt_of_mem hu
          have h₃ := sizeOfT_fst_lt s
          simp; omega
        exact (ihP a u hlt).1 hΓ hra₁ (hty u hu) (hrel u hu)
      obtain ⟨v', hv'⟩ := hrf₂ s hs hty N N' hN₂ hN'₂ ⟨convT_of_tyConv hcN hdom₁⟩ hrel₂
      exact ⟨v, (ihQ s.2 (sizeOf_out_lt_pi hs)).2 hΓ hv
        (lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, .refl _⟩ ⟨_, .refl _⟩ s.2 hv')⟩

/-- At a spine-coded type index `LRSCoreSLT R E n Γ A A₂ (.sort w) (.spine r' args')`, neither `A`
    nor `A₂` reads back to a sort, `A₂` never reads back to a Π, and `Nonempty (TyConvT E n Γ A A₂)`
    holds (`lrSCoreSLT_spine_data_of_tyIdx`). -/
theorem lrSCoreSLT_spine_data_of_tyIdx (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {A A₂ : Expr Nat} {w : Level} {r' : Nat} {args' : List CptT}
    (h : LRSCoreSLT R E n Γ A A₂ (.sort w) (.spine r' args')) :
    (∀ l, ¬ RedR R Γ A (.sort l)) ∧ (∀ l, ¬ RedR R Γ A₂ (.sort l)) ∧
      (∀ D B, ¬ RedR R Γ A₂ (.pi D B)) ∧ Nonempty (TyConvT E n Γ A A₂) := by
  rw [lrSCoreSLT_spine_iff] at h
  obtain ⟨hns₁, hns₂, htyc⟩ := lrSCoreSL_spine_data_of_tyIdx hL hNU
    ((lrSCoreSL_spine_iff Γ A A₂ (.sort w) r' args').mpr h.1)
  obtain ⟨_, hnp₂⟩ := spineClauseSL_not_pi hL hNU h.1
  exact ⟨hns₁, hns₂, hnp₂, htyc⟩

/-- `IrrelAtSLT a u` from the package below (`irrel_stepSLT`). -/
theorem irrel_stepSLT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtSLT R E n c' ∧ TransTyAtSLT R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAtSLT R E n a' u' ∧ SymmTmAtSLT R E n a' u' ∧ TransTmAtSLT R E n a' u') :
    IrrelAtSLT R E n a u := by
  intro Γ hΓ A₁ A₂ w hAA hu N N' h
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreSLT_bot _ _ _ _
  | prop =>
      rw [lrSCoreSLT_prop_iff] at hAA
      obtain ⟨_, l₁, l₂, h1, h2⟩ := hAA
      exact lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨_, h2⟩ u h
  | sort =>
      rw [lrSCoreSLT_sort_iff] at hAA
      obtain ⟨_, l₁, l₂, h1, h2⟩ := hAA
      exact lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨_, h2⟩ u h
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreSLT_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreSLT_bot _ _ _ _
      · obtain ⟨hns₁, hns₂, hnp₂, ⟨hc₁₂⟩⟩ := lrSCoreSLT_spine_data_of_tyIdx hL hNU hAA
        rw [lrSCoreSLT_spine_iff] at h ⊢
        refine ⟨⟨?_, h.1.2⟩, fun ⟨D, B, hpi⟩ => (hnp₂ D B hpi).elim⟩
        rcases h.1.1 with ⟨_, hsub⟩ | ⟨_, ⟨hconv⟩⟩
        · rcases hsub with ⟨l, hl⟩ | hne
          · exact (hns₁ l hl).elim
          · obtain ⟨hconv⟩ := hne
            exact Or.inr ⟨hns₂, ⟨convT_of_tyConv hconv hc₁₂⟩⟩
        · exact Or.inr ⟨hns₂, ⟨convT_of_tyConv hconv hc₁₂⟩⟩
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreSLT_bot _ _ _ _
      · rw [LRSCoreSLT.eq_def] at h
        obtain ⟨A₁₁, B₁₁, hr₁, ⟨hΓ₁₁⟩, hclause⟩ := h
        rw [LRSCoreSLT.eq_def] at hAA
        obtain ⟨_, A₁₁', B₁₁', A₂₁, B₂₁, hr₁', hr₂, _, ⟨hdomT⟩, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr₁ hr₁'
        subst eA; subst eB
        have hlt_a' : sizeOf a' < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
          have := sizeOf_dom_lt_pi a' g; omega
        obtain ⟨hsa, hta⟩ := ihQ a' hlt_a'
        have hra' : LRSCoreSLT R E n Γ A₂₁ A₁₁ (.sort u₁) a' := hsa hΓ hra
        have hself₁ : LRSCoreSLT R E n Γ A₁₁ A₁₁ (.sort u₁) a' := hta hΓ hra hra'
        rw [LRSCoreSLT.eq_def]
        cases hΓ₁₁ with
        | assumption _ _ u₀ _ hA₁₁ =>
            obtain ⟨v₀, hA₂₁⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hdomT hA₁₁
            refine ⟨A₂₁, B₂₁, hr₂, ⟨.assumption Γ A₂₁ v₀ hΓ hA₂₁⟩, ?_⟩
            intro s hs M M' hM hM' hcM hrel
            obtain ⟨hcM⟩ := hcM
            have hM₁ : HasTyT E n Γ M A₁₁ := hasTyT_of_tyConvT hM hdomT.symmT
            have hM'₁ : HasTyT E n Γ M' A₁₁ := hasTyT_of_tyConvT hM' hdomT.symmT
            have hc₁ : ConvT E n Γ M M' A₁₁ := convT_of_tyConv hcM hdomT.symmT
            have hltP : ∀ v ∈ s.1,
                sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
              fun v hv => by
                have := sizeOf_dom_lt_pi a' g
                have := sizeOf_dem_lt_lam hs hv
                omega
            have hrel₁ : ∀ v ∈ s.1, LRSCoreSLT R E n Γ M M' A₁₁ v := fun v hv =>
              (ihP a' v (hltP v hv)).1 hΓ hra' (hdom s hs v hv) (hrel v hv)
            have hcore := hclause s hs M M' hM₁ hM'₁ ⟨hc₁⟩ hrel₁
            rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
            · rw [h0]; exact lrSCoreSLT_bot _ _ _ _
            · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
              have hrelMM : ∀ v ∈ t.1, LRSCoreSLT R E n Γ M M A₁₁ v := fun v hv =>
                (ihP a' v (hltP v (hcomp v hv))).2.2 hΓ hself₁ (htyt v hv) (hrel₁ v (hcomp v hv))
                  ((ihP a' v (hltP v (hcomp v hv))).2.1 hΓ hself₁ (htyt v hv) (hrel₁ v (hcomp v hv)))
              obtain ⟨v₁, hv₁⟩ := hrf t ht htyt M M hM₁ hM₁ ⟨.refl _ _ _ hM₁⟩ hrelMM
              have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
                have := sizeOf_out_lt_pi (a := a') ht
                have := sizeOf_out_lt_lam hs
                omega
              exact (ihP t.2 s.2 hlt_t).1 hΓ hv₁ (hcod s hs t ht hcomp) hcore

/-- `SymmTmAtSLT a u` from the package below (`symmTm_stepSLT`). -/
theorem symmTm_stepSLT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtSLT R E n c' ∧ TransTyAtSLT R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAtSLT R E n a' u' ∧ SymmTmAtSLT R E n a' u' ∧ TransTmAtSLT R E n a' u') :
    SymmTmAtSLT R E n a u := by
  intro Γ hΓ A w hAA hu N N' h
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreSLT_bot _ _ _ _
  | prop =>
      rw [lrSCoreSLT_prop_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.prop + sizeOf u := by
        have := CptT.sizeOf_pos CptT.prop; omega
      have h' := lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h
      exact lrSCoreSLT_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).1 hΓ h')
  | sort =>
      rw [lrSCoreSLT_sort_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.sort + sizeOf u := by
        have := CptT.sizeOf_pos CptT.sort; omega
      have h' := lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h
      exact lrSCoreSLT_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).1 hΓ h')
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreSLT_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreSLT_bot _ _ _ _
      · rw [lrSCoreSLT_spine_iff] at h ⊢
        exact spineClauseSLT_symm hW hΓ h
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreSLT_bot _ _ _ _
      · rw [LRSCoreSLT.eq_def] at h
        obtain ⟨A₁, B₁, hr, ⟨hΓ₁⟩, hclause⟩ := h
        rw [LRSCoreSLT.eq_def] at hAA
        obtain ⟨_, A₁', B₁', A₁'', B₁'', hr', hr'', _, _, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr''
        subst eA; subst eB
        have hltP : ∀ {s : List CptT × CptT}, s ∈ f → ∀ v ∈ s.1,
            sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
          fun {s} hs v hv => by
            have := sizeOf_dom_lt_pi a' g
            have := sizeOf_dem_lt_lam hs hv
            omega
        rw [LRSCoreSLT.eq_def]
        refine ⟨A₁, B₁, hr, ⟨hΓ₁⟩, ?_⟩
        intro s hs M M' hM hM' hcM hrel
        obtain ⟨hcM⟩ := hcM
        have hrel' : ∀ v ∈ s.1, LRSCoreSLT R E n Γ M' M A₁ v := fun v hv =>
          (ihP a' v (hltP hs v hv)).2.1 hΓ hra (hdom s hs v hv) (hrel v hv)
        have hcore := hclause s hs M' M hM' hM ⟨.symm _ _ _ _ hcM⟩ hrel'
        rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
        · rw [h0]; exact lrSCoreSLT_bot _ _ _ _
        · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
          have hrelM'M : ∀ v ∈ t.1, LRSCoreSLT R E n Γ M' M A₁ v := fun v hv => hrel' v (hcomp v hv)
          have hrelMM : ∀ v ∈ t.1, LRSCoreSLT R E n Γ M M A₁ v := fun v hv =>
            (ihP a' v (hltP hs v (hcomp v hv))).2.2 hΓ hra (htyt v hv) (hrel v (hcomp v hv))
              (hrelM'M v hv)
          obtain ⟨v₁, hv₁⟩ := hrf t ht htyt M' M hM' hM ⟨.symm _ _ _ _ hcM⟩ hrelM'M
          obtain ⟨v₂, hv₂⟩ := hrf t ht htyt M M hM hM ⟨.refl _ _ _ hM⟩ hrelMM
          have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
            have := sizeOf_out_lt_pi (a := a') ht
            have := sizeOf_out_lt_lam hs
            omega
          have hmoved := (ihP t.2 s.2 hlt_t).1 hΓ hv₁ (hcod s hs t ht hcomp) hcore
          exact (ihP t.2 s.2 hlt_t).2.1 hΓ hv₂ (hcod s hs t ht hcomp) hmoved

/-- `TransTmAtSLT a u` from the package below (`transTm_stepSLT`). -/
theorem transTm_stepSLT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAtSLT R E n c' ∧ TransTyAtSLT R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAtSLT R E n a' u' ∧ SymmTmAtSLT R E n a' u' ∧ TransTmAtSLT R E n a' u') :
    TransTmAtSLT R E n a u := by
  intro Γ hΓ A w hAA hu N N' N'' h₁ h₂
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreSLT_bot _ _ _ _
  | prop =>
      rw [lrSCoreSLT_prop_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.prop + sizeOf u := by
        have := CptT.sizeOf_pos CptT.prop; omega
      have h₁' := lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₁
      have h₂' := lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₂
      exact lrSCoreSLT_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).2 hΓ h₁' h₂')
  | sort =>
      rw [lrSCoreSLT_sort_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.sort + sizeOf u := by
        have := CptT.sizeOf_pos CptT.sort; omega
      have h₁' := lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₁
      have h₂' := lrSCoreSLT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₂
      exact lrSCoreSLT_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).2 hΓ h₁' h₂')
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreSLT_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreSLT_bot _ _ _ _
      · rw [lrSCoreSLT_spine_iff] at h₁ h₂ ⊢
        exact spineClauseSLT_trans hNU hW hΓ h₁ h₂
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreSLT_bot _ _ _ _
      · rw [LRSCoreSLT.eq_def] at h₁ h₂
        obtain ⟨A₁, B₁, hr, ⟨hΓ₁⟩, hcl₁⟩ := h₁
        obtain ⟨A₁', B₁', hr', _, hcl₂⟩ := h₂
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        rw [LRSCoreSLT.eq_def] at hAA
        obtain ⟨_, A₁', B₁', A₁'', B₁'', hr', hr'', _, _, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr''
        subst eA; subst eB
        have hltP : ∀ {s : List CptT × CptT}, s ∈ f → ∀ v ∈ s.1,
            sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
          fun {s} hs v hv => by
            have := sizeOf_dom_lt_pi a' g
            have := sizeOf_dem_lt_lam hs hv
            omega
        rw [LRSCoreSLT.eq_def]
        refine ⟨A₁, B₁, hr, ⟨hΓ₁⟩, ?_⟩
        intro s hs M M' hM hM' hcM hrel
        obtain ⟨hcM⟩ := hcM
        have hrelMM : ∀ v ∈ s.1, LRSCoreSLT R E n Γ M M A₁ v := fun v hv =>
          (ihP a' v (hltP hs v hv)).2.2 hΓ hra (hdom s hs v hv) (hrel v hv)
            ((ihP a' v (hltP hs v hv)).2.1 hΓ hra (hdom s hs v hv) (hrel v hv))
        have hc₁ := hcl₁ s hs M M hM hM ⟨.refl _ _ _ hM⟩ hrelMM
        have hc₂ := hcl₂ s hs M M' hM hM' ⟨hcM⟩ hrel
        rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
        · rw [h0]; exact lrSCoreSLT_bot _ _ _ _
        · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
          obtain ⟨v₂, hv₂⟩ := hrf t ht htyt M M hM hM ⟨.refl _ _ _ hM⟩
            (fun v hv => hrelMM v (hcomp v hv))
          have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
            have := sizeOf_out_lt_pi (a := a') ht
            have := sizeOf_out_lt_lam hs
            omega
          exact (ihP t.2 s.2 hlt_t).2.2 hΓ hv₂ (hcod s hs t ht hcomp) hc₁ hc₂

/-- **Unconditional 5-Part Mutual PER for `LRSCoreSLT` Under `EnvWfT E` Alone (`typedPERSLT_of_envWfT`):** -/
theorem typedPERSLT_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) :
    ∀ k : Nat,
      (∀ c : CptT, sizeOf c ≤ k → SymmTyAtSLT R E n c ∧ TransTyAtSLT R E n c) ∧
      (∀ a u : CptT, sizeOf a + sizeOf u ≤ k →
        IrrelAtSLT R E n a u ∧ SymmTmAtSLT R E n a u ∧ TransTmAtSLT R E n a u) := by
  intro k
  induction k with
  | zero =>
      refine ⟨fun c hc => ?_, fun a u hau => ?_⟩
      · exact absurd hc (Nat.not_le_of_gt (CptT.sizeOf_pos c))
      · exact absurd hau (Nat.not_le_of_gt (Nat.add_pos_left (CptT.sizeOf_pos a) _))
  | succ k ih =>
      refine ⟨fun c hc => ?_, fun a u hau => ?_⟩
      · by_cases hk : sizeOf c ≤ k
        · exact ih.1 c hk
        · have ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAtSLT R E n c' ∧ TransTyAtSLT R E n c' :=
            fun c' _ => ih.1 c' (by omega)
          have ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf c →
              IrrelAtSLT R E n a' u' ∧ SymmTmAtSLT R E n a' u' ∧ TransTmAtSLT R E n a' u' :=
            fun a' u' _ => ih.2 a' u' (by omega)
          exact ⟨symmTy_stepSLT hL hW c ihQ ihP, transTy_stepSLT hL hNU hW c ihQ ihP⟩
      · by_cases hk : sizeOf a + sizeOf u ≤ k
        · exact ih.2 a u hk
        · have ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u →
              SymmTyAtSLT R E n c' ∧ TransTyAtSLT R E n c' :=
            fun c' _ => ih.1 c' (by omega)
          have ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
              IrrelAtSLT R E n a' u' ∧ SymmTmAtSLT R E n a' u' ∧ TransTmAtSLT R E n a' u' :=
            fun a' u' _ => ih.2 a' u' (by omega)
          exact ⟨irrel_stepSLT hL hNU hW a u ihQ ihP, symmTm_stepSLT hL hNU hW a u ihQ ihP,
            transTm_stepSLT hL hNU hW a u ihQ ihP⟩

theorem lrSCoreSLT_irrel_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSLT R E n Γ A₁ A₂ (.sort w) a) (hu : CTyS E u a) {N N' : Expr Nat}
    (h : LRSCoreSLT R E n Γ N N' A₁ u) : LRSCoreSLT R E n Γ N N' A₂ u :=
  ((typedPERSLT_of_envWfT hL hNU hW _).2 a u (Nat.le_refl _)).1 hΓ hAA hu h

theorem lrSCoreSLT_symm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {w : Level} {c : CptT}
    (h : LRSCoreSLT R E n Γ A₁ A₂ (.sort w) c) :
    LRSCoreSLT R E n Γ A₂ A₁ (.sort w) c :=
  ((typedPERSLT_of_envWfT hL hNU hW _).1 c (Nat.le_refl _)).1 hΓ h

theorem lrSCoreSLT_trans_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ A₃ : Expr Nat} {w : Level} {c : CptT}
    (h₁ : LRSCoreSLT R E n Γ A₁ A₂ (.sort w) c) (h₂ : LRSCoreSLT R E n Γ A₂ A₃ (.sort w) c) :
    LRSCoreSLT R E n Γ A₁ A₃ (.sort w) c :=
  ((typedPERSLT_of_envWfT hL hNU hW _).1 c (Nat.le_refl _)).2 hΓ h₁ h₂

theorem lrSCoreSLT_symm_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSLT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' : Expr Nat} (h : LRSCoreSLT R E n Γ N N' A u) :
    LRSCoreSLT R E n Γ N' N A u :=
  ((typedPERSLT_of_envWfT hL hNU hW _).2 a u (Nat.le_refl _)).2.1 hΓ hAA hu h

theorem lrSCoreSLT_trans_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSLT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' N'' : Expr Nat} (h₁ : LRSCoreSLT R E n Γ N N' A u) (h₂ : LRSCoreSLT R E n Γ N' N'' A u) :
    LRSCoreSLT R E n Γ N N'' A u :=
  ((typedPERSLT_of_envWfT hL hNU hW _).2 a u (Nat.le_refl _)).2.2 hΓ hAA hu h₁ h₂

theorem lrSSLT_symm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ : Expr Nat} {w : Level} {c : CptT}
    (h : LRSSLT R E n Γ A₁ A₂ (.sort w) c) :
    LRSSLT R E n Γ A₂ A₁ (.sort w) c := by
  rcases h with hP | h
  · exact Or.inl hP
  · exact Or.inr (lrSCoreSLT_symm_of_envWfT hL hNU hW hΓ h)

theorem lrSSLT_trans_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ A₂ A₃ : Expr Nat} {w : Level} {c : CptT}
    (h₁ : LRSSLT R E n Γ A₁ A₂ (.sort w) c) (h₂ : LRSSLT R E n Γ A₂ A₃ (.sort w) c) :
    LRSSLT R E n Γ A₁ A₃ (.sort w) c := by
  rcases h₁ with hP | h₁
  · exact Or.inl hP
  · rcases h₂ with hP | h₂
    · exact Or.inl hP
    · exact Or.inr (lrSCoreSLT_trans_of_envWfT hL hNU hW hΓ h₁ h₂)

theorem lrSSLT_symm_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSLT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' : Expr Nat} (h : LRSSLT R E n Γ N N' A u) :
    LRSSLT R E n Γ N' N A u := by
  rcases h with hP | h
  · exact Or.inl hP
  · exact Or.inr (lrSCoreSLT_symm_tm_of_envWfT hL hNU hW hΓ hAA hu h)

theorem lrSSLT_trans_tm_of_envWfT (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreSLT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' N'' : Expr Nat} (h₁ : LRSSLT R E n Γ N N' A u) (h₂ : LRSSLT R E n Γ N' N'' A u) :
    LRSSLT R E n Γ N N'' A u := by
  rcases h₁ with hP | h₁
  · exact Or.inl hP
  · rcases h₂ with hP | h₂
    · exact Or.inl hP
    · exact Or.inr (lrSCoreSLT_trans_tm_of_envWfT hL hNU hW hΓ hAA hu h₁ h₂)

/-- 3-Observation Transport Bridge from `LRSCoreSLT` (`famObsTransport_of_lrSCoreSLT_probes`). -/
theorem famObsTransport_of_lrSCoreSLT_probes (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N I : Expr Nat}
    (hreal : FamProbeRealizedAtT R E n Γ M)
    (hrel : ∀ c, FamSatProbeCptT E c → ApproxT E (ctxEnvT E Γ) M c → LRSCoreSLT R E n Γ M N I c) :
    FamObsTransport R E n Γ M N := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hread⟩
    obtain ⟨_, _, v, _, hN⟩ := (lrSCoreSLT_sortCode_iff u).mp
      (hrel (sortCode u) (famSatProbeCptT_sortCode u) (hreal.1.1 u hread))
    exact ⟨v, hN⟩
  · intro A B hread hΓA
    exact piRead_of_lrSCoreSL_left hL hNU hread
      (piProbeSLT_iff_lrSCoreSL.mp (hrel (.pi .bot []) .piBotNil (hreal.1.2 A B hread hΓA)))
  · intro r m ls xs w hm hind hread hty hlen hargs
    have hSLT := hrel (.spine r (botVecT xs)) (famSatProbeCptT_spine_botVecT hm hind hlen)
      (hreal.2 r m ls xs w hm hind hread hty hlen hargs)
    rw [lrSCoreSLT_spine_iff] at hSLT
    exact famSpineRead_of_lrSCoreSL_left hL hNU hW hΓ hm hind hread hlen
      ((lrSCoreSL_spine_iff Γ M N I r (botVecT xs)).mpr hSLT.1)

/-- 3-Observation Equivalence Bridge from `LRSCoreSLT` (`famObsEquiv_of_lrSCoreSLT_probes`). -/
theorem famObsEquiv_of_lrSCoreSLT_probes (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N I : Expr Nat}
    (hrealM : FamProbeRealizedAtT R E n Γ M)
    (hrealN : FamProbeRealizedAtT R E n Γ N)
    (hrel : ∀ c, FamSatProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) M c ∨ ApproxT E (ctxEnvT E Γ) N c) →
      LRSCoreSLT R E n Γ M N I c) :
    FamObsEquiv R E n Γ M N :=
  ⟨famObsTransport_of_lrSCoreSLT_probes hL hNU hW hΓ hrealM
      (fun c hc hM => hrel c hc (Or.inl hM)),
   famObsTransport_of_lrSCoreSLT_probes hL hNU hW hΓ hrealN
      (fun c hc hN => lrSCoreSLT_famProbe_symm hW hΓ (famSatProbeCptT_to_famProbeCptT hc)
        (hrel c hc (Or.inr hN)))⟩

/-- Lambda-demand application step for `LRSCoreSLT` (`lrSCoreSLT_app_of_lambda_demand`). -/
theorem lrSCoreSLT_app_of_lambda_demand (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B : Expr Nat} {graph : List (List CptT × CptT)} {s : List CptT × CptT}
    (_hc_fg : ConvT E n Γ f g (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hfg : LRSCoreSLT R E n Γ f g (.pi A B) (.lam graph))
    (hs : s ∈ graph)
    (hab : ∀ u ∈ s.1, LRSCoreSLT R E n Γ a b A u) :
    LRSCoreSLT R E n Γ (.app f a) (.app g b) (instantiate0 a B) s.2 := by
  rw [LRSCoreSLT.eq_def] at hfg
  obtain ⟨A₁, B₁, hr, _, hclause⟩ := hfg
  obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU (.refl (.pi A B)) hr
  subst eA; subst eB
  obtain ⟨ha_ty, hb_ty, _⟩ := convEnds hW hΓ hc_ab
  exact hclause s hs a b ha_ty hb_ty ⟨hc_ab⟩ hab

/-- Spine-growth application step for `LRSCoreSLT` on admitted `.inductiveM` family spines
    (`lrSCoreSLT_app_of_famSpine_step`). -/
theorem lrSCoreSLT_app_of_famSpine_step (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {f g a b A B : Expr Nat} {args : List CptT} (u : CptT)
    (hc_fg : ConvT E n Γ f g (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hf_sp : LRSCoreSLT R E n Γ f g (.pi A B) (.spine r args))
    (hsp_ty : ∀ ls₁ xs₁, RedR R Γ f (foldApps (.const r ls₁) xs₁) →
      ∃ df_sp : HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.pi A B),
        xs₁.length < (piDomsOf m.mtype).length ∧
        PiTowerLinkBelow R E n (sizeOf df_sp) ∧
        (xs₁.length + 1 = (piDomsOf m.mtype).length →
          ∀ D' B', ¬ RedR R Γ (instantiate0 a B) (.pi D' B'))) :
    LRSCoreSLT R E n Γ (.app f a) (.app g b) (instantiate0 a B) (.spine r (args ++ [u])) := by
  rw [lrSCoreSLT_spine_iff] at hf_sp ⊢
  have hf_sl : LRSCoreSL R E n Γ f g (.pi A B) (.spine r args) :=
    (lrSCoreSL_spine_iff Γ f g (.pi A B) r args).mpr hf_sp.1
  have hstep_sl := lrSCoreSL_app_of_famSpine_step hL hNU hW hΓ hm hind u hc_fg hc_ab hf_sl
    (fun ls₁ xs₁ hred => let ⟨df, hlt, hlink, _⟩ := hsp_ty ls₁ xs₁ hred; ⟨df, hlt, hlink⟩)
  rw [lrSCoreSL_spine_iff] at hstep_sl
  refine ⟨hstep_sl, ?_⟩
  rintro ⟨D', B', hpi⟩
  rcases hf_sp.1.2 with ⟨m', ls₁, _, xs₁, _, hm', _, _, _, _, hred₁, _, _, _, _, ha1, _, _⟩ | ⟨hnone, _⟩
  · have em : m = m' := Option.some.inj (hm.symm.trans hm')
    subst em
    obtain ⟨_, hlt, _, hnot_pi⟩ := hsp_ty ls₁ xs₁ hred₁
    rcases Nat.lt_or_eq_of_le (show xs₁.length + 1 ≤ (piDomsOf m.mtype).length from hlt) with hlt1 | heq1
    · refine ⟨m, hm, hind, ?_⟩
      simp only [List.length_append, List.length_singleton]
      omega
    · exact (hnot_pi heq1 D' B' hpi).elim
  · exact (hnone m hm).elim


/-! #### §12 Part C — Semantic Non-Sort Proposition Classifier `IsSemNoSortPropRecKCanon`, Term Logical Relation `LRTermFamNoSortRKCanon` & `LRTermFamNoSortBiProbeRKCanon`, 4-Line Local `TyConvT` Transport, and Open-Predicate `ConvT.irr` Closure -/

/-- **`ZeroSortCoherence`-Free Semantic Non-Sort Proposition Classifier Over `ApproxDIKCanon`
    (`IsSemNoSortPropRecKCanon E n Γ A`):**
    `A` is `TyConvT`-convertible to some `P` with `HasTyT E n Γ P (.sort .zero)` (`Prop`) and
    satisfies `¬ ApproxDIKCanon E Γ A .sort`.
    Strictly extends §20's `IsSemRigidPropRecKCanon` to open proposition variables `.bvar i : Prop`
    and applied open predicate spines `foldApps (.bvar i) xs : Prop` (`lookupValue Γ i = none`) while
    retaining unconditional all-type PER and 4-line local `TyConvT` transport with **zero**
    `EnvWfT E` and **zero** `ZeroSortCoherence E n`! -/
def IsSemNoSortPropRecKCanon (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) : Prop :=
  (∃ P : Expr Nat, Nonempty (HasTyT E n Γ P (.sort .zero)) ∧ Nonempty (TyConvT E n Γ P A)) ∧
    ¬ ApproxDIKCanon E Γ A .sort

/-- Every `.pi A₁ B₁` satisfies `¬ ApproxDIKCanon E Γ (.pi A₁ B₁) .sort` (`not_approxDIKCanon_pi_sort`). -/
theorem not_approxDIKCanon_pi_sort (E : ResolvedEnv) (Γ : LCtx) (A₁ B₁ : Expr Nat) :
    ¬ ApproxDIKCanon E Γ (.pi A₁ B₁) .sort := by
  intro h
  rcases approxDI_pi_inv ((approxDIKCanon_pi_iff E Γ A₁ B₁ .sort).mp h) with hbot | ⟨_, _, heq, _, _⟩
  · exact CptI.noConfusion hbot
  · exact CptI.noConfusion heq

/-- Under `EnvWfT E`, every admitted `.inductiveM` family spine `foldApps (.const r ls) xs`
    satisfies `¬ ApproxDIKCanon E Γ (foldApps (.const r ls) xs) .sort`
    (`not_approxDIKCanon_famApp_sort`). -/
theorem not_approxDIKCanon_famApp_sort (hW : EnvWfT E) (Γ : LCtx)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (ls : List Level) (xs : List (Expr Nat)) :
    ¬ ApproxDIKCanon E Γ (foldApps (.const r ls) xs) .sort := by
  intro h
  have hDI : PiModelDeltaIotaAudit.ApproxDI E (ctxEnvDI E Γ) (foldApps (.const r ls) xs) .sort :=
    (approxDIKCanon_famApp_iff hW Γ hm hind ls xs .sort).mp h
  rcases (PiModelDeltaIotaAudit.approxDI_foldApps_rigid_iff ls
    (rigidConst_of_inductiveM hW hm hind) xs .sort).mp hDI with hbot | ⟨_, _, heq⟩
  · exact CptI.noConfusion hbot
  · exact CptI.noConfusion heq

/-- Every open assumption-variable spine `foldApps (.bvar i) xs` (`lookupValue Γ i = none`)
    satisfies `¬ ApproxDIKCanon E Γ (foldApps (.bvar i) xs) .sort`
    (`not_approxDIKCanon_bvarSpine_sort`). -/
theorem not_approxDIKCanon_bvarSpine_sort {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) (xs : List (Expr Nat)) :
    ¬ ApproxDIKCanon E Γ (foldApps (.bvar i) xs) .sort := by
  intro h
  exact CptI.noConfusion ((approxDIKCanon_foldApps_bvar_of_lookupValue_none_iff hnone xs .sort).mp h)

/-- Under `EnvWfT E`, every `IsSemRigidPropRecKCanon E n Γ A` is an `IsSemNoSortPropRecKCanon E n Γ A`
    (`isSemNoSortPropRecKCanon_of_isSemRigidPropRecKCanon`). -/
theorem isSemNoSortPropRecKCanon_of_isSemRigidPropRecKCanon (hW : EnvWfT E)
    {Γ : LCtx} {A : Expr Nat} (h : IsSemRigidPropRecKCanon E n Γ A) :
    IsSemNoSortPropRecKCanon E n Γ A := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨A₁, B₁, hpi⟩ | ⟨r, m, ls, xs, hm, hind, _, hfam⟩
  · intro hs
    exact not_approxDIKCanon_pi_sort E Γ A₁ B₁
      ((whRedRecKCanon_approxDIKCanon_iff_of_envWfT hW hpi .sort).mp hs)
  · intro hs
    exact not_approxDIKCanon_famApp_sort hW Γ hm hind ls xs
      ((whRedRecKCanon_approxDIKCanon_iff_of_envWfT hW hfam .sort).mp hs)

/-- Every open predicate spine `foldApps (.bvar i) xs : Prop` (`lookupValue Γ i = none`) satisfies
    `IsSemNoSortPropRecKCanon` (`isSemNoSortPropRecKCanon_bvarSpine`). -/
theorem isSemNoSortPropRecKCanon_bvarSpine {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) (xs : List (Expr Nat))
    (h0 : HasTyT E n Γ (foldApps (.bvar i) xs) (.sort .zero)) :
    IsSemNoSortPropRecKCanon E n Γ (foldApps (.bvar i) xs) :=
  ⟨⟨foldApps (.bvar i) xs, ⟨h0⟩, ⟨.refl Γ _⟩⟩, not_approxDIKCanon_bvarSpine_sort hnone xs⟩

/-- Every open proposition variable `.bvar i : Prop` (`lookupValue Γ i = none`) satisfies
    `IsSemNoSortPropRecKCanon` (`isSemNoSortPropRecKCanon_bvar`). -/
theorem isSemNoSortPropRecKCanon_bvar {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) (h0 : HasTyT E n Γ (.bvar i) (.sort .zero)) :
    IsSemNoSortPropRecKCanon E n Γ (.bvar i) :=
  isSemNoSortPropRecKCanon_bvarSpine hnone [] h0

/-- No `.sort u` satisfies `IsSemNoSortPropRecKCanon` (`not_isSemNoSortPropRecKCanon_sort`), with
    **zero** hypotheses! -/
theorem not_isSemNoSortPropRecKCanon_sort (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (u : Level) :
    ¬ IsSemNoSortPropRecKCanon E n Γ (.sort u) :=
  fun h => h.2 (approxDIKCanon_sort E Γ u)

/-- No `A` with `WhRedRecKCanon E Γ A (.sort u)` satisfies `IsSemNoSortPropRecKCanon E n Γ A`
    (`not_isSemNoSortPropRecKCanon_of_whRed_sort`), with **zero** hypotheses! -/
theorem not_isSemNoSortPropRecKCanon_of_whRed_sort {Γ : LCtx} {A : Expr Nat} {u : Level}
    (hsort : WhRedRecKCanon E Γ A (.sort u)) :
    ¬ IsSemNoSortPropRecKCanon E n Γ A :=
  fun h => h.2 (approxDIKCanon_of_whRedRecKCanon hsort (approxDIKCanon_sort E Γ u))

/-- **4-Line Local `TyConvT` Transport for `IsSemNoSortPropRecKCanon`
    (`isSemNoSortPropRecKCanon_transport_of_typeRel`):**
    Requires **only** `TyConvT E n Γ A A'` and `LRTypeFamINBiProbeRKCanon E n Γ A A'` — with
    **zero** `EnvWfT E`, **zero** `ZeroSortCoherence E n`, and **zero** `FundamentalLRFamINProbeRKCanon E n`! -/
theorem isSemNoSortPropRecKCanon_transport_of_typeRel {Γ : LCtx} {A A' : Expr Nat}
    (hcAA' : TyConvT E n Γ A A')
    (hrelAA' : LRTypeFamINBiProbeRKCanon E n Γ A A')
    (h : IsSemNoSortPropRecKCanon E n Γ A) :
    IsSemNoSortPropRecKCanon E n Γ A' := by
  obtain ⟨⟨P, ⟨hP⟩, ⟨hcPA⟩⟩, hns⟩ := h
  refine ⟨⟨P, ⟨hP⟩, ⟨.trans Γ P A A' hcPA hcAA'⟩⟩, fun hcA' => ?_⟩
  cases hrelAA' .sort .sort (Or.inr hcA') with
  | sort hA _ => exact hns (approxDIKCanon_of_whRedRecKCanon hA (approxDIKCanon_sort E Γ _))

/-- All-cutoff weakening of `IsSemNoSortPropRecKCanon` across any `d : LocalDecl` and `k ≤ Γ.length`
    (`isSemNoSortPropRecKCanon_weaken`). -/
theorem isSemNoSortPropRecKCanon_weaken (hcl : EnvClosed E) (d : LocalDecl) {k : Nat} {Γ : LCtx}
    (hk : k ≤ Γ.length) {A : Expr Nat} (h : IsSemNoSortPropRecKCanon E n Γ A) :
    IsSemNoSortPropRecKCanon E n (insertAt d k Γ) (lift k 1 A) := by
  obtain ⟨⟨P, ⟨hP⟩, ⟨hcPA⟩⟩, hns⟩ := h
  exact ⟨⟨lift k 1 P, ⟨hasTyTWeaken d hcl (c := k) hP⟩, ⟨tyConvTWeaken d hcl (c := k) hcPA⟩⟩,
    fun hs => hns ((approxDIKCanon_lift_iff hcl d hk A .sort).mp hs)⟩

/-- **Semantic Non-Sort Proposition Term Logical Relation Over `WhRedRecKCanon`
    (`LRTermFamNoSortRKCanon E n Γ M M' A c`):** -/
def LRTermFamNoSortRKCanon (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (M M' A : Expr Nat) : CptI → Prop
  | .bot => True
  | c =>
      IsSemNoSortPropRecKCanon E n Γ A ∨
        ((∃ l, WhRedRecKCanon E Γ A (.sort l)) ∧ LRTypeFamINRKCanon E n Γ M M' c)

@[simp] theorem lrTermFamNoSortRKCanon_bot (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (M M' A : Expr Nat) :
    LRTermFamNoSortRKCanon E n Γ M M' A .bot := trivial

theorem lrTermFamNoSortRKCanon_of_ne_bot_iff {Γ : LCtx}
    {M M' A : Expr Nat} {c : CptI} (hc : c ≠ .bot) :
    LRTermFamNoSortRKCanon E n Γ M M' A c ↔
      (IsSemNoSortPropRecKCanon E n Γ A ∨
        ((∃ l, WhRedRecKCanon E Γ A (.sort l)) ∧ LRTypeFamINRKCanon E n Γ M M' c)) := by
  cases c with
  | bot => exact (hc rfl).elim
  | sort | pi _ _ | lam _ | spine _ _ => rfl

theorem lrTermFamNoSortRKCanon_of_isSemNoSortPropRecKCanon {Γ : LCtx}
    {M M' A : Expr Nat} (h : IsSemNoSortPropRecKCanon E n Γ A) (c : CptI) :
    LRTermFamNoSortRKCanon E n Γ M M' A c := by
  cases c <;> first | exact trivial | exact Or.inl h

theorem lrTermFamNoSortRKCanon_of_lrTermFamSemRKCanon (hW : EnvWfT E) {Γ : LCtx}
    {M M' A : Expr Nat} (c : CptI)
    (h : LRTermFamSemRKCanon E n Γ M M' A c) :
    LRTermFamNoSortRKCanon E n Γ M M' A c := by
  cases c with
  | bot => exact trivial
  | sort | pi _ _ | lam _ | spine _ _ =>
      rcases h with hprop | hsort
      · exact Or.inl (isSemNoSortPropRecKCanon_of_isSemRigidPropRecKCanon hW hprop)
      · exact Or.inr hsort

/-- At any `A` with `WhRedRecKCanon E Γ A (.sort u)`, `LRTermFamNoSortRKCanon E n Γ M M' A c` is
    logically equivalent (`↔`) to `LRTypeFamINRKCanon E n Γ M M' c` with **zero** hypotheses
    (`lrTermFamNoSortRKCanon_whRed_sort_iff_lrTypeFamINRKCanon`)! -/
theorem lrTermFamNoSortRKCanon_whRed_sort_iff_lrTypeFamINRKCanon {Γ : LCtx}
    {M M' A : Expr Nat} {u : Level}
    (hA : WhRedRecKCanon E Γ A (.sort u)) (c : CptI) :
    LRTermFamNoSortRKCanon E n Γ M M' A c ↔ LRTypeFamINRKCanon E n Γ M M' c := by
  cases c with
  | bot => exact ⟨fun _ => .bot _ _ _, fun _ => trivial⟩
  | sort | pi _ _ | lam _ | spine _ _ =>
      exact ⟨fun h => h.elim (fun hp => (not_isSemNoSortPropRecKCanon_of_whRed_sort hA hp).elim) And.right,
             fun h => Or.inr ⟨⟨u, hA⟩, h⟩⟩

theorem lrTermFamNoSortRKCanon_sort_iff_lrTypeFamINRKCanon {Γ : LCtx}
    (M M' : Expr Nat) (u : Level) (c : CptI) :
    LRTermFamNoSortRKCanon E n Γ M M' (.sort u) c ↔ LRTypeFamINRKCanon E n Γ M M' c :=
  lrTermFamNoSortRKCanon_whRed_sort_iff_lrTypeFamINRKCanon (.refl (.sort u)) c

/-- Unconditional symmetry of `LRTermFamNoSortRKCanon` across all compacts `c : CptI` under
    `EnvWfT E` and `CtxWfT E n Γ` alone (`lrTermFamNoSortRKCanon_symm_of_envWfT`). -/
theorem lrTermFamNoSortRKCanon_symm_of_envWfT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A : Expr Nat} (c : CptI)
    (h : LRTermFamNoSortRKCanon E n Γ M M' A c) :
    LRTermFamNoSortRKCanon E n Γ M' M A c := by
  cases c with
  | bot => exact trivial
  | sort | pi _ _ | lam _ | spine _ _ =>
      rcases h with hprop | ⟨hl, hLR⟩
      · exact Or.inl hprop
      · exact Or.inr ⟨hl, lrTypeFamINRKCanon_symm_of_envWfT hW hΓ hLR⟩

/-- Unconditional transitivity of `LRTermFamNoSortRKCanon` across all compacts `c : CptI` under
    `EnvWfT E` and `CtxWfT E n Γ` alone (`lrTermFamNoSortRKCanon_trans_of_envWfT`). -/
theorem lrTermFamNoSortRKCanon_trans_of_envWfT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N P A : Expr Nat} (c : CptI)
    (h₁ : LRTermFamNoSortRKCanon E n Γ M N A c)
    (h₂ : LRTermFamNoSortRKCanon E n Γ N P A c) :
    LRTermFamNoSortRKCanon E n Γ M P A c := by
  cases c with
  | bot => exact trivial
  | sort | pi _ _ | lam _ | spine _ _ =>
      rcases h₁ with hprop | ⟨hl, hLR₁⟩
      · exact Or.inl hprop
      · rcases h₂ with hprop | ⟨_, hLR₂⟩
        · exact Or.inl hprop
        · exact Or.inr ⟨hl, lrTypeFamINRKCanon_trans_of_envWfT hW hΓ hLR₁ hLR₂⟩

/-- **4-Line Local Index Transport for `LRTermFamNoSortRKCanon` Across All Compacts `c : CptI`
    (`lrTermFamNoSortRKCanon_transport_of_typeRel`):**
    Requires **only** `TyConvT E n Γ A A'` and `LRTypeFamINBiProbeRKCanon E n Γ A A'` (zero `EnvWfT E`,
    zero `ZeroSortCoherence E n`, zero `FundamentalLRFamINProbeRKCanon E n`)! -/
theorem lrTermFamNoSortRKCanon_transport_of_typeRel {Γ : LCtx} {A A' M M' : Expr Nat}
    (hcAA' : TyConvT E n Γ A A')
    (hrelAA' : LRTypeFamINBiProbeRKCanon E n Γ A A')
    (c : CptI)
    (h : LRTermFamNoSortRKCanon E n Γ M M' A c) :
    LRTermFamNoSortRKCanon E n Γ M M' A' c := by
  cases c with
  | bot => exact trivial
  | sort | pi _ _ | lam _ | spine _ _ =>
      rcases h with hprop | ⟨⟨l, hl⟩, hLR⟩
      · exact Or.inl (isSemNoSortPropRecKCanon_transport_of_typeRel hcAA' hrelAA' hprop)
      · have hcA : ApproxDIKCanon E Γ A .sort :=
          approxDIKCanon_of_whRedRecKCanon hl (approxDIKCanon_sort E Γ l)
        cases hrelAA' .sort .sort (Or.inl hcA) with
        | sort _ hl' => exact Or.inr ⟨⟨_, hl'⟩, hLR⟩

/-- Bidirectional `FamProbeCpt E`-restricted counterpart of `LRTermFamNoSortRKCanon`
    (`LRTermFamNoSortBiProbeRKCanon`). -/
def LRTermFamNoSortBiProbeRKCanon (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (M M' A : Expr Nat) : Prop :=
  ∀ c, FamProbeCpt E c →
    (ApproxDIKCanon E Γ M c ∨ ApproxDIKCanon E Γ M' c) →
    LRTermFamNoSortRKCanon E n Γ M M' A c

theorem lrTermFamNoSortBiProbeRKCanon_of_lrTermFamSemBiProbeRKCanon (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat}
    (h : LRTermFamSemBiProbeRKCanon E n Γ M M' A) :
    LRTermFamNoSortBiProbeRKCanon E n Γ M M' A :=
  fun c hc hap => lrTermFamNoSortRKCanon_of_lrTermFamSemRKCanon hW c (h c hc hap)

theorem lrTermFamNoSortBiProbeRKCanon_whRed_sort_iff {Γ : LCtx}
    {M M' A : Expr Nat} {u : Level}
    (hA : WhRedRecKCanon E Γ A (.sort u)) :
    LRTermFamNoSortBiProbeRKCanon E n Γ M M' A ↔
      LRTypeFamINBiProbeRKCanon E n Γ M M' :=
  ⟨fun h c hc hap =>
     (lrTermFamNoSortRKCanon_whRed_sort_iff_lrTypeFamINRKCanon hA c).mp (h c hc hap),
   fun h c hc hap =>
     (lrTermFamNoSortRKCanon_whRed_sort_iff_lrTypeFamINRKCanon hA c).mpr (h c hc hap)⟩

theorem lrTermFamNoSortBiProbeRKCanon_sort_iff {Γ : LCtx} (M M' : Expr Nat) (u : Level) :
    LRTermFamNoSortBiProbeRKCanon E n Γ M M' (.sort u) ↔
      LRTypeFamINBiProbeRKCanon E n Γ M M' :=
  lrTermFamNoSortBiProbeRKCanon_whRed_sort_iff (.refl (.sort u))

theorem lrTermFamNoSortBiProbeRKCanon_symm_of_envWfT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A : Expr Nat}
    (h : LRTermFamNoSortBiProbeRKCanon E n Γ M M' A) :
    LRTermFamNoSortBiProbeRKCanon E n Γ M' M A :=
  fun c hc hap => lrTermFamNoSortRKCanon_symm_of_envWfT hW hΓ c (h c hc hap.symm)

theorem lrTermFamNoSortBiProbeRKCanon_trans_of_envWfT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M N P A : Expr Nat}
    (h₁ : LRTermFamNoSortBiProbeRKCanon E n Γ M N A)
    (h₂ : LRTermFamNoSortBiProbeRKCanon E n Γ N P A) :
    LRTermFamNoSortBiProbeRKCanon E n Γ M P A := by
  intro c hc happrox
  have hAt : ∀ hbot : c ≠ .bot, LRTermFamNoSortRKCanon E n Γ M P A c := by
    intro hbot
    rcases happrox with hM | hP
    · have r₁ := h₁ c hc (Or.inl hM)
      rcases (lrTermFamNoSortRKCanon_of_ne_bot_iff hbot).mp r₁ with hprop | ⟨_, hLR₁⟩
      · exact lrTermFamNoSortRKCanon_of_isSemNoSortPropRecKCanon hprop c
      · have hN := (approxDIKCanon_of_lrTypeFamINRKCanon_famProbeCpt hW hc hLR₁).2
        exact lrTermFamNoSortRKCanon_trans_of_envWfT hW hΓ c r₁ (h₂ c hc (Or.inl hN))
    · have r₂ := h₂ c hc (Or.inr hP)
      rcases (lrTermFamNoSortRKCanon_of_ne_bot_iff hbot).mp r₂ with hprop | ⟨_, hLR₂⟩
      · exact lrTermFamNoSortRKCanon_of_isSemNoSortPropRecKCanon hprop c
      · have hN := (approxDIKCanon_of_lrTypeFamINRKCanon_famProbeCpt hW hc hLR₂).1
        exact lrTermFamNoSortRKCanon_trans_of_envWfT hW hΓ c (h₁ c hc (Or.inr hN)) r₂
  cases hc with
  | bot => exact trivial
  | sort => exact hAt CptI.noConfusion
  | pi_bot_nil => exact hAt CptI.noConfusion
  | famSpine _ _ _ _ => exact hAt CptI.noConfusion

theorem lrTermFamNoSortBiProbeRKCanon_transport_of_typeRel {Γ : LCtx} {A A' M M' : Expr Nat}
    (hcAA' : TyConvT E n Γ A A')
    (hrelAA' : LRTypeFamINBiProbeRKCanon E n Γ A A')
    (h : LRTermFamNoSortBiProbeRKCanon E n Γ M M' A) :
    LRTermFamNoSortBiProbeRKCanon E n Γ M M' A' :=
  fun c hc hap => lrTermFamNoSortRKCanon_transport_of_typeRel hcAA' hrelAA' c (h c hc hap)

/-- **Direct `ConvT.irr` Closure in `LRTermFamNoSortBiProbeRKCanon` From `¬ ApproxDIKCanon E Γ P .sort`
    (`lrTermFamNoSortBiProbeRKCanon_irr_of_not_approx_sort`):**
    Reduces `ConvT.irr Γ P p q` for **arbitrary** propositions `P` (`HasTyT E n Γ P (.sort .zero)`)
    to the single condition `¬ ApproxDIKCanon E Γ P .sort`! -/
theorem lrTermFamNoSortBiProbeRKCanon_irr_of_not_approx_sort {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hns : ¬ ApproxDIKCanon E Γ P .sort) :
    LRTermFamNoSortBiProbeRKCanon E n Γ p q P :=
  fun c _ _ => lrTermFamNoSortRKCanon_of_isSemNoSortPropRecKCanon ⟨⟨P, ⟨hP⟩, ⟨.refl Γ P⟩⟩, hns⟩ c

/-- **Unconditional `ConvT.irr` Closure in `LRTermFamNoSortBiProbeRKCanon` on Open Predicate Spines
    (`lrTermFamNoSortBiProbeRKCanon_irr_bvarSpine`):**
    For any open assumption-variable predicate spine `P = foldApps (.bvar i) xs : Prop`
    (`lookupValue Γ i = none`), `LRTermFamNoSortBiProbeRKCanon E n Γ p q (foldApps (.bvar i) xs)`
    holds **unconditionally** for all `p, q : Expr Nat`! -/
theorem lrTermFamNoSortBiProbeRKCanon_irr_bvarSpine {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) (xs : List (Expr Nat)) {p q : Expr Nat}
    (hP : HasTyT E n Γ (foldApps (.bvar i) xs) (.sort .zero)) :
    LRTermFamNoSortBiProbeRKCanon E n Γ p q (foldApps (.bvar i) xs) :=
  lrTermFamNoSortBiProbeRKCanon_irr_of_not_approx_sort hP (not_approxDIKCanon_bvarSpine_sort hnone xs)

/-- Unconditional `ConvT.irr` closure in `LRTermFamNoSortBiProbeRKCanon` on open proposition
    variables `.bvar i : Prop` (`lookupValue Γ i = none`) (`lrTermFamNoSortBiProbeRKCanon_irr_bvar`). -/
theorem lrTermFamNoSortBiProbeRKCanon_irr_bvar {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) {p q : Expr Nat}
    (hP : HasTyT E n Γ (.bvar i) (.sort .zero)) :
    LRTermFamNoSortBiProbeRKCanon E n Γ p q (.bvar i) :=
  lrTermFamNoSortBiProbeRKCanon_irr_bvarSpine hnone [] hP


/-! ### §13 — Direct Bridges to Landed `#7740` (`RcicNativeTypedModelRelS` / `RcicNativeTypedModelFund` /
    `RcicNativeTypedModelFamSpine` / `RcicNativeTypedModelFundStrong` / `RcicNativeTypedModelProbe` /
    `RcicSubstTTyped`): Unconditional `LevelCongrT`, `ConvArgsSymmS` Refutation on `polyAxEnv`,
    `ConvArgsSymmS`/`ConvArgsTransS`-Free PER & Read-Off for `LRSCoreS` on `FamProbeCptT` and
    `piTowerCptT`, Unconditional `RelSubstIdT` at `EnvT.bot` and `ctxEnvT` from `FundamentalSAtT`,
    Refutation of Unrestricted `TypingLemmaEnvT`, and `W-FAMSPINE` Resolution in `LRSCoreS` -/

/-! #### §13 Part A — Unconditional Discharge of `RcicNativeTypedModelFamSpine.LevelCongrT`,
    `polyAxEnv` Refutation of `ConvArgsSymmS`, and `ConvArgsSymmS`/`ConvArgsTransS`-Free PER &
    Read-Off for Landed `LRSCoreS` on `FamProbeCptT E` and `piTowerCptT k` -/

/-- **Unconditional Discharge of `RcicNativeTypedModelFamSpine.LevelCongrT` Under `EnvWfT E` Alone
    (`levelCongrT_of_envWfT`):**
    Discharges `#7740`'s `TypedModelAudit.LevelCongrT E n` (`RcicNativeTypedModelFamSpine`) directly
    from `hW : EnvWfT E` via `convT_instantiateLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW)`
    (`RcicTypedLevelsCongr`). -/
theorem levelCongrT_of_envWfT (hW : EnvWfT E) : TypedModelAudit.LevelCongrT E n := by
  intro a ls ls' hbel hbel' hlen _ heqN Γ T u hT
  exact ⟨convT_instantiateLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW)
    heqN hbel hbel' hlen hT⟩

/-- **Obstruction to Unguarded `RcicNativeTypedModelRelS.ConvArgsSymmS` on `polyAxEnv`
    (`convT_piDom_of_convArgsSymmS_polyAxEnv`):**
    Any proof of `#7740`'s `TypedModelAudit.ConvArgsSymmS polyAxEnv n` (`RcicNativeTypedModelRelS`)
    forces Π-domain conversion transport `ConvT polyAxEnv n Γ x y A₁ → Nonempty (ConvT polyAxEnv n Γ y x A₂)`
    across any `ConvT polyAxEnv n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort polyAxDomSort)`! -/
theorem convT_piDom_of_convArgsSymmS_polyAxEnv
    (hSymm : TypedModelAudit.ConvArgsSymmS polyAxEnv n)
    {Γ : LCtx} (hΓ : CtxWfT polyAxEnv n Γ)
    {A₁ B₁ A₂ B₂ x y : Expr Nat}
    (hcPi : ConvT polyAxEnv n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort polyAxDomSort))
    (hxy : ConvT polyAxEnv n Γ x y A₁) :
    Nonempty (ConvT polyAxEnv n Γ y x A₂) :=
  convT_piDom_of_unguarded_convArgsSymmS_polyAxEnv
    (fun {_} hΓ₀ {_ _} hm {_ _ _ _} _ _ _ heqN hargs => hSymm hΓ₀ hm heqN hargs) hΓ hcPi hxy

/-- Both universe codes `.prop` and `.sort` have the exact same `LRSCoreS` clause (`SortClauseT`). -/
theorem lrSCoreS_sortCode_iff {Γ : LCtx} {M M' A : Expr Nat} (l : Level) :
    LRSCoreS R E n Γ M M' A (sortCode l) ↔ SortClauseT R Γ M M' A := by
  rcases sortCode_prop_or_sort l with h | h
  · rw [h, lrSCoreS_prop_iff]
  · rw [h, lrSCoreS_sort_iff]

/-- **Symmetry of `SpineClauseS` at Any Admitted `.inductiveM` Head and Sort Index Under `EnvWfT E`
    Alone (`spineClauseS_inductiveM_sort_symm`):**
    Because `SpineClauseS` at `m.mclass = .inductiveM` and `∃ l, RedR R Γ A (.sort l)` supplies
    both saturation equalities and both sort typings `HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.sort w)`
    and `HasTyT E n Γ (foldApps (.const r ls₂) xs₂) (.sort w')`, `convArgs_symm_instMtype_of_envWfT`
    flips `ConvArgsT` under `EnvWfT E` and `CtxWfT E n Γ` **alone** — with **zero** `ConvArgsSymmS`! -/
theorem spineClauseS_inductiveM_sort_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {M M' A : Expr Nat} (hA : ∃ l, RedR R Γ A (.sort l)) {args : List CptT}
    (h : SpineClauseS R E n Γ M M' A r args) :
    SpineClauseS R E n Γ M' M A r args := by
  obtain ⟨m', ls₁, ls₂, xs₁, xs₂, hm', h1, h2, hn₁, hn₂, heq, hl₁, hl₂, hca, hty⟩ := h
  have em : m = m' := Option.some.inj (hm.symm.trans hm')
  subst em
  obtain ⟨e₁, e₂, ⟨w, ⟨hw⟩⟩, ⟨w', ⟨hw'⟩⟩⟩ := hty hA hind
  refine ⟨m, ls₂, ls₁, xs₂, xs₁, hm, h2, h1, hn₂, hn₁, eqNList_symm'' heq, hl₂, hl₁,
    convArgs_symm_instMtype_of_envWfT hW hΓ hm hind hw hw' heq hca,
    fun _ _ => ⟨e₂, e₁, ⟨w', ⟨hw'⟩⟩, ⟨w, ⟨hw⟩⟩⟩⟩

/-- **Transitivity of `SpineClauseS` at Any Admitted `.inductiveM` Head and Sort Index Under `EnvWfT E`
    Alone (`spineClauseS_inductiveM_sort_trans`):**
    Uses `convArgs_trans_instMtype_of_envWfT` under `NormalUniqueR R`, `EnvWfT E`, and `CtxWfT E n Γ`
    **alone** — with **zero** `ConvArgsTransS`! -/
theorem spineClauseS_inductiveM_sort_trans (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {M M' M'' A : Expr Nat} (hA : ∃ l, RedR R Γ A (.sort l)) {args : List CptT}
    (h₁ : SpineClauseS R E n Γ M M' A r args)
    (h₂ : SpineClauseS R E n Γ M' M'' A r args) :
    SpineClauseS R E n Γ M M'' A r args := by
  obtain ⟨m₁, ls₁, ls₂, xs₁, xs₂, hm₁, h1, h2, hn₁, hn₂, heq, hl₁, _, hca, hty₁⟩ := h₁
  obtain ⟨m₂, ls₂', ls₃, xs₂', xs₃, hm₂, h2', h3, hn₂', hn₃, heq', _, hl₃, hca', hty₂⟩ := h₂
  have em₁ : m = m₁ := Option.some.inj (hm.symm.trans hm₁)
  subst em₁
  have em₂ : m = m₂ := Option.some.inj (hm.symm.trans hm₂)
  subst em₂
  have e := hNU Γ h2 hn₂ h2' hn₂'
  obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
  injection hconst with _ hls
  subst hls; subst hxs
  obtain ⟨e₁, _, ⟨w₁, ⟨hw₁⟩⟩, ⟨w₂, ⟨hw₂⟩⟩⟩ := hty₁ hA hind
  obtain ⟨_, e₃, _, ⟨w₃, ⟨hw₃⟩⟩⟩ := hty₂ hA hind
  refine ⟨m, ls₁, ls₃, xs₁, xs₃, hm, h1, h3, hn₁, hn₃, eqNList_trans'' heq heq', hl₁, hl₃,
    convArgs_trans_instMtype_of_envWfT hW hΓ hm hind hw₁ hw₂ heq hca hca',
    fun _ _ => ⟨e₁, e₃, ⟨w₁, ⟨hw₁⟩⟩, ⟨w₃, ⟨hw₃⟩⟩⟩⟩

/-- **Symmetry of Landed `LRSCoreS` on All `FamProbeCptT E` Compacts at Any Sort Index Under `EnvWfT E`
    Alone (`famProbeS_symm`):**
    Generalizes `RcicNativeTypedModelProbe.piProbeS_symm` from `.pi .bot []` to **all** `FamProbeCptT E`
    compacts (`.bot`, `.prop`, `.sort`, `.pi .bot []`, and `.spine r args` for admitted `.inductiveM`
    heads) with **zero** `ConvArgsSymmS`! -/
theorem famProbeS_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {c : CptT} (hc : FamProbeCptT E c) {M N A : Expr Nat}
    (hA : ∃ l, RedR R Γ A (.sort l))
    (h : LRSCoreS R E n Γ M N A c) :
    LRSCoreS R E n Γ N M A c := by
  cases hc with
  | bot => exact lrSCoreS_bot _ _ _ _
  | prop =>
      rw [lrSCoreS_prop_iff] at h ⊢
      obtain ⟨hI, u, u', h1, h2⟩ := h
      exact ⟨hI, u', u, h2, h1⟩
  | sort =>
      rw [lrSCoreS_sort_iff] at h ⊢
      obtain ⟨hI, u, u', h1, h2⟩ := h
      exact ⟨hI, u', u, h2, h1⟩
  | piBotNil => exact piProbeS_symm hW hΓ h
  | @spine r m args hm hind _ =>
      rw [lrSCoreS_spine_iff] at h ⊢
      exact spineClauseS_inductiveM_sort_symm hW hΓ hm hind hA h

/-- **Transitivity of Landed `LRSCoreS` on All `FamProbeCptT E` Compacts at Any Sort Index Under
    `EnvWfT E` Alone (`famProbeS_trans`):**
    Generalizes `RcicNativeTypedModelProbe.piProbeS_trans` from `.pi .bot []` to **all** `FamProbeCptT E`
    compacts with **zero** `ConvArgsTransS`! -/
theorem famProbeS_trans (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {c : CptT} (hc : FamProbeCptT E c) {M N P A : Expr Nat}
    (hA : ∃ l, RedR R Γ A (.sort l))
    (h₁ : LRSCoreS R E n Γ M N A c) (h₂ : LRSCoreS R E n Γ N P A c) :
    LRSCoreS R E n Γ M P A c := by
  cases hc with
  | bot => exact lrSCoreS_bot _ _ _ _
  | prop =>
      rw [lrSCoreS_prop_iff] at h₁ h₂ ⊢
      obtain ⟨hI, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hI, u, u'', h1, h3⟩
  | sort =>
      rw [lrSCoreS_sort_iff] at h₁ h₂ ⊢
      obtain ⟨hI, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hI, u, u'', h1, h3⟩
  | piBotNil => exact piProbeS_trans hL hNU hW hΓ h₁ h₂
  | @spine r m args hm hind _ =>
      rw [lrSCoreS_spine_iff] at h₁ h₂ ⊢
      exact spineClauseS_inductiveM_sort_trans hNU hW hΓ hm hind hA h₁ h₂

/-- **Right-Diagonal Recovery for Landed `LRSCoreS` on All `FamProbeCptT E` Compacts
    (`famProbeS_right_diag`):**
    Generalizes `RcicNativeTypedModelProbe.piProbeS_right_diag` from `.pi .bot []` to **all**
    `FamProbeCptT E` compacts: a single link `LRSCoreS R E n Γ M N A c` supplies its own next
    diagonal `LRSCoreS R E n Γ N N A c` with **zero** `ReadbackModelInvT` and **zero**
    `ConvArgsSymmS` / `ConvArgsTransS`! -/
theorem famProbeS_right_diag (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {c : CptT} (hc : FamProbeCptT E c) {M N A : Expr Nat}
    (hA : ∃ l, RedR R Γ A (.sort l))
    (h : LRSCoreS R E n Γ M N A c) :
    LRSCoreS R E n Γ N N A c :=
  famProbeS_trans hL hNU hW hΓ hc hA (famProbeS_symm hW hΓ hc hA h) h

/-- **Exact Equivalence Between Landed `LRSCoreS` at `piTowerCptT k` and `LRSCore` at `piTowerCpt k`
    (`piTowerS_iff`):**
    Generalizes `RcicNativeTypedModelProbe.piProbeS_iff` (`k = 0`) to every Π-tower height `k : Nat`. -/
theorem piTowerS_iff :
    ∀ (k : Nat) {Γ : LCtx} {M N A : Expr Nat},
      LRSCoreS R E n Γ M N A (piTowerCptT k) ↔ LRSCore R E n Γ M N A (piTowerCpt k)
  | 0, Γ, M, N, A => piProbeS_iff
  | k + 1, Γ, M, N, A => by
      simp only [piTowerCptT, piTowerCpt]
      rw [LRSCoreS.eq_def, LRSCore.eq_def]
      constructor
      · rintro ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod, _, hrf⟩
        refine ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod,
          ⟨.zero, lrSCore_bot _ _ _ _⟩, ?_⟩
        intro s hs N₁ N₂ hN₁ hN₂ hcN _
        have es := List.mem_singleton.mp hs
        subst es
        obtain ⟨v, hv⟩ := hrf ([], piTowerCptT k) (List.mem_singleton.mpr rfl)
          (fun _ hu => (List.not_mem_nil _ hu).elim) N₁ N₂ hN₁ hN₂ hcN
          (fun _ hu => (List.not_mem_nil _ hu).elim)
        exact ⟨v, (piTowerS_iff k).mp hv⟩
      · rintro ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod, _, hrf⟩
        refine ⟨hA, A₁, B₁, A₂, B₂, h1, h2, hΓ₁, hdom, hcod,
          ⟨.zero, lrSCoreS_bot _ _ _ _⟩, ?_⟩
        intro s hs _ N₁ N₂ hN₁ hN₂ hcN _
        have es := List.mem_singleton.mp hs
        subst es
        obtain ⟨v, hv⟩ := hrf ([], piTowerCpt k) (List.mem_singleton.mpr rfl)
          N₁ N₂ hN₁ hN₂ hcN (fun _ hu => (List.not_mem_nil _ hu).elim)
        exact ⟨v, (piTowerS_iff k).mpr hv⟩

/-- Symmetry of `LRSCoreS` at `piTowerCptT k` from `EnvWfT E` and `CtxWfT E n Γ` alone. -/
theorem piTowerS_symm (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {k : Nat} {M N A : Expr Nat}
    (h : LRSCoreS R E n Γ M N A (piTowerCptT k)) :
    LRSCoreS R E n Γ N M A (piTowerCptT k) :=
  (piTowerS_iff k).mpr (piTower_symm hW hΓ ((piTowerS_iff k).mp h))

/-- Transitivity of `LRSCoreS` at `piTowerCptT k` from `ReadbackLaws E R`, `NormalUniqueR R`,
    `EnvWfT E`, and `CtxWfT E n Γ` alone. -/
theorem piTowerS_trans (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {k : Nat} {M N P A : Expr Nat}
    (h₁ : LRSCoreS R E n Γ M N A (piTowerCptT k))
    (h₂ : LRSCoreS R E n Γ N P A (piTowerCptT k)) :
    LRSCoreS R E n Γ M P A (piTowerCptT k) :=
  (piTowerS_iff k).mpr
    (piTower_trans hL hNU hW hΓ ((piTowerS_iff k).mp h₁) ((piTowerS_iff k).mp h₂))

/-- Right-diagonal extraction for `LRSCoreS` at `piTowerCptT k` with zero `ConvArgsSymmS` /
    `ConvArgsTransS` and zero `BackTransportT`. -/
theorem piTowerS_right_diagonal (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {k : Nat} {M N A : Expr Nat}
    (h : LRSCoreS R E n Γ M N A (piTowerCptT k)) :
    LRSCoreS R E n Γ N N A (piTowerCptT k) :=
  piTowerS_trans hL hNU hW hΓ (piTowerS_symm hW hΓ h) h

/-- Extract `TyConvT E n Γ A₁ A₂` and `TyConvT E n (.assumption A₁ :: Γ) B₁ B₂` from `LRSCoreS`
    at `piTowerCptT k`. -/
theorem piTowerS_pi_components (hL : ReadbackLaws E R) {Γ : LCtx} {k : Nat}
    {A₁ B₁ A₂ B₂ A : Expr Nat}
    (h : LRSCoreS R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCptT k)) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :=
  piTower_pi_components hL ((piTowerS_iff k).mp h)

/-- Step down `piTowerCptT (k + 1) → piTowerCptT k` in `LRSCoreS` along convertible arguments. -/
theorem piTowerS_step (hL : ReadbackLaws E R) {Γ : LCtx} {k : Nat}
    {A₁ B₁ A₂ B₂ x y A : Expr Nat}
    (h : LRSCoreS R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCptT (k + 1)))
    (hx : HasTyT E n Γ x A₁) (hy : HasTyT E n Γ y A₁)
    (hxy : ConvT E n Γ x y A₁) :
    ∃ v, LRSCoreS R E n Γ (instantiate0 x B₁) (instantiate0 y B₂) (.sort v) (piTowerCptT k) := by
  obtain ⟨v, hv⟩ := piTower_step hL ((piTowerS_iff (k + 1)).mp h) hx hy hxy
  exact ⟨v, (piTowerS_iff k).mpr hv⟩

/-- Same-argument specialization of `piTowerS_step`. -/
theorem piTowerS_step_same (hL : ReadbackLaws E R) {Γ : LCtx} {k : Nat}
    {A₁ B₁ A₂ B₂ x A : Expr Nat}
    (h : LRSCoreS R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) A (piTowerCptT (k + 1)))
    (hx : HasTyT E n Γ x A₁) :
    ∃ v, LRSCoreS R E n Γ (instantiate0 x B₁) (instantiate0 x B₂) (.sort v) (piTowerCptT k) :=
  piTowerS_step hL h hx hx (.refl Γ x A₁ hx)

/-- **Family-Spine Readback Extraction from Landed `LRSCoreS` at a Sort Index `I`
    (`famSpineRead_of_lrSCoreS_sort`):**
    From `LRSCoreS R E n Γ M N I (.spine r args)` with `∃ l, RedR R Γ I (.sort l)` and
    `RedR R Γ M (foldApps (.const r ls) xs)` at an admitted `.inductiveM` head `r`, extracts the
    target spine `RedR R Γ N (foldApps (.const r ls') xs')`, its sort typing, `TyConvT`, `eqNList ls ls'`,
    `xs'.length = (piDomsOf m.mtype).length`, and `ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs'`! -/
theorem famSpineRead_of_lrSCoreS_sort (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx}
    {M N I : Expr Nat} (hI : ∃ l, RedR R Γ I (.sort l))
    {r : Nat} {m : CheckedMember} {ls : List Level} {xs : List (Expr Nat)} {args : List CptT}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hread : RedR R Γ M (foldApps (.const r ls) xs))
    (h : LRSCoreS R E n Γ M N I (.spine r args)) :
    ∃ (ls' : List Level) (xs' : List (Expr Nat)) (w' : Level),
      RedR R Γ N (foldApps (.const r ls') xs') ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w')) ∧
      Nonempty (TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) ∧
      eqNList ls ls' ∧
      xs'.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  rw [lrSCoreS_spine_iff] at h
  obtain ⟨m', ls₁, ls₂, xs₁, xs₂, hm', h1, h2, hn₁, _, heqN, _, _, hargs, hty⟩ := h
  have em : m = m' := Option.some.inj (hm.symm.trans hm')
  subst em
  have e := hNU Γ hread (fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs) h1 hn₁
  obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
  injection hconst with _ hls
  subst hls; subst hxs
  obtain ⟨hxs₁, hxs₂, ⟨w₁, ⟨hty₁⟩⟩, ⟨w₂, ⟨hty₂⟩⟩⟩ := hty hI hind
  obtain ⟨hlsl₁, hbel₁⟩ := NativeFamilyProjection.native_level_facts hm hty₁
  obtain ⟨_, hbel₂⟩ := NativeFamilyProjection.native_level_facts hm hty₂
  obtain ⟨htyc⟩ := tyConvT_famApp_of_convArgsT hW hm hind hlsl₁ hbel₁ hbel₂ heqN hxs₁ hargs
  exact ⟨ls₂, xs₂, w₂, h2, ⟨hty₂⟩, ⟨htyc⟩, heqN, hxs₂, hargs⟩

/-- **Family-Spine Read-Off from Landed `LRSCoreS` (`lrSCoreS_famApp_components`):**
    The family counterpart of `RcicNativeTypedModelFamSpine.lrSCoreS_pi_components`! -/
theorem lrSCoreS_famApp_components (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {m : CheckedMember} {ls ls' : List Level} {xs xs' : List (Expr Nat)}
    {u : Level} {args : List CptT}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (h : LRSCoreS R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')
      (.sort u) (.spine r args)) :
    eqNList ls ls' ∧
      xs.length = (piDomsOf m.mtype).length ∧
      xs'.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  rw [lrSCoreS_spine_iff] at h
  obtain ⟨m', ls₁, ls₂, xs₁, xs₂, hm', h1, h2, _, _, heqN, _, _, hargs, hty⟩ := h
  have em : m = m' := Option.some.inj (hm.symm.trans hm')
  subst em
  have e₁ := redR_famApp_eq hL hW hm hind h1
  have e₂ := redR_famApp_eq hL hW hm hind h2
  obtain ⟨hconst₁, hxs₁⟩ := foldApps_const_inj e₁
  obtain ⟨hconst₂, hxs₂⟩ := foldApps_const_inj e₂
  injection hconst₁ with _ hls₁
  injection hconst₂ with _ hls₂
  subst hls₁; subst hxs₁; subst hls₂; subst hxs₂
  obtain ⟨hlen₁, hlen₂, _, _⟩ := hty ⟨u, .refl _⟩ hind
  exact ⟨heqN, hlen₁, hlen₂, hargs⟩

/-- **Building `LRSCoreS` on a Saturated Family Spine (`lrSCoreS_famApp_of_components`):** -/
theorem lrSCoreS_famApp_of_components (hL : ReadbackLaws E R) (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w w' : Level} {A : Expr Nat}
    {args : List CptT}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (hty' : HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w'))
    (heqN : eqNList ls ls')
    (hlen : xs.length = (piDomsOf m.mtype).length)
    (hlen' : xs'.length = (piDomsOf m.mtype).length)
    (ha₁ : args.length ≤ xs.length) (ha₂ : args.length ≤ xs'.length)
    (hargs : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs') :
    LRSCoreS R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')
      A (.spine r args) := by
  rw [lrSCoreS_spine_iff]
  exact ⟨m, ls, ls', xs, xs', hm, .refl _, .refl _,
    fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs,
    fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs,
    heqN, ha₁, ha₂, hargs,
    fun _ _ => ⟨hlen, hlen', ⟨w, ⟨hty⟩⟩, ⟨w', ⟨hty'⟩⟩⟩⟩

/-- **Self-Relatedness of a Saturated Well-Typed Family Spine in `LRSCoreS` (`lrSCoreS_famApp_self`):**
    The family counterpart of `RcicNativeTypedModelProbe.lrSCoreS_pi_self`! -/
theorem lrSCoreS_famApp_self (hL : ReadbackLaws E R) (hW : EnvWfT E) (hpi : PiRowField E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level} {xs : List (Expr Nat)} {u : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort u))
    (hsat : xs.length = (piDomsOf m.mtype).length) :
    LRSCoreS R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls) xs)
      (.sort u) (.spine r (botVecT xs)) :=
  lrSCoreS_famApp_of_components hL hW hm hind hty hty (eqNList_refl ls) hsat hsat
    (by rw [botVecT_length]; exact Nat.le_refl _) (by rw [botVecT_length]; exact Nat.le_refl _)
    (convArgs_refl_instMtype hW hpi hΓ hm hind hsat hty)

/-- Unconditional self-relatedness of `.sort l` at `.sort` in `LRSCoreS`. -/
theorem lrSCoreS_sort_self (Γ : LCtx) (l u : Level) :
    LRSCoreS R E n Γ (.sort l) (.sort l) (.sort u) .sort := by
  rw [lrSCoreS_sort_iff]
  exact ⟨⟨u, .refl _⟩, l, l, .refl _, .refl _⟩

/-- Unconditional self-relatedness of a well-typed `.pi A B` at `.pi .bot []` in `LRSCoreS`. -/
theorem lrSCoreS_pi_self_of_hasTyT {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B : Expr Nat} {u : Level} (hPi : HasTyT E n Γ (.pi A B) (.sort u)) :
    LRSCoreS R E n Γ (.pi A B) (.pi A B) (.sort u) (.pi .bot []) := by
  obtain ⟨u₁, _, hA, _, _⟩ := hasTyTInv_pi hPi rfl
  exact lrSCoreS_pi_self hΓ hA

/-- **Relation-Seeded Single `ConvT` Link Interface Over Landed `LRSCoreS` on `FamProbeCptT E`
    (`FamProbeLinkS R E n`):**
    Generalizes `RcicNativeTypedModelProbe.LinkSeededBelow` from `.pi .bot []` to all `FamProbeCptT E`
    compacts! -/
def FamProbeLinkS (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level},
    ConvT E n Γ A B (.sort u) →
    ∀ c, FamProbeCptT E c →
      LRSCoreS R E n Γ A A (.sort u) c → LRSCoreS R E n Γ A B (.sort u) c

/-- **`TyConvT` Chaining Over Landed `LRSCoreS` Across `FamProbeCptT E` Compacts (`famProbe_chainS`):**
    Chains `TyConvT.trans A B C` at the **exact same compact `c`** using `famProbeS_right_diag` and
    `famProbeS_trans` under `ReadbackLaws E R`, `NormalUniqueR R`, and `EnvWfT E` alone — with **zero**
    `BackTransportT`, **zero** `ConvArgsSymmS` / `ConvArgsTransS`, and **zero** `PiRowField`! -/
theorem famProbe_chainS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hlink : FamProbeLinkS R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hc : TyConvT E n Γ A A')
    {c : CptT} (hpc : FamProbeCptT E c)
    (hAA : LRSCoreS R E n Γ A A (.sort u) c) :
    LRSCoreS R E n Γ A A' (.sort u) c := by
  revert u
  induction hc with
  | refl A => intro u _ hAA; exact hAA
  | of A B v hc =>
      intro u _ hAA
      have hAA_v : LRSCoreS R E n Γ A A (.sort v) c :=
        lrSCoreS_sortIdx_irrel hL hNU ⟨u, .refl _⟩ ⟨v, .refl _⟩ c hAA
      exact lrSCoreS_sortIdx_irrel hL hNU ⟨v, .refl _⟩ ⟨u, .refl _⟩ c
        (hlink hΓ hc c hpc hAA_v)
  | trans A B C c₁ _ ih₁ ih₂ =>
      intro u hA hAA
      obtain ⟨v, hB⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ c₁ hA
      have r₁ : LRSCoreS R E n Γ A B (.sort u) c := ih₁ hA hAA
      have hBB_u : LRSCoreS R E n Γ B B (.sort u) c :=
        famProbeS_right_diag hL hNU hW hΓ hpc ⟨u, .refl _⟩ r₁
      have hBB_v : LRSCoreS R E n Γ B B (.sort v) c :=
        lrSCoreS_sortIdx_irrel hL hNU ⟨u, .refl _⟩ ⟨v, .refl _⟩ c hBB_u
      have r₂ : LRSCoreS R E n Γ B C (.sort v) c := ih₂ hB hBB_v
      have r₂_u : LRSCoreS R E n Γ B C (.sort u) c :=
        lrSCoreS_sortIdx_irrel hL hNU ⟨v, .refl _⟩ ⟨u, .refl _⟩ c r₂
      exact famProbeS_trans hL hNU hW hΓ hpc ⟨u, .refl _⟩ r₁ r₂_u

/-- **`PiRowField E n` Directly from `FamProbeLinkS R E n` (`piRowField_of_famProbeLinkS`):** -/
theorem piRowField_of_famProbeLinkS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkS R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrSCoreS_pi_components hL
      (famProbe_chainS hL hNU hW hlink hΓ hPi hc .piBotNil
        (lrSCoreS_pi_self_of_hasTyT hΓ hPi))

theorem not_tyConvT_pi_sort_of_famProbeLinkS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkS R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.pi A B) (.sort l)) : False := by
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · exact Expr.noConfusion heq
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    have hLR := famProbe_chainS hL hNU hW hlink hΓ hPi hc .piBotNil
      (lrSCoreS_pi_self_of_hasTyT hΓ hPi)
    rw [LRSCoreS.eq_def] at hLR
    obtain ⟨_, _, _, _, _, _, hred', _⟩ := hLR
    exact Expr.noConfusion (redR_sort_eq hL hred')

theorem not_tyConvT_sort_pi_of_famProbeLinkS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkS R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (hc : TyConvT E n Γ (.sort l) (.pi A B)) : False := by
  have hLR := famProbe_chainS hL hNU hW hlink hΓ (.sort Γ l) hc .sort
    (lrSCoreS_sort_self Γ l (.succ l))
  rw [LRSCoreS.eq_def] at hLR
  obtain ⟨_, _, _, _, hred'⟩ := hLR
  exact Expr.noConfusion (redR_pi_eq hL hred')

/-- Family-spine saturation from `FamProbeLinkS R E n` (`famApp_saturated_of_famProbeLinkS`). -/
theorem famApp_saturated_of_famProbeLinkS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkS R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (_hind : m.mclass = .inductiveM)
    {doms : List (Expr Nat)} {u : Level}
    (hpi : instantiateLevels ls m.mtype = policyPi doms (.sort u))
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = doms.length := by
  have hprow : PiRowField E n := piRowField_of_famProbeLinkS hL hNU hW hlink
  rcases Nat.lt_trichotomy xs.length doms.length with hlt | heq | hgt
  · exfalso
    have hne : doms.drop xs.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hlt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hpi' : instantiateLevels ls m.mtype =
        policyPi (doms.take xs.length) (policyPi (doms.drop xs.length) (.sort u)) := by
      rw [← List.take_append_drop xs.length doms] at hpi
      rw [hpi, policyPi_append]
    have hlen' : (doms.take xs.length).length = xs.length := by
      rw [List.length_take]
      first
        | exact Nat.min_eq_right (Nat.le_of_lt hlt)
        | exact Nat.min_eq_left (Nat.le_of_lt hlt)
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi' xs hlen' hty
    rw [hrest] at hconv
    simp only [policyPi] at hconv
    rw [instPrefix_pi] at hconv
    exact not_tyConvT_pi_sort_of_famProbeLinkS hL hNU hW hlink hΓ hconv
  · exact heq
  · exfalso
    have hne : xs.drop doms.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hgt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨_, _, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hsplit : foldApps (.const r ls) xs =
        foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
      calc foldApps (.const r ls) xs
          = foldApps (.const r ls) (xs.take doms.length ++ xs.drop doms.length) := by
              rw [List.take_append_drop]
        _ = foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
            foldApps_append _ _ _
    obtain ⟨_, _, ⟨hf⟩⟩ := hasTyT_foldApps_prefix_pi
      (f := foldApps (.const r ls) (xs.take doms.length))
      (hsplit ▸ hty) hrest
    have hlen' : doms.length = (xs.take doms.length).length := by
      rw [List.length_take]
      first
        | exact (Nat.min_eq_right (Nat.le_of_lt hgt)).symm
        | exact (Nat.min_eq_left (Nat.le_of_lt hgt)).symm
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows hW hprow hΓ hm hpi
      (xs.take doms.length) hlen' hf
    rw [instPrefix_sort] at hconv
    exact not_tyConvT_sort_pi_of_famProbeLinkS hL hNU hW hlink hΓ hconv

theorem famApp_length_eq_piDomsOf_of_famProbeLinkS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkS R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = (piDomsOf m.mtype).length := by
  have hlen := famApp_saturated_of_famProbeLinkS hL hNU hW hlink hΓ hm hind
    (instMtype_policyPi_of_inductiveM hW hm hind ls) hty
  rwa [List.length_map] at hlen

/-- **`FamAppRowLink E n` Directly from `FamProbeLinkS R E n` (`famAppRow_of_famProbeLinkS`):**
    Requires **only** `ReadbackLaws E R`, `NormalUniqueR R`, `EnvWfT E`, and `FamProbeLinkS R E n` —
    with **zero** `BackTransportT` and **zero** `ConvArgsSymmS` / `ConvArgsTransS`! -/
theorem famAppRow_of_famProbeLinkS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkS R E n) :
    FamAppRowLink E n := by
  intro Γ hΓ r m ls ls' xs xs' _ hm hind hty hc
  have hprow : PiRowField E n := piRowField_of_famProbeLinkS hL hNU hW hlink
  have hsat : xs.length = (piDomsOf m.mtype).length :=
    famApp_length_eq_piDomsOf_of_famProbeLinkS hL hNU hW hlink hΓ hm hind hty
  have h := lrSCoreS_famApp_components hL hW hm hind
    (famProbe_chainS hL hNU hW hlink hΓ hty hc
      (famProbeCptT_spine_botVecT hm hind xs)
      (lrSCoreS_famApp_self hL hW hprow hΓ hm hind hty hsat))
  exact ⟨h.1, h.2.1.trans h.2.2.1.symm, h.2.2.2⟩

/-- **`FamRelevantSlotConv E n` (#7525) Directly from `FamProbeLinkS R E n`
    (`famRelevantSlotConv_of_famProbeLinkS`):** -/
theorem famRelevantSlotConv_of_famProbeLinkS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hlink : FamProbeLinkS R E n) :
    FamRelevantSlotConv E n := by
  intro Γ hΓ r m ls ls' xs xs' w hm hind hty hc
  exact relevantSlotConv_of_convArgsT hW hm hind
    (famAppRow_of_famProbeLinkS hL hNU hW hlink hΓ hm hind hty hc).2.2

/-- **`TypedRowsWf E n` Directly from `FamProbeLinkS R E n` + `AllBelowScoped`
    (`typedRowsWf_of_allBelowScoped_famProbeLinkS`):** -/
theorem typedRowsWf_of_allBelowScoped_famProbeLinkS (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hlink : FamProbeLinkS R E n) :
    TypedRowsWf E n where
  sortRow := sortRow_of_allBelowScoped_build hW hBel
  piRow := piRowField_of_famProbeLinkS hL hNU hW hlink
  famAppRow := famAppRow_of_famProbeLinkS hL hNU hW hlink

/-- **3-Observation Transport Bridge from Landed `LRSCoreS` at a Sort Index `I`
    (`famObsTransport_of_lrSCoreS_probes`):** -/
theorem famObsTransport_of_lrSCoreS_probes (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} {M N I : Expr Nat}
    (hI : ∃ l, RedR R Γ I (.sort l))
    (hreal : FamProbeRealizedAtT R E n Γ M)
    (hrel : ∀ c, FamProbeCptT E c → ApproxT E (ctxEnvT E Γ) M c → LRSCoreS R E n Γ M N I c) :
    FamObsTransport R E n Γ M N := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, hread⟩
    have h := hrel (sortCode u) (famProbeCptT_sortCode u) (hreal.1.1 u hread)
    obtain ⟨_, _, v, _, hN⟩ := (lrSCoreS_sortCode_iff u).mp h
    exact ⟨v, hN⟩
  · intro A B hread hΓA
    have h := hrel (.pi .bot []) .piBotNil (hreal.1.2 A B hread hΓA)
    rw [LRSCoreS.eq_def] at h
    obtain ⟨_, A₁, B₁, A₂, B₂, h1, h2, _, hdom, hcod, _⟩ := h
    obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hread h1
    subst eA; subst eB
    exact ⟨A₂, B₂, h2, hdom, hcod⟩
  · intro r m ls xs w hm hind hread hty hlen hargs
    exact famSpineRead_of_lrSCoreS_sort hL hNU hW hI hm hind hread
      (hrel (.spine r (botVecT xs)) (famProbeCptT_spine_botVecT hm hind xs)
        (hreal.2 r m ls xs w hm hind hread hty hlen hargs))

/-- **3-Observation Equivalence Bridge from Landed `LRSCoreS` at a Sort Index `I`
    (`famObsEquiv_of_lrSCoreS_probes`):**
    Uses `famProbeS_symm` to obtain both directions of `FamObsEquiv R E n Γ M N` from a single
    forward `LRSCoreS R E n Γ M N I c` hypothesis on `FamProbeCptT E` compacts (with **zero**
    `ConvArgsSymmS`)! -/
theorem famObsEquiv_of_lrSCoreS_probes (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M N I : Expr Nat}
    (hI : ∃ l, RedR R Γ I (.sort l))
    (hrealM : FamProbeRealizedAtT R E n Γ M)
    (hrealN : FamProbeRealizedAtT R E n Γ N)
    (hrel : ∀ c, FamProbeCptT E c →
      (ApproxT E (ctxEnvT E Γ) M c ∨ ApproxT E (ctxEnvT E Γ) N c) →
      LRSCoreS R E n Γ M N I c) :
    FamObsEquiv R E n Γ M N :=
  ⟨famObsTransport_of_lrSCoreS_probes hL hNU hW hI hrealM
      (fun c hc hM => hrel c hc (Or.inl hM)),
   famObsTransport_of_lrSCoreS_probes hL hNU hW hI hrealN
      (fun c hc hN => famProbeS_symm hW hΓ hc hI (hrel c hc (Or.inr hN)))⟩


/-! #### §13 Part B — Unconditional Discharge of `RelSubstIdT` at `EnvT.bot` and `ctxEnvT E Γ` from
    `FundamentalSAtT`, Refutation of Unrestricted `TypingLemmaEnvT`, and Direct `PiRowField` /
    `FamAppRowLink` / `FamRelevantSlotConv` / `TypedRowsWf` Consequences -/

/-- A substitution `σ : SubstT` from `Γ` into `Δ` steps each let-bound variable `i` (`lookupValue Γ i = some v`)
    in one readback step `R Δ (σ i) (substT σ v)`. -/
def ZetaStepSubst (R : Readback) (Δ : LCtx) (σ : SubstT) (Γ : LCtx) : Prop :=
  ∀ (i : Nat) (v : Expr Nat), lookupValue Γ i = some v → R Δ (σ i) (substT σ v)

/-- Under local let-unfolding (`∀ Γ i v, lookupValue Γ i = some v → R Γ (.bvar i) v`, satisfied by
    `.zetaLocal` in `WhStepCtx E`, `WhStepK E n`, `WhStepCK E n`, and `WhStepRecKCanon E`),
    `SubstT.id` satisfies `ZetaStepSubst R Γ SubstT.id Γ` unconditionally. -/
theorem zetaStepSubst_id
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (Γ : LCtx) :
    ZetaStepSubst R Γ SubstT.id Γ := by
  intro i v hv
  rw [substT_id]
  exact hZL Γ hv

/-- Shifting a `ZetaStepSubst R Δ σ (d :: Γ)` substitution by `SubstT.shiftAt 0` preserves
    `ZetaStepSubst R Δ (SubstT.shiftAt 0 σ) Γ`. -/
theorem zetaStepSubst_shiftAt_zero {Δ : LCtx} {σ : SubstT} {d : LocalDecl} {Γ : LCtx}
    (hZ : ZetaStepSubst R Δ σ (d :: Γ)) :
    ZetaStepSubst R Δ (SubstT.shiftAt 0 σ) Γ := by
  intro i v hv
  have hv' : lookupValue (d :: Γ) (i + 1) = some (lift 0 1 v) := by
    rw [lookupValue_cons_succ, hv]; rfl
  have hstep := hZ (i + 1) (lift 0 1 v) hv'
  have sh : SubstT.shiftAt 0 σ i = σ (i + 1) := by simp [SubstT.shiftAt]
  rw [sh, ← substT_lift 0 σ v]
  exact hstep

/-- Shifting a `TypedSubstT E n Δ σ (d :: Γ)` substitution by `SubstT.shiftAt 0` preserves
    `TypedSubstT E n Δ (SubstT.shiftAt 0 σ) Γ`. -/
theorem typedSubstT_shiftAt_zero {Δ : LCtx} {σ : SubstT} {d : LocalDecl} {Γ : LCtx}
    (hT : TypedSubstT E n Δ σ (d :: Γ)) :
    TypedSubstT E n Δ (SubstT.shiftAt 0 σ) Γ := by
  have e : ∀ (A : Expr Nat), substT (SubstT.shiftAt 0 σ) A = substT σ (lift 0 1 A) :=
    fun A => (substT_lift 0 σ A).symm
  have sh : ∀ (i : Nat), SubstT.shiftAt 0 σ i = σ (i + 1) := fun i => by
    simp [SubstT.shiftAt]
  refine ⟨fun i A hA => ?_, fun i v hv => ?_⟩
  · have hA' : lookupType (d :: Γ) (i + 1) = some (lift 0 1 A) := by
      rw [lookupType_cons_succ, hA]; rfl
    obtain ⟨ht⟩ := hT.1 (i + 1) (lift 0 1 A) hA'
    rw [sh, e]
    exact ⟨ht⟩
  · have hv' : lookupValue (d :: Γ) (i + 1) = some (lift 0 1 v) := by
      rw [lookupValue_cons_succ, hv]; rfl
    obtain ⟨A', hA', ⟨hc⟩⟩ := hT.2 (i + 1) (lift 0 1 v) hv'
    rw [lookupType_cons_succ] at hA'
    cases hA₀ : lookupType Γ i with
    | none => rw [hA₀] at hA'; exact Option.noConfusion hA'
    | some A₀ =>
        rw [hA₀] at hA'; injection hA' with hA'; subst hA'
        exact ⟨A₀, rfl, ⟨by rw [sh, e, e]; exact hc⟩⟩

/-- Reflexivity of `ConvSubstT E n Δ σ σ Γ` from `TypedSubstT E n Δ σ Γ`. -/
theorem convSubstT_refl_of_typedSubstT {Δ : LCtx} {σ : SubstT} {Γ : LCtx}
    (hT : TypedSubstT E n Δ σ Γ) : ConvSubstT E n Δ σ σ Γ :=
  fun i A hA => let ⟨ht⟩ := hT.1 i A hA; ⟨.refl Δ (σ i) (substT σ A) ht⟩

/-- Weakening `FundTyAt M R n Γ e A` by `lift 0 1` under any binder `d : LocalDecl` via reindexing
    (`relSubstAtT_tail`), generalizing `RcicNativeTypedModelFundStrong.tyValidAt_lift`. -/
theorem fundTyAt_lift {M : CtxModelT E} (hM : CtxModelTLaws' M) {Γ : LCtx} {e A : Expr Nat}
    (d : LocalDecl) (hF : FundTyAt M R n Γ e A) :
    FundTyAt M R n (d :: Γ) (lift 0 1 e) (lift 0 1 A) := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have hS' := relSubstAtT_tail hM hS
  have hc' : M.Ap (EnvT.tail ρ) e c ∨ M.Ap (EnvT.tail ρ') e c := by
    rcases hc with hc | hc
    · exact Or.inl (hM.lift0_elim (S := ρ 0) (ρ := EnvT.tail ρ) (by rw [EnvT.cons_tail]; exact hc))
    · exact Or.inr (hM.lift0_elim (S := ρ' 0) (ρ := EnvT.tail ρ') (by rw [EnvT.cons_tail]; exact hc))
  have := hF hΔ hS' c hc'
  rw [substT_lift, substT_lift, substT_lift]
  exact this

/-- **Related Substitution at `EnvT.bot` Along Any `TypedSubstT` + `ZetaStepSubst` Substitution
    (`relSubstAtT_bot_of_zetaStep`):**
    Proved by induction on `hΓ : CtxWfT E n Γ`: at each `.letBinding A₀ v₀` binder, the tail
    substitution `SubstT.shiftAt 0 σ` already satisfies `RelSubstAtT` on `Γ₀` by the induction
    hypothesis, so `hFund` relates `substT σ (lift 0 1 v₀)` to itself and `lrSCoreS_expand`
    absorbs `R Δ (σ 0) (substT σ (lift 0 1 v₀))`! -/
theorem relSubstAtT_bot_of_zetaStep (hL : ReadbackLaws E R) {M : CtxModelT E} (hM : CtxModelTLaws M)
    (hFund : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {e A : Expr Nat}, HasTyT E n Γ e A → FundTyAt M R n Γ e A) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ →
      ∀ {Δ : LCtx}, CtxWfT E n Δ →
      ∀ {σ : SubstT}, TypedSubstT E n Δ σ Γ → ZetaStepSubst R Δ σ Γ →
      RelSubstAtT M R n Δ EnvT.bot EnvT.bot σ σ Γ
  | [], .nil, Δ, _, σ, hT, _ =>
      ⟨hT, hT, convSubstT_refl_of_typedSubstT hT,
        fun _ _ h => by simp [lookupType] at h,
        fun _ _ _ hv => by simp [lookupValue] at hv⟩
  | _ :: _, .assumption Γ₀ A₀ u₀ hΓ₀ _, Δ, hΔ, σ, hT, hZ => by
      have ih := relSubstAtT_bot_of_zetaStep hL hM hFund hΓ₀ hΔ
        (typedSubstT_shiftAt_zero hT) (zetaStepSubst_shiftAt_zero hZ)
      have e : ∀ (A : Expr Nat), substT (SubstT.shiftAt 0 σ) A = substT σ (lift 0 1 A) :=
        fun A => (substT_lift 0 σ A).symm
      have sh : ∀ (i : Nat), SubstT.shiftAt 0 σ i = σ (i + 1) := fun i => by
        simp [SubstT.shiftAt]
      refine ⟨hT, hT, convSubstT_refl_of_typedSubstT hT, ?_, ?_⟩
      · intro i A _ c hc
        have hbot : c = .bot := hc.elim id id
        subst hbot
        exact ⟨lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _,
          lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _⟩
      · intro i v A hv hA c hc
        cases i with
        | zero => simp [lookupValue] at hv
        | succ i =>
            rw [lookupValue_cons_succ] at hv
            rw [lookupType_cons_succ] at hA
            cases hv₀ : lookupValue Γ₀ i with
            | none => rw [hv₀] at hv; exact Option.noConfusion hv
            | some v₀ =>
                cases hA₀ : lookupType Γ₀ i with
                | none => rw [hA₀] at hA; exact Option.noConfusion hA
                | some A₀' =>
                    rw [hv₀] at hv; rw [hA₀] at hA
                    injection hv with hv; injection hA with hA
                    subst hv; subst hA
                    have hc₀ : EnvT.bot i c ∨ EnvT.bot i c ∨
                        M.Ap EnvT.bot v₀ c ∨ M.Ap EnvT.bot v₀ c := by
                      rcases hc with h | h | h | h
                      · exact Or.inl h
                      · exact Or.inr (Or.inl h)
                      · exact Or.inr (Or.inr (Or.inl
                          (hM.lift0_elim (S := EnvT.bot 0) (ρ := EnvT.tail EnvT.bot)
                            (by rw [EnvT.cons_tail]; exact h))))
                      · exact Or.inr (Or.inr (Or.inr
                          (hM.lift0_elim (S := EnvT.bot 0) (ρ := EnvT.tail EnvT.bot)
                            (by rw [EnvT.cons_tail]; exact h))))
                    have hres := ih.2.2.2.2 i v₀ A₀' hv₀ hA₀ c hc₀
                    rw [sh, e v₀, e A₀'] at hres
                    exact hres
  | _ :: _, .letBinding Γ₀ A₀ u₀ v₀ hΓ₀ _ hv₀, Δ, hΔ, σ, hT, hZ => by
      have ih := relSubstAtT_bot_of_zetaStep hL hM hFund hΓ₀ hΔ
        (typedSubstT_shiftAt_zero hT) (zetaStepSubst_shiftAt_zero hZ)
      have e : ∀ (A : Expr Nat), substT (SubstT.shiftAt 0 σ) A = substT σ (lift 0 1 A) :=
        fun A => (substT_lift 0 σ A).symm
      have sh : ∀ (i : Nat), SubstT.shiftAt 0 σ i = σ (i + 1) := fun i => by
        simp [SubstT.shiftAt]
      refine ⟨hT, hT, convSubstT_refl_of_typedSubstT hT, ?_, ?_⟩
      · intro i A _ c hc
        have hbot : c = .bot := hc.elim id id
        subst hbot
        exact ⟨lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _,
          lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _⟩
      · intro i v A hv hA c hc
        cases i with
        | zero =>
            have hv0 : lookupValue (.letBinding A₀ v₀ :: Γ₀) 0 = some (lift 0 1 v₀) := rfl
            have hA0 : lookupType (.letBinding A₀ v₀ :: Γ₀) 0 = some (lift 0 1 A₀) := rfl
            rw [hv0] at hv; rw [hA0] at hA
            injection hv with hv; injection hA with hA
            subst hv; subst hA
            have hgoal : LRSCoreS R E n Δ (σ 0) (substT σ (lift 0 1 v₀))
                (substT σ (lift 0 1 A₀)) c := by
              rcases hc with hbot | hbot | hap | hap
              · have hb : c = .bot := hbot; subst hb; exact lrSCoreS_bot _ _ _ _
              · have hb : c = .bot := hbot; subst hb; exact lrSCoreS_bot _ _ _ _
              · have hap₀ : M.Ap EnvT.bot v₀ c :=
                  hM.lift0_elim (S := EnvT.bot 0) (ρ := EnvT.tail EnvT.bot)
                    (by rw [EnvT.cons_tail]; exact hap)
                have hvv := hFund hΓ₀ hv₀ hΔ ih c (Or.inl hap₀)
                rw [e v₀, e A₀] at hvv
                exact lrSCoreS_expand hL (hZ 0 (lift 0 1 v₀) rfl) c hvv
              · have hap₀ : M.Ap EnvT.bot v₀ c :=
                  hM.lift0_elim (S := EnvT.bot 0) (ρ := EnvT.tail EnvT.bot)
                    (by rw [EnvT.cons_tail]; exact hap)
                have hvv := hFund hΓ₀ hv₀ hΔ ih c (Or.inl hap₀)
                rw [e v₀, e A₀] at hvv
                exact lrSCoreS_expand hL (hZ 0 (lift 0 1 v₀) rfl) c hvv
            exact ⟨hgoal, hgoal, hgoal, hgoal⟩
        | succ i =>
            rw [lookupValue_cons_succ] at hv
            rw [lookupType_cons_succ] at hA
            cases hv₁ : lookupValue Γ₀ i with
            | none => rw [hv₁] at hv; exact Option.noConfusion hv
            | some v₁ =>
                cases hA₁ : lookupType Γ₀ i with
                | none => rw [hA₁] at hA; exact Option.noConfusion hA
                | some A₁ =>
                    rw [hv₁] at hv; rw [hA₁] at hA
                    injection hv with hv; injection hA with hA
                    subst hv; subst hA
                    have hc₀ : EnvT.bot i c ∨ EnvT.bot i c ∨
                        M.Ap EnvT.bot v₁ c ∨ M.Ap EnvT.bot v₁ c := by
                      rcases hc with h | h | h | h
                      · exact Or.inl h
                      · exact Or.inr (Or.inl h)
                      · exact Or.inr (Or.inr (Or.inl
                          (hM.lift0_elim (S := EnvT.bot 0) (ρ := EnvT.tail EnvT.bot)
                            (by rw [EnvT.cons_tail]; exact h))))
                      · exact Or.inr (Or.inr (Or.inr
                          (hM.lift0_elim (S := EnvT.bot 0) (ρ := EnvT.tail EnvT.bot)
                            (by rw [EnvT.cons_tail]; exact h))))
                    have hres := ih.2.2.2.2 i v₁ A₁ hv₁ hA₁ c hc₀
                    rw [sh, e v₁, e A₁] at hres
                    exact hres

/-- **Unconditional Discharge of `RelSubstIdT M R n Γ EnvT.bot` from `FundamentalSAtT`
    (`relSubstIdT_bot_of_fundamentalSAtT`):**
    Holds for **any** `M : CtxModelT E` with `CtxModelTLaws M` and **any** well-formed context `Γ`
    (including contexts with `letBinding`s)! -/
theorem relSubstIdT_bot_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    {M : CtxModelT E} (hM : CtxModelTLaws M) (hFund : FundamentalSAtT M R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    RelSubstIdT M R n Γ EnvT.bot :=
  relSubstAtT_bot_of_zetaStep hL hM hFund.1 hΓ hΓ
    (typedSubstT_id (envClosed_of_envWfT hW) hΓ) (zetaStepSubst_id hZL Γ)

/-- **Unconditional Discharge of `RelSubstTypedAtT` at `EnvT.bot` from `FundamentalSAtT`
    (`relSubstTypedAtT_bot_id_of_fundamentalSAtT`):**
    Combines `relSubstIdT_bot_of_fundamentalSAtT` with `envTypedAtT_bot` to inhabit `#7740`'s full
    typed substitution package `RelSubstTypedAtT` (`RcicNativeTypedModelProbe`) at `EnvT.bot` for
    **every** well-formed context `Γ`! -/
theorem relSubstTypedAtT_bot_id_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    RelSubstTypedAtT (ctxModelT_approxT E) R n Γ EnvT.bot EnvT.bot SubstT.id SubstT.id Γ :=
  ⟨relSubstIdT_bot_of_fundamentalSAtT hL hZL hW (ctxModelTLaws_approxT E) hFund hΓ,
    envTypedAtT_bot Γ, envTypedAtT_bot Γ⟩

/-- **Related Substitution at `ctxEnvT E Γ` Along Any `TypedSubstT` + `ZetaStepSubst` Substitution
    (`relSubstAtT_ctxEnvT_of_zetaStep`):**
    Proved by induction on `hΓ : CtxWfT E n Γ`: at each `.letBinding A₀ v₀` binder, `ctxEnvT` assigns
    `ApproxT E (ctxEnvT E Γ₀) v₀` to `.bvar 0`, so `hFund` + `lrSCoreS_expand` proves Field 5 at `i = 0`
    and `lrSCoreS_expand` + `lrSCoreS_expand_right` proves Field 4 at `i = 0` — with **zero**
    `ConvArgsSymmS` / `ConvArgsTransS`! -/
theorem relSubstAtT_ctxEnvT_of_zetaStep (hL : ReadbackLaws E R)
    (hFund : ∀ {Γ : LCtx}, CtxWfT E n Γ →
      ∀ {e A : Expr Nat}, HasTyT E n Γ e A → FundTyAt (ctxModelT_approxT E) R n Γ e A) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ →
      ∀ {Δ : LCtx}, CtxWfT E n Δ →
      ∀ {σ : SubstT}, TypedSubstT E n Δ σ Γ → ZetaStepSubst R Δ σ Γ →
      RelSubstAtT (ctxModelT_approxT E) R n Δ (ctxEnvT E Γ) (ctxEnvT E Γ) σ σ Γ
  | [], .nil, Δ, _, σ, hT, _ =>
      ⟨hT, hT, convSubstT_refl_of_typedSubstT hT,
        fun _ _ h => by simp [lookupType] at h,
        fun _ _ _ hv => by simp [lookupValue] at hv⟩
  | _ :: _, .assumption Γ₀ A₀ u₀ hΓ₀ _, Δ, hΔ, σ, hT, hZ => by
      have ih := relSubstAtT_ctxEnvT_of_zetaStep hL hFund hΓ₀ hΔ
        (typedSubstT_shiftAt_zero hT) (zetaStepSubst_shiftAt_zero hZ)
      have e : ∀ (A : Expr Nat), substT (SubstT.shiftAt 0 σ) A = substT σ (lift 0 1 A) :=
        fun A => (substT_lift 0 σ A).symm
      have sh : ∀ (i : Nat), SubstT.shiftAt 0 σ i = σ (i + 1) := fun i => by
        simp [SubstT.shiftAt]
      refine ⟨hT, hT, convSubstT_refl_of_typedSubstT hT, ?_, ?_⟩
      · intro i A hA c hc
        cases i with
        | zero =>
            have hbot : c = .bot := hc.elim id id
            subst hbot
            exact ⟨lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _,
              lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _⟩
        | succ i =>
            rw [lookupType_cons_succ] at hA
            cases hA₀ : lookupType Γ₀ i with
            | none => rw [hA₀] at hA; exact Option.noConfusion hA
            | some A₀' =>
                rw [hA₀] at hA; injection hA with hA; subst hA
                have hres := ih.2.2.2.1 i A₀' hA₀ c hc
                rw [sh, e A₀'] at hres
                exact hres
      · intro i v A hv hA c hc
        cases i with
        | zero => simp [lookupValue] at hv
        | succ i =>
            rw [lookupValue_cons_succ] at hv
            rw [lookupType_cons_succ] at hA
            cases hv₀ : lookupValue Γ₀ i with
            | none => rw [hv₀] at hv; exact Option.noConfusion hv
            | some v₀ =>
                cases hA₀ : lookupType Γ₀ i with
                | none => rw [hA₀] at hA; exact Option.noConfusion hA
                | some A₀' =>
                    rw [hv₀] at hv; rw [hA₀] at hA
                    injection hv with hv; injection hA with hA
                    subst hv; subst hA
                    have hc₀ : ctxEnvT E Γ₀ i c ∨ ctxEnvT E Γ₀ i c ∨
                        ApproxT E (ctxEnvT E Γ₀) v₀ c ∨ ApproxT E (ctxEnvT E Γ₀) v₀ c := by
                      rcases hc with h | h | h | h
                      · exact Or.inl h
                      · exact Or.inr (Or.inl h)
                      · exact Or.inr (Or.inr (Or.inl ((approxT_cons_lift0_iff _ _ _ _ _).mp h)))
                      · exact Or.inr (Or.inr (Or.inr ((approxT_cons_lift0_iff _ _ _ _ _).mp h)))
                    have hres := ih.2.2.2.2 i v₀ A₀' hv₀ hA₀ c hc₀
                    rw [sh, e v₀, e A₀'] at hres
                    exact hres
  | _ :: _, .letBinding Γ₀ A₀ u₀ v₀ hΓ₀ _ hv₀, Δ, hΔ, σ, hT, hZ => by
      have ih := relSubstAtT_ctxEnvT_of_zetaStep hL hFund hΓ₀ hΔ
        (typedSubstT_shiftAt_zero hT) (zetaStepSubst_shiftAt_zero hZ)
      have e : ∀ (A : Expr Nat), substT (SubstT.shiftAt 0 σ) A = substT σ (lift 0 1 A) :=
        fun A => (substT_lift 0 σ A).symm
      have sh : ∀ (i : Nat), SubstT.shiftAt 0 σ i = σ (i + 1) := fun i => by
        simp [SubstT.shiftAt]
      refine ⟨hT, hT, convSubstT_refl_of_typedSubstT hT, ?_, ?_⟩
      · intro i A hA c hc
        cases i with
        | zero =>
            have hA0 : lookupType (.letBinding A₀ v₀ :: Γ₀) 0 = some (lift 0 1 A₀) := rfl
            rw [hA0] at hA; injection hA with hA; subst hA
            have hap₀ : ApproxT E (ctxEnvT E Γ₀) v₀ c := hc.elim id id
            have hvv := hFund hΓ₀ hv₀ hΔ ih c (Or.inl hap₀)
            rw [e v₀, e A₀] at hvv
            have hstep := hZ 0 (lift 0 1 v₀) rfl
            have hgoal : LRSCoreS R E n Δ (σ 0) (σ 0) (substT σ (lift 0 1 A₀)) c :=
              lrSCoreS_expand_right hL hstep c (lrSCoreS_expand hL hstep c hvv)
            exact ⟨hgoal, hgoal, hgoal, hgoal⟩
        | succ i =>
            rw [lookupType_cons_succ] at hA
            cases hA₀ : lookupType Γ₀ i with
            | none => rw [hA₀] at hA; exact Option.noConfusion hA
            | some A₀' =>
                rw [hA₀] at hA; injection hA with hA; subst hA
                have hres := ih.2.2.2.1 i A₀' hA₀ c hc
                rw [sh, e A₀'] at hres
                exact hres
      · intro i v A hv hA c hc
        cases i with
        | zero =>
            have hv0 : lookupValue (.letBinding A₀ v₀ :: Γ₀) 0 = some (lift 0 1 v₀) := rfl
            have hA0 : lookupType (.letBinding A₀ v₀ :: Γ₀) 0 = some (lift 0 1 A₀) := rfl
            rw [hv0] at hv; rw [hA0] at hA
            injection hv with hv; injection hA with hA
            subst hv; subst hA
            have hap₀ : ApproxT E (ctxEnvT E Γ₀) v₀ c := by
              rcases hc with h | h | h | h
              · exact h
              · exact h
              · exact (approxT_cons_lift0_iff _ _ _ _ _).mp h
              · exact (approxT_cons_lift0_iff _ _ _ _ _).mp h
            have hvv := hFund hΓ₀ hv₀ hΔ ih c (Or.inl hap₀)
            rw [e v₀, e A₀] at hvv
            have hgoal : LRSCoreS R E n Δ (σ 0) (substT σ (lift 0 1 v₀))
                (substT σ (lift 0 1 A₀)) c :=
              lrSCoreS_expand hL (hZ 0 (lift 0 1 v₀) rfl) c hvv
            exact ⟨hgoal, hgoal, hgoal, hgoal⟩
        | succ i =>
            rw [lookupValue_cons_succ] at hv
            rw [lookupType_cons_succ] at hA
            cases hv₁ : lookupValue Γ₀ i with
            | none => rw [hv₁] at hv; exact Option.noConfusion hv
            | some v₁ =>
                cases hA₁ : lookupType Γ₀ i with
                | none => rw [hA₁] at hA; exact Option.noConfusion hA
                | some A₁ =>
                    rw [hv₁] at hv; rw [hA₁] at hA
                    injection hv with hv; injection hA with hA
                    subst hv; subst hA
                    have hc₀ : ctxEnvT E Γ₀ i c ∨ ctxEnvT E Γ₀ i c ∨
                        ApproxT E (ctxEnvT E Γ₀) v₁ c ∨ ApproxT E (ctxEnvT E Γ₀) v₁ c := by
                      rcases hc with h | h | h | h
                      · exact Or.inl h
                      · exact Or.inr (Or.inl h)
                      · exact Or.inr (Or.inr (Or.inl ((approxT_cons_lift0_iff _ _ _ _ _).mp h)))
                      · exact Or.inr (Or.inr (Or.inr ((approxT_cons_lift0_iff _ _ _ _ _).mp h)))
                    have hres := ih.2.2.2.2 i v₁ A₁ hv₁ hA₁ c hc₀
                    rw [sh, e v₁, e A₁] at hres
                    exact hres

/-- **Unconditional Discharge of `RelSubstIdT (ctxModelT_approxT E) R n Γ (ctxEnvT E Γ)` from
    `FundamentalSAtT` (`relSubstIdT_ctxEnvT_of_fundamentalSAtT`):**
    Discharges `#7740`'s `RelSubstIdT` (`RcicNativeTypedModelProbe`) at `ctxEnvT E Γ` for **every**
    well-formed context `Γ`! -/
theorem relSubstIdT_ctxEnvT_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    RelSubstIdT (ctxModelT_approxT E) R n Γ (ctxEnvT E Γ) :=
  relSubstAtT_ctxEnvT_of_zetaStep hL hFund.1 hΓ hΓ
    (typedSubstT_id (envClosed_of_envWfT hW) hΓ) (zetaStepSubst_id hZL Γ)

/-- **`RelSubstIdT`-Free Identity-Substitution Evaluation of `FundamentalSAtT` at `EnvT.bot`
    (`fundConvAt_bot_of_fundamentalSAtT`):**
    Eliminates the `hId : RelSubstIdT` premise from `RcicNativeTypedModelProbe.fundConvAt_ctx_of_id`! -/
theorem fundConvAt_bot_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    {M : CtxModelT E} (hM : CtxModelTLaws M) (hFund : FundamentalSAtT M R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b A : Expr Nat}
    (h : ConvT E n Γ a b A) (c : CptT)
    (hc : M.Ap EnvT.bot a c ∨ M.Ap EnvT.bot b c) :
    LRSCoreS R E n Γ a b A c :=
  fundConvAt_ctx_of_id hΓ (relSubstIdT_bot_of_fundamentalSAtT hL hZL hW hM hFund hΓ)
    (hFund.2 hΓ h) c hc

/-- `RelSubstIdT`-free typing evaluation of `FundamentalSAtT` at `EnvT.bot` (`fundTyAt_bot_of_fundamentalSAtT`). -/
theorem fundTyAt_bot_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    {M : CtxModelT E} (hM : CtxModelTLaws M) (hFund : FundamentalSAtT M R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A : Expr Nat}
    (h : HasTyT E n Γ e A) (c : CptT)
    (hc : M.Ap EnvT.bot e c) :
    LRSCoreS R E n Γ e e A c :=
  fundTyAt_ctx_of_id hΓ (relSubstIdT_bot_of_fundamentalSAtT hL hZL hW hM hFund hΓ)
    (hFund.1 hΓ h) c hc

/-- **`RelSubstIdT`-Free Identity-Substitution Evaluation of `FundamentalSAtT` at `ctxEnvT E Γ`
    (`fundConvAt_ctxEnvT_of_fundamentalSAtT`):**
    Eliminates the `hId : RelSubstIdT` premise from `RcicNativeTypedModelProbe.fundConvAt_ctx_of_id`
    at `ctxEnvT E Γ`! -/
theorem fundConvAt_ctxEnvT_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b A : Expr Nat}
    (h : ConvT E n Γ a b A) (c : CptT)
    (hc : ApproxT E (ctxEnvT E Γ) a c ∨ ApproxT E (ctxEnvT E Γ) b c) :
    LRSCoreS R E n Γ a b A c :=
  fundConvAt_ctx_of_id hΓ (relSubstIdT_ctxEnvT_of_fundamentalSAtT hL hZL hW hFund hΓ)
    (hFund.2 hΓ h) c hc

/-- `RelSubstIdT`-free typing evaluation of `FundamentalSAtT` at `ctxEnvT E Γ`
    (`fundTyAt_ctxEnvT_of_fundamentalSAtT`). -/
theorem fundTyAt_ctxEnvT_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A : Expr Nat}
    (h : HasTyT E n Γ e A) (c : CptT)
    (hc : ApproxT E (ctxEnvT E Γ) e c) :
    LRSCoreS R E n Γ e e A c :=
  fundTyAt_ctx_of_id hΓ (relSubstIdT_ctxEnvT_of_fundamentalSAtT hL hZL hW hFund hΓ)
    (hFund.1 hΓ h) c hc

/-- **Direct Single-Sort `ConvT` Π-Injectivity from `FundamentalSAtT` Alone
    (`convT_pi_inj_of_fundamentalSAtT`):**
    Evaluates `fundConvAt_bot_of_fundamentalSAtT` at `EnvT.bot` and `.pi .bot []` (`approxT_pi_bot_nil`)
    — requiring **zero** `RelSubstIdT` and **zero** `FamTypedProbeRealizationT`! -/
theorem convT_pi_inj_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ B₁ A₂ B₂ : Expr Nat} {u : Level}
    (hc : ConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort u)) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :=
  lrSCoreS_pi_components hL
    (fundConvAt_bot_of_fundamentalSAtT hL hZL hW (ctxModelTLaws_approxT E) hFund hΓ hc (.pi .bot [])
      (Or.inl (approxT_pi_bot_nil E EnvT.bot A₁ B₁)))

/-- **Direct Single-Sort `ConvT` Family-Spine Injectivity from `FundamentalSAtT` Alone
    (`convT_famApp_inj_of_fundamentalSAtT`):**
    Evaluates `fundConvAt_bot_of_fundamentalSAtT` at `EnvT.bot` and `.spine r (botVecT xs)`
    (`approxT_famApp_botVecT`) — requiring **zero** `RelSubstIdT` and **zero**
    `FamTypedProbeRealizationT`! -/
theorem convT_famApp_inj_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls ls' : List Level} {xs xs' : List (Expr Nat)} {u : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hc : ConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort u)) :
    eqNList ls ls' ∧
      xs.length = (piDomsOf m.mtype).length ∧
      xs'.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' :=
  lrSCoreS_famApp_components hL hW hm hind
    (fundConvAt_bot_of_fundamentalSAtT hL hZL hW (ctxModelTLaws_approxT E) hFund hΓ hc
      (.spine r (botVecT xs))
      (Or.inl (approxT_famApp_botVecT hW EnvT.bot hm hind ls xs)))

/-- **Direct Single-Sort `ConvT` Relevant-Slot Conversion (#7525) from `FundamentalSAtT` Alone
    (`convT_famApp_relevantSlotConv_of_fundamentalSAtT`):** -/
theorem convT_famApp_relevantSlotConv_of_fundamentalSAtT (hL : ReadbackLaws E R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} {ls ls' : List Level} {xs xs' : List (Expr Nat)} {u : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hc : ConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.sort u)) :
    RelevantSlotConv E n Γ [] ((piDomsOf m.mtype).map (instantiateLevels ls)) xs xs' :=
  relevantSlotConv_of_convArgsT hW hm hind
    (convT_famApp_inj_of_fundamentalSAtT hL hZL hW hFund hΓ hm hind hc).2.2.2

/-- **`FamProbeLinkS R E n` from `FundamentalSAtT` + `FamTypedProbeRealizationT`
    (`famProbeLinkS_of_fundamentalSAtT_realization`):** -/
theorem famProbeLinkS_of_fundamentalSAtT_realization (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    (hreal : FamTypedProbeRealizationT R E n) :
    FamProbeLinkS R E n := by
  intro Γ hΓ A B u hc c hpc hAA
  have hA : HasTyT E n Γ A (.sort u) := (convEnds hW hΓ hc).1
  have hrealA : FamProbeRealizedAtT R E n Γ A := hreal hΓ hA
  cases hpc with
  | bot => exact lrSCoreS_bot _ _ _ _
  | prop =>
      rw [lrSCoreS_prop_iff] at hAA
      obtain ⟨_, l, _, hread, _⟩ := hAA
      have h := fundConvAt_ctxEnvT_of_fundamentalSAtT hL hZL hW hFund hΓ hc (sortCode l)
        (Or.inl (hrealA.1.1 l hread))
      exact (lrSCoreS_prop_iff _ _ _ _).mpr ((lrSCoreS_sortCode_iff l).mp h)
  | sort =>
      rw [lrSCoreS_sort_iff] at hAA
      obtain ⟨_, l, _, hread, _⟩ := hAA
      have h := fundConvAt_ctxEnvT_of_fundamentalSAtT hL hZL hW hFund hΓ hc (sortCode l)
        (Or.inl (hrealA.1.1 l hread))
      exact (lrSCoreS_sort_iff _ _ _ _).mpr ((lrSCoreS_sortCode_iff l).mp h)
  | piBotNil =>
      rw [LRSCoreS.eq_def] at hAA
      obtain ⟨_, A₁, B₁, _, _, hread, _, ⟨hΓ₁⟩, _⟩ := hAA
      exact fundConvAt_ctxEnvT_of_fundamentalSAtT hL hZL hW hFund hΓ hc (.pi .bot [])
        (Or.inl (hrealA.1.2 A₁ B₁ hread hΓ₁))
  | @spine r m args hm hind _ =>
      rw [lrSCoreS_spine_iff] at hAA
      obtain ⟨m', ls₁, _, xs₁, xs₂, hm', hread₁, hread₂, hn₁, hn₂, _, ha₁, _, hargs, hty⟩ := hAA
      have em : m = m' := Option.some.inj (hm.symm.trans hm')
      subst em
      have e_sp := hNU Γ hread₁ hn₁ hread₂ hn₂
      obtain ⟨_, hxs_eq⟩ := foldApps_const_inj e_sp
      subst hxs_eq
      obtain ⟨hxs₁, _, ⟨w₁, ⟨hty₁⟩⟩, _⟩ := hty ⟨u, .refl _⟩ hind
      have h := fundConvAt_ctxEnvT_of_fundamentalSAtT hL hZL hW hFund hΓ hc (.spine r (botVecT xs₁))
        (Or.inl (hrealA.2 r m ls₁ xs₁ w₁ hm hind hread₁ hty₁ hxs₁ hargs))
      rw [lrSCoreS_spine_iff] at h ⊢
      obtain ⟨m'', ls₁', ls₂', xs₁', xs₂', hm'', h1', h2', hn₁', hn₂', heqN', _, _, hargs', hty'⟩ := h
      have em' : m = m'' := Option.some.inj (hm.symm.trans hm'')
      subst em'
      obtain ⟨hlen₁', hlen₂', hw₁', hw₂'⟩ := hty' ⟨u, .refl _⟩ hind
      have ha₂' : args.length ≤ xs₂'.length := by omega
      have ha₁' : args.length ≤ xs₁'.length := by omega
      exact ⟨m, ls₁', ls₂', xs₁', xs₂', hm, h1', h2', hn₁', hn₂', heqN', ha₁', ha₂', hargs',
        fun _ _ => ⟨hlen₁', hlen₂', hw₁', hw₂'⟩⟩

/-- **`PiRowField E n` from `FundamentalSAtT` + `FamTypedProbeRealizationT`
    (`piRowField_of_fundamentalSAtT_realization`):** -/
theorem piRowField_of_fundamentalSAtT_realization (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    (hreal : FamTypedProbeRealizationT R E n) :
    PiRowField E n :=
  piRowField_of_famProbeLinkS hL hNU hW
    (famProbeLinkS_of_fundamentalSAtT_realization hL hNU hZL hW hFund hreal)

/-- **`FamAppRowLink E n` from `FundamentalSAtT` + `FamTypedProbeRealizationT`
    (`famAppRow_of_fundamentalSAtT_realization`):** -/
theorem famAppRow_of_fundamentalSAtT_realization (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    (hreal : FamTypedProbeRealizationT R E n) :
    FamAppRowLink E n :=
  famAppRow_of_famProbeLinkS hL hNU hW
    (famProbeLinkS_of_fundamentalSAtT_realization hL hNU hZL hW hFund hreal)

/-- **`FamRelevantSlotConv E n` (#7525) from `FundamentalSAtT` + `FamTypedProbeRealizationT`
    (`famRelevantSlotConv_of_fundamentalSAtT_realization`):** -/
theorem famRelevantSlotConv_of_fundamentalSAtT_realization (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    (hreal : FamTypedProbeRealizationT R E n) :
    FamRelevantSlotConv E n :=
  famRelevantSlotConv_of_famProbeLinkS hL hNU hW
    (famProbeLinkS_of_fundamentalSAtT_realization hL hNU hZL hW hFund hreal)

/-- **`TypedRowsWf E n` from `AllBelowScoped` + `FundamentalSAtT` + `FamTypedProbeRealizationT`
    (`typedRowsWf_of_allBelowScoped_fundamentalSAtT_realization`):** -/
theorem typedRowsWf_of_allBelowScoped_fundamentalSAtT_realization (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R)
    (hZL : ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat}, lookupValue Γ i = some v → R Γ (.bvar i) v)
    (hW : EnvWfT E)
    {Aw : Nat → Nat} (hBel : AllBelowScoped E Aw (tableOf hW))
    (hFund : FundamentalSAtT (ctxModelT_approxT E) R n)
    (hreal : FamTypedProbeRealizationT R E n) :
    TypedRowsWf E n :=
  typedRowsWf_of_allBelowScoped_famProbeLinkS hL hNU hW hBel
    (famProbeLinkS_of_fundamentalSAtT_realization hL hNU hZL hW hFund hreal)

/-- **Universal Refutation of Unrestricted `TypingLemmaEnvT (ctxModelT_approxT E) n`
    (`not_typingLemmaEnvT_all`):**
    Because `envTypedAtT_bot [] : EnvTypedAtT (ctxModelT_approxT E) [] EnvT.bot` holds unconditionally
    (`RcicNativeTypedModelProbe`), unrestricted `TypingLemmaEnvT (ctxModelT_approxT E) n` is refuted
    for **every** `E : ResolvedEnv` and **every** `n : Nat` by the closed term `famCexIdLam : famCexIdPi`
    at `famCexIdLamCpt` (`not_elT_famCexIdPi_cpt`)! -/
theorem not_typingLemmaEnvT_all (E : ResolvedEnv) (n : Nat) :
    ¬ TypingLemmaEnvT (ctxModelT_approxT E) n :=
  fun hTL => not_elT_famCexIdPi_cpt E EnvT.bot
    (hTL (hasTyT_famCexIdLam E n) (envTypedAtT_bot []) famCexIdLamCpt
      (approxT_famCexIdLam_cpt E EnvT.bot))

/-- **Refutation of `EnvTypedAtT (ctxModelT_approxT E) Γ (ctxEnvT E Γ)` Under Let-Bindings
    (`not_envTypedAtT_ctxEnvT_letCex`):**
    In the well-formed context `Γ = [.letBinding famCexIdPi famCexIdLam]`, `ctxEnvT E Γ` assigns
    `ApproxT E (ctxEnvT E []) famCexIdLam` to `.bvar 0` (which contains `famCexIdLamCpt`), whereas
    `lookupType Γ 0 = some (lift 0 1 famCexIdPi) = some famCexIdPi` and `¬ ElT E (ctxEnvT E Γ) famCexIdPi famCexIdLamCpt`!
    By contrast, `envTypedAtT_bot Γ : EnvTypedAtT (ctxModelT_approxT E) Γ EnvT.bot` holds for **every** `Γ`! -/
theorem not_envTypedAtT_ctxEnvT_letCex (E : ResolvedEnv) :
    ¬ EnvTypedAtT (ctxModelT_approxT E)
        [.letBinding famCexIdPi famCexIdLam]
        (ctxEnvT E [.letBinding famCexIdPi famCexIdLam]) := by
  intro hEnv
  have hlook : lookupType [.letBinding famCexIdPi famCexIdLam] 0 = some famCexIdPi := rfl
  obtain ⟨a, hap, hcty⟩ := hEnv 0 famCexIdPi hlook famCexIdLamCpt
    (approxT_famCexIdLam_cpt E (ctxEnvT E []))
  exact not_elT_famCexIdPi_cpt E (ctxEnvT E [.letBinding famCexIdPi famCexIdLam]) ⟨a, hap, hcty⟩


/-! #### §13 Part C — Resolution of `W-FAMSPINE` in `RcicNativeTypedModelFund.fundT_app`
    (`lrSCoreS_app_of_famSpine_step`, `lrSCoreS_app_of_famSpine_syntactic`,
    `lrSCoreS_app_of_approxT_famProbe`) and Concrete `LRSCoreS (WhStepRecKCanon E)` Witnesses -/

/-- `LRSCoreS` formulation of `PiTowerLinkBelow` at `piTowerCptT k` (`PiTowerLinkBelowS`). -/
def PiTowerLinkBelowS (R : Readback) (E : ResolvedEnv) (n : Nat) (bound : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A B : Expr Nat} {u : Level} (hc : ConvT E n Γ A B (.sort u)),
      sizeOf hc < bound →
      ∀ {k : Nat},
        LRSCoreS R E n Γ A A (.sort u) (piTowerCptT k) →
        LRSCoreS R E n Γ A B (.sort u) (piTowerCptT k)

/-- `PiTowerLinkBelowS R E n bound` is logically equivalent (`↔`) to `PiTowerLinkBelow R E n bound`. -/
theorem piTowerLinkBelowS_iff {bound : Nat} :
    PiTowerLinkBelowS R E n bound ↔ PiTowerLinkBelow R E n bound := by
  constructor
  · intro hS Γ hΓ A B u hc hsz k hAA
    exact (piTowerS_iff k).mp (hS hΓ hc hsz ((piTowerS_iff k).mpr hAA))
  · intro hI Γ hΓ A B u hc hsz k hAA
    exact (piTowerS_iff k).mpr (hI hΓ hc hsz ((piTowerS_iff k).mp hAA))

theorem PiTowerLinkBelowS.mono {b₁ b₂ : Nat} (hb : b₁ ≤ b₂)
    (h : PiTowerLinkBelowS R E n b₂) : PiTowerLinkBelowS R E n b₁ := by
  intro Γ hΓ A B u hc hsz k hAA
  exact h hΓ hc (Nat.lt_of_lt_of_le hsz hb) hAA

/-- **Lambda-Demand Application Step for Landed `LRSCoreS` (`lrSCoreS_app_of_lambda_demand`):** -/
theorem lrSCoreS_app_of_lambda_demand (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B : Expr Nat} {graph : List (List CptT × CptT)} {s : List CptT × CptT}
    (_hc_fg : ConvT E n Γ f g (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hfg : LRSCoreS R E n Γ f g (.pi A B) (.lam graph))
    (hs : s ∈ graph)
    (hab : ∀ u ∈ s.1, LRSCoreS R E n Γ a b A u) :
    LRSCoreS R E n Γ (.app f a) (.app g b) (instantiate0 a B) s.2 := by
  rw [LRSCoreS.eq_def] at hfg
  obtain ⟨A₁, B₁, hr, _, hclause⟩ := hfg
  obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU (.refl (.pi A B)) hr
  subst eA; subst eB
  obtain ⟨ha_ty, hb_ty, _⟩ := convEnds hW hΓ hc_ab
  exact hclause s hs a b ha_ty hb_ty ⟨hc_ab⟩ hab

/-- **Resolution of `W-FAMSPINE` in Landed `LRSCoreS`: Spine-Growth Application Step on Admitted
    `.inductiveM` Family Spines (`lrSCoreS_app_of_famSpine_step`):**
    Directly resolves the `.spine r (args ++ [u])` case excluded by `hns : ∀ r args, c ≠ .spine r args`
    in `RcicNativeTypedModelFund.fundT_app`:
    - Uses `wholeSpine_convArgsT_snoc_of_links` (from `PiTowerLinkBelowS R E n (sizeOf df_sp)`,
      strictly smaller than the application derivation) to extend `ConvArgsT` along the declared
      telescope `instantiateLevels ls₁ m.mtype` from `(xs₁, xs₂)` to `(xs₁ ++ [a], xs₂ ++ [b])`.
    - When `xs₁.length + 1 < (piDomsOf m.mtype).length` (unsaturated), `not_redR_sort_of_wholeSpine_lt`
      discharges `SpineClauseS`'s sort-index conditional vacuously.
    - When `(xs₁ ++ [a]).length = (piDomsOf m.mtype).length` (saturated), `hasTyT_famApp_both_of_levelFacts_convArgsT`
      recovers both sort typings and `(xs₂ ++ [b]).length = (piDomsOf m.mtype).length`! -/
theorem lrSCoreS_app_of_famSpine_step (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {f g a b A B : Expr Nat} {args : List CptT} (u : CptT)
    (hc_ab : ConvT E n Γ a b A)
    (hf_sp : LRSCoreS R E n Γ f g (.pi A B) (.spine r args))
    (hsp_ty : ∀ ls₁ ls₂ xs₁ xs₂,
      RedR R Γ f (foldApps (.const r ls₁) xs₁) →
      RedR R Γ g (foldApps (.const r ls₂) xs₂) →
      eqNList ls₁ ls₂ →
      ∃ df_sp : HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.pi A B),
        levelsBounded n ls₂ = true ∧
        xs₁.length < (piDomsOf m.mtype).length ∧
        PiTowerLinkBelowS R E n (sizeOf df_sp)) :
    LRSCoreS R E n Γ (.app f a) (.app g b) (instantiate0 a B) (.spine r (args ++ [u])) := by
  rw [lrSCoreS_spine_iff] at hf_sp ⊢
  obtain ⟨m', ls₁, ls₂, xs₁, xs₂, hm', hred₁, hred₂, _, _, heqN, ha₁, ha₂, hargs, _⟩ := hf_sp
  have em : m = m' := Option.some.inj (hm.symm.trans hm')
  subst em
  obtain ⟨df_sp, hbel₂, hlt, hlinkS⟩ := hsp_ty ls₁ ls₂ xs₁ xs₂ hred₁ hred₂ heqN
  have hlink : PiTowerLinkBelow R E n (sizeOf df_sp) := piTowerLinkBelowS_iff.mp hlinkS
  obtain ⟨ha_ty, _, _⟩ := convEnds hW hΓ hc_ab
  have hargs_snoc : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) (xs₁ ++ [a]) (xs₂ ++ [b]) :=
    wholeSpine_convArgsT_snoc_of_links hL hNU hW hΓ hm ls₁ df_sp hlt hlink hargs hc_ab
  have hred_fa : RedR R Γ (.app f a) (foldApps (.const r ls₁) (xs₁ ++ [a])) := by
    rw [foldApps_snoc]; exact redR_appHead hL hred₁
  have hred_gb : RedR R Γ (.app g b) (foldApps (.const r ls₂) (xs₂ ++ [b])) := by
    rw [foldApps_snoc]; exact redR_appHead hL hred₂
  have hn_fa : NormalR R Γ (foldApps (.const r ls₁) (xs₁ ++ [a])) :=
    fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs
  have hn_gb : NormalR R Γ (foldApps (.const r ls₂) (xs₂ ++ [b])) :=
    fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs
  have ha₁_snoc : (args ++ [u]).length ≤ (xs₁ ++ [a]).length := by
    simp only [List.length_append, List.length_singleton]; omega
  have ha₂_snoc : (args ++ [u]).length ≤ (xs₂ ++ [b]).length := by
    simp only [List.length_append, List.length_singleton]; omega
  refine ⟨m, ls₁, ls₂, xs₁ ++ [a], xs₂ ++ [b], hm, hred_fa, hred_gb, hn_fa, hn_gb,
    heqN, ha₁_snoc, ha₂_snoc, hargs_snoc, ?_⟩
  intro hsort _
  have hbnd_snoc : (xs₁ ++ [a]).length ≤ (piDomsOf m.mtype).length := by
    simp only [List.length_append, List.length_singleton]; exact hlt
  rcases Nat.lt_or_eq_of_le hbnd_snoc with hlt_sat | hlen_sat
  · have hlt1 : xs₁.length + 1 < (piDomsOf m.mtype).length := by
      simpa only [List.length_append, List.length_singleton] using hlt_sat
    obtain ⟨l, hl⟩ := hsort
    exact (not_redR_sort_of_wholeSpine_lt hL hNU hW hΓ hm df_sp ha_ty hlt1 hlink l hl).elim
  · obtain ⟨hlen₁, hbel₁⟩ := NativeFamilyProjection.native_level_facts hm df_sp
    obtain ⟨hxs₂, ⟨w₁, w₂, hty₁, hty₂⟩, _⟩ :=
      hasTyT_famApp_both_of_levelFacts_convArgsT hW hΓ hm hind hlen₁ hbel₁ hbel₂ heqN
        hlen_sat hargs_snoc
    exact ⟨hlen_sat, hxs₂, ⟨w₁, hty₁⟩, ⟨w₂, hty₂⟩⟩

/-- **Syntactic-Spine Specialization of `lrSCoreS_app_of_famSpine_step`
    (`lrSCoreS_app_of_famSpine_syntactic`):**
    When `f = foldApps (.const r ls) xs` and `g = foldApps (.const r ls') xs'` (as in
    `substT σ (foldApps (.const r ls) xs)` and `substT σ' (foldApps (.const r ls) xs)`), both
    `df_sp` and `levelsBounded n ls' = true` are extracted directly from `hc_fg : ConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.pi A B)`! -/
theorem lrSCoreS_app_of_famSpine_syntactic (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {a b A B : Expr Nat}
    {args : List CptT} (u : CptT)
    (hc_fg : ConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs') (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hlt : xs.length < (piDomsOf m.mtype).length)
    (hlink : PiTowerLinkBelowS R E n (sizeOf (convEnds hW hΓ hc_fg).1))
    (hf_sp : LRSCoreS R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')
      (.pi A B) (.spine r args)) :
    LRSCoreS R E n Γ
      (.app (foldApps (.const r ls) xs) a)
      (.app (foldApps (.const r ls') xs') b)
      (instantiate0 a B) (.spine r (args ++ [u])) := by
  obtain ⟨_, hbel'⟩ := NativeFamilyProjection.native_level_facts hm (convEnds hW hΓ hc_fg).2.1
  refine lrSCoreS_app_of_famSpine_step hL hNU hW hΓ hm hind u hc_ab hf_sp ?_
  intro ls₁ ls₂ xs₁ xs₂ hred₁ hred₂ _
  have e₁ := (redR_famApp_eq hL hW hm hind hred₁).symm
  obtain ⟨hconst₁, hxs₁⟩ := foldApps_const_inj e₁
  injection hconst₁ with _ hls₁
  subst hls₁; subst hxs₁
  have e₂ := (redR_famApp_eq hL hW hm hind hred₂).symm
  obtain ⟨hconst₂, _⟩ := foldApps_const_inj e₂
  injection hconst₂ with _ hls₂
  subst hls₂
  exact ⟨(convEnds hW hΓ hc_fg).1, hbel', hlt, hlink⟩

/-- **Unified `ApproxT` Application Demand Theorem for Landed `LRSCoreS` Across All `FamProbeCptT E`
    Compacts (`lrSCoreS_app_of_approxT_famProbe`):**
    Removes the `hns : ∀ r args, c ≠ .spine r args` restriction of `RcicNativeTypedModelFund.fundT_app`
    across all `FamProbeCptT E` compacts! -/
theorem lrSCoreS_app_of_approxT_famProbe (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g a b A B : Expr Nat} {c : CptT}
    (hc_fg : ConvT E n Γ f g (.pi A B))
    (hc_ab : ConvT E n Γ a b A)
    (hc : FamProbeCptT E c)
    (happrox : ApproxT E (ctxEnvT E Γ) (.app f a) c)
    (hf : ∀ d, ApproxT E (ctxEnvT E Γ) f d → LRSCoreS R E n Γ f g (.pi A B) d)
    (ha : ∀ u, ApproxT E (ctxEnvT E Γ) a u → LRSCoreS R E n Γ a b A u)
    (hsp_ty : ∀ r m ls₁ ls₂ xs₁ xs₂,
      E.members r = some m → m.mclass = .inductiveM →
      RedR R Γ f (foldApps (.const r ls₁) xs₁) →
      RedR R Γ g (foldApps (.const r ls₂) xs₂) →
      eqNList ls₁ ls₂ →
      ∃ df_sp : HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.pi A B),
        levelsBounded n ls₂ = true ∧
        xs₁.length < (piDomsOf m.mtype).length ∧
        PiTowerLinkBelowS R E n (sizeOf df_sp)) :
    LRSCoreS R E n Γ (.app f a) (.app g b) (instantiate0 a B) c := by
  cases hc with
  | bot => exact lrSCoreS_bot _ _ _ _
  | prop =>
      rcases approxT_app_inv happrox with hbot | ⟨graph, s, heq_s, hfg, hs, hax⟩ | ⟨_, _, _, heq, _, _⟩
      · exact CptT.noConfusion hbot
      · rw [heq_s]
        exact lrSCoreS_app_of_lambda_demand hL hNU hW hΓ hc_fg hc_ab
          (hf (.lam graph) hfg) hs (fun u hu => ha u (hax u hu))
      · exact CptT.noConfusion heq
  | sort =>
      rcases approxT_app_inv happrox with hbot | ⟨graph, s, heq_s, hfg, hs, hax⟩ | ⟨_, _, _, heq, _, _⟩
      · exact CptT.noConfusion hbot
      · rw [heq_s]
        exact lrSCoreS_app_of_lambda_demand hL hNU hW hΓ hc_fg hc_ab
          (hf (.lam graph) hfg) hs (fun u hu => ha u (hax u hu))
      · exact CptT.noConfusion heq
  | piBotNil =>
      rcases approxT_app_inv happrox with hbot | ⟨graph, s, heq_s, hfg, hs, hax⟩ | ⟨_, _, _, heq, _, _⟩
      · exact CptT.noConfusion hbot
      · rw [heq_s]
        exact lrSCoreS_app_of_lambda_demand hL hNU hW hΓ hc_fg hc_ab
          (hf (.lam graph) hfg) hs (fun u hu => ha u (hax u hu))
      · exact CptT.noConfusion heq
  | @spine r m args hm hind _ =>
      rcases approxT_app_inv happrox with hbot | ⟨graph, s, heq_s, hfg, hs, hax⟩ |
        ⟨r', args₀, u₀, heq, hfs, _⟩
      · exact CptT.noConfusion hbot
      · rw [heq_s]
        exact lrSCoreS_app_of_lambda_demand hL hNU hW hΓ hc_fg hc_ab
          (hf (.lam graph) hfg) hs (fun u hu => ha u (hax u hu))
      · injection heq with hr hargs_eq
        subst hr; subst hargs_eq
        exact lrSCoreS_app_of_famSpine_step hL hNU hW hΓ hm hind u₀ hc_ab
          (hf (.spine r args₀) hfs)
          (fun ls₁ ls₂ xs₁ xs₂ hred₁ hred₂ heqN =>
            hsp_ty r m ls₁ ls₂ xs₁ xs₂ hm hind hred₁ hred₂ heqN)

/-- Concrete `LRSCoreS (WhStepRecKCanon trueEnvU)` witness on `trueVarSort` at `.sort`. -/
theorem lrSCoreS_whStepRecKCanon_trueVarSort (n : Nat) :
    LRSCoreS (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarSort (.sort .zero) (.sort (.succ .zero)) .sort := by
  rw [lrSCoreS_sort_iff]
  exact ⟨⟨_, .refl _⟩, _, _, redR_of_whRedRecKCanon whRedRecKCanon_trueVarSort, .refl _⟩

/-- Concrete `LRSCoreS (WhStepRecKCanon trueEnvU)` witness on `trueVarPi` at `.pi .bot []`. -/
theorem lrSCoreS_whStepRecKCanon_trueVarPi (n : Nat) :
    LRSCoreS (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarPi PiModelDeltaIotaAudit.idPiProp (.sort (.succ .zero)) (.pi .bot []) :=
  piProbeS_iff.mpr (lrSCore_whStepRecKCanon_trueVarPi n)

/-- Concrete `LRSCoreS (WhStepRecKCanon trueEnvU)` witness on `trueVarFam` at `.spine 0 []`. -/
theorem lrSCoreS_whStepRecKCanon_trueVarFam (n : Nat) :
    LRSCoreS (WhStepRecKCanon trueEnvU) trueEnvU n trueVarCtx
      trueVarFam (.const 0 []) (.sort .zero) (.spine 0 []) := by
  rw [lrSCoreS_spine_iff]
  have hm0 : trueEnvU.members 0 = some trueFamMember := rfl
  have h1 : RedR (WhStepRecKCanon trueEnvU) trueVarCtx trueVarFam (foldApps (.const 0 []) []) :=
    redR_of_whRedRecKCanon whRedRecKCanon_trueVarFam
  have hty0 : HasTyT trueEnvU n trueVarCtx (foldApps (.const 0 []) []) (.sort .zero) :=
    .const trueVarCtx 0 [] trueFamMember hm0 rfl rfl
  exact ⟨trueFamMember, [], [], [], [], hm0, h1, .refl _,
    fun _ hs => whStepRecKCanon_famApp_false trueEnvUWfT hm0 rfl hs,
    fun _ hs => whStepRecKCanon_famApp_false trueEnvUWfT hm0 rfl hs,
    trivial, Nat.le_refl 0, Nat.le_refl 0, .nil _,
    fun _ _ => ⟨rfl, rfl, ⟨.zero, ⟨hty0⟩⟩, ⟨.zero, ⟨hty0⟩⟩⟩⟩

/-- Concrete `LRSCoreS (WhStepRecKCanon andEnvU)` witness on `mixAndRedex` at `.pi .bot []`. -/
theorem lrSCoreS_whStepRecKCanon_mixAnd :
    LRSCoreS (WhStepRecKCanon andEnvU) andEnvU 0 mixAndCtx
      mixAndRedex mixPi (.sort (.succ .zero)) (.pi .bot []) :=
  piProbeS_iff.mpr lrSCore_whStepRecKCanon_mixAnd

/-- Concrete `LRSCoreS (WhStepRecKCanon eqEnvT)` witness on `eqCanonGapRedex` at `.sort`. -/
theorem lrSCoreS_whStepRecKCanon_eqCanonGap_sort :
    LRSCoreS (WhStepRecKCanon eqEnvT) eqEnvT 0 eqCanonGapCtx
      eqCanonGapRedex (.sort .zero) (.sort (.succ .zero)) .sort := by
  rw [lrSCoreS_sort_iff]
  exact ⟨⟨_, .refl _⟩, .zero, .zero, redR_whStepRecKCanon_eqCanonGapRedex, .refl _⟩

/-- Concrete `LRSCoreS (WhStepRecKCanon pinLoopEnvT)` witness on `loopCanonRedex` at `.sort`. -/
theorem lrSCoreS_whStepRecKCanon_loopCanon_sort :
    LRSCoreS (WhStepRecKCanon pinLoopEnvT) pinLoopEnvT 0 loopCanonCtx
      loopCanonRedex (.sort .zero) (.sort (.succ .zero)) .sort := by
  rw [lrSCoreS_sort_iff]
  exact ⟨⟨_, .refl _⟩, .zero, .zero, redR_whStepRecKCanon_loopCanonRedex, .refl _⟩

#print axioms typeSpineT_symm_of_envWfT
#print axioms typeSpineT_trans_of_envWfT
#print axioms lrSCoreT_irrel_of_envWfT
#print axioms lrSCoreT_symm_of_envWfT
#print axioms lrSCoreT_trans_of_envWfT
#print axioms lrSCoreT_symm_tm_of_envWfT
#print axioms lrSCoreT_trans_tm_of_envWfT
#print axioms lrST_symm_of_envWfT
#print axioms lrST_trans_of_envWfT
#print axioms lrST_symm_tm_of_envWfT
#print axioms lrST_trans_tm_of_envWfT
#print axioms typeSpineR_symm_of_envWfT
#print axioms typeSpineR_trans_of_inductiveM
#print axioms lrSCore_symm_botFamCpt
#print axioms lrSCore_trans_botFamCpt
#print axioms lrS_symm_botFamCpt
#print axioms lrS_trans_botFamCpt
#print axioms eq_botVecI_of_botDemand
#print axioms modelAt_right_of_lrSCore_famProbeCpt
#print axioms FundamentalLRSTMFamProbe
#print axioms fundamentalLRSTM_to_famProbe
#print axioms fundamentalLRSTMProbe_of_famProbe
#print axioms fundamentalLRSTMFamProbe_of_links
#print axioms piRowField_of_fundamentalLRSTMFamProbe
#print axioms not_tyConvT_pi_sort_of_fundamentalLRSTMProbe
#print axioms not_tyConvT_sort_pi_of_fundamentalLRSTMProbe
#print axioms famApp_saturated_of_fundamentalLRSTMProbe
#print axioms famApp_length_eq_piDomsOf_of_fundamentalLRSTMProbe
#print axioms famAppRow_of_fundamentalLRSTMFamProbe
#print axioms famRelevantSlotConv_of_fundamentalLRSTMFamProbe
#print axioms typedRowsWf_of_allBelowScoped_fundamentalLRSTMFamProbe
#print axioms famAppRow_of_links
#print axioms famRelevantSlotConv_of_links
#print axioms typedRowsWf_of_allBelowScoped_links
#print axioms lrSCore_right_diag_botFamCpt
#print axioms lrSCore_sort_self
#print axioms lrSCore_pi_self_of_hasTyT
#print axioms lrSCore_famApp_of_components
#print axioms lrSCore_famApp_refl_of_saturated
#print axioms FamProbeLink
#print axioms famProbe_chain
#print axioms piRowField_of_famProbeLink
#print axioms not_tyConvT_pi_sort_of_famProbeLink
#print axioms not_tyConvT_sort_pi_of_famProbeLink
#print axioms famApp_saturated_of_famProbeLink
#print axioms famApp_length_eq_piDomsOf_of_famProbeLink
#print axioms famAppRow_of_famProbeLink
#print axioms famRelevantSlotConv_of_famProbeLink
#print axioms typedRowsWf_of_allBelowScoped_famProbeLink
#print axioms redR_of_whRedRecKCanon
#print axioms whRedRecKCanon_of_redR
#print axioms readbackLaws_whStepRecKCanon
#print axioms detR_whStepRecKCanon
#print axioms normalUniqueR_whStepRecKCanon
#print axioms famAppRow_of_famProbeLink_whStepRecKCanon
#print axioms famRelevantSlotConv_of_famProbeLink_whStepRecKCanon
#print axioms typedRowsWf_of_allBelowScoped_famProbeLink_whStepRecKCanon
#print axioms lrSCore_whStepRecKCanon_trueVarSort
#print axioms lrSCore_whStepRecKCanon_trueVarSort_symm
#print axioms lrSCore_whStepRecKCanon_trueVarPi
#print axioms lrSCore_whStepRecKCanon_trueVarFam
#print axioms lrSCore_whStepRecKCanon_mixAnd
#print axioms ApproxTArgs
#print axioms approxTArgs_length
#print axioms approxTArgs_snoc
#print axioms approxTArgs_snoc_inv
#print axioms approxT_foldApps_spine
#print axioms not_propCtorT_of_inductiveM
#print axioms approxT_const_inductiveM
#print axioms approxT_const_inductiveM_inv
#print axioms approxT_famApp
#print axioms approxT_foldApps_const_inductiveM_inv_aux
#print axioms approxT_foldApps_const_inductiveM_inv
#print axioms approxT_famApp_iff
#print axioms botVecT
#print axioms botVecT_length
#print axioms botVecT_eq_of_length_eq
#print axioms botDemandT_botVecT
#print axioms eq_botVecT_of_botDemandT
#print axioms approxTArgs_botVecT
#print axioms approxT_famApp_botVecT
#print axioms approxT_famApp_botVecT_of_length_eq
#print axioms slotVecT
#print axioms approxTArgs_slotVecT
#print axioms approxTArgs_slotVecT_inv
#print axioms approxT_famApp_slotVecT
#print axioms semEqT_famApp_head_length
#print axioms semEqT_famApp_slot
#print axioms semEqT_famApp_inj
#print axioms semEqT_pi_famApp_disjoint
#print axioms semEqT_sort_famApp_disjoint
#print axioms SemEqTArgs
#print axioms semEqTArgs_refl
#print axioms semEqTArgs_symm
#print axioms semEqTArgs_trans
#print axioms approxTArgs_congr
#print axioms semEqT_const_inductiveM_ls
#print axioms semEqT_famApp_congr
#print axioms tyCodeCT_of_approxT_famApp
#print axioms isPropCT_of_approxT_famApp_prop
#print axioms elT_famApp_prop_bot
#print axioms not_isPropCT_spine_of_piBody_ne_zero
#print axioms elT_famApp_nonprop_spine
#print axioms typingLemma_at_famApp_prop
#print axioms typingLemma_at_famApp_nonprop
#print axioms lrSCoreT_spine_sort_iff
#print axioms lrSCoreT_spine_sort_args_irrel
#print axioms typeSpineT_expand
#print axioms lrSCoreT_spine_sort_expand
#print axioms lrSCoreT_famApp_components
#print axioms lrSCoreT_famApp_of_components
#print axioms lrSCoreT_famApp_refl_of_saturated
#print axioms lrSCoreT_pi_components
#print axioms FamProbeCptT
#print axioms famProbeCptT_sortCode
#print axioms famProbeCptT_spine_botVecT
#print axioms lrSCoreT_sortCode_iff
#print axioms ReadbackModelInvT
#print axioms redR_modelInvT
#print axioms ctyS_of_approxT_lam_eq_bot
#print axioms approxT_app_lamDomain_id_eq_bot
#print axioms not_readbackModelInvT_pi_bot_nil_of_readbackLaws
#print axioms not_readbackModelInvT_of_readbackLaws
#print axioms not_readbackModelInvT_whStepRecKCanon
#print axioms lrSCoreT_right_diag_of_envWfT
#print axioms lrSCoreT_sort_self
#print axioms lrSCoreT_pi_self_of_hasTyT
#print axioms FamProbeLinkT
#print axioms famProbe_chainT
#print axioms FundamentalLRSTTTyped
#print axioms FundamentalLRSTTFamProbe
#print axioms fundamentalLRSTTFamProbe_of_fundamentalLRSTTTyped
#print axioms fundamentalLRSTTFamProbe_of_links
#print axioms piRowField_of_fundamentalLRSTTFamProbe
#print axioms famAppRow_of_fundamentalLRSTTFamProbe
#print axioms famRelevantSlotConv_of_fundamentalLRSTTFamProbe
#print axioms typedRowsWf_of_allBelowScoped_fundamentalLRSTTFamProbe
#print axioms piRowField_of_linksT
#print axioms not_tyConvT_pi_sort_of_linksT
#print axioms not_tyConvT_sort_pi_of_linksT
#print axioms famApp_saturated_of_linksT
#print axioms famApp_length_eq_piDomsOf_of_linksT
#print axioms famAppRow_of_linksT
#print axioms famRelevantSlotConv_of_linksT
#print axioms typedRowsWf_of_allBelowScoped_linksT
#print axioms famAppRow_of_linksT_whStepRecKCanon
#print axioms famRelevantSlotConv_of_linksT_whStepRecKCanon
#print axioms typedRowsWf_of_allBelowScoped_linksT_whStepRecKCanon
#print axioms lrSCoreT_sorts_probe
#print axioms lrSCoreT_sort_diag_probe
#print axioms approxT_ctxEnvT_bvar_of_lookupValue_none
#print axioms approxT_ctxEnvT_foldApps_bvar_of_lookupValue_none
#print axioms lrSCoreT_bvar_of_lookupValue_none_probe
#print axioms approxT_pi_famProbeCptT
#print axioms lrSCoreT_pi_probe
#print axioms lrSCoreT_pi_diag_probe
#print axioms lrSCoreT_famSpine_of_convArgsT_probe
#print axioms lrSCoreT_famSpine_diag_probe
#print axioms dt012_of_allBelowScoped_fundamentalLRSTTFamProbe
#print axioms dt010_of_allBelowScoped_fundamentalLRSTTFamProbe
#print axioms dt011_of_allBelowScoped_fundamentalLRSTTFamProbe
#print axioms dt019_of_allBelowScoped_fundamentalLRSTTFamProbe
#print axioms ia024_of_allBelowScoped_fundamentalLRSTTFamProbe
#print axioms lrTermFamSemBiProbeRKCanon_famSpine_step_app_partial
#print axioms lrTermFamSemBiProbeRKCanon_famSpine_step_app_saturated
#print axioms lrTermFamSemBiProbeRKCanon_app_of_fn_and_arg
#print axioms lrTermFamSemBiProbeRKCanon_app_fn_of_letBinding
#print axioms lrTermFamSemBiProbeRKCanon_eta_of_left_probe_bot
#print axioms lrTermFamSemBiProbeRKCanon_eta_lam
#print axioms lrTermFamSemBiProbeRKCanon_eta_bvarSpine
#print axioms lrTermFamSemBiProbeRKCanon_eta_ctorSpine
#print axioms lrTermFamSemBiProbeRKCanon_eta_famSpine_partial
#print axioms lrTermFamSemBiProbeRKCanon_eta_of_whRedRecKCanon
#print axioms instantiateLevels_policyPi_piDomsOf_piTailOf
#print axioms domsRel_of_levelFacts
#print axioms domsRel_of_typedSpines
#print axioms convArgs_symm_domsRel_anyTail
#print axioms convArgs_trans_domsRel_anyTail
#print axioms convArgs_symm_member_of_levelFacts
#print axioms convArgs_trans_member_of_levelFacts
#print axioms convArgs_symm_member_of_typedSpines
#print axioms convArgs_trans_member_of_typedSpines
#print axioms convArgs_symm_member_of_convSpines
#print axioms convArgs_trans_member_of_convSpines
#print axioms lrTypeFamINRKCanon_diag_sort_iff
#print axioms lrTypeFamINRKCanon_diag_pi_bot_nil_iff
#print axioms lrTypeFamINRKCanon_diag_famSpine_iff
#print axioms WhFamApproxAdequateAt
#print axioms lrTypeFamINBiProbeRKCanon_diag_iff
#print axioms WhFamTermApproxAdequateAt
#print axioms lrTermFamSemBiProbeRKCanon_diag_iff
#print axioms lrTermFamSemBiProbeRKCanon_app_diag_of_letBinding
#print axioms lrTermFamSemBiProbeRKCanon_app_of_letDiag_and_subst0Congr
#print axioms polyAxDomSort
#print axioms polyAxType
#print axioms polyAxMember
#print axioms polyAxEnv
#print axioms hasTyT_polyAxType
#print axioms lift_polyAxType
#print axioms exprLevelsBounded_polyAxType
#print axioms envWfT_polyAxEnv
#print axioms polyAxEnv_members_zero
#print axioms piDomsOf_polyAxType
#print axioms piTailOf_polyAxType
#print axioms polyAxArg0
#print axioms polyAxArgs
#print axioms hasTyT_polyAxArg0
#print axioms convArgsT_polyAxArgs
#print axioms not_convArgsT_length_le_piDoms_polyAxEnv
#print axioms not_allMember_convArgsT_length_le_piDoms
#print axioms convT_piDom_of_unguarded_convArgsSymmS_polyAxEnv
#print axioms IsNonBvarNonPi
#print axioms NonBvarTail
#print axioms piTailOf_ne_pi
#print axioms isNonBvarNonPi_piTailOf_of_nonBvarTail
#print axioms isNonBvarNonPi_instantiateLevels
#print axioms isNonBvarNonPi_instantiate
#print axioms convArgsT_length_le_policyPi_of_isNonBvarNonPi
#print axioms convArgsT_length_le_piDoms_of_nonBvarTail
#print axioms nonBvarTail_of_isArity
#print axioms nonBvarTail_of_inductiveM
#print axioms convArgsT_length_le_piDoms_of_isArity
#print axioms convArgsT_length_le_piDoms_of_inductiveM
#print axioms convArgs_symm_of_nonBvarTail_levelFacts
#print axioms convArgs_trans_of_nonBvarTail_levelFacts
#print axioms FamSortReadTransport
#print axioms FamPiReadTransport
#print axioms FamSpineReadTransport
#print axioms FamObsTransport
#print axioms FamObsEquiv
#print axioms FamConvObsMotive
#print axioms FamObsConvLinks
#print axioms famSpineReadTransport_refl
#print axioms famSpineReadTransport_trans
#print axioms famObsTransport_refl
#print axioms famObsTransport_trans
#print axioms famObsEquiv_refl
#print axioms famObsEquiv_symm
#print axioms famObsEquiv_trans
#print axioms famObsEquiv_chain
#print axioms lrSCore_of_famObsTransport
#print axioms lrSCoreT_of_famObsTransport
#print axioms famProbeLink_of_famObsConvLinks
#print axioms famProbeLinkT_of_famObsConvLinks
#print axioms piProbeLinkT_of_famObsConvLinks
#print axioms piRowField_of_famObsConvLinks
#print axioms not_tyConvT_pi_sort_of_famObsConvLinks
#print axioms not_tyConvT_sort_pi_of_famObsConvLinks
#print axioms famApp_saturated_of_famObsConvLinks
#print axioms famApp_length_eq_piDomsOf_of_famObsConvLinks
#print axioms famAppRow_of_famObsConvLinks
#print axioms famRelevantSlotConv_of_famObsConvLinks
#print axioms typedRowsWf_of_allBelowScoped_famObsConvLinks
#print axioms famConvObs_refl
#print axioms famConvObs_symm
#print axioms famConvObs_trans
#print axioms famConvObs_tyConv
#print axioms famObsTransport_sorts
#print axioms famConvObs_sorts
#print axioms famObsTransport_pi
#print axioms famConvObs_pi
#print axioms famObsTransport_of_readback_imp
#print axioms famObsEquiv_of_stepR
#print axioms famObsEquiv_of_redR
#print axioms famConvObs_beta
#print axioms famObsEquiv_famSpine_of_convArgsT
#print axioms famConvObs_whStepRecKCanon_zeta
#print axioms famConvObs_whStepRecKCanon_zetaLocal
#print axioms famConvObs_whStepRecKCanon_delta
#print axioms famConvObs_whStepRecKCanon_iota
#print axioms famConvObs_whStepRecKCanon_lit
#print axioms famConvObs_whStepRecKCanon_lam
#print axioms famObsEquiv_whStepRecKCanon_trueVarSort
#print axioms famObsEquiv_whStepRecKCanon_trueVarPi
#print axioms famObsEquiv_whStepRecKCanon_trueVarFam
#print axioms famObsEquiv_whStepRecKCanon_mixAnd
#print axioms dt012_of_allBelowScoped_famObsConvLinks
#print axioms dt010_of_allBelowScoped_famObsConvLinks
#print axioms dt011_of_allBelowScoped_famObsConvLinks
#print axioms dt019_of_allBelowScoped_famObsConvLinks
#print axioms ia024_of_allBelowScoped_famObsConvLinks
#print axioms piTowerCpt
#print axioms piTowerCptT
#print axioms botPiCpt_piTowerCpt
#print axioms botFamCpt_piTowerCpt
#print axioms piTower_typed_iff
#print axioms piTower_symm
#print axioms piTower_trans
#print axioms piTower_right_diagonal
#print axioms piTower_symmT
#print axioms piTower_transT
#print axioms piTower_right_diagonalT
#print axioms piTower_pi_read
#print axioms piTower_pi_components
#print axioms piTower_step
#print axioms piTower_step_same
#print axioms piTower_pi_componentsT
#print axioms piTower_stepT
#print axioms piTower_step_sameT
#print axioms instTailPrefix
#print axioms instTelescope_policyPi
#print axioms instTelescope_policyPi_eq_of_length_eq
#print axioms instTelescope_policyPi_eq_pi_of_lt
#print axioms instTelescope_member_eq_pi_of_lt
#print axioms TelescopeConvRel
#print axioms telescopeConvRel_head
#print axioms telescopeConvRel_cons_inv
#print axioms convT_policyPi_of_telescopeConvRel
#print axioms ctxWfT_of_telescopeConvRel
#print axioms convT_subst_prefix_assumption
#print axioms telescopeConvRel_step
#print axioms telescopeConvRel_of_levelFacts
#print axioms lrSCore_piTowerCpt_of_telescopeConvRel
#print axioms lrSCoreT_piTowerCptT_of_telescopeConvRel
#print axioms lrSCore_piTowerCpt_member_of_levelFacts
#print axioms lrSCore_piTowerCpt_instMtype_diag
#print axioms lrSCoreT_piTowerCptT_instMtype_diag
#print axioms FamConvChainBelow
#print axioms FamConvChainBelow.mono
#print axioms FamConvChainBelow.append
#print axioms famConvChainBelow_const
#print axioms famConvChainBelow_app
#print axioms PiTowerLinkBelow
#print axioms PiTowerLinkBelowT
#print axioms piTowerLinkBelow_iff_typed
#print axioms PiTowerLinkBelow.mono
#print axioms PiTowerLinkBelowT.mono
#print axioms piTower_chain
#print axioms piTower_chainT
#print axioms wholeSpine_piTower_of_links
#print axioms wholeSpine_piTower_of_linksT
#print axioms wholeSpine_nodeDeclAlign_of_links
#print axioms wholeSpine_nodeDeclAlign_of_linksT
#print axioms wholeSpine_convArgsT_snoc_of_links
#print axioms wholeSpine_convArgsT_snoc_of_linksT
#print axioms eqCanonGapIdx
#print axioms eqCanonGapEqTy
#print axioms eqCanonGapCtx
#print axioms eqCanonGapMot
#print axioms eqCanonGapRedex
#print axioms eqCanonGapW
#print axioms eqCanonGapCtx_wf
#print axioms whStepRecKCanon_eqCanonGapRedex
#print axioms whRedRecKCanon_eqCanonGapRedex
#print axioms redR_whStepRecKCanon_eqCanonGapRedex
#print axioms semEqDIKCanon_eqCanonGapRedex
#print axioms approxDIKCanon_eqCanonGapRedex
#print axioms lrTypeFamINRKCanon_eqCanonGap
#print axioms lrTypeFamINBiRKCanon_eqCanonGap
#print axioms lrTypeFamINBiProbeRKCanon_eqCanonGap
#print axioms lrTermFamSemBiProbeRKCanon_eqCanonGap
#print axioms lrSCore_whStepRecKCanon_eqCanonGap
#print axioms lrSCore_whStepRecKCanon_eqCanonGap_symm
#print axioms lrSCoreT_whStepRecKCanon_eqCanonGap_prop
#print axioms lrSCoreT_whStepRecKCanon_eqCanonGap_sort
#print axioms famObsEquiv_whStepRecKCanon_eqCanonGap
#print axioms loopCanonCtx
#print axioms loopCanonMot
#print axioms loopCanonMin
#print axioms loopCanonRedex
#print axioms loopCanonW
#print axioms whRedRecKCanon_loopCanonRedex
#print axioms redR_whStepRecKCanon_loopCanonRedex
#print axioms semEqDIKCanon_loopCanonRedex
#print axioms lrTypeFamINBiRKCanon_loopCanon
#print axioms lrTypeFamINBiProbeRKCanon_loopCanon
#print axioms lrSCore_whStepRecKCanon_loopCanon
#print axioms lrSCoreT_whStepRecKCanon_loopCanon_prop
#print axioms lrSCoreT_whStepRecKCanon_loopCanon_sort
#print axioms famObsEquiv_whStepRecKCanon_loopCanon
#print axioms famSortReadTransport_eq_sortReadTransportT
#print axioms famPiReadTransport_eq_piReadTransportT
#print axioms famObsTransport_iff_probeTransportT_and_famSpine
#print axioms FamSpineEquiv
#print axioms famSpineEquiv_refl
#print axioms famSpineEquiv_symm
#print axioms famSpineEquiv_trans
#print axioms famObsEquiv_iff_probeEquivT_and_famSpineEquiv
#print axioms famConvObsMotive_iff_convProbeMotiveT_and_famSpineEquiv
#print axioms FamSpineConvLinks
#print axioms probeConvLinksT_of_famObsConvLinks
#print axioms famSpineConvLinks_of_famObsConvLinks
#print axioms famObsConvLinks_iff_probeConvLinksT_and_famSpineConvLinks
#print axioms famAppRow_of_probeConvLinksT_and_famSpineConvLinks
#print axioms famRelevantSlotConv_of_probeConvLinksT_and_famSpineConvLinks
#print axioms typedRowsWf_of_allBelowScoped_probeConvLinksT_and_famSpineConvLinks
#print axioms instantiateLevels_mtype_of_inductiveM_zeroArity
#print axioms famObsTransport_consts_opaque
#print axioms famObsEquiv_consts_opaque
#print axioms famObsEquiv_consts_body_of_detR
#print axioms famConvObs_whStepRecKCanon_consts
#print axioms famObsEquiv_whStepK_consts_body
#print axioms famConvObs_whStepK_consts
#print axioms constsFam_trueEnvU_conversion
#print axioms constsFam_trueEnvU_nonvacuity
#print axioms famConvObs_whStepK_beta
#print axioms famConvObs_whStepK_zeta
#print axioms famConvObs_whStepK_zetaLocal
#print axioms famConvObs_whStepK_delta
#print axioms famConvObs_whStepK_lit
#print axioms famConvObs_whStepK_lam
#print axioms famObsTransport_whStepK_native_iota_reverse
#print axioms FamNativeIotaForwardAt
#print axioms famConvObs_whStepK_iota_iff_forward
#print axioms famNativeIotaForwardAt_whStepRecKCanon
#print axioms FamFunctionNoTypeProbeAt
#print axioms FamFunctionNoTypeProbe
#print axioms FamPropNoTypeProbe
#print axioms functionNoTypeProbeAtT_of_fam
#print axioms famFunctionNoTypeProbeAt_whStepRecKCanon_lam
#print axioms famFunctionNoTypeProbeAt_whStepK_lam
#print axioms famObsTransport_of_famFunctionNoTypeProbeAt
#print axioms famObsEquiv_whStepRecKCanon_eta_iff_famFunctionNoTypeProbeAt
#print axioms famConvObs_whStepRecKCanon_eta_of_functionNoTypeProbe
#print axioms famConvObs_irr_of_local_exclusions
#print axioms famConvObs_irr_of_famPropNoTypeProbe
#print axioms FamProbeRealizedAtT
#print axioms FamTypedProbeRealizationT
#print axioms not_elT_pi_spine
#print axioms FamSatProbeCptT
#print axioms famSatProbeCptT_to_famProbeCptT
#print axioms famSatProbeCptT_sortCode
#print axioms famSatProbeCptT_spine_botVecT
#print axioms FamProbeTypingLemmaT
#print axioms famProbeTypingLemmaT_of_typingLemmaT
#print axioms famFunctionNoTypeProbe_of_typing_realization
#print axioms famPropNoTypeProbe_of_typing_realization
#print axioms famProbeRealizedAt_sort
#print axioms famProbeRealizedAt_pi
#print axioms famProbeRealizedAt_famApp
#print axioms FamAppHeadAction
#print axioms FamAppArgAction
#print axioms famConvObs_app_of_actions
#print axioms famObsEquiv_iff_of_ends
#print axioms famObsEquiv_whStepRecKCanon_app_lam_iff_subst
#print axioms famObsEquiv_whStepRecKCanon_letE_iff_subst
#print axioms FamMixedSubstEdges
#print axioms famObsEquiv_subst_of_edges
#print axioms famConvObs_whStepRecKCanon_app_lam_of_mixedSubst
#print axioms famConvObs_whStepRecKCanon_letE_of_mixedSubst
#print axioms famMixedSubstEdges_refl
#print axioms famMixedSubstEdges_lift
#print axioms famAppHeadAction_refl
#print axioms famAppArgAction_whStepRecKCanon_lam_lift
#print axioms famObsEquiv_famSpine_partial
#print axioms famObsEquiv_famSpine_step_app_partial
#print axioms famObsEquiv_famSpine_step_app_saturated
#print axioms famObsConvLinks_whStepRecKCanon_of_four_ports
#print axioms semEqDI_wEx
#print axioms rigidConst_exEnv_zero
#print axioms approxDI_exFieldVal
#print axioms approxDI_exRhs
#print axioms approxDI_exLhs
#print axioms whStepRecKCanon_wEx
#print axioms whRedRecKCanon_wEx_rhs_to_fieldVal
#print axioms whRedRecKCanon_wEx_to_fieldVal
#print axioms approxDIKCanon_exLhs
#print axioms approxDIKCanon_exRhs
#print axioms elT_exEnv_famApp_bot
#print axioms hasTyT_famApp_both_of_levelFacts_convArgsT
#print axioms SpineClauseSL
#print axioms spineClauseSL_of_nonBvarTail
#print axioms spineClauseSL_symm
#print axioms spineClauseSL_trans
#print axioms spineClauseSL_not_sort
#print axioms LRSCoreSL
#print axioms LRSSL
#print axioms lrSCoreSL_bot
#print axioms lrSCoreSL_prop_iff
#print axioms lrSCoreSL_sort_iff
#print axioms lrSCoreSL_prop_iff_sort
#print axioms lrSCoreSL_sortCode_iff
#print axioms lrSCoreSL_spine_iff
#print axioms lrSCoreSL_sortIdx_irrel
#print axioms piProbeSL_iff_lrSCoreT
#print axioms piProbeSL_iff_lrSCore
#print axioms famProbeSL_iff_lrSCoreT
#print axioms lrSCoreSL_famProbe_symm
#print axioms lrSCoreSL_famProbe_trans
#print axioms IrrelAtSL
#print axioms SymmTmAtSL
#print axioms TransTmAtSL
#print axioms SymmTyAtSL
#print axioms TransTyAtSL
#print axioms symmTy_stepSL
#print axioms transTy_stepSL
#print axioms lrSCoreSL_spine_data_of_tyIdx
#print axioms irrel_stepSL
#print axioms symmTm_stepSL
#print axioms transTm_stepSL
#print axioms typedPERSL_of_envWfT
#print axioms lrSCoreSL_irrel_of_envWfT
#print axioms lrSCoreSL_symm_of_envWfT
#print axioms lrSCoreSL_trans_of_envWfT
#print axioms lrSCoreSL_symm_tm_of_envWfT
#print axioms lrSCoreSL_trans_tm_of_envWfT
#print axioms lrSSL_symm_of_envWfT
#print axioms lrSSL_trans_of_envWfT
#print axioms lrSSL_symm_tm_of_envWfT
#print axioms lrSSL_trans_tm_of_envWfT
#print axioms sortRead_of_lrSCoreSL_left
#print axioms piRead_of_lrSCoreSL_left
#print axioms piRead_of_lrSCoreT_left
#print axioms famSpineRead_of_lrSCoreSL_left
#print axioms famSpineRead_of_lrSCoreT_sort
#print axioms famObsTransport_of_lrSCoreSL_probes
#print axioms famObsEquiv_of_lrSCoreSL_probes
#print axioms famObsTransport_of_lrSCoreT_probes
#print axioms lrSCoreSL_app_of_lambda_demand
#print axioms lrSCoreT_app_of_lambda_demand
#print axioms not_redR_sort_of_wholeSpine_lt
#print axioms lrSCoreSL_app_of_famSpine_step
#print axioms lrSCoreSL_app_of_famSpine_syntactic
#print axioms lrSCoreSL_app_of_approxT_famProbe
#print axioms famObsEquiv_app_of_lrSCoreSL
#print axioms famAppHeadAction_of_lrSCoreSL
#print axioms famAppArgAction_of_lrSCoreSL
#print axioms FamModelProbeAtSubst
#print axioms famModelProbeAtSubst_id_of_realized
#print axioms famObsEquiv_of_substRelation_lrSCoreSL
#print axioms famBodyAtValue_of_lrSCoreSL
#print axioms famValueInBody_of_lrSCoreSL
#print axioms famMixedSubstEdges_of_lrSCoreSL
#print axioms FamProbeAdapterInputsRKCanon
#print axioms famObsConvLinks_whStepRecKCanon_of_adapterInputs
#print axioms piRowField_of_whStepRecKCanon_adapterInputs
#print axioms famAppRow_of_whStepRecKCanon_adapterInputs
#print axioms famRelevantSlotConv_of_whStepRecKCanon_adapterInputs
#print axioms typedRowsWf_of_allBelowScoped_whStepRecKCanon_adapterInputs
#print axioms lrSCoreSL_whStepRecKCanon_trueVarSort
#print axioms lrSCoreSL_whStepRecKCanon_trueVarPi
#print axioms lrSCoreSL_whStepRecKCanon_trueVarFam
#print axioms lrSCoreSL_whStepRecKCanon_mixAnd
#print axioms lrSCoreSL_whStepRecKCanon_eqCanonGap_sort
#print axioms lrSCoreSL_whStepRecKCanon_loopCanon_sort
#print axioms famLevelsBounded_replicate_zero
#print axioms rigidConst_of_inductiveM_noBody
#print axioms not_typingLemmaT_of_inductiveM_noBody_posArity
#print axioms not_typingLemmaT_of_inductiveM_posArity
#print axioms not_typingLemmaT_andEnvU
#print axioms not_typingLemmaT_exEnv
#print axioms not_typingLemmaT_eqEnvT
#print axioms famCexIdLam
#print axioms famCexIdPi
#print axioms famCexIdLamCpt
#print axioms hasTyT_famCexIdLam
#print axioms approxT_famCexIdLam_cpt
#print axioms not_elT_famCexIdPi_cpt
#print axioms not_typingLemmaT_all
#print axioms not_famProbeCptT_lam
#print axioms not_famSatProbeCptT_lam
#print axioms not_famSatProbeCptT_spine_of_length_ne
#print axioms not_famProbeCptT_spine_of_not_inductiveM
#print axioms not_famSatProbeCptT_spine_of_not_inductiveM
#print axioms elT_pi_iff_eq_bot_of_famProbeCptT
#print axioms isPropCT_pi_bot_nil
#print axioms tyCodeCT_pi_bot_nil
#print axioms ctyS_pi_bot_nil_sortCode
#print axioms elT_sort_pi_bot_nil
#print axioms famProbeTyping_at_sort
#print axioms famProbeTyping_at_pi
#print axioms famProbeTyping_at_lam
#print axioms famProbeTyping_at_famApp_unsaturated
#print axioms famProbeTyping_at_famApp_allArity
#print axioms famProbeTyping_at_nonInductive_rigidSpine
#print axioms famProbeTyping_at_bvarSpine_of_lookupValue_none
#print axioms not_redR_pi_of_normal
#print axioms spineClauseSL_not_pi
#print axioms SpineClauseSLT
#print axioms spineClauseSLT_symm
#print axioms spineClauseSLT_trans
#print axioms spineClauseSLT_iff_spineClauseSL_of_not_pi
#print axioms spineClauseSLT_iff_spineClauseSL_of_sort
#print axioms LRSCoreSLT
#print axioms LRSSLT
#print axioms lrSCoreSLT_bot
#print axioms lrSCoreSLT_prop_iff
#print axioms lrSCoreSLT_sort_iff
#print axioms lrSCoreSLT_sortCode_iff
#print axioms lrSCoreSLT_spine_iff
#print axioms lrSCoreSLT_sortIdx_irrel
#print axioms piProbeSLT_iff_lrSCoreSL
#print axioms piProbeSLT_iff_lrSCore
#print axioms famProbeSLT_iff_lrSCoreSL_of_not_pi
#print axioms famProbeSLT_iff_lrSCoreSL_of_sort
#print axioms lrSCoreSLT_famProbe_symm
#print axioms lrSCoreSLT_famProbe_trans
#print axioms not_lrSCoreSLT_nonInductive_at_pi
#print axioms not_lrSCoreSLT_satSpine_at_pi
#print axioms lrSCoreSLT_satProbe_at_pi_iff_eq_bot
#print axioms IrrelAtSLT
#print axioms SymmTmAtSLT
#print axioms TransTmAtSLT
#print axioms SymmTyAtSLT
#print axioms TransTyAtSLT
#print axioms symmTy_stepSLT
#print axioms transTy_stepSLT
#print axioms lrSCoreSLT_spine_data_of_tyIdx
#print axioms irrel_stepSLT
#print axioms symmTm_stepSLT
#print axioms transTm_stepSLT
#print axioms typedPERSLT_of_envWfT
#print axioms lrSCoreSLT_irrel_of_envWfT
#print axioms lrSCoreSLT_symm_of_envWfT
#print axioms lrSCoreSLT_trans_of_envWfT
#print axioms lrSCoreSLT_symm_tm_of_envWfT
#print axioms lrSCoreSLT_trans_tm_of_envWfT
#print axioms lrSSLT_symm_of_envWfT
#print axioms lrSSLT_trans_of_envWfT
#print axioms lrSSLT_symm_tm_of_envWfT
#print axioms lrSSLT_trans_tm_of_envWfT
#print axioms famObsTransport_of_lrSCoreSLT_probes
#print axioms famObsEquiv_of_lrSCoreSLT_probes
#print axioms lrSCoreSLT_app_of_lambda_demand
#print axioms lrSCoreSLT_app_of_famSpine_step
#print axioms IsSemNoSortPropRecKCanon
#print axioms not_approxDIKCanon_pi_sort
#print axioms not_approxDIKCanon_famApp_sort
#print axioms not_approxDIKCanon_bvarSpine_sort
#print axioms isSemNoSortPropRecKCanon_of_isSemRigidPropRecKCanon
#print axioms isSemNoSortPropRecKCanon_bvarSpine
#print axioms isSemNoSortPropRecKCanon_bvar
#print axioms not_isSemNoSortPropRecKCanon_sort
#print axioms not_isSemNoSortPropRecKCanon_of_whRed_sort
#print axioms isSemNoSortPropRecKCanon_transport_of_typeRel
#print axioms isSemNoSortPropRecKCanon_weaken
#print axioms LRTermFamNoSortRKCanon
#print axioms lrTermFamNoSortRKCanon_bot
#print axioms lrTermFamNoSortRKCanon_of_ne_bot_iff
#print axioms lrTermFamNoSortRKCanon_of_isSemNoSortPropRecKCanon
#print axioms lrTermFamNoSortRKCanon_of_lrTermFamSemRKCanon
#print axioms lrTermFamNoSortRKCanon_whRed_sort_iff_lrTypeFamINRKCanon
#print axioms lrTermFamNoSortRKCanon_sort_iff_lrTypeFamINRKCanon
#print axioms lrTermFamNoSortRKCanon_symm_of_envWfT
#print axioms lrTermFamNoSortRKCanon_trans_of_envWfT
#print axioms lrTermFamNoSortRKCanon_transport_of_typeRel
#print axioms LRTermFamNoSortBiProbeRKCanon
#print axioms lrTermFamNoSortBiProbeRKCanon_of_lrTermFamSemBiProbeRKCanon
#print axioms lrTermFamNoSortBiProbeRKCanon_whRed_sort_iff
#print axioms lrTermFamNoSortBiProbeRKCanon_sort_iff
#print axioms lrTermFamNoSortBiProbeRKCanon_symm_of_envWfT
#print axioms lrTermFamNoSortBiProbeRKCanon_trans_of_envWfT
#print axioms lrTermFamNoSortBiProbeRKCanon_transport_of_typeRel
#print axioms lrTermFamNoSortBiProbeRKCanon_irr_of_not_approx_sort
#print axioms lrTermFamNoSortBiProbeRKCanon_irr_bvarSpine
#print axioms lrTermFamNoSortBiProbeRKCanon_irr_bvar
#print axioms levelCongrT_of_envWfT
#print axioms convT_piDom_of_convArgsSymmS_polyAxEnv
#print axioms lrSCoreS_sortCode_iff
#print axioms spineClauseS_inductiveM_sort_symm
#print axioms spineClauseS_inductiveM_sort_trans
#print axioms famProbeS_symm
#print axioms famProbeS_trans
#print axioms famProbeS_right_diag
#print axioms piTowerS_iff
#print axioms piTowerS_symm
#print axioms piTowerS_trans
#print axioms piTowerS_right_diagonal
#print axioms piTowerS_pi_components
#print axioms piTowerS_step
#print axioms piTowerS_step_same
#print axioms famSpineRead_of_lrSCoreS_sort
#print axioms lrSCoreS_famApp_components
#print axioms lrSCoreS_famApp_of_components
#print axioms lrSCoreS_famApp_self
#print axioms lrSCoreS_sort_self
#print axioms lrSCoreS_pi_self_of_hasTyT
#print axioms FamProbeLinkS
#print axioms famProbe_chainS
#print axioms piRowField_of_famProbeLinkS
#print axioms not_tyConvT_pi_sort_of_famProbeLinkS
#print axioms not_tyConvT_sort_pi_of_famProbeLinkS
#print axioms famApp_saturated_of_famProbeLinkS
#print axioms famApp_length_eq_piDomsOf_of_famProbeLinkS
#print axioms famAppRow_of_famProbeLinkS
#print axioms famRelevantSlotConv_of_famProbeLinkS
#print axioms typedRowsWf_of_allBelowScoped_famProbeLinkS
#print axioms famObsTransport_of_lrSCoreS_probes
#print axioms famObsEquiv_of_lrSCoreS_probes
#print axioms ZetaStepSubst
#print axioms zetaStepSubst_id
#print axioms zetaStepSubst_shiftAt_zero
#print axioms typedSubstT_shiftAt_zero
#print axioms convSubstT_refl_of_typedSubstT
#print axioms fundTyAt_lift
#print axioms relSubstAtT_bot_of_zetaStep
#print axioms relSubstIdT_bot_of_fundamentalSAtT
#print axioms relSubstTypedAtT_bot_id_of_fundamentalSAtT
#print axioms relSubstAtT_ctxEnvT_of_zetaStep
#print axioms relSubstIdT_ctxEnvT_of_fundamentalSAtT
#print axioms fundConvAt_bot_of_fundamentalSAtT
#print axioms fundTyAt_bot_of_fundamentalSAtT
#print axioms fundConvAt_ctxEnvT_of_fundamentalSAtT
#print axioms fundTyAt_ctxEnvT_of_fundamentalSAtT
#print axioms convT_pi_inj_of_fundamentalSAtT
#print axioms convT_famApp_inj_of_fundamentalSAtT
#print axioms convT_famApp_relevantSlotConv_of_fundamentalSAtT
#print axioms famProbeLinkS_of_fundamentalSAtT_realization
#print axioms piRowField_of_fundamentalSAtT_realization
#print axioms famAppRow_of_fundamentalSAtT_realization
#print axioms famRelevantSlotConv_of_fundamentalSAtT_realization
#print axioms typedRowsWf_of_allBelowScoped_fundamentalSAtT_realization
#print axioms not_typingLemmaEnvT_all
#print axioms not_envTypedAtT_ctxEnvT_letCex
#print axioms PiTowerLinkBelowS
#print axioms piTowerLinkBelowS_iff
#print axioms PiTowerLinkBelowS.mono
#print axioms lrSCoreS_app_of_lambda_demand
#print axioms lrSCoreS_app_of_famSpine_step
#print axioms lrSCoreS_app_of_famSpine_syntactic
#print axioms lrSCoreS_app_of_approxT_famProbe
#print axioms lrSCoreS_whStepRecKCanon_trueVarSort
#print axioms lrSCoreS_whStepRecKCanon_trueVarPi
#print axioms lrSCoreS_whStepRecKCanon_trueVarFam
#print axioms lrSCoreS_whStepRecKCanon_mixAnd
#print axioms lrSCoreS_whStepRecKCanon_eqCanonGap_sort
#print axioms lrSCoreS_whStepRecKCanon_loopCanon_sort

end Rcic.Declarative.NativeValleys.FamModelAudit
