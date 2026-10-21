import rcic.RcicNativePiModelDeltaIotaTerm
import rcic.RcicNativePiModelLRTermDSubst
import rcic.RcicCensusWallsForall
import rcic.RcicPiModelInversion

/-!
# RcicNativePiModelDeltaIotaConv — Constructor-by-Constructor `HasTyT` / `ConvT` Clauses, `envWfT` Member Trichotomy, `let`-Substitution Stability, and Bidirectional `LRTermDBiDI`

Builds on `RcicNativePiModelDeltaIota` (#7656), `RcicNativePiModelDeltaIotaTerm` (#7657), and
`RcicNativePiModelLRTermDSubst` (#7655/#7663). All constructions are concrete `def` / `inductive` /
`theorem` declarations; zero `structure` or `class` declarations are introduced.

## Summary of Main Results

1. **§1. Admitted Obstructions on `HasTyT.const` and `ConvT.consts` in Raw `ApproxI` vs
   Unconditional `EnvWfT` Trichotomy and Repair in `ApproxDI`:**
   * Concrete well-formed environment `defIdEnv` (`defIdEnvWfT : EnvWfT defIdEnv`) with transparent
     definition `const 0 : Sort 0 → Sort 0 := λ (x : Sort 0), x` (`hasTyT_defIdEnv_const0`).
   * **Admitted Obstruction (`not_lrTermDCore_defIdEnv_const0_spine0`,
     `not_lrTermS_defIdEnv_const0_spine0`, `not_lrTermD_defIdEnv_const0_spine0_of_sortRow`):**
     In raw `ApproxI`, `ApproxI EnvI.bot (.const 0 []) (.spine 0 [])` holds (`FirstOrderCpt (.spine 0 [])`),
     yet in `defIdEnv`, `.const 0 []` steps by `WhStep.delta` to `.lam (.sort .zero) (.bvar 0)`, so no
     weak-head reduct of `.const 0 []` is a `WhNormal` constant spine `foldApps (.const 0 ls₁) args₁`.
     Consequently, `HasTyT.const` and `ConvT.consts` fail in raw `ApproxI` at `.spine 0 []` for both
     `LRTermDCore` and `LRTermS` (unconditionally for every `n : Nat`) and for `LRTermD` under `SortRow`.
   * **Unconditional `EnvWfT` Member Trichotomy and `ApproxDI` Repair:**
     - `rigidConst_body_none_of_envWfT` & `ctor_body_none_of_envWfT`: in any `EnvWfT E`, every
       `RigidConst E r` (and in particular every constructor) has `m.body = none` and hence is
       weak-head normal (`whNormal_const_of_rigidConst`).
     - `envWfT_member_trichotomy`: for every `E` with `EnvWfT E` and `E.members r = some m`,
       either `(RigidConst E r ∧ m.body = none)`, `(m.mclass = .recursorM ∧ m.body = none)`, or
       `(∃ b, m.body = some b ∧ DeltaConst E r m b ∧ exprClosedAt 0 b = true)`.
     - `lrTermDCore_rigidConst_consts`, `lrTermD_rigidConst_consts`, `lrTermSDI_rigidConst_consts`:
       across **all compacts `u : CptI`** in `ApproxDI E EnvI.bot (.const r ls) u`, `HasTyT.const`
       and `ConvT.consts` hold unconditionally for every `RigidConst E r` at `EnvWfT E`.
     - Positive verification on `defIdEnv` in `ApproxDI`: `not_approxDI_defIdEnv_const0_spine0`,
       `approxDI_defIdEnv_const0_iff`, `lrTermD_defIdEnv_const0_botPiCpt`, and
       `lrTermD_defIdEnv_const0_lam_nil`.

2. **§2. Full `LRTermD` Assumption/Let-Substitution Stability on `BotPiCpt` & Discharging
   `RcicNativePiModelLRTermDSubst`'s (`#7655`) Open `hι` and `hns` Premises:**
   * Side-condition-free `LRTermD` weakening and assumption-substitution stability on `BotPiCpt`:
     `lrTermD_weaken_botPiCpt`, `lrTermD_weaken0_botPiCpt`, `lrTermD_subst_botPiCpt_of_sortRow`,
     `lrTermD_subst0_botPiCpt_of_sortRow`, `lrTermD_subst_botPiCpt_of_botDI`,
     `lrTermD_subst0_botPiCpt_of_botDI`.
   * Full `let`-substitution (`letBinding` / `substRemove`) stability on `BotPiCpt` for `LRTermS`,
     `LRTermSDI`, `LRTermDCore`, and `LRTermD`:
     `lrTermS_substLet_botPiCpt`, `lrTermS_substLet0_botPiCpt`, `lrTermSDI_substLet_botPiCpt`,
     `lrTermSDI_substLet0_botPiCpt`, `lrTermDCore_substLet_botPiCpt`, `lrTermDCore_substLet0_botPiCpt`,
     `lrTermD_substLet_botPiCpt_of_sortRow`, `lrTermD_substLet0_botPiCpt_of_sortRow`,
     `lrTermD_substLet_botPiCpt_of_botDI`, `lrTermD_substLet0_botPiCpt_of_botDI`.
   * Direct discharge of `RcicNativePiModelLRTermDSubst`'s (`#7655`/`#7663`) open `hι` and `hns`
     hypotheses: `whStepD_instantiate_of_envClosed`, `whRedD_instantiate_of_envClosed`,
     `lrTermDCore_sort_subst_of_envClosed`, `fundamentalTermDIS_of_envClosed`,
     `fundamentalTermDIS_typed_of_sortRow`, `fundamentalTermDIS_typed_of_botDI`.

3. **§3. Structural `BotPiCpt` Exclusions in `ApproxDI` and `LRTermDCore` Reverse Adequacy:**
   * Structural `BotPiCpt` collapse to `.bot`: `not_botPiCpt_curryStep`,
     `approxDI_lam_botPiCpt_eq_bot`, `approxDI_rigidConst_botPiCpt_eq_bot`,
     `approxDI_recursor_botPiCpt_eq_bot`, `approxDI_const_body_none_botPiCpt_eq_bot`,
     `approxDI_foldApps_rigidConst_botPiCpt_eq_bot`.
   * `lrTermDCore_botPiCpt_forces_sort` and `approxDI_of_lrTermDCore_botPiCpt`: on any `BotPiCpt c`
     with `c ≠ .bot`, `LRTermDCore E n Γ M M' A c` implies `EnvWfT E → ApproxDI E EnvI.bot M c ∧
     ApproxDI E EnvI.bot M' c` (eliminating `TypeSoundness` from `ConvT.trans` at the term level!).
   * `not_lrTermDCore_at_pi_of_botPiCpt_ne_bot` and `lrTermD_at_pi_of_botPiCpt`: on any `BotPiCpt c`,
     `LRTermD E n Γ M M' (.pi A B) c` implies `c = .bot ∨ IsPropTyI E n Γ (.pi A B)` and hence
     `LRTermD E n Γ N N' (.pi A B) c` for **all** `N, N' : Expr Nat`.

4. **§4. Constructor-by-Constructor `HasTyT` / `ConvT` Clauses for `FundamentalTermBotDI` and
   Bidirectional `LRTermDBiDI`:**
   * Individual `HasTyT` and `ConvT` constructor theorems for `FundamentalTermBotDI`:
     `fundTermBotDI_sort`, `fundTermBotDI_bvar`, `fundTermBotDI_lam`,
     `fundTermBotDI_const_of_body_none`, `fundTermBotDI_rigidConst`, `fundTermBotDI_recursor`,
     `fundTermBotDI_deltaConst`, `fundTermBotDI_pi` (closing directly at `EnvI.bot` via
     `approxDI_cons_botDemand_bot_iff` without substitution induction!), `fundTermBotDI_lit`,
     `fundTermBotDI_letE`, `fundTermBotDI_conv`, `fundConvBotDI_refl`,
     `fundConvBotDI_trans` (**without `TypeSoundness` or `LRTermIndexTransport`**!),
     `fundConvBotDI_beta`, `fundConvBotDI_zeta`, `fundConvBotDI_zetaLocal` (unconditional!),
     `fundConvBotDI_delta`, `fundConvBotDI_iota`, `fundConvBotDI_lit`,
     `fundConvBotDI_lam` (unconditional!), `fundConvBotDI_pi` (direct at `EnvI.bot`!),
     `fundConvBotDI_letE`, `fundConvBotDI_sorts`, `fundConvBotDI_consts_of_body_none`,
     `fundConvBotDI_rigidConsts`, `fundConvBotDI_recursorConsts`, `fundConvBotDI_deltaConsts`,
     `fundConvBotDI_eta` (unconditional!), `fundConvBotDI_irr_of_sortRow`,
     `fundConvBotDI_irr_of_botDI`.
   * Bidirectional `LRTermDBiDI`: `lrTermDBiDI_symm` and `lrTermDBiDI_trans` (both unconditional at
     `EnvWfT E` with **no `TypeSoundness`** and **no index transport**), constructor clauses
     including `lrTermDBiDI_eta` (from `f`'s diagonal!), `FundamentalTermBiBotDI`, and
     `piRow_of_fundamentalTermBiBotDI`.

5. **§5. Vacuity Teeth on Un-Restricted Contexts at `zetaLocalSortCtx` (`W-ZETALOCAL`) vs
   Repaired Let-Free `BotPiCpt` Supplies (`LetFreeCtx`, `FundamentalLRINBotDI_letFree`,
   `FundamentalTermBotDI_letFree`, `FundamentalTermBiBotDI_letFree`):**
   * Proves `not_lrTypeIN_zetaLocalSortCtx_symm`, `not_lrTypeINBiDI_zetaLocalSortCtx`,
     `not_lrTermD_zetaLocalSortCtx_symm`, `not_lrTermDBiDI_zetaLocalSortCtx`,
     `not_fundamentalLRINBotDI_zetaLocal`, `not_fundamentalTermBotDI_zetaLocal`, and
     `not_fundamentalTermBiBotDI_zetaLocal`: in `zetaLocalSortCtx`, `ConvT.symm (.zetaLocal ...)`
     converts `.sort .zero` to `.bvar 0`, which is `WhNormal E`, refuting all context-free
     `WhRed E` / `EnvI.bot` fundamental-lemma interfaces on contexts containing `.letBinding`.
   * Defines `LetFreeCtx Γ` (`∀ i, lookupValue Γ i = none`), proves its structural closure
     (`letFreeCtx_nil`, `letFreeCtx_assumption`, `letFreeCtx_tail`, `not_letFreeCtx_letBinding`,
     `letFreeCtx_substRemove`), proves that `ConvT.zetaLocal` is vacuously sound on `LetFreeCtx Γ`
     (`lrTypeINBiDI_zetaLocal_letFree`, `lrTermDBiDI_zetaLocal_letFree`), and defines the repaired
     let-free supplies `FundamentalLRINBotDI_letFree`, `FundamentalTermBotDI_letFree`, and
     `FundamentalTermBiBotDI_letFree`.

6. **§6. Typed Let-Expansion (`expandLetAt`, `hasTyT_conv_expandLetAt`), Context-Conversion of
   `insertAt (.letBinding t w0) j (substRemove w0 j Γ)`, and Lifting Let-Free `piRow` / `sortRow`
   to Arbitrary Contexts (`piRow_of_letFree_piRow`, `sortRow_of_letFree_sortRow`):**
   * Defines `expandLetAt w0 j e := lift j 1 (instantiate j (lift 0 j w0) e)` and proves the
     9-constructor structural induction `hasTyT_conv_expandLetAt : HasTyT E n Γ e A →
     Γ[j]? = some (.letBinding t w0) → HasTyT E n Γ (lift 0 (j + 1) w0) (lift 0 (j + 1) t) →
     ConvT E n Γ e (expandLetAt w0 j e) A` (using `ConvT.zetaLocal` at `i = j` and `ConvT.refl` at
     `i ≠ j`).
   * Defines `letCount : LCtx → Nat` and `FirstLetAt : LCtx → Nat → Expr Nat → Expr Nat → Type`,
     proves `ctxWfT_substRemove_of_firstLetAt`, `ctxConvT_insertAt_substRemove_of_firstLetAt`,
     and `tyConvT_of_substRemove_firstLetAt`, and proves **`piRow_of_letFree_piRow`** and
     **`sortRow_of_letFree_sortRow`**: by induction on `letCount Γ`, `piRow` and `sortRow` on
     `LetFreeCtx` contexts lift to **all** well-formed contexts `CtxWfT E n Γ` (including
     `zetaLocalSortCtx`), yielding `piRow_of_fundamentalLRINBotDI_letFree`,
     `piRow_of_fundamentalTermBotDI_letFree`, and `piRow_of_fundamentalTermBiBotDI_letFree`.

7. **§7. Obstruction on Un-Guarded Substitution-Style Π-Clause (`polyPiType` at `polyPiTypeCpt`) &
   The `ConvT`-Guarded Substitution-Style Logical Relation (`LRTermDSubCore` / `LRTermDSub`):**
   * Proves that on `polyPiType = .pi (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))` at the
     `BotPiCpt` compact `polyPiTypeCpt = .pi .bot [([], .pi .bot [])]`, an un-guarded
     substitution-style Π-clause (`∀ N N', HasTyT Γ N A₁ → HasTyT Γ N' A₁ → ...` without
     `ConvT E n Γ N N' A₁`) forces `TyConvT E n [] (.pi (.sort .zero) (.sort .zero)) (.sort .zero)`
     (`tyConvT_pi_sort_of_unguarded_pi_polyPiType`).
   * Defines the `ConvT`-guarded substitution-style logical relation `LRTermDSubCore` and
     `LRTermDSub` and proves unconditional satisfaction on `idPiProp` across **all** compacts `c`
     in `ApproxDI E EnvI.bot idPiProp` (`lrTermDSubCore_idPiProp_sortStep`,
     `lrTermDSubCore_idPiProp_all`, `lrTermDSub_idPiProp_all`) as well as satisfaction on
     `polyPiType` at `polyPiTypeCpt` under `EnvWfT E` (`lrTermDSubCore_polyPiType_of_envWfT`).

8. **§8. Weak-Head Expansion, Head-Step `ConvT` Clauses, General `not_isPropTyI_pi_sort`, Full
   `closedIrrPi` Repair at `closedIrrPiCpt`, and `PiRowField` Extraction for `LRTermDSub`:**
   * Proves `lrTermDSubCore_spine_iff`, `lrTermDSubCore_lam_iff`, `lrTermDSubCore_whRed_expand`,
     `lrTermDSub_whRed_expand`, `fundConvDSub_of_whRed`, `fundConvDSub_of_whStep`,
     `fundConvDSub_beta`, `fundConvDSub_zeta`, `fundConvDSub_delta`, `fundConvDSub_iota`,
     `fundConvDSub_lit`, `fundConvDSub_zetaLocal_letFree`, and `fundConvDSub_irr_of_sortRow`.
   * Proves `convT_instantiate0_sort_of_convT` and `tyConvT_instantiate0_sort_of_convT` (showing
     that `LRTermDSubCore`'s `ConvT E n Γ N N' A₁` guard is the exact syntactic counterpart of
     instantiating `TyConvT` codomains).
   * Proves `eval_const_zero_isSome` and `not_isPropTyI_pi_sort` (`¬ IsPropTyI E n Γ (.pi A (.sort l))`
     for **every** domain `A` and sort level `l` under `SortRow`).
   * **Full Positive Repair of `closedIrrPi` at `closedIrrPiCpt` (`lrTermDSubCore_closedIrrPi_of_sortRow`,
     `lrTermDSub_closedIrrPi_of_sortRow`):** Proves that in any `EnvWfT E` and `CtxWfT E n Γ` under
     `SortRow`, `LRTermDSubCore E n Γ closedIrrPiL closedIrrPiR (.sort w) closedIrrPiCpt` and
     `LRTermDSub E n Γ closedIrrPiL closedIrrPiR (.sort w) closedIrrPiCpt` hold (repairing
     `not_lrTypeIN_closedIrrPi`, `not_lrTermDCore_closedIrrPi`, and `not_lrTermD_closedIrrPi`).
   * Proves `lrTypeIN_pi_bot_nil_of_lrTermDSubCore` and `lrTypeIN_pi_bot_nil_of_lrTermDSub`, defines
     `FundamentalTermDSubBotDI_letFree`, and derives `piRow_letFree_of_fundamentalTermDSubBotDI_letFree`
     and `piRow_of_fundamentalTermDSubBotDI_letFree`.

9. **§9. Recursor-Determinism from `recRef` Alone (`iotaWitnessS_same_recRef`,
   `iotaWitnessS_unique_of_nMinors_one`), `W-K` Characterization of `ApproxDI` on `trueEnvU` &
   `andEnvU` (Compiling `#7670`'s Open Observation), and `W-K` Teeth on `LetFreeCtx` Supplies:**
   * Proves `iotaWitnessS_same_recRef` (from `w₁.recRef = w₂.recRef` alone via `hmajorTy`,
     `w₁.familyRef = w₂.familyRef`, `w₁.nMinors = w₂.nMinors`, `w₁.nindices = w₂.nindices`, and
     `w₁.nparams = w₂.nparams`) and `iotaWitnessS_unique_of_nMinors_one` (for single-constructor
     inductives `w₁.nMinors = 1`, `w₁.recRef = w₂.recRef` uniquely determines `ctorRef`,
     `fields.length`, `shapes`, and `schema`), plus `iotaWitnessS_of_iotaWitness_envWfT`.
   * Proves `approxDI_recursor_elim_no_ctor_inv` and `approxDI_recursor_elim_bvar_bot_inv`
     (compiling `#7670`'s uncompiled observation: in `ApproxDI E EnvI.bot`, any recursor elimination
     `recCall (.const w.recRef ls) pre (.bvar i)` at an open variable major only has compact `.bot`),
     refuting `ApproxDI`, `SemEqDI`, `PEqDI`, `MajorStableDI`, and `DomTyped` at `EnvI.bot` on
     `trueEnvU_kRecVar` (`not_approxDI_trueEnvU_kRecVar_sort`, `not_semEqDI_trueEnvU_kRecVar_sort`,
     `not_pEqDI_trueEnvU_kRecVar_sort`, `not_majorStableDI_trueEnvU`, `not_domTyped_trueEnvU_recElim`)
     and on `mixAndRedex` (`not_approxDI_andEnvU_mixAndRedex_pi`,
     `not_semEqDI_andEnvU_mixAndRedex_mixPi`), while proving positive `SemEqDI` satisfaction on the
     closed β-redex major `trueEnvU_kRecIdTt` (`semEqDI_trueEnvU_kRecIdTt`, where `WhRed` is stuck)
     and under canonical-constructor valuations (`semEqDI_trueEnvU_kRecVar_canonEnv`,
     `semEqDI_andEnvU_mixAndRedex_canonEnv`).
   * Proves `W-K` vacuity teeth on `FundamentalLRINBotDI_letFree`, `FundamentalTermBotDI_letFree`,
     `FundamentalTermBiBotDI_letFree`, and `FundamentalTermDSubBotDI_letFree` at both `trueEnvU`
     and `andEnvU`.

10. **§10. Concrete K-Aware $\delta/\iota$ Lower-Ideal Model `ApproxDIK` (`denDIK`, `SemEqDIK`,
    `PEqDIK`), Compiled `ConvT`-Soundness of Proposition-Major Reduction (`convT_of_pmajor`,
    `convT_of_pmajor_constMotive`), and K-Aware Π Readback (`WhStepPiK`, `WhRedPiK`,
    `LRTypeINPiK`, `FundamentalLRINBotDIK_letFree`):**
    * Defines `ApproxDIK E ρ e c` with the proposition-major recursor clause `recursorK` for
      single-constructor `Prop` inductives (`piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1`,
      `∀ u ∈ u_maj, IsBotC u`, and field demands `List.replicate w.fields.length []`), proves its
      full lower-ideal substitution/lifting algebra and canonical $\iota$ soundness `approxDIK_iotaS`
      (using `iotaWitnessS_unique_of_nMinors_one`), proves unconditional open/closed proof-major $K$
      soundness for 0-field `Prop` inductives (`semEqDIK_k_zeroFields`, `semEqDIK_trueEnvU_kRec_all`
      for **every** `x : Expr Nat` and `ρ : EnvI`), and proves unconditional fieldful $K$ soundness
      for `⊥`-approximated fields (`semEqDIK_k_botFields`, `semEqDIK_andEnvU_mixAndRedex_mixPi`).
    * Compiles the `ConvT`-soundness of proposition-major ι reduction (`convT_of_pmajor` and
      `convT_of_pmajor_constMotive`, left uncompiled in `#7670`), defines the K-aware Π readback
      `WhStepPiK` / `WhRedPiK` and proves that every `WhStepPiK` / `WhRedPiK` step is sound in
      `ApproxDIK E EnvI.bot` (`semEqDIK_whStepPiK`, `semEqDIK_whRedPiK`), yielding soundness-free
      right-approximation extraction `approxDIK_of_lrTypeINPiK_botPiCpt`, positive satisfaction at
      all four walls (`idPiProp`, `closedIrrPi`, `trueEnvU` `kRec`, `andEnvU` `mixAndRedex`), and
      full `PiRowField E n` extraction (`piRow_of_fundamentalLRINBotDIK_letFree`).

11. **§11. `lift 0 1` Invariance & Context-Aware `ctxEnvDIK`, `LRTypeINPiK` Symmetry/Context-Conversion,
    Canonical Deterministic K-Readback `WhStepPiKCanon` / `WhRedPiKCanon` (`whDetPiKCanon_of_envWfT`),
    and `LRTypeINPiKCanon` / `LRTypeINBiDIKCanon` Transitivity & Chain Closure:**
    * Proves `approxDIK_lift0_one_iff`, `denDIK_lift0_one_eq`, and `semEqDIK_lift0_one_iff`; defines
      the context-aware K-model valuation `ctxEnvDIK E Γ`, proves `bot_le_ctxEnvDIK`,
      `ctxEnvDIK_none_bot`, `ctxEnvDIK_letFree_le_bot`, `approxDIK_ctxEnvDIK_letFree_iff`, and
      unconditional `ConvT.zetaLocal` soundness `semEqDIK_ctxEnvDIK_zetaLocal` (`lookupValue Γ i =
      some v → SemEqDIK E (ctxEnvDIK E Γ) (.bvar i) v`, pinned on `zetaLocalSortCtx`).
    * Proves `not_whRedPiK_sort_and_pi`, `lrTypeINPiK_ctx`, `lrTypeINPiK_assump_dom`, `lrTypeINPiK_symm`
      (across all compacts `c : CptI`), and `lrTypeINBiDIK_symm`.
    * Defines the canonical deterministic K-readback `WhStepPiKCanon` / `WhRedPiKCanon` (fixing
      `w.fields = List.replicate w.fields.length (.bvar 0)` in `iotaKCanon`), proves `whStepPiK_lam_false`,
      `not_whStepPiK_recursor_prefix`, `approxDIK_ctor_spine_bot`, `not_whStep_and_iotaK`,
      `iotaKCanon_det`, and **exact single-step determinism `whDetPiKCanon_of_envWfT`** at every
      `EnvWfT E`, while still reducing both 0-field `trueEnvU_kRecVar`
      (`whRedPiKCanon_trueEnvU_kRecVar_sort`) and fieldful `mixAndRedex`
      (`whRedPiKCanon_andEnvU_mixAndRedex_mixPi`).
    * Defines `LRTypeINPiKCanon` and `LRTypeINBiDIKCanon`, proves `lrTypeINPiKCanon_symm` and
      `lrTypeINPiKCanon_trans_of_envWfT` across **all** compacts `c : CptI` (with **zero** external
      `WhDet`, `TypeSoundness`, or `Diamond` hypotheses), `lrTypeINBiDIKCanon_symm`,
      `lrTypeINBiDIKCanon_trans`, `fundamentalLRINBotDIKCanon_letFree_of_links`, and
      `piRow_of_fundamentalLRINBotDIKCanon_letFree`, plus positive satisfaction on all four walls
      (`idPiProp`, `closedIrrPi`, `trueEnvU_kRecVar`, `mixAndRedex`).

12. **§12. K-Aware `ConvT`-Guarded Substitution-Style Term Logical Relation `LRTermDSubKCore` /
    `LRTermDSubK` Over `WhRedPiKCanon` and `ApproxDIK`:**
    * Defines `LRTermDSubKCore` and `LRTermDSubK` over `WhRedPiKCanon` and `LRTypeINPiKCanon`,
      combining substitution-style `ConvT`-guarded codomain instantiation with canonical deterministic
      K-readback.
    * Proves simultaneous positive satisfaction across all four concrete obstructions in one unified
      relation:
      - `W-DEMAND`: `lrTermDSubKCore_idPiProp_all`, `lrTermDSubKCore_idPiProp_sortStep`,
        `lrTermDSubK_idPiProp_all` (across all compacts in `ApproxDIK E EnvI.bot idPiProp`), and
        `lrTermDSubKCore_polyPiType_of_envWfT`.
      - `W-IrrPi`: `lrTermDSubKCore_closedIrrPi_of_sortRow` and `lrTermDSubK_closedIrrPi_of_sortRow`
        at `closedIrrPiCpt`.
      - `W-K` (0-field & fieldful): `lrTermDSubKCore_trueEnvU_kRecVar_sort`,
        `lrTermDSubK_trueEnvU_kRecVar_sort`, `lrTermDSubKCore_andEnvU_mixAndRedex_mixPi`, and
        `lrTermDSubK_andEnvU_mixAndRedex_mixPi`.
    * Proves `lrTermDSubKCore_whRedPiKCanon_expand`, `lrTermDSubK_whRedPiKCanon_expand`, head-step
      `ConvT` clauses (`fundConvDSubK_beta`, `fundConvDSubK_zeta`, `fundConvDSubK_delta`,
      `fundConvDSubK_iota`, `fundConvDSubK_lit`, `fundConvDSubK_iotaKCanon`,
      `fundConvDSubK_zetaLocal_letFree`, `fundConvDSubK_sorts`, `fundConvDSubK_irr_of_sortRow`),
      `lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubKCore`, `lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubK`,
      `FundamentalTermDSubKBotDIK_letFree`, `piRow_letFree_of_fundamentalTermDSubKBotDIK_letFree`,
      and `piRow_of_fundamentalTermDSubKBotDIK_letFree` (lifting let-free `PiRowField` to all
      `CtxWfT E n Γ` via `piRow_of_letFree_piRow`, resolving `W-ZETALOCAL`).

`closure_claim = 0`. Zero `sorry`, zero new axioms, zero `structure`/`class` declarations.
-/

namespace Rcic.Declarative.NativeValleys.PiModelDeltaIotaConvAudit

open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelIrrAudit
open Rcic.Declarative.NativeValleys.PiModelKAudit
open Rcic.Declarative.NativeValleys.PiModelTermAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaTermAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ## §1. Admitted Obstructions on `HasTyT.const` and `ConvT.consts` in Raw `ApproxI` vs
Unconditional `EnvWfT` Trichotomy and Repair in `ApproxDI` -/

/-- The checked member for `const 0 : Sort 0 → Sort 0 := λ (x : Sort 0), x`. -/
def defIdMember : CheckedMember :=
  ⟨.definitionM, 0, .pi (.sort .zero) (.sort .zero), some (.lam (.sort .zero) (.bvar 0))⟩

/-- Concrete well-formed environment with transparent definition
    `const 0 : Π (_ : Sort 0), Sort 0 := λ (x : Sort 0), x`. -/
def defIdEnv : ResolvedEnv :=
  extendEnv emptyEnv 0 defIdMember

/-- `defIdEnv` is well-formed in `EnvWfT`. -/
def defIdEnvWfT : EnvWfT defIdEnv :=
  .definition emptyEnv 0
    (.pi (.sort .zero) (.sort .zero))
    (.lam (.sort .zero) (.bvar 0))
    (.imax (.succ .zero) (.succ .zero))
    .empty rfl
    (.pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
      (.sort [] .zero) (.sort [.assumption (.sort .zero)] .zero))
    (.lam [] (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
      (.sort [] .zero) (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl))
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- In `defIdEnv`, `.const 0 []` has type `.pi (.sort .zero) (.sort .zero)` in every context `Γ`. -/
def hasTyT_defIdEnv_const0 (n : Nat) (Γ : LCtx) :
    HasTyT defIdEnv n Γ (.const 0 []) (.pi (.sort .zero) (.sort .zero)) :=
  .const Γ 0 [] defIdMember rfl rfl rfl

/-- In `defIdEnv`, `.const 0 []` weak-head steps by `WhStep.delta` to `.lam (.sort .zero) (.bvar 0)`. -/
theorem whStep_defIdEnv_const0 :
    WhStep defIdEnv (.const 0 []) (.lam (.sort .zero) (.bvar 0)) :=
  .delta (m := defIdMember) rfl rfl

/-- In `defIdEnv`, `.const 0 []` is NOT weak-head normal. -/
theorem not_whNormal_defIdEnv_const0 :
    ¬ WhNormal defIdEnv (.const 0 []) :=
  fun hn => hn _ whStep_defIdEnv_const0

/-- Any weak-head step from `.const 0 []` in `defIdEnv` produces `.lam (.sort .zero) (.bvar 0)`. -/
theorem whStep_defIdEnv_const0_unique {Y : Expr Nat}
    (h : WhStep defIdEnv (.const 0 []) Y) :
    Y = .lam (.sort .zero) (.bvar 0) :=
  (whDet_of_envWfT defIdEnvWfT h whStep_defIdEnv_const0)

/-- Any weak-head reduct of `.const 0 []` in `defIdEnv` is either `.const 0 []` or
    `.lam (.sort .zero) (.bvar 0)`. -/
theorem whRed_defIdEnv_const0_inv {Y : Expr Nat}
    (h : WhRed defIdEnv (.const 0 []) Y) :
    Y = .const 0 [] ∨ Y = .lam (.sort .zero) (.bvar 0) := by
  cases h with
  | refl => exact Or.inl rfl
  | step hs hrest =>
      have hY := whStep_defIdEnv_const0_unique hs
      subst hY
      cases hrest with
      | refl => exact Or.inr rfl
      | step hs' _ => exact (whStep_lam_false hs').elim

/-- No weak-head reduct of `.const 0 []` in `defIdEnv` is a `WhNormal` constant-headed spine
    `foldApps (.const 0 ls₁) args₁`. -/
theorem not_whRed_whNormal_foldApps_defIdEnv_const0 (ls₁ : List Level) (args₁ : List (Expr Nat))
    (hred : WhRed defIdEnv (.const 0 []) (foldApps (.const 0 ls₁) args₁))
    (hnorm : WhNormal defIdEnv (foldApps (.const 0 ls₁) args₁)) : False := by
  rcases whRed_defIdEnv_const0_inv hred with heq | heq
  · rw [heq] at hnorm
    exact not_whNormal_defIdEnv_const0 hnorm
  · have hs := congrArg appsSpine heq
    rw [appsSpine_foldApps_const] at hs
    have hs' : (Expr.const 0 ls₁, args₁) = (Expr.lam (.sort .zero) (.bvar 0), []) := hs
    rw [Prod.mk.injEq] at hs'
    exact Expr.noConfusion hs'.1

/-- **Admitted Obstruction (`HasTyT.const` / `ConvT.consts` in raw `ApproxI` for `LRTermDCore`):**
    Although `HasTyT defIdEnv n [] (.const 0 []) (.pi (.sort .zero) (.sort .zero))` and
    `ApproxI EnvI.bot (.const 0 []) (.spine 0 [])` holds (`FirstOrderCpt (.spine 0 [])`),
    `LRTermDCore defIdEnv n [] (.const 0 []) (.const 0 []) (.pi (.sort .zero) (.sort .zero)) (.spine 0 [])`
    is **unconditionally false** for every `n : Nat`. -/
theorem not_lrTermDCore_defIdEnv_const0_spine0 (n : Nat) :
    ¬ LRTermDCore defIdEnv n [] (.const 0 []) (.const 0 [])
        (.pi (.sort .zero) (.sort .zero)) (.spine 0 []) := by
  intro h
  rw [lrTermDCore_spine_iff] at h
  rcases h with ⟨⟨l, hsort⟩, _⟩ | ⟨ls₁, _, args₁, _, hred₁, _, hnorm₁, _⟩
  · exact Expr.noConfusion (whRed_pi_eq hsort)
  · exact not_whRed_whNormal_foldApps_defIdEnv_const0 ls₁ args₁ hred₁ hnorm₁

/-- **Admitted Obstruction (`HasTyT.const` / `ConvT.consts` in raw `ApproxI` for `LRTermS`):**
    `LRTermS defIdEnv n [] (.const 0 []) (.const 0 []) (.pi (.sort .zero) (.sort .zero)) (.spine 0 [])`
    is **unconditionally false** for every `n : Nat`. -/
theorem not_lrTermS_defIdEnv_const0_spine0 (n : Nat) :
    ¬ LRTermS defIdEnv n [] (.const 0 []) (.const 0 [])
        (.pi (.sort .zero) (.sort .zero)) (.spine 0 []) := by
  intro h
  rw [lrTermS_spine_iff] at h
  rcases h with ⟨⟨l, hsort⟩, _⟩ | ⟨⟨r', args', hsp⟩, _⟩
  · exact Expr.noConfusion (whRed_pi_eq hsort)
  · rcases approxI_pi_inv hsp with h0 | ⟨_, _, h0, _, _⟩ <;> cases h0

/-- **Admitted Obstruction (`HasTyT.const` / `ConvT.consts` in raw `ApproxI` for `LRTermD`):**
    Under universe consistency `hSort` (`SortRow`),
    `LRTermD defIdEnv n [] (.const 0 []) (.const 0 []) (.pi (.sort .zero) (.sort .zero)) (.spine 0 [])`
    is false, even though `ApproxI EnvI.bot (.const 0 []) (.spine 0 [])` holds. -/
theorem not_lrTermD_defIdEnv_const0_spine0_of_not_pi_sort {n : Nat}
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level},
      TyConvT defIdEnv n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂) :
    ¬ LRTermD defIdEnv n [] (.const 0 []) (.const 0 [])
        (.pi (.sort .zero) (.sort .zero)) (.spine 0 []) := by
  intro h
  rcases h with hP | hC
  · exact not_isPropTyI_pi_sort0_sort0 hSort [] hP
  · exact not_lrTermDCore_defIdEnv_const0_spine0 n hC

/-! ### Unconditional `EnvWfT` Member Trichotomy and `ApproxDI` Repair -/

/-- In any well-formed environment `EnvWfT E`, every `RigidConst E r` member has `m.body = none`
    (combining `envWfT_member_body_closed` and `not_rigidConst_of_deltaConst`). -/
theorem rigidConst_body_none_of_envWfT (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} (hrig : RigidConst E r) (hm : E.members r = some m) :
    m.body = none := by
  cases hb : m.body with
  | none => rfl
  | some b =>
      exact (not_rigidConst_of_deltaConst (envWfT_member_body_closed hW r m b hm hb).1 hrig).elim

/-- In any well-formed environment `EnvWfT E`, every constructor member (`m.mclass = .constructorM`)
    has `m.body = none`. -/
theorem ctor_body_none_of_envWfT (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hctor : m.mclass = .constructorM) :
    m.body = none :=
  rigidConst_body_none_of_envWfT hW (rigidConst_of_ctor hm hctor) hm

/-- In any well-formed environment `EnvWfT E`, every `RigidConst E r` member `.const r ls` is
    weak-head normal (`WhNormal E (.const r ls)`). -/
theorem whNormal_const_of_rigidConst (hW : EnvWfT E)
    {r : Nat} {ls : List Level} {m : CheckedMember}
    (hrig : RigidConst E r) (hm : E.members r = some m) :
    WhNormal E (.const r ls) :=
  whNormal_const_of_opaque hm (rigidConst_body_none_of_envWfT hW hrig hm)

/-- Any member `E.members r = some m` with `m.body = none` and `m.mclass ≠ .recursorM` is a
    `RigidConst E r`. -/
theorem rigidConst_of_body_none {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hb : m.body = none) (hnrec : m.mclass ≠ .recursorM) :
    RigidConst E r := by
  intro m' hm'
  have heq : m' = m := Option.some.inj (hm'.symm.trans hm)
  subst heq
  exact ⟨Or.inl hb, hnrec⟩

/-- **Unconditional `EnvWfT` Member Trichotomy:** for every `E` with `EnvWfT E` and every member
    `E.members r = some m`, `m` is either:
    1. a body-less `RigidConst E r` (axioms, inductive families, constructors),
    2. a body-less recursor (`m.mclass = .recursorM ∧ m.body = none`), or
    3. a closed `DeltaConst E r m b` (`m.body = some b ∧ exprClosedAt 0 b = true`). -/
theorem envWfT_member_trichotomy (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) :
    (RigidConst E r ∧ m.body = none) ∨
      (m.mclass = .recursorM ∧ m.body = none) ∨
      (∃ b, m.body = some b ∧ DeltaConst E r m b ∧ exprClosedAt 0 b = true) := by
  cases hb : m.body with
  | none =>
      by_cases hrec : m.mclass = .recursorM
      · exact Or.inr (Or.inl ⟨hrec, rfl⟩)
      · exact Or.inl ⟨rigidConst_of_body_none hm hb hrec, rfl⟩
  | some b =>
      obtain ⟨hd, hcl⟩ := envWfT_member_body_closed hW r m b hm hb
      exact Or.inr (Or.inr ⟨b, rfl, hd, hcl⟩)

/-- **Unconditional `ConvT.consts` / `HasTyT.const` in `ApproxDI` for `RigidConst` (`LRTermDCore`):**
    Under `EnvWfT E`, for any `RigidConst E r` with `E.members r = some m` and
    `ConvT E n Γ (.const r ls) (.const r ls') A`, `LRTermDCore E n Γ (.const r ls) (.const r ls') A u`
    holds across **every** compact `u` with `ApproxDI E EnvI.bot (.const r ls) u` (including
    `u = .spine r []`). -/
theorem lrTermDCore_rigidConst_consts (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember} {A : Expr Nat}
    (hrig : RigidConst E r) (hm : E.members r = some m)
    (hconv : ConvT E n Γ (.const r ls) (.const r ls') A)
    {u : CptI} (hu : ApproxDI E EnvI.bot (.const r ls) u) :
    LRTermDCore E n Γ (.const r ls) (.const r ls') A u := by
  rcases approxDI_rigid_const_inv hrig hu with rfl | rfl
  · exact lrTermDCore_bot _ _ _ _
  · rw [lrTermDCore_spine_iff]
    exact Or.inr ⟨ls, ls', [], [], .refl _, .refl _,
      whNormal_const_of_rigidConst hW hrig hm,
      whNormal_const_of_rigidConst hW hrig hm,
      ⟨hconv⟩, [], Nat.le_refl 0, Nat.le_refl 0, rfl,
      fun i => absurd i.isLt (Nat.not_lt_zero _)⟩

/-- **Unconditional `HasTyT.const` diagonal in `ApproxDI` for `RigidConst` (`LRTermDCore`):**
    Under `EnvWfT E`, for any `RigidConst E r` with `E.members r = some m` and
    `HasTyT E n Γ (.const r ls) A`, `LRTermDCore E n Γ (.const r ls) (.const r ls) A u`
    holds for every `u` with `ApproxDI E EnvI.bot (.const r ls) u`. -/
theorem lrTermDCore_rigidConst_diag (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {A : Expr Nat}
    (hrig : RigidConst E r) (hm : E.members r = some m)
    (hty : HasTyT E n Γ (.const r ls) A)
    {u : CptI} (hu : ApproxDI E EnvI.bot (.const r ls) u) :
    LRTermDCore E n Γ (.const r ls) (.const r ls) A u :=
  lrTermDCore_rigidConst_consts hW hrig hm (.refl Γ (.const r ls) A hty) hu

/-- **Unconditional `ConvT.consts` in `ApproxDI` for `RigidConst` (`LRTermD`):**
    Under `EnvWfT E`, `LRTermD E n Γ (.const r ls) (.const r ls') A u` holds across every
    `ApproxDI E EnvI.bot (.const r ls) u` for any `RigidConst E r`. -/
theorem lrTermD_rigidConst_consts (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember} {A : Expr Nat}
    (hrig : RigidConst E r) (hm : E.members r = some m)
    (hconv : ConvT E n Γ (.const r ls) (.const r ls') A)
    {u : CptI} (hu : ApproxDI E EnvI.bot (.const r ls) u) :
    LRTermD E n Γ (.const r ls) (.const r ls') A u :=
  Or.inr (lrTermDCore_rigidConst_consts hW hrig hm hconv hu)

/-- **Unconditional `HasTyT.const` diagonal in `ApproxDI` for `RigidConst` (`LRTermD`):**
    Under `EnvWfT E`, `LRTermD E n Γ (.const r ls) (.const r ls) A u` holds across every
    `ApproxDI E EnvI.bot (.const r ls) u` for any `RigidConst E r`. -/
theorem lrTermD_rigidConst_diag (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {A : Expr Nat}
    (hrig : RigidConst E r) (hm : E.members r = some m)
    (hty : HasTyT E n Γ (.const r ls) A)
    {u : CptI} (hu : ApproxDI E EnvI.bot (.const r ls) u) :
    LRTermD E n Γ (.const r ls) (.const r ls) A u :=
  Or.inr (lrTermDCore_rigidConst_diag hW hrig hm hty hu)

/-- **Unconditional `ConvT.consts` in `ApproxDI` for `RigidConst` (`LRTermSDI`):**
    Under `EnvWfT E`, `LRTermSDI E n Γ (.const r ls) (.const r ls') A u` holds across every
    `ApproxDI E EnvI.bot (.const r ls) u` for any `RigidConst E r` at any spine-inhabited type `A`. -/
theorem lrTermSDI_rigidConst_consts (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember} {A : Expr Nat}
    (hrig : RigidConst E r) (hm : E.members r = some m)
    (hA : ∃ r' args', ApproxDI E EnvI.bot A (.spine r' args'))
    (hconv : ConvT E n Γ (.const r ls) (.const r ls') A)
    {u : CptI} (hu : ApproxDI E EnvI.bot (.const r ls) u) :
    LRTermSDI E n Γ (.const r ls) (.const r ls') A u := by
  rcases approxDI_rigid_const_inv hrig hu with rfl | rfl
  · exact lrTermSDI_bot _ _ _ _
  · rw [lrTermSDI_spine_iff]
    exact Or.inr ⟨hA, .const r ls, .const r ls', .refl _, .refl _,
      whNormal_const_of_rigidConst hW hrig hm,
      whNormal_const_of_rigidConst hW hrig hm,
      ⟨hconv⟩⟩

/-- **Unconditional `HasTyT.const` diagonal in `ApproxDI` for `RigidConst` (`LRTermSDI`):** -/
theorem lrTermSDI_rigidConst_diag (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {A : Expr Nat}
    (hrig : RigidConst E r) (hm : E.members r = some m)
    (hA : ∃ r' args', ApproxDI E EnvI.bot A (.spine r' args'))
    (hty : HasTyT E n Γ (.const r ls) A)
    {u : CptI} (hu : ApproxDI E EnvI.bot (.const r ls) u) :
    LRTermSDI E n Γ (.const r ls) (.const r ls) A u :=
  lrTermSDI_rigidConst_consts hW hrig hm hA (.refl Γ (.const r ls) A hty) hu

/-- **Positive repair of the `defIdEnv` obstruction in `ApproxDI`:**
    In `defIdEnv`, `DeltaConst defIdEnv 0 defIdMember (.lam (.sort .zero) (.bvar 0))` holds, so
    `.spine 0 []` is **not** in `ApproxDI defIdEnv ρ (.const 0 [])`; instead, `.const 0 []` has
    the exact same approximations as `.lam (.sort .zero) (.bvar 0)`. -/
theorem deltaConst_defIdEnv_const0 :
    DeltaConst defIdEnv 0 defIdMember (.lam (.sort .zero) (.bvar 0)) :=
  ⟨rfl, rfl, by decide, by decide⟩

theorem approxDI_defIdEnv_const0_iff (ρ : EnvI) (c : CptI) :
    ApproxDI defIdEnv ρ (.const 0 []) c ↔
      ApproxDI defIdEnv EnvI.bot (.lam (.sort .zero) (.bvar 0)) c :=
  approxDI_delta_bot deltaConst_defIdEnv_const0 c

theorem not_approxDI_defIdEnv_const0_spine0 (ρ : EnvI) :
    ¬ ApproxDI defIdEnv ρ (.const 0 []) (.spine 0 []) := by
  rw [approxDI_defIdEnv_const0_iff]
  intro h
  rcases approxDI_lam_inv h with h0 | ⟨_, h0, _⟩ <;> cases h0

/-- In `defIdEnv`, `LRTermDCore` holds on `.const 0 []` at `.lam []` (and at every `BotPiCpt`
    compact in `ApproxDI defIdEnv EnvI.bot (.const 0 [])`). -/
theorem lrTermDCore_defIdEnv_const0_lam_nil (n : Nat) :
    LRTermDCore defIdEnv n [] (.const 0 []) (.const 0 [])
      (.pi (.sort .zero) (.sort .zero)) (.lam []) := by
  rw [LRTermDCore.eq_def]
  exact ⟨.sort .zero, .sort .zero, .succ .zero, .refl _,
    ⟨.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)⟩,
    ⟨.sort [.assumption (.sort .zero)] .zero⟩,
    fun s hs => (List.not_mem_nil _ hs).elim⟩

/-! ## §2. Full `LRTermD` Assumption/Let-Substitution Stability on `BotPiCpt` & Discharging
`RcicNativePiModelLRTermDSubst`'s (`#7655`) Open `hι` and `hns` Premises -/

/-- `LRTermD` on any `BotPiCpt` compact `c` is stable under `insertAt d k Γ` / `lift k 1`
    at every `EnvClosed E` (with **no** side conditions). -/
theorem lrTermD_weaken_botPiCpt (hcl : EnvClosed E) (d : LocalDecl)
    {c : CptI} (hc : BotPiCpt c) {Γ : LCtx} {M M' A : Expr Nat} {k : Nat}
    (hins : CtxWfT E n (insertAt d k Γ))
    (h : LRTermD E n Γ M M' A c) :
    LRTermD E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_weaken hcl d hP)
  · exact Or.inr (lrTermDCore_weaken_botPiCpt hcl hc d k hins hC)

/-- Head (`k = 0`) weakening of `LRTermD` on any `BotPiCpt` compact. -/
theorem lrTermD_weaken0_botPiCpt (hcl : EnvClosed E) (d : LocalDecl)
    {c : CptI} (hc : BotPiCpt c) {Γ : LCtx} {M M' A : Expr Nat}
    (hins : CtxWfT E n (d :: Γ))
    (h : LRTermD E n Γ M M' A c) :
    LRTermD E n (d :: Γ) (lift 0 1 M) (lift 0 1 M') (lift 0 1 A) c := by
  simpa only [insertAt] using lrTermD_weaken_botPiCpt hcl d hc (k := 0) hins h

/-- `LRTermD` on any `BotPiCpt` compact `c` is stable under `substRemove v j Γ` /
    `instantiate j (lift 0 j v)` under `EnvWfT E` and `SortRow` (with **no** `∀ l, v ≠ .sort l`
    side condition). -/
theorem lrTermD_subst_botPiCpt_of_sortRow (hW : EnvWfT E)
    (hSR : ∀ {Γ : LCtx} {u v : Level}, TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    (v t : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove v j Γ))
    (h : LRTermD E n Γ M M' A c) :
    LRTermD E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_subst_of_sortRow hW hSR hget hvty hP)
  · exact Or.inr (lrTermDCore_subst_botPiCpt (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) v t hc hget hvty hΓ' hC)

/-- Head (`j = 0`) specialization: `LRTermD` on any `BotPiCpt` compact is stable under
    `instantiate0 v` under `EnvWfT E` and `SortRow`. -/
theorem lrTermD_subst0_botPiCpt_of_sortRow (hW : EnvWfT E)
    (hSR : ∀ {Γ : LCtx} {u v : Level}, TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t M M' A : Expr Nat}
    (hv : HasTyT E n Γ v t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermD E n (.assumption t :: Γ) M M' A c) :
    LRTermD E n Γ (instantiate0 v M) (instantiate0 v M') (instantiate0 v A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_subst0_of_sortRow hW hSR hv hP)
  · exact Or.inr (lrTermDCore_subst0_botPiCpt hW hΓ hv hc hC)

/-- `LRTermD` on any `BotPiCpt` compact `c` is stable under `substRemove v j Γ` /
    `instantiate j (lift 0 j v)` under `EnvWfT E` and `TypedRowsWf E n`. -/
theorem lrTermD_subst_botPiCpt_of_botDI (hW : EnvWfT E) (hRows : TypedRowsWf E n)
    (v t : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove v j Γ))
    (h : LRTermD E n Γ M M' A c) :
    LRTermD E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_subst_of_botDI hW hRows hΓ' hget hvty hP)
  · exact Or.inr (lrTermDCore_subst_botPiCpt (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) v t hc hget hvty hΓ' hC)

/-- Head (`j = 0`) specialization: `LRTermD` on any `BotPiCpt` compact is stable under
    `instantiate0 v` under `EnvWfT E` and `TypedRowsWf E n`. -/
theorem lrTermD_subst0_botPiCpt_of_botDI (hW : EnvWfT E) (hRows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t M M' A : Expr Nat}
    (hv : HasTyT E n Γ v t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermD E n (.assumption t :: Γ) M M' A c) :
    LRTermD E n Γ (instantiate0 v M) (instantiate0 v M') (instantiate0 v A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_subst0_of_botDI hW hRows hΓ hv hP)
  · exact Or.inr (lrTermDCore_subst0_botPiCpt hW hΓ hv hc hC)

/-! ### Full `let`-Substitution (`letBinding` / `substRemove`) Stability on `BotPiCpt` -/

/-- `LRTermS` on any `BotPiCpt` compact `c` is stable under `substRemove w0 j Γ` /
    `instantiate j (lift 0 j w0)` at a `.letBinding t w0` hole. -/
theorem lrTermS_substLet_botPiCpt (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (t w0 : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.letBinding t w0))
    (hvty : HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove w0 j Γ))
    (h : LRTermS E n Γ M M' A c) :
    LRTermS E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) M) (instantiate j (lift 0 j w0) M')
      (instantiate j (lift 0 j w0) A) c := by
  cases hc with
  | bot => exact lrTermS_bot _ _ _ _
  | sort =>
      rw [lrTermS_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j w0)⟩,
        lrTypeIN_substLet_botPiCpt hcl hinst t w0 .sort hget hvty hΓ' hLR⟩
  | pi ha hbd hf =>
      rw [lrTermS_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j w0)⟩,
        lrTypeIN_substLet_botPiCpt hcl hinst t w0 (.pi ha hbd hf) hget hvty hΓ' hLR⟩

/-- Head (`j = 0`) specialization: `LRTermS` on any `BotPiCpt` compact is stable under
    `instantiate0 w0` from `.letBinding t w0 :: Γ`. -/
theorem lrTermS_substLet0_botPiCpt (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 M M' A : Expr Nat}
    (hw0 : HasTyT E n Γ w0 t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermS E n (.letBinding t w0 :: Γ) M M' A c) :
    LRTermS E n Γ (instantiate0 w0 M) (instantiate0 w0 M') (instantiate0 w0 A) c := by
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have h0 := lrTermS_substLet_botPiCpt (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) t w0 hc hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hw0)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- `LRTermSDI` on any `BotPiCpt` compact `c` is stable under `substRemove w0 j Γ` /
    `instantiate j (lift 0 j w0)` at a `.letBinding t w0` hole. -/
theorem lrTermSDI_substLet_botPiCpt (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (t w0 : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.letBinding t w0))
    (hvty : HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove w0 j Γ))
    (h : LRTermSDI E n Γ M M' A c) :
    LRTermSDI E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) M) (instantiate j (lift 0 j w0) M')
      (instantiate j (lift 0 j w0) A) c := by
  cases hc with
  | bot => exact lrTermSDI_bot _ _ _ _
  | sort =>
      rw [lrTermSDI_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j w0)⟩,
        lrTypeIN_substLet_botPiCpt hcl hinst t w0 .sort hget hvty hΓ' hLR⟩
  | pi ha hbd hf =>
      rw [lrTermSDI_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j w0)⟩,
        lrTypeIN_substLet_botPiCpt hcl hinst t w0 (.pi ha hbd hf) hget hvty hΓ' hLR⟩

/-- Head (`j = 0`) specialization: `LRTermSDI` on any `BotPiCpt` compact is stable under
    `instantiate0 w0` from `.letBinding t w0 :: Γ`. -/
theorem lrTermSDI_substLet0_botPiCpt (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 M M' A : Expr Nat}
    (hw0 : HasTyT E n Γ w0 t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermSDI E n (.letBinding t w0 :: Γ) M M' A c) :
    LRTermSDI E n Γ (instantiate0 w0 M) (instantiate0 w0 M') (instantiate0 w0 A) c := by
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have h0 := lrTermSDI_substLet_botPiCpt (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) t w0 hc hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hw0)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- `LRTermDCore` on any `BotPiCpt` compact `c` is stable under `substRemove w0 j Γ` /
    `instantiate j (lift 0 j w0)` at a `.letBinding t w0` hole. -/
theorem lrTermDCore_substLet_botPiCpt (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (t w0 : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.letBinding t w0))
    (hvty : HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove w0 j Γ))
    (h : LRTermDCore E n Γ M M' A c) :
    LRTermDCore E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) M) (instantiate j (lift 0 j w0) M')
      (instantiate j (lift 0 j w0) A) c := by
  cases hc with
  | bot => exact lrTermDCore_bot _ _ _ _
  | sort =>
      rw [lrTermDCore_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j w0)⟩,
        lrTypeIN_substLet_botPiCpt hcl hinst t w0 .sort hget hvty hΓ' hLR⟩
  | pi ha hbd hf =>
      rw [lrTermDCore_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j w0)⟩,
        lrTypeIN_substLet_botPiCpt hcl hinst t w0 (.pi ha hbd hf) hget hvty hΓ' hLR⟩

/-- Head (`j = 0`) specialization: `LRTermDCore` on any `BotPiCpt` compact is stable under
    `instantiate0 w0` from `.letBinding t w0 :: Γ`. -/
theorem lrTermDCore_substLet0_botPiCpt (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 M M' A : Expr Nat}
    (hw0 : HasTyT E n Γ w0 t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermDCore E n (.letBinding t w0 :: Γ) M M' A c) :
    LRTermDCore E n Γ (instantiate0 w0 M) (instantiate0 w0 M') (instantiate0 w0 A) c := by
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have h0 := lrTermDCore_substLet_botPiCpt (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) t w0 hc hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hw0)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- `LRTermD` on any `BotPiCpt` compact `c` is stable under `substRemove w0 j Γ` /
    `instantiate j (lift 0 j w0)` at a `.letBinding t w0` hole under `EnvWfT E` and `SortRow`. -/
theorem lrTermD_substLet_botPiCpt_of_sortRow (hW : EnvWfT E)
    (hSR : ∀ {Γ : LCtx} {u v : Level}, TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    (t w0 : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.letBinding t w0))
    (hvty : HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove w0 j Γ))
    (h : LRTermD E n Γ M M' A c) :
    LRTermD E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) M) (instantiate j (lift 0 j w0) M')
      (instantiate j (lift 0 j w0) A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_substLet_of_sortRow hW hSR hget hvty hP)
  · exact Or.inr (lrTermDCore_substLet_botPiCpt (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) t w0 hc hget hvty hΓ' hC)

/-- Head (`j = 0`) specialization: `LRTermD` on any `BotPiCpt` compact is stable under
    `instantiate0 w0` from `.letBinding t w0 :: Γ` under `EnvWfT E` and `SortRow`. -/
theorem lrTermD_substLet0_botPiCpt_of_sortRow (hW : EnvWfT E)
    (hSR : ∀ {Γ : LCtx} {u v : Level}, TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 M M' A : Expr Nat}
    (hw0 : HasTyT E n Γ w0 t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermD E n (.letBinding t w0 :: Γ) M M' A c) :
    LRTermD E n Γ (instantiate0 w0 M) (instantiate0 w0 M') (instantiate0 w0 A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_substLet0_of_sortRow hW hSR hw0 hP)
  · exact Or.inr (lrTermDCore_substLet0_botPiCpt hW hΓ hw0 hc hC)

/-- `LRTermD` on any `BotPiCpt` compact `c` is stable under `substRemove w0 j Γ` /
    `instantiate j (lift 0 j w0)` at a `.letBinding t w0` hole under `EnvWfT E` and
    `TypedRowsWf E n`. -/
theorem lrTermD_substLet_botPiCpt_of_botDI (hW : EnvWfT E) (hRows : TypedRowsWf E n)
    (t w0 : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.letBinding t w0))
    (hvty : HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove w0 j Γ))
    (h : LRTermD E n Γ M M' A c) :
    LRTermD E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) M) (instantiate j (lift 0 j w0) M')
      (instantiate j (lift 0 j w0) A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_substLet_of_sortRow hW (hRows.sortRow hΓ') hget hvty hP)
  · exact Or.inr (lrTermDCore_substLet_botPiCpt (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) t w0 hc hget hvty hΓ' hC)

/-- Head (`j = 0`) specialization: `LRTermD` on any `BotPiCpt` compact is stable under
    `instantiate0 w0` from `.letBinding t w0 :: Γ` under `EnvWfT E` and `TypedRowsWf E n`. -/
theorem lrTermD_substLet0_botPiCpt_of_botDI (hW : EnvWfT E) (hRows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 M M' A : Expr Nat}
    (hw0 : HasTyT E n Γ w0 t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermD E n (.letBinding t w0 :: Γ) M M' A c) :
    LRTermD E n Γ (instantiate0 w0 M) (instantiate0 w0 M') (instantiate0 w0 A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_substLet0_of_sortRow hW (hRows.sortRow hΓ) hw0 hP)
  · exact Or.inr (lrTermDCore_substLet0_botPiCpt hW hΓ hw0 hc hC)

/-! ### Direct Discharge of `RcicNativePiModelLRTermDSubst`'s (`#7655`) Open `hι` and `hns` Premises -/

/-- Unconditional discharge of `hι` in `RcicNativePiModelLRTermDSubst.lrTermDCore_sort_subst`
    at every `EnvClosed E` (using `whStep_iota_instantiate`). -/
theorem lrTermDCore_sort_subst_of_envClosed (hcl : EnvClosed E)
    {j : Nat} {r r' : Expr Nat} {Γ₁ Γ₂ : LCtx} {M M' A : Expr Nat}
    (h : LRTermDCore E n Γ₁ M M' A .sort) :
    LRTermDCore E n Γ₂ (instantiate j (lift 0 j r) M)
      (instantiate j (lift 0 j r') M') (instantiate j (lift 0 j r) A) .sort :=
  lrTermDCore_sort_subst (fun hι j s => whStep_iota_instantiate hι j s) hcl h

/-- Unconditional discharge of `hι` in `RcicNativePiModelLRTermDSubst.fundamentalTermDIS`
    at every `EnvClosed E`. -/
theorem fundamentalTermDIS_of_envClosed (hcl : EnvClosed E)
    {ρ : EnvI} {j : Nat} {r r' T : Expr Nat} {Γ : LCtx}
    (hrel : ∀ c, ApproxI (EnvI.drop ρ j) r c →
      LRTermD E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermD E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M M' A : Expr Nat},
        LRTermDCore E n Γ M M' A .sort →
        LRTermD E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxI ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermD E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) :=
  fundamentalTermDIS (fun hι j s => whStep_iota_instantiate hι j s) hcl hrel

/-- Discharge of **both** `hι` and `hns : ∀ l, r ≠ .sort l` in
    `RcicNativePiModelLRTermDSubst.fundamentalTermDIS_typed` under `EnvWfT E` and `SortRow`. -/
theorem fundamentalTermDIS_typed_of_sortRow (hW : EnvWfT E)
    (hSR : ∀ {Γ : LCtx} {u v : Level}, TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    {ρ : EnvI} {j : Nat} {r r' T T₀ : Expr Nat} {Γ Γ' : LCtx}
    (hj : Γ'[j]? = some (.assumption T₀))
    (hr : HasTyT E n Γ (lift 0 j r) (lift 0 j T₀))
    (hΓ : Γ = substRemove r j Γ')
    (hrel : ∀ c, ApproxI (EnvI.drop ρ j) r c →
      LRTermD E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermD E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M M' A : Expr Nat},
        LRTermD E n Γ' M M' A .sort →
        LRTermD E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxI ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermD E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) := by
  subst hΓ
  have base := fundamentalTermDIS_of_envClosed (envClosed_of_envWfT hW) hrel
  refine ⟨base.1, ?_, base.2.2⟩
  intro M M' A h
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_subst_of_sortRow hW hSR hj hr hP)
  · exact Or.inr (lrTermDCore_sort_subst_of_envClosed (envClosed_of_envWfT hW) hC)

/-! ## §3. Structural `BotPiCpt` Exclusions in `ApproxDI` and `LRTermDCore` Reverse Adequacy -/

/-- For any non-empty demand list `u :: us`, `curryStep (u :: us) c₀ = .lam [(u, curryStep us c₀)]`
    is never a `BotPiCpt`. -/
theorem not_botPiCpt_curryStep (u : List CptI) (us : List (List CptI)) (c₀ : CptI) :
    ¬ BotPiCpt (curryStep (u :: us) c₀) :=
  not_botPiCpt_lam [(u, curryStep us c₀)]

/-- Every `BotPiCpt` approximation of a $\lambda$-abstraction `.lam A b` in `ApproxDI E ρ` is `.bot`. -/
theorem approxDI_lam_botPiCpt_eq_bot {ρ : EnvI} {A b : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (h : ApproxDI E ρ (.lam A b) c) : c = .bot := by
  rcases approxDI_lam_inv h with rfl | ⟨f, rfl, _⟩
  · rfl
  · exact (not_botPiCpt_lam f hc).elim

/-- Every `BotPiCpt` approximation of a `RigidConst E r` constant `.const r ls` in `ApproxDI E ρ`
    is `.bot`. -/
theorem approxDI_rigidConst_botPiCpt_eq_bot {ρ : EnvI} {r : Nat} {ls : List Level} {c : CptI}
    (hrig : RigidConst E r) (hc : BotPiCpt c) (h : ApproxDI E ρ (.const r ls) c) : c = .bot := by
  rcases approxDI_rigid_const_inv hrig h with rfl | rfl
  · rfl
  · exact (not_botPiCpt_spine r [] hc).elim

/-- Every `BotPiCpt` approximation of a recursor constant `.const r ls` (`m.mclass = .recursorM`)
    in `ApproxDI E ρ` is `.bot`. -/
theorem approxDI_recursor_botPiCpt_eq_bot {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {c : CptI}
    (hrec : E.members r = some m) (hrecK : m.mclass = .recursorM)
    (hc : BotPiCpt c) (h : ApproxDI E ρ (.const r ls) c) : c = .bot := by
  rcases approxDI_recursor_const_inv hrec hrecK h with
    rfl | ⟨w, us_pre, us_fields, c₀, _, _, _, _, rfl⟩
  · rfl
  · cases hlist : us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields] with
    | nil =>
        have hlen := congrArg List.length hlist
        simp at hlen
    | cons u us =>
        rw [hlist] at hc
        exact (not_botPiCpt_curryStep u us c₀ hc).elim

/-- Every `BotPiCpt` approximation of any body-less constant (`E.members r = some m` with
    `m.body = none`) in `ApproxDI E ρ` is `.bot`. -/
theorem approxDI_const_body_none_botPiCpt_eq_bot {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {c : CptI}
    (hm : E.members r = some m) (hb : m.body = none)
    (hc : BotPiCpt c) (h : ApproxDI E ρ (.const r ls) c) : c = .bot := by
  by_cases hrec : m.mclass = .recursorM
  · exact approxDI_recursor_botPiCpt_eq_bot hm hrec hc h
  · exact approxDI_rigidConst_botPiCpt_eq_bot (rigidConst_of_body_none hm hb hrec) hc h

/-- On any `BotPiCpt c` with `c ≠ .bot`, `LRTermDCore E n Γ M M' A c` forces
    `(∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' c`. -/
theorem lrTermDCore_botPiCpt_forces_sort {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (hne : c ≠ .bot)
    (h : LRTermDCore E n Γ M M' A c) :
    (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' c := by
  cases hc with
  | bot => exact (hne rfl).elim
  | sort => exact (lrTermDCore_sort_iff Γ M M' A).mp h
  | pi => exact (lrTermDCore_pi_iff Γ M M' A _ _).mp h

/-- **Term-Level Reverse Adequacy on `BotPiCpt`:** at every `EnvWfT E`, if `BotPiCpt c` and
    `LRTermDCore E n Γ M M' A c` holds, then **both** `ApproxDI E EnvI.bot M c` and
    `ApproxDI E EnvI.bot M' c` hold (via `approxDI_of_lrTypeIN_botPiCpt`).
    This eliminates `TypeSoundness` (`hsound`) from `ConvT.trans` on `BotPiCpt`! -/
theorem approxDI_of_lrTermDCore_botPiCpt (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : BotPiCpt c)
    (h : LRTermDCore E n Γ M M' A c) :
    ApproxDI E EnvI.bot M c ∧ ApproxDI E EnvI.bot M' c := by
  cases hc with
  | bot => exact ⟨.bot _ _, .bot _ _⟩
  | sort =>
      exact approxDI_of_lrTypeIN_botPiCpt hW .sort
        ((lrTermDCore_sort_iff Γ M M' A).mp h).2
  | pi hca hbd hcf =>
      exact approxDI_of_lrTypeIN_botPiCpt hW (.pi hca hbd hcf)
        ((lrTermDCore_pi_iff Γ M M' A _ _).mp h).2

/-- On any `BotPiCpt c` with `c ≠ .bot`, `LRTermDCore E n Γ M M' (.pi A B) c` is impossible
    (since `.pi A B` is `WhNormal` and never weak-head reduces to `.sort l`). -/
theorem not_lrTermDCore_at_pi_of_botPiCpt_ne_bot {Γ : LCtx} {M M' A B : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (hne : c ≠ .bot) :
    ¬ LRTermDCore E n Γ M M' (.pi A B) c := by
  intro h
  obtain ⟨⟨l, hred⟩, _⟩ := lrTermDCore_botPiCpt_forces_sort hc hne h
  exact Expr.noConfusion (whRed_pi_eq hred)

/-- On any `BotPiCpt c`, if `LRTermD E n Γ M M' (.pi A B) c` holds, then `c = .bot ∨
    IsPropTyI E n Γ (.pi A B)`, and therefore `LRTermD E n Γ N N' (.pi A B) c` holds for
    **every** pair of expressions `N, N' : Expr Nat`. -/
theorem lrTermD_at_pi_of_botPiCpt {Γ : LCtx} {M M' A B : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (h : LRTermD E n Γ M M' (.pi A B) c)
    (N N' : Expr Nat) :
    LRTermD E n Γ N N' (.pi A B) c := by
  cases hc with
  | bot => exact lrTermD_bot _ _ _ _
  | sort =>
      rcases h with hP | hC
      · exact Or.inl hP
      · exact (not_lrTermDCore_at_pi_of_botPiCpt_ne_bot .sort (fun h0 => by cases h0) hC).elim
  | pi hca hbd hcf =>
      rcases h with hP | hC
      · exact Or.inl hP
      · exact (not_lrTermDCore_at_pi_of_botPiCpt_ne_bot
          (.pi hca hbd hcf) (fun h0 => by cases h0) hC).elim

/-! ## §4. Constructor-by-Constructor `HasTyT` / `ConvT` Clauses for `FundamentalTermBotDI` and
Bidirectional `LRTermDBiDI` -/

/-- `HasTyT.sort` diagonal case for `FundamentalTermBotDI` (unconditional). -/
theorem fundTermBotDI_sort {Γ : LCtx} (l : Level) {c : CptI} (_hc : BotPiCpt c)
    (h : ApproxDI E EnvI.bot (.sort l) c) :
    LRTermD E n Γ (.sort l) (.sort l) (.sort (.succ l)) c :=
  fundTermD_DI_sorts l c h

/-- `HasTyT.bvar` diagonal case for `FundamentalTermBotDI` (unconditional). -/
theorem fundTermBotDI_bvar {Γ : LCtx} (i : Nat) (A : Expr Nat) {c : CptI} (_hc : BotPiCpt c)
    (h : ApproxDI E EnvI.bot (.bvar i) c) :
    LRTermD E n Γ (.bvar i) (.bvar i) A c := by
  rw [approxDI_bot_bvar_inv h]
  exact lrTermD_bot _ _ _ _

/-- `HasTyT.lam` diagonal case for `FundamentalTermBotDI` (unconditional: every `BotPiCpt`
    approximation of `.lam A body` is `.bot`). -/
theorem fundTermBotDI_lam {Γ : LCtx} (A body B : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    (h : ApproxDI E EnvI.bot (.lam A body) c) :
    LRTermD E n Γ (.lam A body) (.lam A body) (.pi A B) c := by
  rw [approxDI_lam_botPiCpt_eq_bot hc h]
  exact lrTermD_bot _ _ _ _

/-- `HasTyT.const` diagonal case for `FundamentalTermBotDI` on any body-less member
    (`m.body = none`, covering all axioms, inductive families, constructors, and recursors in
    `EnvWfT E` — unconditional). -/
theorem fundTermBotDI_const_of_body_none {Γ : LCtx} {r : Nat} (ls : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = none)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (.const r ls) A c := by
  rw [approxDI_const_body_none_botPiCpt_eq_bot hm hb hc h]
  exact lrTermD_bot _ _ _ _

/-- `HasTyT.const` diagonal case for `FundamentalTermBotDI` on any `RigidConst E r`
    (unconditional). -/
theorem fundTermBotDI_rigidConst {Γ : LCtx} {r : Nat} (ls : List Level) (A : Expr Nat)
    (hrig : RigidConst E r) {c : CptI} (hc : BotPiCpt c)
    (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (.const r ls) A c := by
  rw [approxDI_rigidConst_botPiCpt_eq_bot hrig hc h]
  exact lrTermD_bot _ _ _ _

/-- `HasTyT.const` diagonal case for `FundamentalTermBotDI` on any recursor (`m.mclass = .recursorM`
    — unconditional). -/
theorem fundTermBotDI_recursor {Γ : LCtx} {r : Nat} (ls : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (.const r ls) A c := by
  rw [approxDI_recursor_botPiCpt_eq_bot hm hrec hc h]
  exact lrTermD_bot _ _ _ _

/-- `HasTyT.const` diagonal case for `FundamentalTermBotDI` on a `DeltaConst E r m b`:
    reduces directly via `WhStep.delta` and `lrTermD_expand` to the diagonal of
    `instantiateLevels ls b`. -/
theorem fundTermBotDI_deltaConst {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b A : Expr Nat} (hdelta : DeltaConst E r m b)
    (ihb : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot (instantiateLevels ls b) c →
      LRTermD E n Γ (instantiateLevels ls b) (instantiateLevels ls b) A c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (.const r ls) A c := by
  have hstep : WhRed E (.const r ls) (instantiateLevels ls b) :=
    .step (.delta hdelta.1 hdelta.2.1) (.refl _)
  exact lrTermD_expand hstep hstep c (ihb c hc (approxDI_delta_const_inv hdelta h))

/-- `HasTyT.pi` diagonal case for `FundamentalTermBotDI` at `EnvI.bot`:
    because `BotPiCpt (.pi a f)` forces `BotDemand s.1` for every `s ∈ f`,
    `approxDI_cons_botDemand_bot_iff` collapses `EnvI.cons (demand s.1) EnvI.bot` directly to
    `EnvI.bot`, closing `HasTyT.pi` from `ihA` and `ihB` at `EnvI.bot` **without related
    substitutions**. -/
theorem fundTermBotDI_pi {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hΓ₁ : CtxWfT E n (.assumption A :: Γ))
    (ihA : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot A c → LRTermD E n Γ A A (.sort u) c)
    (ihB : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot B c →
      LRTermD E n (.assumption A :: Γ) B B (.sort v) c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.pi A B) c) :
    LRTermD E n Γ (.pi A B) (.pi A B) (.sort (.imax u v)) c := by
  rcases approxDI_pi_inv h with rfl | ⟨a, f, rfl, ha, hf⟩
  · exact lrTermD_bot _ _ _ _
  · cases hc with
    | pi hca hbd hcf =>
        refine Or.inr ?_
        rw [lrTermDCore_pi_iff]
        refine ⟨⟨.imax u v, .refl _⟩,
          lrTypeIN_pi_congr hΓ₁ (.refl Γ A) (.refl (.assumption A :: Γ) B)
            (lrTypeIN_of_lrTermD_sort a (ihA a hca ha)) (fun s hs => ?_)⟩
        have hb : ApproxDI E EnvI.bot B s.2 :=
          (approxDI_cons_botDemand_bot_iff (hbd s hs) B s.2).mp (hf s hs)
        exact lrTypeIN_of_lrTermD_sort s.2 (ihB s.2 (hcf s hs) hb)

/-- `HasTyT.lit` diagonal case for `FundamentalTermBotDI` (reduces directly to `natExpand t`). -/
theorem fundTermBotDI_lit {Γ : LCtx} (t : Nat) (T : Expr Nat)
    (ih : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot (natExpand t) c →
      LRTermD E n Γ (natExpand t) (natExpand t) T c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.lit t) c) :
    LRTermD E n Γ (.lit t) (.lit t) T c := by
  have hstep : WhRed E (.lit t) (natExpand t) := .step (.lit t) (.refl _)
  exact lrTermD_expand hstep hstep c (ih c hc ((approxDI_lit E EnvI.bot t c).mp h))

/-- `HasTyT.letE` diagonal case for `FundamentalTermBotDI` (reduces directly via `WhStep.zeta` and
    `approxDI_zeta` to the contractum `instantiate0 v b`). -/
theorem fundTermBotDI_letE {Γ : LCtx} (A v b B : Expr Nat)
    (ih : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot (instantiate0 v b) c →
      LRTermD E n Γ (instantiate0 v b) (instantiate0 v b) (instantiate0 v B) c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.letE A v b) c) :
    LRTermD E n Γ (.letE A v b) (.letE A v b) (instantiate0 v B) c := by
  have hstep : WhRed E (.letE A v b) (instantiate0 v b) := .step (.zeta A v b) (.refl _)
  exact lrTermD_expand hstep hstep c (ih c hc ((approxDI_zeta E EnvI.bot A v b c).mp h))

/-- `HasTyT.conv` diagonal case for `FundamentalTermBotDI` (via `lrTermD_transport`). -/
theorem fundTermBotDI_conv (hW : EnvWfT E) (hBot : FundamentalLRINBotDI E n)
    (hProp : PropTyTransport E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e A B : Expr Nat} {u : Level} (hA : HasTyT E n Γ A (.sort u)) (hcAB : TyConvT E n Γ A B)
    (ih : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot e c → LRTermD E n Γ e e A c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot e c) :
    LRTermD E n Γ e e B c :=
  lrTermD_transport hW hBot hProp hΓ hA hcAB c (ih c hc h)

/-! ### `ConvT` Constructor Cases for `FundamentalTermBotDI` -/

/-- `ConvT.refl` case for `FundamentalTermBotDI`. -/
theorem fundConvBotDI_refl {Γ : LCtx} {M A : Expr Nat}
    (hdiag : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot M c → LRTermD E n Γ M M A c) :
    ∀ c, BotPiCpt c → ApproxDI E EnvI.bot M c → LRTermD E n Γ M M A c :=
  hdiag

/-- **`ConvT.trans` case for `FundamentalTermBotDI` WITHOUT `TypeSoundness` or `LRTermIndexTransport`:**
    At every `EnvWfT E`, `h₁₂` and `h₂₃` compose directly on `BotPiCpt` because whenever
    `¬ IsPropTyI E n Γ A`, `approxDI_of_lrTermDCore_botPiCpt` extracts
    `ApproxDI E EnvI.bot M₂ c` from `LRTermDCore E n Γ M₁ M₂ A c` automatically! -/
theorem fundConvBotDI_trans (hW : EnvWfT E)
    {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat}
    (h₁₂ : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot M₁ c → LRTermD E n Γ M₁ M₂ A c)
    (h₂₃ : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot M₂ c → LRTermD E n Γ M₂ M₃ A c)
    {c : CptI} (hc : BotPiCpt c) (h₁ : ApproxDI E EnvI.bot M₁ c) :
    LRTermD E n Γ M₁ M₃ A c := by
  rcases h₁₂ c hc h₁ with hP | hC₁₂
  · exact Or.inl hP
  · have h₂ : ApproxDI E EnvI.bot M₂ c :=
      (approxDI_of_lrTermDCore_botPiCpt hW hc hC₁₂).2
    exact lrTermD_botPiCpt_trans hW hc (Or.inr hC₁₂) (h₂₃ c hc h₂)

/-- `ConvT.beta` case for `FundamentalTermBotDI` (unconditional from contractum diagonal). -/
theorem fundConvBotDI_beta {Γ : LCtx} (A body arg T : Expr Nat)
    (hdiag : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot (instantiate0 arg body) c →
      LRTermD E n Γ (instantiate0 arg body) (instantiate0 arg body) T c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.app (.lam A body) arg) c) :
    LRTermD E n Γ (.app (.lam A body) arg) (instantiate0 arg body) T c := by
  have hstep : WhRed E (.app (.lam A body) arg) (instantiate0 arg body) :=
    .step (.beta A body arg) (.refl _)
  exact lrTermD_expand hstep (.refl _) c
    (hdiag c hc ((approxDI_beta E EnvI.bot A body arg c).mp h))

/-- `ConvT.zeta` case for `FundamentalTermBotDI` (unconditional from contractum diagonal). -/
theorem fundConvBotDI_zeta {Γ : LCtx} (A value body T : Expr Nat)
    (hdiag : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot (instantiate0 value body) c →
      LRTermD E n Γ (instantiate0 value body) (instantiate0 value body) T c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.letE A value body) c) :
    LRTermD E n Γ (.letE A value body) (instantiate0 value body) T c := by
  have hstep : WhRed E (.letE A value body) (instantiate0 value body) :=
    .step (.zeta A value body) (.refl _)
  exact lrTermD_expand hstep (.refl _) c
    (hdiag c hc ((approxDI_zeta E EnvI.bot A value body c).mp h))

/-- **`ConvT.zetaLocal` case for `FundamentalTermBotDI` (UNCONDITIONAL):**
    At `EnvI.bot`, the left-hand side `.bvar i` of `ConvT.zetaLocal` has only `c = .bot`,
    so `LRTermD E n Γ (.bvar i) v A c` holds unconditionally for every `E, n, Γ, i, v, A`. -/
theorem fundConvBotDI_zetaLocal {Γ : LCtx} (i : Nat) (v A : Expr Nat)
    {c : CptI} (_hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.bvar i) c) :
    LRTermD E n Γ (.bvar i) v A c := by
  rw [approxDI_bot_bvar_inv h]
  exact lrTermD_bot _ _ _ _

/-- `ConvT.delta` case for `FundamentalTermBotDI` (at `EnvWfT E` from contractum diagonal). -/
theorem fundConvBotDI_delta (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b T : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hdiag : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot (instantiateLevels ls b) c →
      LRTermD E n Γ (instantiateLevels ls b) (instantiateLevels ls b) T c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (instantiateLevels ls b) T c := by
  have hstep : WhRed E (.const r ls) (instantiateLevels ls b) :=
    .step (.delta hres hbody) (.refl _)
  have hrhs : ApproxDI E EnvI.bot (instantiateLevels ls b) c :=
    (semEqDI_of_whStep_delta hW hres hbody EnvI.bot c).mp h
  exact lrTermD_expand hstep (.refl _) c (hdiag c hc hrhs)

/-- `ConvT.delta` case on `BotPiCpt` directly via `approxDI_delta_const_inv` (requiring only
    `DeltaConst E r m b`, without `EnvWfT E`). -/
theorem fundConvBotDI_delta_of_deltaConst {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b T : Expr Nat} (hdelta : DeltaConst E r m b)
    (hdiag : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot (instantiateLevels ls b) c →
      LRTermD E n Γ (instantiateLevels ls b) (instantiateLevels ls b) T c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (instantiateLevels ls b) T c :=
  lrTermD_expand (.step (.delta hdelta.1 hdelta.2.1) (.refl _)) (.refl _) c
    (hdiag c hc (approxDI_delta_const_inv hdelta h))

/-- `ConvT.iota` case for `FundamentalTermBotDI` (at `EnvWfT E` from contractum diagonal). -/
theorem fundConvBotDI_iota (hW : EnvWfT E) {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hiota : DerivedIota E lhs rhs)
    (hdiag : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot rhs c → LRTermD E n Γ rhs rhs T c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot lhs c) :
    LRTermD E n Γ lhs rhs T c := by
  have hstep : WhRed E lhs rhs := .step (.iota (derivedIotaU_ofDerivedIota hiota)) (.refl _)
  have hrhs : ApproxDI E EnvI.bot rhs c :=
    (semEqDI_of_convT_iota hW hiota EnvI.bot c).mp h
  exact lrTermD_expand hstep (.refl _) c (hdiag c hc hrhs)

/-- `ConvT.lit` case for `FundamentalTermBotDI` (unconditional from contractum diagonal). -/
theorem fundConvBotDI_lit {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp)
    (hdiag : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot exp c → LRTermD E n Γ exp exp T c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.lit t) c) :
    LRTermD E n Γ (.lit t) exp T c := by
  cases hlit
  have hstep : WhRed E (.lit t) (natExpand t) := .step (.lit t) (.refl _)
  exact lrTermD_expand hstep (.refl _) c
    (hdiag c hc ((approxDI_lit E EnvI.bot t c).mp h))

/-- **`ConvT.lam` case for `FundamentalTermBotDI` (UNCONDITIONAL):**
    Every `BotPiCpt` approximation of `.lam A b` in `ApproxDI E EnvI.bot` is `.bot`, where
    `LRTermD` holds trivially. -/
theorem fundConvBotDI_lam {Γ : LCtx} (A A' b b' B : Expr Nat)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.lam A b) c) :
    LRTermD E n Γ (.lam A b) (.lam A' b') (.pi A B) c := by
  rw [approxDI_lam_botPiCpt_eq_bot hc h]
  exact lrTermD_bot _ _ _ _

/-- **`ConvT.pi` case for `FundamentalTermBotDI` AT `EnvI.bot` (WITHOUT substitution induction):**
    Because `BotPiCpt (.pi a f)` forces `BotDemand s.1` for every `s ∈ f`,
    `approxDI_cons_botDemand_bot_iff` reduces `EnvI.cons (demand s.1) EnvI.bot` directly to
    `EnvI.bot`, closing `ConvT.pi` from `ihA` and `ihB` at `EnvI.bot`. -/
theorem fundConvBotDI_pi {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hΓ₁ : CtxWfT E n (.assumption A :: Γ))
    (hdom : TyConvT E n Γ A A')
    (hcod : TyConvT E n (.assumption A :: Γ) B B')
    (ihA : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot A c → LRTermD E n Γ A A' (.sort u) c)
    (ihB : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot B c →
      LRTermD E n (.assumption A :: Γ) B B' (.sort v) c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.pi A B) c) :
    LRTermD E n Γ (.pi A B) (.pi A' B') (.sort (.imax u v)) c := by
  rcases approxDI_pi_inv h with rfl | ⟨a, f, rfl, ha, hf⟩
  · exact lrTermD_bot _ _ _ _
  · cases hc with
    | pi hca hbd hcf =>
        refine Or.inr ?_
        rw [lrTermDCore_pi_iff]
        refine ⟨⟨.imax u v, .refl _⟩,
          lrTypeIN_pi_congr hΓ₁ hdom hcod
            (lrTypeIN_of_lrTermD_sort a (ihA a hca ha)) (fun s hs => ?_)⟩
        have hb : ApproxDI E EnvI.bot B s.2 :=
          (approxDI_cons_botDemand_bot_iff (hbd s hs) B s.2).mp (hf s hs)
        exact lrTypeIN_of_lrTermD_sort s.2 (ihB s.2 (hcf s hs) hb)

/-- `ConvT.letE` case for `FundamentalTermBotDI` (reduces via `WhStep.zeta` on both sides and
    `approxDI_zeta` on the left to `instantiate0 v b` vs `instantiate0 v' b'`). -/
theorem fundConvBotDI_letE {Γ : LCtx} (A A' v v' b b' B : Expr Nat)
    (ih : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot (instantiate0 v b) c →
      LRTermD E n Γ (instantiate0 v b) (instantiate0 v' b') (instantiate0 v B) c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.letE A v b) c) :
    LRTermD E n Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B) c := by
  have hL : WhRed E (.letE A v b) (instantiate0 v b) := .step (.zeta A v b) (.refl _)
  have hR : WhRed E (.letE A' v' b') (instantiate0 v' b') := .step (.zeta A' v' b') (.refl _)
  exact lrTermD_expand hL hR c (ih c hc ((approxDI_zeta E EnvI.bot A v b c).mp h))

/-- **`ConvT.sorts` case for `FundamentalTermBotDI` (UNCONDITIONAL):** -/
theorem fundConvBotDI_sorts {Γ : LCtx} (l₁ l₂ : Level)
    {c : CptI} (_hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.sort l₁) c) :
    LRTermD E n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) c := by
  rcases approxDI_sort_inv h with rfl | rfl
  · exact lrTermD_bot _ _ _ _
  · refine Or.inr ?_
    rw [lrTermDCore_sort_iff]
    exact ⟨⟨.succ l₁, .refl _⟩, lrTypeIN_sort_congr Γ l₁ l₂⟩

/-- `ConvT.consts` case for `FundamentalTermBotDI` on any body-less member (`m.body = none`
    — unconditional). -/
theorem fundConvBotDI_consts_of_body_none {Γ : LCtx} {r : Nat} (ls ls' : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = none)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (.const r ls') A c := by
  rw [approxDI_const_body_none_botPiCpt_eq_bot hm hb hc h]
  exact lrTermD_bot _ _ _ _

/-- `ConvT.consts` case for `FundamentalTermBotDI` on any `RigidConst E r` (unconditional). -/
theorem fundConvBotDI_rigidConsts {Γ : LCtx} {r : Nat} (ls ls' : List Level) (A : Expr Nat)
    (hrig : RigidConst E r) {c : CptI} (hc : BotPiCpt c)
    (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (.const r ls') A c := by
  rw [approxDI_rigidConst_botPiCpt_eq_bot hrig hc h]
  exact lrTermD_bot _ _ _ _

/-- `ConvT.consts` case for `FundamentalTermBotDI` on any recursor (`m.mclass = .recursorM`
    — unconditional). -/
theorem fundConvBotDI_recursorConsts {Γ : LCtx} {r : Nat} (ls ls' : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (.const r ls') A c := by
  rw [approxDI_recursor_botPiCpt_eq_bot hm hrec hc h]
  exact lrTermD_bot _ _ _ _

/-- `ConvT.consts` case for `FundamentalTermBotDI` on a `DeltaConst E r m b`:
    reduces via `WhStep.delta` on both sides to `instantiateLevels ls b` vs
    `instantiateLevels ls' b`. -/
theorem fundConvBotDI_deltaConsts {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember} {b A : Expr Nat} (hdelta : DeltaConst E r m b)
    (ih : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot (instantiateLevels ls b) c →
      LRTermD E n Γ (instantiateLevels ls b) (instantiateLevels ls' b) A c)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDI E EnvI.bot (.const r ls) c) :
    LRTermD E n Γ (.const r ls) (.const r ls') A c := by
  have hL : WhRed E (.const r ls) (instantiateLevels ls b) :=
    .step (.delta hdelta.1 hdelta.2.1) (.refl _)
  have hR : WhRed E (.const r ls') (instantiateLevels ls' b) :=
    .step (.delta hdelta.1 hdelta.2.1) (.refl _)
  exact lrTermD_expand hL hR c (ih c hc (approxDI_delta_const_inv hdelta h))

/-- **`ConvT.eta` case for `FundamentalTermBotDI` (UNCONDITIONAL):**
    Because the left-hand side `.lam A (.app (lift 0 1 f) (.bvar 0))` of `ConvT.eta` is a
    $\lambda$-abstraction, its only `BotPiCpt` approximation in `ApproxDI E EnvI.bot` is `.bot`. -/
theorem fundConvBotDI_eta {Γ : LCtx} (f A B : Expr Nat)
    {c : CptI} (hc : BotPiCpt c)
    (h : ApproxDI E EnvI.bot (.lam A (.app (lift 0 1 f) (.bvar 0))) c) :
    LRTermD E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) c := by
  rw [approxDI_lam_botPiCpt_eq_bot hc h]
  exact lrTermD_bot _ _ _ _

/-- **`ConvT.irr` case across ALL compacts `u : CptI` under `SortRow` (with NO `∀ l, P ≠ .sort l`
    side condition):** `isPropTyI_of_hasTyT_sort_zero` discharges `∀ l, P ≠ .sort l` from
    `hP : HasTyT E n Γ P (.sort .zero)` automatically. -/
theorem fundConvBotDI_irr_of_sortRow
    (hSR : ∀ {u v : Level}, TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero)) (u : CptI) :
    LRTermD E n Γ p q P u :=
  Or.inl (isPropTyI_of_hasTyT_sort_zero hSR hP)

/-- **`ConvT.irr` case across ALL compacts `u : CptI` under `TypedRowsWf E n`
    (with NO `∀ l, P ≠ .sort l` side condition):** -/
theorem fundConvBotDI_irr_of_botDI (hRows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (u : CptI) :
    LRTermD E n Γ p q P u :=
  Or.inl (isPropTyI_of_hasTyT_sort_zero_botDI hRows hΓ hP)

/-! ### Bidirectional `BotPiCpt` Term-Level Logical Relation `LRTermDBiDI` -/

/-- Bidirectional `BotPiCpt`-restricted term-level logical relation over `ApproxDI E EnvI.bot`:
    for every `BotPiCpt c` approximating either `M` or `M'`, `LRTermD E n Γ M M' A c` holds.
    This is the term-level counterpart of `LRTypeINBiDI` (`RcicNativePiModelDeltaIota.lean:3492`). -/
def LRTermDBiDI (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : Prop :=
  ∀ c, BotPiCpt c →
    (ApproxDI E EnvI.bot M c ∨ ApproxDI E EnvI.bot M' c) →
    LRTermD E n Γ M M' A c

/-- **Unconditional Symmetry of `LRTermDBiDI` at `EnvWfT E`** (requiring **no** `TypeSoundness`
    and **no** `LRTermIndexTransport`). -/
theorem lrTermDBiDI_symm (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (h : LRTermDBiDI E n Γ M M' A) :
    LRTermDBiDI E n Γ M' M A :=
  fun c hc hor => lrTermD_botPiCpt_symm hW hc (h c hc hor.symm)

/-- **Unconditional Transitivity of `LRTermDBiDI` at `EnvWfT E`** (requiring **no** `TypeSoundness`
    and **no** `LRTermIndexTransport`): `approxDI_of_lrTermDCore_botPiCpt` reconstructs
    `ApproxDI E EnvI.bot M₂ c` on the middle term whenever `¬ IsPropTyI E n Γ A`. -/
theorem lrTermDBiDI_trans (hW : EnvWfT E) {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat}
    (h₁₂ : LRTermDBiDI E n Γ M₁ M₂ A)
    (h₂₃ : LRTermDBiDI E n Γ M₂ M₃ A) :
    LRTermDBiDI E n Γ M₁ M₃ A := by
  intro c hc hor
  rcases hor with h₁ | h₃
  · rcases h₁₂ c hc (Or.inl h₁) with hP | hC₁₂
    · exact Or.inl hP
    · have h₂ : ApproxDI E EnvI.bot M₂ c :=
        (approxDI_of_lrTermDCore_botPiCpt hW hc hC₁₂).2
      exact lrTermD_botPiCpt_trans hW hc (Or.inr hC₁₂) (h₂₃ c hc (Or.inl h₂))
  · rcases h₂₃ c hc (Or.inr h₃) with hP | hC₂₃
    · exact Or.inl hP
    · have h₂ : ApproxDI E EnvI.bot M₂ c :=
        (approxDI_of_lrTermDCore_botPiCpt hW hc hC₂₃).1
      exact lrTermD_botPiCpt_trans hW hc (h₁₂ c hc (Or.inr h₂)) (Or.inr hC₂₃)

/-- `ConvT.sorts` and `HasTyT.sort` for `LRTermDBiDI` (unconditional). -/
theorem lrTermDBiDI_sorts (Γ : LCtx) (l₁ l₂ : Level) :
    LRTermDBiDI E n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) := by
  intro c _ hor
  rcases hor with h | h
  · rcases approxDI_sort_inv h with rfl | rfl
    · exact lrTermD_bot _ _ _ _
    · refine Or.inr ?_; rw [lrTermDCore_sort_iff]; exact ⟨⟨.succ l₁, .refl _⟩, lrTypeIN_sort_congr Γ l₁ l₂⟩
  · rcases approxDI_sort_inv h with rfl | rfl
    · exact lrTermD_bot _ _ _ _
    · refine Or.inr ?_; rw [lrTermDCore_sort_iff]; exact ⟨⟨.succ l₁, .refl _⟩, lrTypeIN_sort_congr Γ l₁ l₂⟩

theorem lrTermDBiDI_sort_diag (Γ : LCtx) (l : Level) :
    LRTermDBiDI E n Γ (.sort l) (.sort l) (.sort (.succ l)) :=
  lrTermDBiDI_sorts Γ l l

/-- `HasTyT.bvar` for `LRTermDBiDI` (unconditional). -/
theorem lrTermDBiDI_bvar_diag (Γ : LCtx) (i : Nat) (A : Expr Nat) :
    LRTermDBiDI E n Γ (.bvar i) (.bvar i) A := by
  intro c hc hor
  exact fundTermBotDI_bvar i A hc (hor.elim id id)

/-- `ConvT.lam` and `HasTyT.lam` for `LRTermDBiDI` (unconditional). -/
theorem lrTermDBiDI_lam (Γ : LCtx) (A A' b b' B : Expr Nat) :
    LRTermDBiDI E n Γ (.lam A b) (.lam A' b') (.pi A B) := by
  intro c hc hor
  rcases hor with h | h
  · exact fundConvBotDI_lam A A' b b' B hc h
  · rw [approxDI_lam_botPiCpt_eq_bot hc h]
    exact lrTermD_bot _ _ _ _

/-- `ConvT.consts` and `HasTyT.const` on any body-less member (`m.body = none`) for `LRTermDBiDI`
    (unconditional). -/
theorem lrTermDBiDI_consts_of_body_none {Γ : LCtx} {r : Nat} (ls ls' : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = none) :
    LRTermDBiDI E n Γ (.const r ls) (.const r ls') A := by
  intro c hc hor
  rcases hor with h | h
  · rw [approxDI_const_body_none_botPiCpt_eq_bot hm hb hc h]; exact lrTermD_bot _ _ _ _
  · rw [approxDI_const_body_none_botPiCpt_eq_bot hm hb hc h]; exact lrTermD_bot _ _ _ _

/-- `ConvT.pi` and `HasTyT.pi` for `LRTermDBiDI` at `EnvI.bot` (without substitution induction). -/
theorem lrTermDBiDI_pi {Γ : LCtx} {A₁ B₁ A₂ B₂ : Expr Nat} {u v : Level}
    (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
    (hdom : TyConvT E n Γ A₁ A₂)
    (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
    (ihA : LRTermDBiDI E n Γ A₁ A₂ (.sort u))
    (ihB : LRTermDBiDI E n (.assumption A₁ :: Γ) B₁ B₂ (.sort v)) :
    LRTermDBiDI E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort (.imax u v)) := by
  intro c hc hor
  rcases hor with h₁ | h₂
  · rcases approxDI_pi_inv h₁ with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact lrTermD_bot _ _ _ _
    · cases hc with
      | pi hca hbd hcf =>
          refine Or.inr ?_
          rw [lrTermDCore_pi_iff]
          refine ⟨⟨.imax u v, .refl _⟩,
            lrTypeIN_pi_congr hΓ₁ hdom hcod
              (lrTypeIN_of_lrTermD_sort a (ihA a hca (Or.inl ha))) (fun s hs => ?_)⟩
          have hb := (approxDI_cons_botDemand_bot_iff (hbd s hs) B₁ s.2).mp (hf s hs)
          exact lrTypeIN_of_lrTermD_sort s.2 (ihB s.2 (hcf s hs) (Or.inl hb))
  · rcases approxDI_pi_inv h₂ with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact lrTermD_bot _ _ _ _
    · cases hc with
      | pi hca hbd hcf =>
          refine Or.inr ?_
          rw [lrTermDCore_pi_iff]
          refine ⟨⟨.imax u v, .refl _⟩,
            lrTypeIN_pi_congr hΓ₁ hdom hcod
              (lrTypeIN_of_lrTermD_sort a (ihA a hca (Or.inr ha))) (fun s hs => ?_)⟩
          have hb := (approxDI_cons_botDemand_bot_iff (hbd s hs) B₂ s.2).mp (hf s hs)
          exact lrTypeIN_of_lrTermD_sort s.2 (ihB s.2 (hcf s hs) (Or.inr hb))

/-- **`ConvT.eta` for `LRTermDBiDI` from `f`'s own `BotPiCpt` diagonal:**
    On the left (`ApproxDI E EnvI.bot (.lam A ...) c`), `c = .bot`; on the right
    (`ApproxDI E EnvI.bot f c`), `lrTermD_at_pi_of_botPiCpt` transfers `LRTermD E n Γ f f (.pi A B) c`
    directly to `LRTermD E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) c`! -/
theorem lrTermDBiDI_eta {Γ : LCtx} {f A B : Expr Nat}
    (hdiag : ∀ c, BotPiCpt c → ApproxDI E EnvI.bot f c → LRTermD E n Γ f f (.pi A B) c) :
    LRTermDBiDI E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) := by
  intro c hc hor
  rcases hor with hlam | hf
  · exact fundConvBotDI_eta f A B hc hlam
  · exact lrTermD_at_pi_of_botPiCpt hc (hdiag c hc hf)
      (.lam A (.app (lift 0 1 f) (.bvar 0))) f

/-- `ConvT.irr` for `LRTermDBiDI` under `SortRow` (with no `∀ l, P ≠ .sort l` side condition). -/
theorem lrTermDBiDI_irr_of_sortRow {Γ : LCtx}
    (hSR : ∀ {u v : Level}, TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero)) :
    LRTermDBiDI E n Γ p q P :=
  fun c _ _ => fundConvBotDI_irr_of_sortRow hSR hP c

/-- `ConvT.tyConv` for `LRTermDBiDI` from `FundamentalLRINBotDI` and `PropTyTransport`. -/
theorem lrTermDBiDI_tyConv (hW : EnvWfT E) (hBot : FundamentalLRINBotDI E n)
    (hProp : PropTyTransport E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A A' : Expr Nat} {v : Level} (hA : HasTyT E n Γ A (.sort v)) (hc : TyConvT E n Γ A A')
    (h : LRTermDBiDI E n Γ M M' A) :
    LRTermDBiDI E n Γ M M' A' :=
  fun c hcbot hor => lrTermD_transport hW hBot hProp hΓ hA hc c (h c hcbot hor)

/-- Bidirectional `BotPiCpt`-restricted term-level fundamental lemma `FundamentalTermBiBotDI E n`
    (named open supply over `LRTermDBiDI`). -/
def FundamentalTermBiBotDI (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    LRTermDBiDI E n Γ M M A) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    LRTermDBiDI E n Γ M M' A)

/-- `FundamentalTermBiBotDI E n` implies `FundamentalTermBotDI E n`. -/
theorem fundamentalTermBotDI_of_biBotDI (F : FundamentalTermBiBotDI E n) :
    FundamentalTermBotDI E n :=
  ⟨fun {_} hΓ {_ _} hM c hc hu => F.1 hΓ hM c hc (Or.inl hu),
   fun {_} hΓ {_ _ _} hconv => F.2 hΓ hconv⟩

/-- Π-injectivity (`piRow` shape) from `FundamentalTermBiBotDI E n` at every `EnvWfT E`
    (requiring **no** `WhDet`, **no** `TypeSoundness`, and **no** `WhApproxInv`). -/
theorem piRow_of_fundamentalTermBiBotDI (hW : EnvWfT E) (F : FundamentalTermBiBotDI E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  piRow_of_fundamentalTermBotDI hW (fundamentalTermBotDI_of_biBotDI F)

/-! ## §5. Vacuity Teeth on Un-Restricted Contexts at `zetaLocalSortCtx` (`W-ZETALOCAL`) vs
Repaired Let-Free `BotPiCpt` Supplies (`LetFreeCtx`, `FundamentalLRINBotDI_letFree`,
`FundamentalTermBotDI_letFree`, `FundamentalTermBiBotDI_letFree`) -/

/-- In `zetaLocalSortCtx = [.letBinding (.sort (.succ .zero)) (.sort .zero)]`, `LRTypeIN` is false
    on `(.sort .zero)` vs `(.bvar 0)` at `.sort` because `WhStep E` has no `zetaLocal` step. -/
theorem not_lrTypeIN_zetaLocalSortCtx_symm (E : ResolvedEnv) (n : Nat) :
    ¬ LRTypeIN E n zetaLocalSortCtx (.sort .zero) (.bvar 0) .sort := by
  intro h
  cases h with
  | sort _ hR => exact nomatch whRed_bvar_eq hR

/-- `LRTypeINBiDI` is false on `(.bvar 0)` vs `(.sort .zero)` in `zetaLocalSortCtx`. -/
theorem not_lrTypeINBiDI_zetaLocalSortCtx (E : ResolvedEnv) (n : Nat) :
    ¬ LRTypeINBiDI E n zetaLocalSortCtx (.bvar 0) (.sort .zero) := by
  intro h
  have hsort := h .sort .sort (Or.inr (.sort EnvI.bot .zero))
  cases hsort with
  | sort hL _ => exact nomatch whRed_bvar_eq hL

/-- `LRTermD` is false on `(.sort .zero)` vs `(.bvar 0)` at `.sort` in `zetaLocalSortCtx`. -/
theorem not_lrTermD_zetaLocalSortCtx_symm (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermD E n zetaLocalSortCtx (.sort .zero) (.bvar 0) (.sort (.succ .zero)) .sort := by
  intro h
  rcases h with hP | hC
  · exact not_isPropTyI_sort E n zetaLocalSortCtx (.succ .zero) hP
  · rw [lrTermDCore_sort_iff] at hC
    exact not_lrTypeIN_zetaLocalSortCtx_symm E n hC.2

/-- `LRTermDBiDI` is false on `(.bvar 0)` vs `(.sort .zero)` in `zetaLocalSortCtx`. -/
theorem not_lrTermDBiDI_zetaLocalSortCtx (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermDBiDI E n zetaLocalSortCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero)) := by
  intro h
  have hsort := h .sort .sort (Or.inr (.sort EnvI.bot .zero))
  rcases hsort with hP | hC
  · exact not_isPropTyI_sort E n zetaLocalSortCtx (.succ .zero) hP
  · rw [lrTermDCore_sort_iff] at hC
    cases hC.2 with
    | sort hL _ => exact nomatch whRed_bvar_eq hL

/-- **Admitted Obstruction (`W-ZETALOCAL` on `FundamentalLRINBotDI`):**
    Because `FundamentalLRINBotDI` quantifies over contexts containing `.letBinding` while
    `LRTypeIN` uses context-free `WhRed E`, `ConvT.symm (zetaLocalSortCtx_conv E n)` refutes
    `FundamentalLRINBotDI E n` for every `E, n`. -/
theorem not_fundamentalLRINBotDI_zetaLocal (E : ResolvedEnv) (n : Nat) :
    ¬ FundamentalLRINBotDI E n := by
  intro F
  have hsymm : ConvT E n zetaLocalSortCtx (.sort .zero) (.bvar 0) (.sort (.succ .zero)) :=
    .symm _ _ _ _ (zetaLocalSortCtx_conv E n)
  exact not_lrTypeIN_zetaLocalSortCtx_symm E n
    (F (zetaLocalSortCtx_wf E n) (.sort zetaLocalSortCtx .zero)
      (.of _ _ _ _ hsymm) .sort .sort (.sort EnvI.bot .zero))

/-- **Admitted Obstruction (`W-ZETALOCAL` on `FundamentalTermBotDI`):**
    `ConvT.symm (zetaLocalSortCtx_conv E n)` refutes `FundamentalTermBotDI E n` for every `E, n`. -/
theorem not_fundamentalTermBotDI_zetaLocal (E : ResolvedEnv) (n : Nat) :
    ¬ FundamentalTermBotDI E n := by
  intro F
  have hsymm : ConvT E n zetaLocalSortCtx (.sort .zero) (.bvar 0) (.sort (.succ .zero)) :=
    .symm _ _ _ _ (zetaLocalSortCtx_conv E n)
  exact not_lrTermD_zetaLocalSortCtx_symm E n
    (F.2 (zetaLocalSortCtx_wf E n) hsymm .sort .sort (Or.inl (.sort EnvI.bot .zero)))

/-- **Admitted Obstruction (`W-ZETALOCAL` on `FundamentalTermBiBotDI`):**
    `zetaLocalSortCtx_conv E n` refutes `FundamentalTermBiBotDI E n` for every `E, n`. -/
theorem not_fundamentalTermBiBotDI_zetaLocal (E : ResolvedEnv) (n : Nat) :
    ¬ FundamentalTermBiBotDI E n :=
  fun F => not_fundamentalTermBotDI_zetaLocal E n (fundamentalTermBotDI_of_biBotDI F)

/-! ### Repaired Let-Free Context Predicate `LetFreeCtx` and Let-Free `BotPiCpt` Supplies -/

/-- A local context `Γ : LCtx` is let-free iff `lookupValue Γ i = none` for every index `i`
    (equivalently, every declaration in `Γ` is an `.assumption A`). -/
def LetFreeCtx (Γ : LCtx) : Prop :=
  ∀ i : Nat, lookupValue Γ i = none

theorem letFreeCtx_nil : LetFreeCtx [] :=
  fun i => by cases i <;> rfl

theorem letFreeCtx_assumption {Γ : LCtx} {A : Expr Nat} (h : LetFreeCtx Γ) :
    LetFreeCtx (.assumption A :: Γ) := by
  intro i
  cases i with
  | zero => rfl
  | succ i => rw [lookupValue_cons_succ, h i]; rfl

theorem not_letFreeCtx_letBinding (A v : Expr Nat) (Γ : LCtx) :
    ¬ LetFreeCtx (.letBinding A v :: Γ) :=
  fun h => Option.noConfusion (h 0)

theorem letFreeCtx_tail {d : LocalDecl} {Γ : LCtx} (h : LetFreeCtx (d :: Γ)) :
    (∃ A, d = .assumption A) ∧ LetFreeCtx Γ := by
  refine ⟨?_, fun i => ?_⟩
  · cases d with
    | assumption A => exact ⟨A, rfl⟩
    | letBinding A v => exact Option.noConfusion (h 0)
  · have hi := h (i + 1)
    rw [lookupValue_cons_succ] at hi
    cases hli : lookupValue Γ i with
    | none => rfl
    | some w => rw [hli] at hi; cases hi

/-- `substRemove v j Γ` preserves `LetFreeCtx`. -/
theorem letFreeCtx_substRemove {Γ : LCtx} (h : LetFreeCtx Γ) (v : Expr Nat) (j : Nat) :
    LetFreeCtx (substRemove v j Γ) := by
  induction Γ generalizing j with
  | nil => cases j <;> exact letFreeCtx_nil
  | cons d Γ₀ ih =>
      obtain ⟨⟨A, rfl⟩, h₀⟩ := letFreeCtx_tail h
      cases j with
      | zero => exact h₀
      | succ j => exact letFreeCtx_assumption (ih h₀ j)

/-- On any `LetFreeCtx Γ`, `ConvT.zetaLocal` is vacuously satisfied in `LRTypeINBiDI` (both
    left-to-right and right-to-left). -/
theorem lrTypeINBiDI_zetaLocal_letFree {Γ : LCtx} (hfree : LetFreeCtx Γ)
    {i : Nat} {v : Expr Nat} (hval : lookupValue Γ i = some v) :
    LRTypeINBiDI E n Γ (.bvar i) v :=
  Option.noConfusion ((hfree i).symm.trans hval)

/-- On any `LetFreeCtx Γ`, `ConvT.zetaLocal` is vacuously satisfied in `LRTermDBiDI` (both
    left-to-right and right-to-left). -/
theorem lrTermDBiDI_zetaLocal_letFree {Γ : LCtx} (hfree : LetFreeCtx Γ)
    {i : Nat} {v A : Expr Nat} (hval : lookupValue Γ i = some v) :
    LRTermDBiDI E n Γ (.bvar i) v A :=
  Option.noConfusion ((hfree i).symm.trans hval)

/-- Let-free `BotPiCpt`-restricted type-level fundamental lemma `FundamentalLRINBotDI_letFree`:
    states `FundamentalLRINBotDI` on let-free contexts `LetFreeCtx Γ`, where `WhStep E` and
    `EnvI.bot` are not subject to `W-ZETALOCAL` (and §6 lifts `piRow` and `sortRow` from
    `LetFreeCtx` to arbitrary `CtxWfT E n Γ`). -/
def FundamentalLRINBotDI_letFree (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, LetFreeCtx Γ → CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) →
    TyConvT E n Γ A B →
    ∀ c, BotPiCpt c → ApproxDI E EnvI.bot A c → LRTypeIN E n Γ A B c

/-- Let-free `BotPiCpt`-restricted term-level fundamental lemma `FundamentalTermBotDI_letFree`. -/
def FundamentalTermBotDI_letFree (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, LetFreeCtx Γ → CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ u, BotPiCpt u → ApproxDI E EnvI.bot M u → LRTermD E n Γ M M A u) ∧
  (∀ {Γ : LCtx}, LetFreeCtx Γ → CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ u, BotPiCpt u →
      (ApproxDI E EnvI.bot M u ∨ ApproxDI E EnvI.bot M' u) →
      LRTermD E n Γ M M' A u)

/-- Let-free bidirectional `BotPiCpt`-restricted term-level fundamental lemma
    `FundamentalTermBiBotDI_letFree`. -/
def FundamentalTermBiBotDI_letFree (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, LetFreeCtx Γ → CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    LRTermDBiDI E n Γ M M A) ∧
  (∀ {Γ : LCtx}, LetFreeCtx Γ → CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    LRTermDBiDI E n Γ M M' A)

theorem fundamentalTermBotDI_letFree_of_biBotDI_letFree
    (F : FundamentalTermBiBotDI_letFree E n) :
    FundamentalTermBotDI_letFree E n :=
  ⟨fun {_} hlf hΓ {_ _} hM c hc hu => F.1 hlf hΓ hM c hc (Or.inl hu),
   fun {_} hlf hΓ {_ _ _} hconv c hc hu => F.2 hlf hΓ hconv c hc hu⟩

/-- `FundamentalLRINBotDI_letFree E n` from diagonal and single-link `LRTypeIN` on let-free
    contexts (requiring **no** `WhDet` and **no** `TypeSoundness`). -/
theorem fundamentalLRINBotDI_letFree_of_links (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, LetFreeCtx Γ → CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level},
      HasTyT E n Γ A (.sort u) → ∀ c, BotPiCpt c → ApproxDI E EnvI.bot A c →
      LRTypeIN E n Γ A A c)
    (hstep : ∀ {Γ : LCtx}, LetFreeCtx Γ → CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level},
      ConvT E n Γ A B (.sort u) → ∀ c, BotPiCpt c → ApproxDI E EnvI.bot A c →
      LRTypeIN E n Γ A B c) :
    FundamentalLRINBotDI_letFree E n := by
  have hcl := envClosed_of_envWfT hW
  intro Γ hlf hΓ A A' u hA hc
  revert u
  induction hc with
  | refl A => intro u hA c hc hcA; exact hdiag hlf hΓ hA c hc hcA
  | of A B v hc => intro _ _ c hcpt hcA; exact hstep hlf hΓ hc c hcpt hcA
  | trans A M B c₁ c₂ ih₁ ih₂ =>
      intro u hA c hcpt hcA
      obtain ⟨v, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA
      have r₁ := ih₁ hA c hcpt hcA
      have hcM := (approxDI_of_lrTypeIN_botPiCpt hW hcpt r₁).2
      exact lrTypeIN_trans_of_envWfT hcl hW r₁ (ih₂ hM c hcpt hcM)

/-- `FundamentalTermBotDI_letFree E n` implies `FundamentalLRINBotDI_letFree E n` at every `EnvWfT E`
    (without `WhDet` or `TypeSoundness`). -/
theorem fundamentalLRINBotDI_letFree_of_termBotDI_letFree (hW : EnvWfT E)
    (F : FundamentalTermBotDI_letFree E n) :
    FundamentalLRINBotDI_letFree E n :=
  fundamentalLRINBotDI_letFree_of_links hW
    (fun {_} hlf hΓ {_ _} hA c hc hAc => lrTypeIN_of_lrTermD_sort c (F.1 hlf hΓ hA c hc hAc))
    (fun {_} hlf hΓ {_ _ _} hconv c hc hAc =>
      lrTypeIN_of_lrTermD_sort c (F.2 hlf hΓ hconv c hc (Or.inl hAc)))

/-- Let-free `piRow` from `FundamentalLRINBotDI_letFree E n` at every `EnvWfT E`. -/
theorem piRow_letFree_of_fundamentalLRINBotDI_letFree (hW : EnvWfT E)
    (F : FundamentalLRINBotDI_letFree E n)
    {Γ : LCtx} (hlf : LetFreeCtx Γ) (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (h : TyConvT E n Γ (.pi A B) (.pi A' B')) :
    Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  rcases tyConvT_firstOf_data h with heq | ⟨_, u, hc₀, _⟩
  · injection heq with eA eB
    subst eA; subst eB
    exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  · have hpi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    have hlr := F hlf hΓ hpi h (.pi .bot []) botPiCpt_pi_bot_nil
      (approxDI_pi_bot_nil E EnvI.bot A B)
    exact lrTypeIN_pi_components hlr

/-- Let-free Π-sort disjointness (`TyConvT (.pi A B) (.sort l) → False`) from
    `FundamentalLRINBotDI_letFree E n`. -/
theorem not_tyConvT_pi_sort_letFree_of_fundamentalLRINBotDI_letFree (hW : EnvWfT E)
    (F : FundamentalLRINBotDI_letFree E n)
    {Γ : LCtx} (hlf : LetFreeCtx Γ) (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {l : Level}
    (h : TyConvT E n Γ (.pi A B) (.sort l)) :
    False := by
  rcases tyConvT_firstOf_data h with heq | ⟨_, u, hc₀, _⟩
  · cases heq
  · have hpi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    have hlr := F hlf hΓ hpi h (.pi .bot []) botPiCpt_pi_bot_nil
      (approxDI_pi_bot_nil E EnvI.bot A B)
    cases hlr with
    | pi _ h' _ _ _ _ _ => exact nomatch whRed_sort_eq h'

/-! ## §6. Typed Let-Expansion (`expandLetAt`, `hasTyT_conv_expandLetAt`), Context-Conversion of
`insertAt (.letBinding t w0) j (substRemove w0 j Γ)`, and Lifting Let-Free `piRow` / `sortRow`
to Arbitrary Contexts (`piRow_of_letFree_piRow`, `sortRow_of_letFree_sortRow`) -/

/-- Exact typed let-expansion at context position `j` with stored value `w0`:
    substitutes `lift 0 j w0` for `.bvar j` (`instantiate j (lift 0 j w0) e`) and then shifts indices
    `≥ j` back up by `1` (`lift j 1`), leaving all `.bvar i` with `i ≠ j` unchanged and replacing
    `.bvar j` by `lift 0 (j + 1) w0` (`lookupValue Γ j`). -/
def expandLetAt (w0 : Expr Nat) (j : Nat) (e : Expr Nat) : Expr Nat :=
  lift j 1 (instantiate j (lift 0 j w0) e)

@[simp]
theorem expandLetAt_sort (w0 : Expr Nat) (j : Nat) (l : Level) :
    expandLetAt w0 j (.sort l) = .sort l := rfl

@[simp]
theorem expandLetAt_const (w0 : Expr Nat) (j : Nat) (r : Nat) (ls : List Level) :
    expandLetAt w0 j (.const r ls) = .const r ls := rfl

@[simp]
theorem expandLetAt_lit (w0 : Expr Nat) (j : Nat) (k : Nat) :
    expandLetAt w0 j (.lit k) = .lit k := rfl

@[simp]
theorem expandLetAt_app (w0 : Expr Nat) (j : Nat) (f a : Expr Nat) :
    expandLetAt w0 j (.app f a) = .app (expandLetAt w0 j f) (expandLetAt w0 j a) := rfl

theorem expandLetAt_pi (w0 : Expr Nat) (j : Nat) (A B : Expr Nat) :
    expandLetAt w0 j (.pi A B) = .pi (expandLetAt w0 j A) (expandLetAt w0 (j + 1) B) := by
  unfold expandLetAt
  simp only [instantiate, lift]
  rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]

theorem expandLetAt_lam (w0 : Expr Nat) (j : Nat) (A b : Expr Nat) :
    expandLetAt w0 j (.lam A b) = .lam (expandLetAt w0 j A) (expandLetAt w0 (j + 1) b) := by
  unfold expandLetAt
  simp only [instantiate, lift]
  rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]

theorem expandLetAt_letE (w0 : Expr Nat) (j : Nat) (A v b : Expr Nat) :
    expandLetAt w0 j (.letE A v b) =
      .letE (expandLetAt w0 j A) (expandLetAt w0 j v) (expandLetAt w0 (j + 1) b) := by
  unfold expandLetAt
  simp only [instantiate, lift]
  rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]

/-- At the let-bound index `j`, `expandLetAt w0 j (.bvar j) = lift 0 (j + 1) w0`. -/
theorem expandLetAt_bvar_eq (w0 : Expr Nat) (j : Nat) :
    expandLetAt w0 j (.bvar j) = lift 0 (j + 1) w0 := by
  unfold expandLetAt
  simp only [instantiate, if_pos rfl]
  exact lift_lift_merge 1 j 0 j (by omega) (by omega) w0

/-- At any variable index `i ≠ j`, `expandLetAt w0 j (.bvar i) = .bvar i`. -/
theorem expandLetAt_bvar_ne (w0 : Expr Nat) {i j : Nat} (hne : i ≠ j) :
    expandLetAt w0 j (.bvar i) = .bvar i := by
  unfold expandLetAt
  bvar_leaves

/-- **Fundamental Typed Let-Expansion Theorem (`hasTyT_conv_expandLetAt`):**
    Under `EnvClosed E`, every well-typed term `HasTyT E n Γ e A` in a context `Γ` with
    `Γ[j]? = some (.letBinding t w0)` is `ConvT`-convertible at its own type `A` to
    `expandLetAt w0 j e = lift j 1 (instantiate j (lift 0 j w0) e)`. -/
def hasTyT_conv_expandLetAt (hcl : EnvClosed E) (t w0 : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTyT E n Γ e A →
    Γ[j]? = some (.letBinding t w0) →
    HasTyT E n Γ (lift 0 (j + 1) w0) (lift 0 (j + 1) t) →
    ConvT E n Γ e (expandLetAt w0 j e) A
  | _, _, _, _, .sort Γ l, _, _ => .refl Γ (.sort l) (.sort (.succ l)) (.sort Γ l)
  | j, _, _, _, .bvar Γ i A hlook, hget, hvwf => by
      by_cases hij : i = j
      · subst hij
        have hty : lookupType Γ i = some (lift 0 (i + 1) t) := lookupType_get_letBinding hget
        have hval : lookupValue Γ i = some (lift 0 (i + 1) w0) := lookupValue_get_letBinding hget
        have eA : A = lift 0 (i + 1) t := Option.some.inj (hlook.symm.trans hty)
        subst eA
        rw [expandLetAt_bvar_eq]
        exact .zetaLocal Γ i (lift 0 (i + 1) t) (lift 0 (i + 1) w0) hval hty hvwf
      · rw [expandLetAt_bvar_ne w0 hij]
        exact .refl Γ (.bvar i) A (.bvar Γ i A hlook)
  | _, _, _, _, .const Γ r ls m hres hlen hwf, _, _ =>
      .refl Γ (.const r ls) (instantiateLevels ls m.mtype) (.const Γ r ls m hres hlen hwf)
  | _, _, _, _, .lit Γ k T hexp, _, _ =>
      .refl Γ (.lit k) T (.lit Γ k T hexp)
  | j, _, _, _, .app Γ f a A B hf ha, hget, hvwf =>
      .app Γ f (expandLetAt w0 j f) a (expandLetAt w0 j a) A B
        (hasTyT_conv_expandLetAt hcl t w0 hf hget hvwf)
        (hasTyT_conv_expandLetAt hcl t w0 ha hget hvwf)
  | j, _, _, _, .pi Γ A u B w hA hB, hget, hvwf => by
      rw [expandLetAt_pi]
      have hget' : (LocalDecl.assumption A :: Γ)[j + 1]? = some (.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hvwf' : HasTyT E n (.assumption A :: Γ) (lift 0 (j + 2) w0) (lift 0 (j + 2) t) := by
        have h0 := hasTyTWeaken (.assumption A) hcl (c := 0) hvwf
        rw [lift_lift_merge 1 (j + 1) 0 0 (by omega) (by omega),
            lift_lift_merge 1 (j + 1) 0 0 (by omega) (by omega)] at h0
        exact h0
      exact .pi Γ A (expandLetAt w0 j A) B (expandLetAt w0 (j + 1) B) u w
        (hasTyT_conv_expandLetAt hcl t w0 hA hget hvwf)
        (hasTyT_conv_expandLetAt hcl t w0 hB hget' hvwf')
  | j, _, _, _, .lam Γ A u body B hA hbody, hget, hvwf => by
      rw [expandLetAt_lam]
      have hget' : (LocalDecl.assumption A :: Γ)[j + 1]? = some (.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hvwf' : HasTyT E n (.assumption A :: Γ) (lift 0 (j + 2) w0) (lift 0 (j + 2) t) := by
        have h0 := hasTyTWeaken (.assumption A) hcl (c := 0) hvwf
        rw [lift_lift_merge 1 (j + 1) 0 0 (by omega) (by omega),
            lift_lift_merge 1 (j + 1) 0 0 (by omega) (by omega)] at h0
        exact h0
      exact .lam Γ A (expandLetAt w0 j A) body (expandLetAt w0 (j + 1) body) B u
        (hasTyT_conv_expandLetAt hcl t w0 hA hget hvwf)
        (hasTyT_conv_expandLetAt hcl t w0 hbody hget' hvwf')
  | j, _, _, _, .letE Γ A u value B body hA hv hbody, hget, hvwf => by
      rw [expandLetAt_letE]
      have hget' : (LocalDecl.letBinding A value :: Γ)[j + 1]? = some (.letBinding t w0) := by
        rw [List.getElem?_cons_succ]; exact hget
      have hvwf' : HasTyT E n (.letBinding A value :: Γ) (lift 0 (j + 2) w0) (lift 0 (j + 2) t) := by
        have h0 := hasTyTWeaken (.letBinding A value) hcl (c := 0) hvwf
        rw [lift_lift_merge 1 (j + 1) 0 0 (by omega) (by omega),
            lift_lift_merge 1 (j + 1) 0 0 (by omega) (by omega)] at h0
        exact h0
      exact .letE Γ A (expandLetAt w0 j A) value (expandLetAt w0 j value)
        body (expandLetAt w0 (j + 1) body) B u
        (hasTyT_conv_expandLetAt hcl t w0 hA hget hvwf)
        (hasTyT_conv_expandLetAt hcl t w0 hv hget hvwf)
        (hasTyT_conv_expandLetAt hcl t w0 hbody hget' hvwf')
  | j, _, _, _, .conv Γ e A B u he hAB, hget, hvwf =>
      .tyConv Γ e (expandLetAt w0 j e) A B u
        (hasTyT_conv_expandLetAt hcl t w0 he hget hvwf) hAB

/-- `TyConvT` chain substitution at a `.letBinding t w0` entry (lifting `convT_substLet_of_envWfT`
    from `RcicTypedSubstLet`). -/
def tyConvT_substLet_of_envWfT (hW : EnvWfT E) (t w0 : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {A B : Expr Nat} →
    TyConvT E n Γ A B →
    Γ[j]? = some (.letBinding t w0) →
    HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
    TyConvT E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) A) (instantiate j (lift 0 j w0) B)
  | _, _, _, _, .refl _ _, _, _ => .refl _ _
  | _, _, _, _, .of _ _ _ u h, hget, hvty =>
      .of _ _ _ u (convT_substLet_of_envWfT hW t w0 h hget hvty)
  | _, _, _, _, .trans _ _ _ _ h1 h2, hget, hvty =>
      .trans _ _ _ _
        (tyConvT_substLet_of_envWfT hW t w0 h1 hget hvty)
        (tyConvT_substLet_of_envWfT hW t w0 h2 hget hvty)

/-- Number of `.letBinding` entries in a local context `Γ`. -/
def letCount : LCtx → Nat
  | [] => 0
  | .assumption _ :: Γ => letCount Γ
  | .letBinding _ _ :: Γ => letCount Γ + 1

/-- Witness that index `j` is the first (innermost) `.letBinding t w0` in `Γ`, with only
    `.assumption` entries at indices `< j`. -/
inductive FirstLetAt : LCtx → Nat → Expr Nat → Expr Nat → Type
  | head (t w0 : Expr Nat) (Γ : LCtx) :
      FirstLetAt (.letBinding t w0 :: Γ) 0 t w0
  | consAssump (A : Expr Nat) {Γ : LCtx} {j : Nat} {t w0 : Expr Nat}
      (h : FirstLetAt Γ j t w0) :
      FirstLetAt (.assumption A :: Γ) (j + 1) t w0

/-- Every local context `Γ` is either `LetFreeCtx Γ` or has a first `.letBinding` witness
    `FirstLetAt Γ j t w0`. -/
def letFree_or_firstLetAt : (Γ : LCtx) → PSum (LetFreeCtx Γ) (Σ' j t w0, FirstLetAt Γ j t w0)
  | [] => .inl letFreeCtx_nil
  | .letBinding t w0 :: Γ => .inr ⟨0, t, w0, .head t w0 Γ⟩
  | .assumption _ :: Γ =>
      match letFree_or_firstLetAt Γ with
      | .inl hfree => .inl (letFreeCtx_assumption hfree)
      | .inr ⟨j, t, w0, hfirst⟩ => .inr ⟨j + 1, t, w0, .consAssump _ hfirst⟩

theorem firstLetAt_get? {Γ : LCtx} {j : Nat} {t w0 : Expr Nat}
    (h : FirstLetAt Γ j t w0) : Γ[j]? = some (.letBinding t w0) := by
  induction h with
  | head => simp
  | consAssump _ _ ih => rw [List.getElem?_cons_succ]; exact ih

theorem letCount_substRemove_of_firstLetAt {Γ : LCtx} {j : Nat} {t w0 : Expr Nat}
    (h : FirstLetAt Γ j t w0) :
    letCount (substRemove w0 j Γ) + 1 = letCount Γ := by
  induction h with
  | head => rfl
  | consAssump _ _ ih => exact ih

/-- Well-formedness and value typing for `substRemove w0 j Γ` at a `FirstLetAt Γ j t w0` witness. -/
def ctxWfT_substRemove_of_firstLetAt (hW : EnvWfT E) :
    {Γ : LCtx} → {j : Nat} → {t w0 : Expr Nat} →
    CtxWfT E n Γ → FirstLetAt Γ j t w0 →
    CtxWfT E n (substRemove w0 j Γ) ×'
      HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) ×'
      HasTyT E n Γ (lift 0 (j + 1) w0) (lift 0 (j + 1) t)
  | _, _, t, w0, .letBinding Γ₀ _ _ _ hΓ₀ _ hw0, .head _ _ _ =>
      have hcl := envClosed_of_envWfT hW
      have hw0' : HasTyT E n (substRemove w0 0 (.letBinding t w0 :: Γ₀))
          (lift 0 0 w0) (lift 0 0 t) := by
        simp only [substRemove, lift_zero]; exact hw0
      ⟨hΓ₀, hw0', hasTyTWeaken (.letBinding t w0) hcl (c := 0) hw0⟩
  | _, _, t, w0, .assumption Γ₀ A u hΓ₀ hA, .consAssump _ (j := j) h₀ => by
      have hcl := envClosed_of_envWfT hW
      let ⟨hΓ_sub, hw0_sub, hw0_Γ₀⟩ := ctxWfT_substRemove_of_firstLetAt hW hΓ₀ h₀
      have hA_sub : HasTyT E n (substRemove w0 j Γ₀) (instantiate j (lift 0 j w0) A) (.sort u) :=
        hasTyT_substLet_of_envWfT hW t w0 hA (firstLetAt_get? h₀) hw0_sub
      have hΓ_sub' : CtxWfT E n (substRemove w0 (j + 1) (.assumption A :: Γ₀)) :=
        .assumption _ _ u hΓ_sub hA_sub
      have hw0_sub' : HasTyT E n (substRemove w0 (j + 1) (.assumption A :: Γ₀))
          (lift 0 (j + 1) w0) (lift 0 (j + 1) t) := by
        have h0 := hasTyTWeaken (.assumption (instantiate j (lift 0 j w0) A)) hcl (c := 0) hw0_sub
        rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
            lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
        exact h0
      have hw0_Γ : HasTyT E n (.assumption A :: Γ₀) (lift 0 (j + 2) w0) (lift 0 (j + 2) t) := by
        have h0 := hasTyTWeaken (.assumption A) hcl (c := 0) hw0_Γ₀
        rw [lift_lift_merge 1 (j + 1) 0 0 (by omega) (by omega),
            lift_lift_merge 1 (j + 1) 0 0 (by omega) (by omega)] at h0
        exact h0
      exact ⟨hΓ_sub', hw0_sub', hw0_Γ⟩

/-- Pointwise context conversion `CtxConvT E n (insertAt (.letBinding t w0) j (substRemove w0 j Γ)) Γ`
    at any `FirstLetAt Γ j t w0` witness. -/
def ctxConvT_insertAt_substRemove_of_firstLetAt (hW : EnvWfT E) :
    {Γ : LCtx} → {j : Nat} → {t w0 : Expr Nat} →
    CtxWfT E n Γ → FirstLetAt Γ j t w0 →
    CtxConvT E n (insertAt (.letBinding t w0) j (substRemove w0 j Γ)) Γ
  | _, _, t, w0, .letBinding Γ₀ _ _ _ _ _ _, .head _ _ _ =>
      ctxConvT_refl (.letBinding t w0 :: Γ₀)
  | _, _, t, w0, .assumption Γ₀ A u hΓ₀ hA, .consAssump _ (j := j) h₀ => by
      have hcl := envClosed_of_envWfT hW
      let ⟨_, _, hw0_Γ₀⟩ := ctxWfT_substRemove_of_firstLetAt hW hΓ₀ h₀
      have hcc₀ := ctxConvT_insertAt_substRemove_of_firstLetAt hW hΓ₀ h₀
      have hcA : ConvT E n Γ₀ A (expandLetAt w0 j A) (.sort u) :=
        hasTyT_conv_expandLetAt hcl t w0 hA (firstLetAt_get? h₀) hw0_Γ₀
      have hA_exp : HasTyT E n Γ₀ (expandLetAt w0 j A) (.sort u) :=
        (convEnds hW hΓ₀ hcA).2.1
      exact .assumption hcc₀ hA_exp hA (.symm _ _ _ _ hcA)

/-- Reconstructs `TyConvT E n Γ X Y` in `Γ` from `TyConvT E n (substRemove w0 j Γ)
    (instantiate j (lift 0 j w0) X) (instantiate j (lift 0 j w0) Y)` whenever `X` and `Y` are
    sort-typed in `Γ`. -/
def tyConvT_of_substRemove_firstLetAt (hW : EnvWfT E)
    {Γ : LCtx} {j : Nat} {t w0 X Y : Expr Nat} {u v : Level}
    (hΓ : CtxWfT E n Γ) (hfirst : FirstLetAt Γ j t w0)
    (hX : HasTyT E n Γ X (.sort u)) (hY : HasTyT E n Γ Y (.sort v))
    (hsub : TyConvT E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) X) (instantiate j (lift 0 j w0) Y)) :
    TyConvT E n Γ X Y := by
  have hcl := envClosed_of_envWfT hW
  let ⟨_, _, hw0_Γ⟩ := ctxWfT_substRemove_of_firstLetAt hW hΓ hfirst
  have hget := firstLetAt_get? hfirst
  have hwk : TyConvT E n (insertAt (.letBinding t w0) j (substRemove w0 j Γ))
      (expandLetAt w0 j X) (expandLetAt w0 j Y) :=
    tyConvTWeaken (.letBinding t w0) hcl (c := j) hsub
  have hctx : TyConvT E n Γ (expandLetAt w0 j X) (expandLetAt w0 j Y) :=
    tyConvT_ctx hcl (ctxConvT_insertAt_substRemove_of_firstLetAt hW hΓ hfirst) hwk
  have hcX : ConvT E n Γ X (expandLetAt w0 j X) (.sort u) :=
    hasTyT_conv_expandLetAt hcl t w0 hX hget hw0_Γ
  have hcY : ConvT E n Γ Y (expandLetAt w0 j Y) (.sort v) :=
    hasTyT_conv_expandLetAt hcl t w0 hY hget hw0_Γ
  exact .trans _ _ _ _ (.of _ _ _ u hcX)
    (.trans _ _ _ _ hctx (TyConvT.symmT (.of _ _ _ v hcY)))

/-- Every `TyConvT E n Γ X Y` in a well-formed context `Γ` is either syntactic equality `X = Y`
    (pure refl) or has both endpoints sort-typed in `Γ`. -/
theorem tyConvT_eq_or_both_typed (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {X Y : Expr Nat} (h : TyConvT E n Γ X Y) :
    X = Y ∨ (∃ u v, Nonempty (HasTyT E n Γ X (.sort u)) ∧ Nonempty (HasTyT E n Γ Y (.sort v))) := by
  rcases TyConvT.firstOf h with rfl | ⟨C, u, ⟨hc₀⟩, ⟨hrest⟩⟩
  · exact Or.inl rfl
  · have hEnds := convEnds hW hΓ hc₀
    obtain ⟨v, hY⟩ := tyConvT_endTyped hW hΓ hrest hEnds.2.1
    exact Or.inr ⟨u, v, ⟨hEnds.1⟩, ⟨hY⟩⟩

/-- Induction on `letCount Γ` lifting `piRow` from let-free contexts to contexts with `k`
    `.letBinding` declarations. -/
theorem piRow_of_letCount (hW : EnvWfT E)
    (hFree : ∀ {Δ : LCtx}, LetFreeCtx Δ → CtxWfT E n Δ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Δ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Δ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Δ) B B')) :
    ∀ (k : Nat) {Γ : LCtx}, letCount Γ = k → CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') := by
  intro k
  induction k with
  | zero =>
      intro Γ hk hΓ A B A' B' hconv
      cases letFree_or_firstLetAt Γ with
      | inl hlf => exact hFree hlf hΓ hconv
      | inr hfst =>
          obtain ⟨j, t, w0, hfirst⟩ := hfst
          have hcnt := letCount_substRemove_of_firstLetAt hfirst
          exact False.elim (Nat.succ_ne_zero _ (hcnt.trans hk))
  | succ k ih =>
      intro Γ hk hΓ A B A' B' hconv
      cases letFree_or_firstLetAt Γ with
      | inl hlf => exact hFree hlf hΓ hconv
      | inr hfst =>
          obtain ⟨j, t, w0, hfirst⟩ := hfst
          have hcnt : letCount (substRemove w0 j Γ) = k :=
            Nat.succ.inj ((letCount_substRemove_of_firstLetAt hfirst).trans hk)
          rcases tyConvT_eq_or_both_typed hW hΓ hconv with heq | ⟨_, _, ⟨hpi⟩, ⟨hpi'⟩⟩
          · injection heq with eA eB
            subst eA; subst eB
            exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
          · let ⟨u₁, v₁, hA, hB, _⟩ := hasTyT_pi_inv hpi rfl
            let ⟨u₂, v₂, hA', hB', _⟩ := hasTyT_pi_inv hpi' rfl
            let ⟨hΓ_sub, hw0_sub, _⟩ := ctxWfT_substRemove_of_firstLetAt hW hΓ hfirst
            have hconv_sub := tyConvT_substLet_of_envWfT hW t w0 hconv
              (firstLetAt_get? hfirst) hw0_sub
            simp only [instantiate] at hconv_sub
            rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)] at hconv_sub
            obtain ⟨⟨hdom_sub⟩, ⟨hcod_sub⟩⟩ := ih hcnt hΓ_sub hconv_sub
            have hdom : TyConvT E n Γ A A' :=
              tyConvT_of_substRemove_firstLetAt hW hΓ hfirst hA hA' hdom_sub
            have hB'_A : HasTyT E n (.assumption A :: Γ) B' (.sort v₂) :=
              hasTyT_tyConvT_head hW hΓ (TyConvT.symmT hdom) hB'
            have hΓ_A : CtxWfT E n (.assumption A :: Γ) := .assumption _ _ u₁ hΓ hA
            have hcod : TyConvT E n (.assumption A :: Γ) B B' :=
              tyConvT_of_substRemove_firstLetAt hW hΓ_A (.consAssump A hfirst) hB hB'_A hcod_sub
            exact ⟨⟨hdom⟩, ⟨hcod⟩⟩

/-- **Lifting Let-Free `piRow` to Arbitrary Well-Formed Contexts (`piRow_of_letFree_piRow`):**
    Under `EnvWfT E`, if `piRow` holds on let-free contexts (`LetFreeCtx Δ`), then `PiRowField E n`
    holds on **all** well-formed contexts `CtxWfT E n Γ` (including contexts with `.letBinding`s). -/
theorem piRow_of_letFree_piRow (hW : EnvWfT E)
    (hFree : ∀ {Δ : LCtx}, LetFreeCtx Δ → CtxWfT E n Δ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Δ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Δ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Δ) B B')) :
    PiRowField E n :=
  fun {_} hΓ {_ _ _ _} hconv => piRow_of_letCount hW hFree _ rfl hΓ hconv

/-- Induction on `letCount Γ` lifting `sortRow` from let-free contexts to arbitrary contexts. -/
theorem sortRow_of_letCount (hW : EnvWfT E)
    (hFree : ∀ {Δ : LCtx}, LetFreeCtx Δ → CtxWfT E n Δ → ∀ {u v : Level},
      TyConvT E n Δ (.sort u) (.sort v) → eqN u v) :
    ∀ (k : Nat) {Γ : LCtx}, letCount Γ = k → CtxWfT E n Γ → ∀ {u v : Level},
      TyConvT E n Γ (.sort u) (.sort v) → eqN u v := by
  intro k
  induction k with
  | zero =>
      intro Γ hk hΓ u v hconv
      cases letFree_or_firstLetAt Γ with
      | inl hlf => exact hFree hlf hΓ hconv
      | inr hfst =>
          obtain ⟨j, t, w0, hfirst⟩ := hfst
          have hcnt := letCount_substRemove_of_firstLetAt hfirst
          exact False.elim (Nat.succ_ne_zero _ (hcnt.trans hk))
  | succ k ih =>
      intro Γ hk hΓ u v hconv
      cases letFree_or_firstLetAt Γ with
      | inl hlf => exact hFree hlf hΓ hconv
      | inr hfst =>
          obtain ⟨j, t, w0, hfirst⟩ := hfst
          have hcnt : letCount (substRemove w0 j Γ) = k :=
            Nat.succ.inj ((letCount_substRemove_of_firstLetAt hfirst).trans hk)
          let ⟨hΓ_sub, hw0_sub, _⟩ := ctxWfT_substRemove_of_firstLetAt hW hΓ hfirst
          have hconv_sub := tyConvT_substLet_of_envWfT hW t w0 hconv
            (firstLetAt_get? hfirst) hw0_sub
          exact ih hcnt hΓ_sub hconv_sub

/-- **Lifting Let-Free `sortRow` to Arbitrary Well-Formed Contexts (`sortRow_of_letFree_sortRow`):**
    Under `EnvWfT E`, if `sortRow` holds on let-free contexts (`LetFreeCtx Δ`), then `sortRow`
    holds on **all** well-formed contexts `CtxWfT E n Γ`. -/
theorem sortRow_of_letFree_sortRow (hW : EnvWfT E)
    (hFree : ∀ {Δ : LCtx}, LetFreeCtx Δ → CtxWfT E n Δ → ∀ {u v : Level},
      TyConvT E n Δ (.sort u) (.sort v) → eqN u v)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level} (h : TyConvT E n Γ (.sort u) (.sort v)) :
    eqN u v :=
  sortRow_of_letCount hW hFree _ rfl hΓ h

/-- Full `PiRowField E n` (on **all** `CtxWfT E n Γ`, including `.letBinding` contexts) from
    `FundamentalLRINBotDI_letFree E n` at every `EnvWfT E`. -/
theorem piRow_of_fundamentalLRINBotDI_letFree (hW : EnvWfT E)
    (F : FundamentalLRINBotDI_letFree E n) :
    PiRowField E n :=
  piRow_of_letFree_piRow hW (fun {_} hlf hΓ {_ _ _ _} hconv =>
    piRow_letFree_of_fundamentalLRINBotDI_letFree hW F hlf hΓ hconv)

/-- Full `PiRowField E n` (on **all** `CtxWfT E n Γ`) from `FundamentalTermBotDI_letFree E n`
    at every `EnvWfT E`. -/
theorem piRow_of_fundamentalTermBotDI_letFree (hW : EnvWfT E)
    (F : FundamentalTermBotDI_letFree E n) :
    PiRowField E n :=
  piRow_of_fundamentalLRINBotDI_letFree hW
    (fundamentalLRINBotDI_letFree_of_termBotDI_letFree hW F)

/-- Full `PiRowField E n` (on **all** `CtxWfT E n Γ`) from `FundamentalTermBiBotDI_letFree E n`
    at every `EnvWfT E`. -/
theorem piRow_of_fundamentalTermBiBotDI_letFree (hW : EnvWfT E)
    (F : FundamentalTermBiBotDI_letFree E n) :
    PiRowField E n :=
  piRow_of_fundamentalTermBotDI_letFree hW
    (fundamentalTermBotDI_letFree_of_biBotDI_letFree F)

/-! ## §7. Obstruction on Un-Guarded Substitution-Style Π-Clause (`polyPiType` at `polyPiTypeCpt`) &
The `ConvT`-Guarded Substitution-Style Logical Relation (`LRTermDSubCore` / `LRTermDSub`) -/

/-- Polymorphic Π-type `Π (X : Sort 1), Π (_ : X), X`. -/
def polyPiType : Expr Nat :=
  .pi (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))

/-- The `BotPiCpt` compact `.pi .bot [([], .pi .bot [])]` approximating `polyPiType` at `EnvI.bot`. -/
def polyPiTypeCpt : CptI :=
  .pi .bot [([], .pi .bot [])]

theorem botPiCpt_polyPiTypeCpt : BotPiCpt polyPiTypeCpt :=
  botPiCpt_pi_nil_step .bot botPiCpt_pi_bot_nil

/-- `polyPiType` is well-typed in `Γ = []` for every `E, n`. -/
def hasTyT_polyPiType (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] polyPiType
      (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) :=
  .pi [] (.sort (.succ .zero)) (.succ (.succ .zero))
    (.pi (.bvar 0) (.bvar 1)) (.imax (.succ .zero) (.succ .zero))
    (.sort [] (.succ .zero))
    (.pi [.assumption (.sort (.succ .zero))] (.bvar 0) (.succ .zero) (.bvar 1) (.succ .zero)
      (.bvar [.assumption (.sort (.succ .zero))] 0 (.sort (.succ .zero)) rfl)
      (.bvar [.assumption (.bvar 0), .assumption (.sort (.succ .zero))] 1 (.sort (.succ .zero)) rfl))

theorem approxDI_polyPiType (E : ResolvedEnv) :
    ApproxDI E EnvI.bot polyPiType polyPiTypeCpt := by
  refine .pi (.bot _ _) (fun s hs => ?_)
  rcases List.mem_singleton.mp hs with rfl
  exact .pi (.bot _ _) (fun _ hs' => (List.not_mem_nil _ hs').elim)

/-- **Obstruction on Un-Guarded Substitution-Style Π-Clause (`polyPiType` at `polyPiTypeCpt`):**
    If the substitution-style `.pi` clause quantifies over `∀ N N', HasTyT E n Γ N A₁ →
    HasTyT E n Γ N' A₁ → (∀ u ∈ s.1, ...) → ...` **without** requiring `ConvT E n Γ N N' A₁`
    (as in `LRTermDCore.lam`), then at `polyPiType = Π (X : Sort 1), X → X` and the `BotPiCpt`
    compact `polyPiTypeCpt = .pi .bot [([], .pi .bot [])]`, the empty demand `s.1 = []` allows
    unrelated `N = .pi (.sort .zero) (.sort .zero)` and `N' = .sort .zero` and forces
    `TyConvT E n [] (.pi (.sort .zero) (.sort .zero)) (.sort .zero)` (Π-sort confusion). -/
theorem tyConvT_pi_sort_of_unguarded_pi_polyPiType {R : Expr Nat → Expr Nat → CptI → Prop}
    (hrf : ∀ s ∈ ([([], .pi .bot [])] : List (List CptI × CptI)),
      ∀ N N' : Expr Nat,
        HasTyT E n [] N (.sort (.succ .zero)) →
        HasTyT E n [] N' (.sort (.succ .zero)) →
        (∀ u ∈ s.1, R N N' u) →
        LRTypeIN E n []
          (instantiate0 N (.pi (.bvar 0) (.bvar 1)))
          (instantiate0 N' (.pi (.bvar 0) (.bvar 1))) s.2) :
    Nonempty (TyConvT E n [] (.pi (.sort .zero) (.sort .zero)) (.sort .zero)) := by
  have hN : HasTyT E n [] (.pi (.sort .zero) (.sort .zero)) (.sort (.succ .zero)) :=
    .conv [] (.pi (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) (.sort (.succ .zero))
      (.succ (.imax (.succ .zero) (.succ .zero)))
      (.pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
        (.sort [] .zero) (.sort [.assumption (.sort .zero)] .zero))
      (.sorts [] (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun _ => rfl))
  have hN' : HasTyT E n [] (.sort .zero) (.sort (.succ .zero)) := .sort [] .zero
  have hstep := hrf ([], .pi .bot []) (List.Mem.head _)
    (.pi (.sort .zero) (.sort .zero)) (.sort .zero) hN hN' (fun _ hu => nomatch hu)
  exact (lrTypeIN_pi_components hstep).1

/-- The `ConvT`-guarded substitution-style logical relation `LRTermDSubCore`:
    * At `.pi a f`, relates the domains `A₁, A₂` at `a` and for every step `s ∈ f` and every pair
      of **convertible** typed arguments `N, N' : A₁` (`ConvT E n Γ N N' A₁`) related on `s.1`,
      relates the instantiated codomains `instantiate0 N B₁` and `instantiate0 N' B₂` at `s.2`.
    * At `.lam g`, likewise requires `ConvT E n Γ N N' A₁` on the test arguments `N, N'`. -/
def LRTermDSubCore (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : CptI → Prop
  | .bot => True
  | .sort => (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' .sort
  | .pi a f =>
      (∃ l, WhRed E A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ u₁ w₁,
        WhRed E M (.pi A₁ B₁) ∧
        WhRed E M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧
        Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        Nonempty (HasTyT E n Γ A₁ (.sort u₁)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁)) ∧
        LRTermDSubCore E n Γ A₁ A₂ (.sort u₁) a ∧
        ∀ s ∈ f, ∀ N N' : Expr Nat,
          HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ → ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubCore E n Γ N N' A₁ u) →
          LRTermDSubCore E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁) s.2
  | .spine r args =>
      ((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
      (∃ ls₁ ls₂ args₁ args₂,
        WhRed E M (foldApps (.const r ls₁) args₁) ∧
        WhRed E M' (foldApps (.const r ls₂) args₂) ∧
        WhNormal E (foldApps (.const r ls₁) args₁) ∧
        WhNormal E (foldApps (.const r ls₂) args₂) ∧
        Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
          (foldApps (.const r ls₂) args₂) A) ∧
        args.length ≤ args₁.length ∧ args.length ≤ args₂.length)
  | .lam g =>
      ∃ A₁ B₁ w, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat,
          HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ → ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubCore E n Γ N N' A₁ u) →
          (IsPropTyI E n Γ (instantiate0 N B₁) ∨
            LRTermDSubCore E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  · omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have h₃ := sizeOfD_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
    have h₃ := sizeOfD_snd_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have h₃ := sizeOfD_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOfD_snd_lt s
    omega

/-- Proposition-collapsed wrapper `LRTermDSub` over `LRTermDSubCore`. -/
def LRTermDSub (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (u : CptI) : Prop :=
  IsPropTyI E n Γ A ∨ LRTermDSubCore E n Γ M M' A u

theorem lrTermDSubCore_bot_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermDSubCore E n Γ M M' A .bot ↔ True := by
  rw [LRTermDSubCore.eq_def]

theorem lrTermDSubCore_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermDSubCore E n Γ M M' A .sort ↔
      (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' .sort := by
  rw [LRTermDSubCore.eq_def]

theorem lrTermDSubCore_pi_iff (Γ : LCtx) (M M' A : Expr Nat) (a : CptI)
    (f : List (List CptI × CptI)) :
    LRTermDSubCore E n Γ M M' A (.pi a f) ↔
      (∃ l, WhRed E A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ u₁ w₁,
        WhRed E M (.pi A₁ B₁) ∧
        WhRed E M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧
        Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        Nonempty (HasTyT E n Γ A₁ (.sort u₁)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁)) ∧
        LRTermDSubCore E n Γ A₁ A₂ (.sort u₁) a ∧
        ∀ s ∈ f, ∀ N N' : Expr Nat,
          HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ → ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubCore E n Γ N N' A₁ u) →
          LRTermDSubCore E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁) s.2 := by
  rw [LRTermDSubCore.eq_def]

/-- **Positive Repair of `W-DEMAND` Across All Compacts (`lrTermDSubCore_idPiProp_all`):**
    For **every** `E, n, Γ` (`CtxWfT E n Γ`) and **every** compact `c : CptI` approximating
    `idPiProp = .pi (.sort .zero) (.bvar 0)` in `ApproxDI E EnvI.bot` (including
    `idPiPropSortStep = .pi .bot [([.sort], .sort)]`), `LRTermDSubCore` holds unconditionally! -/
theorem lrTermDSubCore_idPiProp_all {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level)
    {c : CptI} (h : ApproxDI E EnvI.bot idPiProp c) :
    LRTermDSubCore E n Γ idPiProp idPiProp (.sort w) c := by
  rcases approxDI_pi_inv h with rfl | ⟨a, f, rfl, ha, hf⟩
  · rw [lrTermDSubCore_bot_iff]; trivial
  · rw [lrTermDSubCore_pi_iff]
    refine ⟨⟨w, .refl _⟩, .sort .zero, .bvar 0, .sort .zero, .bvar 0, .succ .zero, .zero,
      .refl _, .refl _,
      ⟨.assumption Γ (.sort .zero) (.succ .zero) hΓ (.sort Γ .zero)⟩,
      ⟨.refl _ _⟩, ⟨.refl _ _⟩,
      ⟨.sort Γ .zero⟩,
      ⟨.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl⟩, ?_, ?_⟩
    · rcases approxDI_sort_inv ha with rfl | rfl
      · rw [lrTermDSubCore_bot_iff]; trivial
      · rw [lrTermDSubCore_sort_iff]
        exact ⟨⟨.succ .zero, .refl _⟩, lrTypeIN_sort_congr Γ .zero .zero⟩
    · intro s hs N N' _ _ _ hrel
      rcases approxDI_bvar_inv (hf s hs) with hbot | hmem
      · rw [hbot, lrTermDSubCore_bot_iff]; trivial
      · rcases hrel s.2 hmem with hP | hsub
        · exact (not_isPropTyI_sort E n Γ .zero hP).elim
        · exact hsub

/-- Unconditional satisfaction of `LRTermDSubCore` on `idPiProp` at `idPiPropSortStep`. -/
theorem lrTermDSubCore_idPiProp_sortStep {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level) :
    LRTermDSubCore E n Γ idPiProp idPiProp (.sort w) idPiPropSortStep :=
  lrTermDSubCore_idPiProp_all hΓ w (approxDI_idPiProp_sortStep E)

/-- Unconditional satisfaction of `LRTermDSub` on `idPiProp` across all compacts in
    `ApproxDI E EnvI.bot idPiProp`. -/
theorem lrTermDSub_idPiProp_all {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level)
    {c : CptI} (h : ApproxDI E EnvI.bot idPiProp c) :
    LRTermDSub E n Γ idPiProp idPiProp (.sort w) c :=
  Or.inr (lrTermDSubCore_idPiProp_all hΓ w h)

/-- **Positive Repair of the `polyPiType` Obstruction (`lrTermDSubCore_polyPiType_of_envWfT`):**
    Because `LRTermDSubCore` requires `ConvT E n Γ N N' A₁` on the test arguments `N, N'`,
    `polyPiType = .pi (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))` positively satisfies
    `LRTermDSubCore` at `polyPiTypeCpt = .pi .bot [([], .pi .bot [])]` in every `EnvWfT E` and
    `CtxWfT E n Γ`! -/
theorem lrTermDSubCore_polyPiType_of_envWfT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (w : Level) :
    LRTermDSubCore E n Γ polyPiType polyPiType (.sort w) polyPiTypeCpt := by
  have hcl := envClosed_of_envWfT hW
  unfold polyPiTypeCpt
  rw [lrTermDSubCore_pi_iff]
  refine ⟨⟨w, .refl _⟩, .sort (.succ .zero), .pi (.bvar 0) (.bvar 1),
    .sort (.succ .zero), .pi (.bvar 0) (.bvar 1),
    .succ (.succ .zero), .imax (.succ .zero) (.succ .zero),
    .refl _, .refl _,
    ⟨.assumption Γ (.sort (.succ .zero)) (.succ (.succ .zero)) hΓ (.sort Γ (.succ .zero))⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩,
    ⟨.sort Γ (.succ .zero)⟩,
    ⟨.pi (.assumption (.sort (.succ .zero)) :: Γ) (.bvar 0) (.succ .zero) (.bvar 1) (.succ .zero)
      (.bvar (.assumption (.sort (.succ .zero)) :: Γ) 0 (.sort (.succ .zero)) rfl)
      (.bvar (.assumption (.bvar 0) :: .assumption (.sort (.succ .zero)) :: Γ) 1
        (.sort (.succ .zero)) rfl)⟩,
    by rw [lrTermDSubCore_bot_iff]; trivial, ?_⟩
  intro s hs N N' hN _ hconv _
  rcases List.mem_singleton.mp hs with rfl
  change LRTermDSubCore E n Γ (.pi N (lift 0 1 N)) (.pi N' (lift 0 1 N'))
    (.sort (.imax (.succ .zero) (.succ .zero))) (.pi .bot [])
  rw [lrTermDSubCore_pi_iff]
  refine ⟨⟨.imax (.succ .zero) (.succ .zero), .refl _⟩,
    N, lift 0 1 N, N', lift 0 1 N', .succ .zero, .succ .zero,
    .refl _, .refl _,
    ⟨.assumption Γ N (.succ .zero) hΓ hN⟩,
    ⟨.of _ _ _ (.succ .zero) hconv⟩,
    ⟨.of _ _ _ (.succ .zero) (convTWeaken (.assumption N) hcl (c := 0) hconv)⟩,
    ⟨hN⟩,
    ⟨hasTyTWeaken (.assumption N) hcl (c := 0) hN⟩,
    by rw [lrTermDSubCore_bot_iff]; trivial,
    fun _ hs' => (List.not_mem_nil _ hs').elim⟩

/-! ## §8. Weak-Head Expansion, Head-Step `ConvT` Clauses, General `not_isPropTyI_pi_sort`,
Full `closedIrrPi` Repair at `closedIrrPiCpt`, and `PiRowField` Extraction for `LRTermDSub` -/

theorem lrTermDSubCore_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptI) :
    LRTermDSubCore E n Γ M M' A (.spine r args) ↔
      ((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
      (∃ ls₁ ls₂ args₁ args₂,
        WhRed E M (foldApps (.const r ls₁) args₁) ∧
        WhRed E M' (foldApps (.const r ls₂) args₂) ∧
        WhNormal E (foldApps (.const r ls₁) args₁) ∧
        WhNormal E (foldApps (.const r ls₂) args₂) ∧
        Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
          (foldApps (.const r ls₂) args₂) A) ∧
        args.length ≤ args₁.length ∧ args.length ≤ args₂.length) := by
  rw [LRTermDSubCore.eq_def]

theorem lrTermDSubCore_lam_iff (Γ : LCtx) (M M' A : Expr Nat)
    (g : List (List CptI × CptI)) :
    LRTermDSubCore E n Γ M M' A (.lam g) ↔
      ∃ A₁ B₁ w, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat,
          HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ → ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubCore E n Γ N N' A₁ u) →
          (IsPropTyI E n Γ (instantiate0 N B₁) ∨
            LRTermDSubCore E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2) := by
  rw [LRTermDSubCore.eq_def]

/-- Weak-head expansion on both sides for `LRTermDSubCore`, by well-founded recursion on `u : CptI`. -/
theorem lrTermDSubCore_whRed_expand {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRed E M X) (hX' : WhRed E M' X') :
    (u : CptI) → LRTermDSubCore E n Γ X X' A u → LRTermDSubCore E n Γ M M' A u
  | .bot, _ => by rw [lrTermDSubCore_bot_iff]; trivial
  | .sort, h => by
      rw [lrTermDSubCore_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .pi a f, h => by
      rw [lrTermDSubCore_pi_iff] at h ⊢
      rcases h with ⟨hl, A₁, B₁, A₂, B₂, u₁, w₁, h1, h2, hΓ₁, hcA, hcB, hA₁, hB₁, ha, hf⟩
      exact ⟨hl, A₁, B₁, A₂, B₂, u₁, w₁,
        whRed_trans hX h1, whRed_trans hX' h2, hΓ₁, hcA, hcB, hA₁, hB₁, ha, hf⟩
  | .spine r args, h => by
      rw [lrTermDSubCore_spine_iff] at h ⊢
      rcases h with ⟨hl, hLR⟩ | ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, hc, hb1, hb2⟩
      · exact Or.inl ⟨hl, lrTypeIN_expand hX hX' hLR⟩
      · exact Or.inr ⟨ls₁, ls₂, args₁, args₂, whRed_trans hX h1, whRed_trans hX' h2,
          n1, n2, hc, hb1, hb2⟩
  | .lam g, h => by
      rw [lrTermDSubCore_lam_iff] at h ⊢
      rcases h with ⟨A₁, B₁, w, hA, hΓ₁, hB₁, happ⟩
      refine ⟨A₁, B₁, w, hA, hΓ₁, hB₁, fun s hs N N' hN hN' hconv hrel => ?_⟩
      rcases happ s hs N N' hN hN' hconv hrel with hP | hsub
      · exact Or.inl hP
      · exact Or.inr (lrTermDSubCore_whRed_expand (whRedD_appHead hX) (whRedD_appHead hX') s.2 hsub)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOfD_snd_lt s
  omega

/-- Weak-head expansion on both sides for `LRTermDSub`. -/
theorem lrTermDSub_whRed_expand {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRed E M X) (hX' : WhRed E M' X') {u : CptI}
    (h : LRTermDSub E n Γ X X' A u) :
    LRTermDSub E n Γ M M' A u := by
  rcases h with hP | hcore
  · exact Or.inl hP
  · exact Or.inr (lrTermDSubCore_whRed_expand hX hX' u hcore)

/-- General `WhRed` soundness for `LRTermDSub` across **all** compacts `u : CptI` in
    `ApproxDI E EnvI.bot`. -/
theorem fundConvDSub_of_whRed (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (hred : WhRed E M M')
    (hM' : ∀ u, ApproxDI E EnvI.bot M' u → LRTermDSub E n Γ M' M' A u) :
    ∀ u, ApproxDI E EnvI.bot M u → LRTermDSub E n Γ M M' A u := by
  intro u hu
  have hu' : ApproxDI E EnvI.bot M' u := (semEqDI_whRed hW hred EnvI.bot u).mp hu
  exact lrTermDSub_whRed_expand hred (.refl M') (hM' u hu')

/-- Single `WhStep` soundness for `LRTermDSub` across **all** compacts `u : CptI` in
    `ApproxDI E EnvI.bot`. -/
theorem fundConvDSub_of_whStep (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (hstep : WhStep E M M')
    (hM' : ∀ u, ApproxDI E EnvI.bot M' u → LRTermDSub E n Γ M' M' A u) :
    ∀ u, ApproxDI E EnvI.bot M u → LRTermDSub E n Γ M M' A u :=
  fundConvDSub_of_whRed hW (.step hstep (.refl M')) hM'

/-- `ConvT.beta` clause for `LRTermDSub` across all compacts `u : CptI`. -/
theorem fundConvDSub_beta (hW : EnvWfT E) {Γ : LCtx} (A body arg B : Expr Nat)
    (hM' : ∀ u, ApproxDI E EnvI.bot (instantiate0 arg body) u →
      LRTermDSub E n Γ (instantiate0 arg body) (instantiate0 arg body) (instantiate0 arg B) u) :
    ∀ u, ApproxDI E EnvI.bot (.app (.lam A body) arg) u →
      LRTermDSub E n Γ (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B) u :=
  fundConvDSub_of_whStep hW (.beta A body arg) hM'

/-- `ConvT.zeta` clause for `LRTermDSub` across all compacts `u : CptI`. -/
theorem fundConvDSub_zeta (hW : EnvWfT E) {Γ : LCtx} (A value body B : Expr Nat)
    (hM' : ∀ u, ApproxDI E EnvI.bot (instantiate0 value body) u →
      LRTermDSub E n Γ (instantiate0 value body) (instantiate0 value body)
        (instantiate0 value B) u) :
    ∀ u, ApproxDI E EnvI.bot (.letE A value body) u →
      LRTermDSub E n Γ (.letE A value body) (instantiate0 value body)
        (instantiate0 value B) u :=
  fundConvDSub_of_whStep hW (.zeta A value body) hM'

/-- `ConvT.delta` clause for `LRTermDSub` across all compacts `u : CptI`. -/
theorem fundConvDSub_delta (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hM' : ∀ u, ApproxDI E EnvI.bot (instantiateLevels ls b) u →
      LRTermDSub E n Γ (instantiateLevels ls b) (instantiateLevels ls b)
        (instantiateLevels ls m.mtype) u) :
    ∀ u, ApproxDI E EnvI.bot (.const r ls) u →
      LRTermDSub E n Γ (.const r ls) (instantiateLevels ls b)
        (instantiateLevels ls m.mtype) u :=
  fundConvDSub_of_whStep hW (.delta hres hbody) hM'

/-- `ConvT.iota` clause for `LRTermDSub` across all compacts `u : CptI`. -/
theorem fundConvDSub_iota (hW : EnvWfT E) {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hι : DerivedIota E lhs rhs)
    (hM' : ∀ u, ApproxDI E EnvI.bot rhs u → LRTermDSub E n Γ rhs rhs T u) :
    ∀ u, ApproxDI E EnvI.bot lhs u → LRTermDSub E n Γ lhs rhs T u :=
  fundConvDSub_of_whStep hW (.iota (derivedIotaU_ofDerivedIota hι)) hM'

/-- `ConvT.lit` clause for `LRTermDSub` across all compacts `u : CptI`. -/
theorem fundConvDSub_lit (hW : EnvWfT E) {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp)
    (hM' : ∀ u, ApproxDI E EnvI.bot exp u → LRTermDSub E n Γ exp exp T u) :
    ∀ u, ApproxDI E EnvI.bot (.lit t) u → LRTermDSub E n Γ (.lit t) exp T u := by
  cases hlit
  exact fundConvDSub_of_whStep hW (.lit t) hM'

/-- On any `LetFreeCtx Γ`, `ConvT.zetaLocal` is vacuously sound for `LRTermDSub`. -/
theorem fundConvDSub_zetaLocal_letFree {Γ : LCtx} (hLF : LetFreeCtx Γ)
    {i : Nat} {A v : Expr Nat} (hval : lookupValue Γ i = some v) (u : CptI) :
    LRTermDSub E n Γ (.bvar i) v A u := by
  rw [hLF i] at hval
  cases hval

/-- `ConvT.irr` clause for `LRTermDSub` under `SortRow`. -/
theorem fundConvDSub_irr_of_sortRow
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero)) (u : CptI) :
    LRTermDSub E n Γ p q P u :=
  Or.inl (isPropTyI_of_hasTyT_sort_zero hSort hP)

/-- Substituting `ConvT`-convertible arguments `N, N' : A₁` into `ConvT`-convertible sort-typed
    codomains `B₁, B₂` yields `ConvT E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁)`
    directly via `ConvT.beta` + `ConvT.lam` + `ConvT.app`. -/
def convT_instantiate0_sort_of_convT {Γ : LCtx} {A₁ B₁ B₂ N N' : Expr Nat} {u₁ w₁ : Level}
    (hA₁ : HasTyT E n Γ A₁ (.sort u₁))
    (hB₁ : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁))
    (hB₂ : HasTyT E n (.assumption A₁ :: Γ) B₂ (.sort w₁))
    (hBconv : ConvT E n (.assumption A₁ :: Γ) B₁ B₂ (.sort w₁))
    (hN : HasTyT E n Γ N A₁)
    (hN' : HasTyT E n Γ N' A₁)
    (hNconv : ConvT E n Γ N N' A₁) :
    ConvT E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁) := by
  have hβ₁ : ConvT E n Γ (.app (.lam A₁ B₁) N) (instantiate0 N B₁) (.sort w₁) :=
    .beta Γ A₁ B₁ N (.sort w₁) u₁ hA₁ hB₁ hN
  have hβ₂ : ConvT E n Γ (.app (.lam A₁ B₂) N') (instantiate0 N' B₂) (.sort w₁) :=
    .beta Γ A₁ B₂ N' (.sort w₁) u₁ hA₁ hB₂ hN'
  have hlam : ConvT E n Γ (.lam A₁ B₁) (.lam A₁ B₂) (.pi A₁ (.sort w₁)) :=
    .lam Γ A₁ A₁ B₁ B₂ (.sort w₁) u₁ (.refl Γ A₁ (.sort u₁) hA₁) hBconv
  have happ : ConvT E n Γ (.app (.lam A₁ B₁) N) (.app (.lam A₁ B₂) N') (.sort w₁) :=
    .app Γ (.lam A₁ B₁) (.lam A₁ B₂) N N' A₁ (.sort w₁) hlam hNconv
  exact .trans Γ _ _ _ (.sort w₁) (.symm Γ _ _ (.sort w₁) hβ₁)
    (.trans Γ _ _ _ (.sort w₁) happ hβ₂)

/-- `TyConvT` counterpart of `convT_instantiate0_sort_of_convT`. -/
def tyConvT_instantiate0_sort_of_convT {Γ : LCtx} {A₁ B₁ B₂ N N' : Expr Nat} {u₁ w₁ : Level}
    (hA₁ : HasTyT E n Γ A₁ (.sort u₁))
    (hB₁ : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁))
    (hB₂ : HasTyT E n (.assumption A₁ :: Γ) B₂ (.sort w₁))
    (hBconv : ConvT E n (.assumption A₁ :: Γ) B₁ B₂ (.sort w₁))
    (hN : HasTyT E n Γ N A₁)
    (hN' : HasTyT E n Γ N' A₁)
    (hNconv : ConvT E n Γ N N' A₁) :
    TyConvT E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) :=
  .of Γ (instantiate0 N B₁) (instantiate0 N' B₂) w₁
    (convT_instantiate0_sort_of_convT hA₁ hB₁ hB₂ hBconv hN hN' hNconv)

/-- Under the total valuation `fun _ => some 0`, every universe level `l : Level` evaluates to
    some natural number `some k`. -/
theorem eval_const_zero_isSome (l : Level) :
    ∃ k : Nat, eval (fun _ => some 0) l = some k := by
  induction l with
  | zero => exact ⟨0, rfl⟩
  | succ l ih =>
      rcases ih with ⟨k, hk⟩
      exact ⟨k + 1, by simp [eval, hk]⟩
  | max a b iha ihb =>
      rcases iha with ⟨ka, hka⟩
      rcases ihb with ⟨kb, hkb⟩
      exact ⟨max ka kb, by simp [eval, hka, hkb]⟩
  | imax a b iha ihb =>
      rcases iha with ⟨ka, hka⟩
      rcases ihb with ⟨kb, hkb⟩
      by_cases h : kb = 0
      · exact ⟨0, by simp [eval, hkb, h]⟩
      · exact ⟨max ka kb, by simp [eval, hka, hkb, h]⟩
  | param i => exact ⟨0, rfl⟩

/-- **General Non-Propositionality of Sort-Codomain Π-Types (`not_isPropTyI_pi_sort`):**
    Under universe consistency (`hSort`), for **every** domain `A : Expr Nat` and **every**
    sort level `l : Level`, `.pi A (.sort l)` (`A → Sort l`) is never a proposition
    (`¬ IsPropTyI E n Γ (.pi A (.sort l))`). -/
theorem not_isPropTyI_pi_sort
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (Γ : LCtx) (A : Expr Nat) (l : Level) :
    ¬ IsPropTyI E n Γ (.pi A (.sort l)) := by
  rintro ⟨⟨hpi⟩, _⟩
  let ⟨u, v, _, hB, hc⟩ := hasTyT_pi_inv hpi rfl
  have hcB := hasTyT_sort_inv hB rfl
  rcases eval_const_zero_isSome u with ⟨ku, hku⟩
  rcases eval_const_zero_isSome l with ⟨kl, hkl⟩
  have hv : eval (fun _ => some 0) v = some (kl + 1) := by
    have h := hSort hcB (fun _ => some 0)
    simp [eval, hkl] at h
    exact h.symm
  have himax : eval (fun _ => some 0) (.imax u v) = some 0 :=
    hSort hc (fun _ => some 0)
  simp [eval, hv, hku] at himax
  omega

/-- Cancelling `instantiate 1 r` against `lift 0 1 (lift 0 1 e)`. -/
theorem instantiate1_lift0_lift0 (r e : Expr Nat) :
    instantiate 1 r (lift 0 1 (lift 0 1 e)) = lift 0 1 e := by
  rw [lift_lift_merge 1 1 0 0 (Nat.le_refl 0) (by omega) e,
    instantiate_lift_cancel 2 0 1 r (Nat.zero_le 1) (by omega) e]

/-- Stage-1 codomain of `closedIrrPiL` after substituting `P` for `bvar 0`. -/
def closedIrrPi1L (P : Expr Nat) : Expr Nat :=
  .pi (.pi P (.sort .zero))
    (.pi (lift 0 1 P) (.pi (lift 0 1 (lift 0 1 P)) (.app (.bvar 2) (.bvar 1))))

/-- Stage-1 codomain of `closedIrrPiR` after substituting `P'` for `bvar 0`. -/
def closedIrrPi1R (P' : Expr Nat) : Expr Nat :=
  .pi (.pi P' (.sort .zero))
    (.pi (lift 0 1 P') (.pi (lift 0 1 (lift 0 1 P')) (.app (.bvar 2) (.bvar 0))))

/-- Stage-2 codomain of `closedIrrPiL` after substituting `F` for `bvar 0`. -/
def closedIrrPi2L (P F : Expr Nat) : Expr Nat :=
  .pi P (.pi (lift 0 1 P) (.app (lift 0 1 (lift 0 1 F)) (.bvar 1)))

/-- Stage-2 codomain of `closedIrrPiR` after substituting `F'` for `bvar 0`. -/
def closedIrrPi2R (P' F' : Expr Nat) : Expr Nat :=
  .pi P' (.pi (lift 0 1 P') (.app (lift 0 1 (lift 0 1 F')) (.bvar 0)))

/-- Stage-3 codomain of `closedIrrPiL` after substituting `p` for `bvar 0`. -/
def closedIrrPi3L (P F p : Expr Nat) : Expr Nat :=
  .pi P (.app (lift 0 1 F) (lift 0 1 p))

/-- Stage-3 codomain of `closedIrrPiR` after substituting `p'` for `bvar 0`. -/
def closedIrrPi3R (P' F' : Expr Nat) : Expr Nat :=
  .pi P' (.app (lift 0 1 F') (.bvar 0))

theorem instantiate0_closedIrrPiL (P : Expr Nat) :
    instantiate0 P (.pi (.pi (.bvar 0) (.sort .zero))
      (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1))))) =
      closedIrrPi1L P :=
  rfl

theorem instantiate0_closedIrrPiR (P' : Expr Nat) :
    instantiate0 P' (.pi (.pi (.bvar 0) (.sort .zero))
      (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0))))) =
      closedIrrPi1R P' :=
  rfl

theorem instantiate0_closedIrrPi1L (P F : Expr Nat) :
    instantiate0 F (.pi (lift 0 1 P) (.pi (lift 0 1 (lift 0 1 P)) (.app (.bvar 2) (.bvar 1)))) =
      closedIrrPi2L P F := by
  dsimp only [closedIrrPi2L, instantiate0, instantiate]
  rw [instantiate_lift_id, instantiate1_lift0_lift0]
  rfl

theorem instantiate0_closedIrrPi1R (P' F' : Expr Nat) :
    instantiate0 F' (.pi (lift 0 1 P') (.pi (lift 0 1 (lift 0 1 P')) (.app (.bvar 2) (.bvar 0)))) =
      closedIrrPi2R P' F' := by
  dsimp only [closedIrrPi2R, instantiate0, instantiate]
  rw [instantiate_lift_id, instantiate1_lift0_lift0]
  rfl

theorem instantiate0_closedIrrPi2L (P F p : Expr Nat) :
    instantiate0 p (.pi (lift 0 1 P) (.app (lift 0 1 (lift 0 1 F)) (.bvar 1))) =
      closedIrrPi3L P F p := by
  dsimp only [closedIrrPi3L, instantiate0, instantiate]
  rw [instantiate_lift_id, instantiate1_lift0_lift0]
  rfl

theorem instantiate0_closedIrrPi2R (P' F' p' : Expr Nat) :
    instantiate0 p' (.pi (lift 0 1 P') (.app (lift 0 1 (lift 0 1 F')) (.bvar 0))) =
      closedIrrPi3R P' F' := by
  dsimp only [closedIrrPi3R, instantiate0, instantiate]
  rw [instantiate_lift_id, instantiate1_lift0_lift0]
  rfl

theorem instantiate0_closedIrrPi3L (F p q : Expr Nat) :
    instantiate0 q (.app (lift 0 1 F) (lift 0 1 p)) = .app F p := by
  simp only [instantiate0, instantiate, instantiate_lift_id]

theorem instantiate0_closedIrrPi3R (F' q' : Expr Nat) :
    instantiate0 q' (.app (lift 0 1 F') (.bvar 0)) = .app F' q' := by
  simp only [instantiate0, instantiate, instantiate_lift_id]
  rfl

/-- Typing and conversion of the Stage-3 codomains of `closedIrrPiL` / `closedIrrPiR`
    in `.assumption P :: Γ`. -/
theorem convT_closedIrrPi3_cod (hcl : EnvClosed E) {Γ : LCtx} {P F F' p : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hF : HasTyT E n Γ F (.pi P (.sort .zero)))
    (hFF' : ConvT E n Γ F F' (.pi P (.sort .zero)))
    (hp : HasTyT E n Γ p P) :
    Nonempty (HasTyT E n (.assumption P :: Γ) (.app (lift 0 1 F) (lift 0 1 p)) (.sort .zero)) ∧
    Nonempty (ConvT E n (.assumption P :: Γ) (.app (lift 0 1 F) (lift 0 1 p))
      (.app (lift 0 1 F') (.bvar 0)) (.sort .zero)) := by
  let Γ₁ : LCtx := .assumption P :: Γ
  have hP₁ : HasTyT E n Γ₁ (lift 0 1 P) (.sort .zero) :=
    hasTyTWeaken (.assumption P) hcl (c := 0) hP
  have hF₁ : HasTyT E n Γ₁ (lift 0 1 F) (.pi (lift 0 1 P) (.sort .zero)) :=
    hasTyTWeaken (.assumption P) hcl (c := 0) hF
  have hFF'₁ : ConvT E n Γ₁ (lift 0 1 F) (lift 0 1 F') (.pi (lift 0 1 P) (.sort .zero)) :=
    convTWeaken (.assumption P) hcl (c := 0) hFF'
  have hp₁ : HasTyT E n Γ₁ (lift 0 1 p) (lift 0 1 P) :=
    hasTyTWeaken (.assumption P) hcl (c := 0) hp
  have hq₁ : HasTyT E n Γ₁ (.bvar 0) (lift 0 1 P) :=
    .bvar Γ₁ 0 (lift 0 1 P) rfl
  exact ⟨⟨.app Γ₁ (lift 0 1 F) (lift 0 1 p) (lift 0 1 P) (.sort .zero) hF₁ hp₁⟩,
    ⟨.app Γ₁ (lift 0 1 F) (lift 0 1 F') (lift 0 1 p) (.bvar 0) (lift 0 1 P) (.sort .zero)
      hFF'₁ (.irr Γ₁ (lift 0 1 P) (lift 0 1 p) (.bvar 0) hP₁ hp₁ hq₁)⟩⟩

/-- Typing and conversion of the Stage-2 codomains of `closedIrrPiL` / `closedIrrPiR`
    in `.assumption P :: Γ`, derived directly from `convT_closedIrrPi3_cod` at `p := .bvar 0`. -/
theorem convT_closedIrrPi2_cod (hcl : EnvClosed E) {Γ : LCtx} {P P' F F' : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hPP' : ConvT E n Γ P P' (.sort .zero))
    (hF : HasTyT E n Γ F (.pi P (.sort .zero)))
    (hFF' : ConvT E n Γ F F' (.pi P (.sort .zero))) :
    Nonempty (HasTyT E n (.assumption P :: Γ)
      (.pi (lift 0 1 P) (.app (lift 0 1 (lift 0 1 F)) (.bvar 1))) (.sort (.imax .zero .zero))) ∧
    Nonempty (ConvT E n (.assumption P :: Γ)
      (.pi (lift 0 1 P) (.app (lift 0 1 (lift 0 1 F)) (.bvar 1)))
      (.pi (lift 0 1 P') (.app (lift 0 1 (lift 0 1 F')) (.bvar 0)))
      (.sort (.imax .zero .zero))) := by
  let Γ₁ : LCtx := .assumption P :: Γ
  have hP₁ : HasTyT E n Γ₁ (lift 0 1 P) (.sort .zero) :=
    hasTyTWeaken (.assumption P) hcl (c := 0) hP
  have hPP'₁ : ConvT E n Γ₁ (lift 0 1 P) (lift 0 1 P') (.sort .zero) :=
    convTWeaken (.assumption P) hcl (c := 0) hPP'
  have hF₁ : HasTyT E n Γ₁ (lift 0 1 F) (.pi (lift 0 1 P) (.sort .zero)) :=
    hasTyTWeaken (.assumption P) hcl (c := 0) hF
  have hFF'₁ : ConvT E n Γ₁ (lift 0 1 F) (lift 0 1 F') (.pi (lift 0 1 P) (.sort .zero)) :=
    convTWeaken (.assumption P) hcl (c := 0) hFF'
  have hb0 : HasTyT E n Γ₁ (.bvar 0) (lift 0 1 P) :=
    .bvar Γ₁ 0 (lift 0 1 P) rfl
  rcases convT_closedIrrPi3_cod hcl hP₁ hF₁ hFF'₁ hb0 with ⟨⟨hcod⟩, ⟨hconv⟩⟩
  exact ⟨⟨.pi Γ₁ (lift 0 1 P) .zero _ .zero hP₁ hcod⟩,
    ⟨.pi Γ₁ (lift 0 1 P) (lift 0 1 P') _ _ .zero .zero hPP'₁ hconv⟩⟩

/-- Typing and conversion of the Stage-1 codomains of `closedIrrPiL` / `closedIrrPiR`
    in `.assumption (.pi P (.sort .zero)) :: Γ`, derived directly from `convT_closedIrrPi2_cod`
    at `F := .bvar 0`. -/
theorem convT_closedIrrPi1_cod (hcl : EnvClosed E) {Γ : LCtx} {P P' : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hPP' : ConvT E n Γ P P' (.sort .zero)) :
    Nonempty (HasTyT E n (.assumption (.pi P (.sort .zero)) :: Γ)
      (.pi (lift 0 1 P) (.pi (lift 0 1 (lift 0 1 P)) (.app (.bvar 2) (.bvar 1))))
      (.sort (.imax .zero (.imax .zero .zero)))) ∧
    Nonempty (ConvT E n (.assumption (.pi P (.sort .zero)) :: Γ)
      (.pi (lift 0 1 P) (.pi (lift 0 1 (lift 0 1 P)) (.app (.bvar 2) (.bvar 1))))
      (.pi (lift 0 1 P') (.pi (lift 0 1 (lift 0 1 P')) (.app (.bvar 2) (.bvar 0))))
      (.sort (.imax .zero (.imax .zero .zero)))) := by
  let Γ₁ : LCtx := .assumption (.pi P (.sort .zero)) :: Γ
  have hP₁ : HasTyT E n Γ₁ (lift 0 1 P) (.sort .zero) :=
    hasTyTWeaken (.assumption (.pi P (.sort .zero))) hcl (c := 0) hP
  have hPP'₁ : ConvT E n Γ₁ (lift 0 1 P) (lift 0 1 P') (.sort .zero) :=
    convTWeaken (.assumption (.pi P (.sort .zero))) hcl (c := 0) hPP'
  have hb0 : HasTyT E n Γ₁ (.bvar 0) (.pi (lift 0 1 P) (.sort .zero)) :=
    .bvar Γ₁ 0 (.pi (lift 0 1 P) (.sort .zero)) rfl
  rcases convT_closedIrrPi2_cod hcl hP₁ hPP'₁ hb0 (.refl Γ₁ (.bvar 0) _ hb0) with ⟨⟨hcod⟩, ⟨hconv⟩⟩
  exact ⟨⟨.pi Γ₁ (lift 0 1 P) .zero _ (.imax .zero .zero) hP₁ hcod⟩,
    ⟨.pi Γ₁ (lift 0 1 P) (lift 0 1 P') _ _ .zero (.imax .zero .zero) hPP'₁ hconv⟩⟩

/-- **Full Positive Repair of `closedIrrPi` in `LRTermDSubCore` (`lrTermDSubCore_closedIrrPi_of_sortRow`):**
    Whereas `LRTypeIN`, `LRTermI`, `LRTermS`, `LRTermSDI`, `LRTermDCore`, and `LRTermD` are all
    refuted on `closedIrrPi_conv` at `closedIrrPiCpt` (`not_lrTypeIN_closedIrrPi`,
    `not_lrTermDCore_closedIrrPi`, `not_lrTermD_closedIrrPi`), `LRTermDSubCore` positively
    satisfies `closedIrrPiL` vs `closedIrrPiR` at `closedIrrPiCpt` in every `EnvWfT E` and
    `CtxWfT E n Γ` under universe consistency (`hSort`)! -/
theorem lrTermDSubCore_closedIrrPi_of_sortRow (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level) :
    LRTermDSubCore E n Γ closedIrrPiL closedIrrPiR (.sort w) closedIrrPiCpt := by
  have hcl := envClosed_of_envWfT hW
  unfold closedIrrPiCpt closedIrrPiL closedIrrPiR
  rw [lrTermDSubCore_pi_iff]
  let Γ₀ : LCtx := .assumption (.sort .zero) :: Γ
  have hΓ₀ : CtxWfT E n Γ₀ :=
    .assumption Γ (.sort .zero) (.succ .zero) hΓ (.sort Γ .zero)
  have hbP : HasTyT E n Γ₀ (.bvar 0) (.sort .zero) := .bvar Γ₀ 0 (.sort .zero) rfl
  rcases convT_closedIrrPi1_cod hcl hbP (.refl Γ₀ (.bvar 0) (.sort .zero) hbP) with ⟨⟨hcod₁⟩, ⟨hconv₁⟩⟩
  have hdom₀ : HasTyT E n Γ₀ (.pi (.bvar 0) (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ₀ (.bvar 0) .zero (.sort .zero) (.succ .zero) hbP (.sort _ .zero)
  refine ⟨⟨w, .refl _⟩,
    .sort .zero,
    .pi (.pi (.bvar 0) (.sort .zero)) (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1)))),
    .sort .zero,
    .pi (.pi (.bvar 0) (.sort .zero)) (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0)))),
    .succ .zero,
    .imax (.imax .zero (.succ .zero)) (.imax .zero (.imax .zero .zero)),
    .refl _, .refl _, ⟨hΓ₀⟩, ⟨.refl _ _⟩,
    ⟨.of _ _ _ _ (.pi Γ₀ _ _ _ _ _ _ (.refl Γ₀ _ _ hdom₀) hconv₁)⟩,
    ⟨.sort Γ .zero⟩,
    ⟨.pi Γ₀ _ _ _ _ hdom₀ hcod₁⟩,
    by rw [lrTermDSubCore_bot_iff]; trivial, ?_⟩
  intro s₁ hs₁ P P' hP _ hPP' _
  rcases List.mem_singleton.mp hs₁ with rfl
  rw [instantiate0_closedIrrPiL, instantiate0_closedIrrPiR]
  unfold closedIrrPi1L closedIrrPi1R
  rw [lrTermDSubCore_pi_iff]
  have hdom₁ : HasTyT E n Γ (.pi P (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ P .zero (.sort .zero) (.succ .zero) hP (.sort _ .zero)
  have hdom₁_conv : ConvT E n Γ (.pi P (.sort .zero)) (.pi P' (.sort .zero))
      (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ P P' (.sort .zero) (.sort .zero) .zero (.succ .zero) hPP'
      (.refl _ (.sort .zero) (.sort (.succ .zero)) (.sort _ .zero))
  rcases convT_closedIrrPi1_cod hcl hP hPP' with ⟨⟨hcod_stage1⟩, ⟨hconv_stage1⟩⟩
  refine ⟨⟨_, .refl _⟩,
    .pi P (.sort .zero),
    .pi (lift 0 1 P) (.pi (lift 0 1 (lift 0 1 P)) (.app (.bvar 2) (.bvar 1))),
    .pi P' (.sort .zero),
    .pi (lift 0 1 P') (.pi (lift 0 1 (lift 0 1 P')) (.app (.bvar 2) (.bvar 0))),
    .imax .zero (.succ .zero),
    .imax .zero (.imax .zero .zero),
    .refl _, .refl _,
    ⟨.assumption Γ (.pi P (.sort .zero)) (.imax .zero (.succ .zero)) hΓ hdom₁⟩,
    ⟨.of _ _ _ _ hdom₁_conv⟩,
    ⟨.of _ _ _ _ hconv_stage1⟩,
    ⟨hdom₁⟩,
    ⟨hcod_stage1⟩,
    by rw [lrTermDSubCore_bot_iff]; trivial, ?_⟩
  intro s₂ hs₂ F F' hF _ hFF' hFrel
  rcases List.mem_singleton.mp hs₂ with rfl
  rw [instantiate0_closedIrrPi1L, instantiate0_closedIrrPi1R]
  unfold closedIrrPi2L closedIrrPi2R
  rw [lrTermDSubCore_pi_iff]
  rcases convT_closedIrrPi2_cod hcl hP hPP' hF hFF' with ⟨⟨hcod_stage2⟩, ⟨hconv_stage2⟩⟩
  refine ⟨⟨_, .refl _⟩,
    P, .pi (lift 0 1 P) (.app (lift 0 1 (lift 0 1 F)) (.bvar 1)),
    P', .pi (lift 0 1 P') (.app (lift 0 1 (lift 0 1 F')) (.bvar 0)),
    .zero, .imax .zero .zero,
    .refl _, .refl _,
    ⟨.assumption Γ P .zero hΓ hP⟩,
    ⟨.of _ _ _ .zero hPP'⟩,
    ⟨.of _ _ _ _ hconv_stage2⟩,
    ⟨hP⟩,
    ⟨hcod_stage2⟩,
    by rw [lrTermDSubCore_bot_iff]; trivial, ?_⟩
  intro s₃ hs₃ p p' hp _ _ _
  rcases List.mem_singleton.mp hs₃ with rfl
  rw [instantiate0_closedIrrPi2L, instantiate0_closedIrrPi2R]
  unfold closedIrrPi3L closedIrrPi3R
  rw [lrTermDSubCore_pi_iff]
  rcases convT_closedIrrPi3_cod hcl hP hF hFF' hp with ⟨⟨hcod_stage3⟩, ⟨hconv_stage3⟩⟩
  refine ⟨⟨_, .refl _⟩,
    P, .app (lift 0 1 F) (lift 0 1 p),
    P', .app (lift 0 1 F') (.bvar 0),
    .zero, .zero,
    .refl _, .refl _,
    ⟨.assumption Γ P .zero hΓ hP⟩,
    ⟨.of _ _ _ .zero hPP'⟩,
    ⟨.of _ _ _ .zero hconv_stage3⟩,
    ⟨hP⟩,
    ⟨hcod_stage3⟩,
    by rw [lrTermDSubCore_bot_iff]; trivial, ?_⟩
  intro s₄ hs₄ q q' _ hq' _ _
  rcases List.mem_singleton.mp hs₄ with rfl
  rw [instantiate0_closedIrrPi3L, instantiate0_closedIrrPi3R]
  have hF_notProp : ¬ IsPropTyI E n Γ (.pi P (.sort .zero)) :=
    not_isPropTyI_pi_sort hSort Γ P .zero
  have hFlam : LRTermDSubCore E n Γ F F' (.pi P (.sort .zero)) (.lam [([.sort], .sort)]) := by
    rcases hFrel (.lam [([.sort], .sort)]) (List.mem_singleton.mpr rfl) with hProp | hcore
    · exact (hF_notProp hProp).elim
    · exact hcore
  rw [lrTermDSubCore_lam_iff] at hFlam
  rcases hFlam with ⟨A₁, B₁, _, hpiRed, _, _, happ⟩
  have hpiEq := (whRed_pi_eq hpiRed).symm
  injection hpiEq with hA₁eq hB₁eq
  subst hA₁eq; subst hB₁eq
  have hpq' : ConvT E n Γ p q' P := .irr Γ P p q' hP hp hq'
  have hP_prop : IsPropTyI E n Γ P := isPropTyI_of_hasTyT_sort_zero hSort hP
  have hstep := happ ([.sort], .sort) (List.mem_singleton.mpr rfl) p q' hp hq' hpq'
    (fun _ _ => Or.inl hP_prop)
  change IsPropTyI E n Γ (.sort .zero) ∨
    LRTermDSubCore E n Γ (.app F p) (.app F' q') (.sort .zero) .sort at hstep
  rcases hstep with hSortProp | hcore
  · exact (not_isPropTyI_sort E n Γ .zero hSortProp).elim
  · exact hcore

/-- Positive satisfaction of `LRTermDSub` on `closedIrrPiL` vs `closedIrrPiR` at `closedIrrPiCpt`
    under `EnvWfT E` and `SortRow`. -/
theorem lrTermDSub_closedIrrPi_of_sortRow (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level) :
    LRTermDSub E n Γ closedIrrPiL closedIrrPiR (.sort w) closedIrrPiCpt :=
  Or.inr (lrTermDSubCore_closedIrrPi_of_sortRow hW hSort hΓ w)

/-- Extracting `LRTypeIN E n Γ A B (.pi .bot [])` from `LRTermDSubCore E n Γ A B (.sort u) (.pi .bot [])`. -/
theorem lrTypeIN_pi_bot_nil_of_lrTermDSubCore {Γ : LCtx} {A B : Expr Nat} {u : Level}
    (h : LRTermDSubCore E n Γ A B (.sort u) (.pi .bot [])) :
    LRTypeIN E n Γ A B (.pi .bot []) := by
  rw [lrTermDSubCore_pi_iff] at h
  rcases h with ⟨_, A₁, B₁, A₂, B₂, _, _, h1, h2, ⟨hΓ₁⟩, ⟨hcA⟩, ⟨hcB⟩, _, _, _, _⟩
  exact .pi h1 h2 hΓ₁ hcA hcB (.bot Γ A₁ A₂) (fun _ hs => (List.not_mem_nil _ hs).elim)

/-- Extracting `LRTypeIN E n Γ A B (.pi .bot [])` from `LRTermDSub E n Γ A B (.sort u) (.pi .bot [])`. -/
theorem lrTypeIN_pi_bot_nil_of_lrTermDSub {Γ : LCtx} {A B : Expr Nat} {u : Level}
    (h : LRTermDSub E n Γ A B (.sort u) (.pi .bot [])) :
    LRTypeIN E n Γ A B (.pi .bot []) := by
  rcases h with hP | hcore
  · exact (not_isPropTyI_sort E n Γ u hP).elim
  · exact lrTypeIN_pi_bot_nil_of_lrTermDSubCore hcore

/-- Repaired let-free `BotPiCpt` fundamental-lemma supply for the `ConvT`-guarded
    substitution-style logical relation `LRTermDSub`. -/
def FundamentalTermDSubBotDI_letFree (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ → ∀ {M A : Expr Nat},
    HasTyT E n Γ M A → ∀ u, BotPiCpt u → ApproxDI E EnvI.bot M u →
      LRTermDSub E n Γ M M A u) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ → ∀ {M M' A : Expr Nat},
    HasTyT E n Γ M A → HasTyT E n Γ M' A → ConvT E n Γ M M' A →
    ∀ u, BotPiCpt u → ApproxDI E EnvI.bot M u → LRTermDSub E n Γ M M' A u)

/-- `FundamentalTermDSubBotDI_letFree E n` implies Π-injectivity on all let-free contexts. -/
theorem piRow_letFree_of_fundamentalTermDSubBotDI_letFree (hW : EnvWfT E)
    (hF : FundamentalTermDSubBotDI_letFree E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hLF : LetFreeCtx Γ)
    {A₁ B₁ A₂ B₂ : Expr Nat}
    (h : TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  have hcl := envClosed_of_envWfT hW
  have hwalk : ∀ {X Y : Expr Nat} {u : Level},
      HasTyT E n Γ X (.sort u) → TyConvT E n Γ X Y →
      ApproxDI E EnvI.bot X (.pi .bot []) → LRTypeIN E n Γ X Y (.pi .bot []) := by
    intro X Y u hX htc
    revert u
    induction htc with
    | refl X =>
        intro u hX hAc
        exact lrTypeIN_pi_bot_nil_of_lrTermDSub
          (hF.1 hΓ hLF hX (.pi .bot []) botPiCpt_pi_bot_nil hAc)
    | of X Y v hc =>
        intro _ _ hAc
        exact lrTypeIN_pi_bot_nil_of_lrTermDSub
          (hF.2 hΓ hLF (convEnds hW hΓ hc).1 (convEnds hW hΓ hc).2.1 hc
            (.pi .bot []) botPiCpt_pi_bot_nil hAc)
    | trans X M Y c₁ c₂ ih₁ ih₂ =>
        intro u hX hAc
        obtain ⟨v, hM⟩ := tyConvT_endTyped hW hΓ c₁ hX
        have r₁ := ih₁ hX hAc
        have hcM := (approxDI_of_lrTypeIN_botPiCpt hW botPiCpt_pi_bot_nil r₁).2
        exact lrTypeIN_trans_of_envWfT hcl hW r₁ (ih₂ hM hcM)
  rcases tyConvT_firstOf_data h with heq | ⟨_, u, hc₀, _⟩
  · injection heq with eA eB
    subst eA; subst eB
    exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  · have hpi : HasTyT E n Γ (.pi A₁ B₁) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrTypeIN_pi_components (hwalk hpi h (approxDI_pi_bot_nil E EnvI.bot A₁ B₁))

/-- **Full Context Lifting (`piRow_of_fundamentalTermDSubBotDI_letFree`):**
    By §6's `piRow_of_letFree_piRow`, `FundamentalTermDSubBotDI_letFree E n` implies `PiRowField E n`
    across **all** well-formed contexts `CtxWfT E n Γ` (including contexts with `.letBinding`
    such as `zetaLocalSortCtx`). -/
theorem piRow_of_fundamentalTermDSubBotDI_letFree (hW : EnvWfT E)
    (hF : FundamentalTermDSubBotDI_letFree E n) :
    PiRowField E n :=
  fun {_} hΓ {_ _ _ _} h =>
    piRow_of_letFree_piRow hW
      (fun {_} hLF hΓ' {_ _ _ _} h' =>
        piRow_letFree_of_fundamentalTermDSubBotDI_letFree hW hF hΓ' hLF h')
      hΓ h

/-! ## §9. Recursor-Determinism from `recRef` Alone (`iotaWitnessS_same_recRef`,
`iotaWitnessS_unique_of_nMinors_one`), `W-K` Characterization of `ApproxDI` on `trueEnvU` &
`andEnvU` (Compiling `#7670`'s Open Observation), and `W-K` Teeth on `LetFreeCtx` Supplies -/

/-- **Recursor-Determinism from `recRef` Alone (`iotaWitnessS_same_recRef`):**
    Any two witnesses `w₁, w₂ : IotaWitnessS E` for the same recursor index `w₁.recRef = w₂.recRef`
    (even without assuming `w₁.ctorRef = w₂.ctorRef`) agree on `recMember`, `preMajor.length`,
    `recDoms`, `recBody`, `familyRef`, `famMember`, `nMinors`, `nindices`, and `nparams`. -/
theorem iotaWitnessS_same_recRef {E : ResolvedEnv} (w₁ w₂ : IotaWitnessS E)
    (hrec : w₁.recRef = w₂.recRef) :
    w₁.recMember = w₂.recMember ∧
      w₁.preMajor.length = w₂.preMajor.length ∧
      w₁.recDoms = w₂.recDoms ∧
      w₁.recBody = w₂.recBody ∧
      w₁.familyRef = w₂.familyRef ∧
      w₁.famMember = w₂.famMember ∧
      w₁.nMinors = w₂.nMinors ∧
      w₁.nindices = w₂.nindices ∧
      w₁.nparams = w₂.nparams := by
  obtain ⟨hmemr, hpreLen⟩ := iotaWitnessS_preMajor_length_eq w₁ w₂ hrec
  have hpeelRecEq : w₁.recDoms = w₂.recDoms ∧ w₁.recBody = w₂.recBody := by
    have a := w₁.hpeelRec
    have b := w₂.hpeelRec
    rw [w₁.hnmin] at a
    rw [w₂.hnmin, ← hmemr] at b
    have eq := Option.some.inj (a.symm.trans b)
    exact ⟨congrArg Prod.fst eq, congrArg Prod.snd eq⟩
  have hfam : w₁.familyRef = w₂.familyRef := by
    have hm₁ := w₁.hmajorTy
    have hm₂ := w₂.hmajorTy
    rw [← w₁.hpre] at hm₁
    rw [← w₂.hpre, ← hpreLen, ← hpeelRecEq.1] at hm₂
    have heq := Option.some.inj (hm₁.symm.trans hm₂)
    have hs := congrArg appsSpine heq
    rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
    injection hs with hc _
    injection hc
  have hmemf : w₁.famMember = w₂.famMember := by
    have a := w₁.hfam
    have b := w₂.hfam
    rw [← hfam] at b
    exact Option.some.inj (a.symm.trans b)
  have hnmin : w₁.nMinors = w₂.nMinors := by
    have a := w₁.hrecIdx
    have b := w₂.hrecIdx
    rw [← hrec, ← hfam] at b
    have := a.symm.trans b
    omega
  have hnidx : w₁.nindices = w₂.nindices := by
    have eq := w₁.hrecBody.symm.trans (hpeelRecEq.2.trans w₂.hrecBody)
    have s₁ := appsSpine_foldApps
      (.bvar (w₁.nMinors + w₁.nindices + 1) : Expr Nat)
      ((List.range w₁.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++ [Expr.bvar 0])
    have s₂ := appsSpine_foldApps
      (.bvar (w₂.nMinors + w₂.nindices + 1) : Expr Nat)
      ((List.range w₂.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++ [Expr.bvar 0])
    simp only [appsSpine_bvar, List.nil_append] at s₁ s₂
    have hs := congrArg appsSpine eq
    rw [s₁, s₂] at hs
    injection hs with hhead _
    injection hhead with hidx
    omega
  have hnpar : w₁.nparams = w₂.nparams := by
    have a := w₁.hnidx
    have b := w₂.hnidx
    rw [hmemf] at a
    omega
  exact ⟨hmemr, hpreLen, hpeelRecEq.1, hpeelRecEq.2, hfam, hmemf, hnmin, hnidx, hnpar⟩

/-- **Single-Constructor Branch Uniqueness (`iotaWitnessS_unique_of_nMinors_one`):**
    If `w₁, w₂ : IotaWitnessS E` share the same recursor `w₁.recRef = w₂.recRef` and belong to a
    single-constructor inductive family (`w₁.nMinors = 1`, e.g. `True`, `And`, `Eq`), then
    `w₁.ctorRef = w₂.ctorRef` holds automatically, and `w₁` and `w₂` agree on `ctorIdx`,
    `ctorRef`, `ctorMember`, `fields.length`, `shapes`, and `schema`. -/
theorem iotaWitnessS_unique_of_nMinors_one {E : ResolvedEnv} (w₁ w₂ : IotaWitnessS E)
    (hrec : w₁.recRef = w₂.recRef) (hmin : w₁.nMinors = 1) :
    w₁.ctorIdx = w₂.ctorIdx ∧
      w₁.ctorRef = w₂.ctorRef ∧
      w₁.ctorMember = w₂.ctorMember ∧
      w₁.fields.length = w₂.fields.length ∧
      w₁.shapes = w₂.shapes ∧
      w₁.schema = w₂.schema := by
  obtain ⟨_, _, _, _, hfam, _, hnmin, _, _⟩ := iotaWitnessS_same_recRef w₁ w₂ hrec
  have hidx₁ : w₁.ctorIdx = 0 := by
    have := w₁.hidx
    omega
  have hidx₂ : w₂.ctorIdx = 0 := by
    have := w₂.hidx
    omega
  have hidx : w₁.ctorIdx = w₂.ctorIdx := hidx₁.trans hidx₂.symm
  have hctor : w₁.ctorRef = w₂.ctorRef := by
    rw [w₁.hctorIdx, w₂.hctorIdx, hfam, hidx]
  have hmemc : w₁.ctorMember = w₂.ctorMember := by
    have a := w₁.hctor
    have b := w₂.hctor
    rw [← hctor] at b
    exact Option.some.inj (a.symm.trans b)
  obtain ⟨_, _, _, _, _, hfldsLen, hshapes, hschema⟩ := iotaWitnessS_same_branch w₁ w₂ hrec hctor
  exact ⟨hidx, hctor, hmemc, hfldsLen, hshapes, hschema⟩

/-- At every `EnvWfT E`, any legacy `w : IotaWitness E` adapts to a typed `wS : IotaWitnessS E`
    with matching `recRef`, `ctorRef`, `ls`, `lsC`, `preMajor`, `fields`, `ctorParams`,
    `familyRef`, `famMember`, `nparams`, `nindices`, `nMinors`, `ctorIdx`, `iotaLhsOfS`, and
    `iotaRhsOfS`. -/
theorem iotaWitnessS_of_iotaWitness_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) :
    ∃ wS : IotaWitnessS E,
      wS.recRef = w.recRef ∧
      wS.ctorRef = w.ctorRef ∧
      wS.ls = w.ls ∧
      wS.lsC = w.lsC ∧
      wS.preMajor = w.preMajor ∧
      wS.fields = w.fields ∧
      wS.ctorParams = w.ctorParams ∧
      wS.familyRef = w.familyRef ∧
      wS.famMember = w.famMember ∧
      wS.nparams = w.nparams ∧
      wS.nindices = w.nindices ∧
      wS.nMinors = w.nMinors ∧
      wS.ctorIdx = w.ctorIdx ∧
      iotaLhsOfS wS = iotaLhsOf w ∧
      iotaRhsOfS wS = iotaRhsOf w := by
  have unpack : ∀ {l r : Expr Nat}, DerivedIotaT E l r →
      ∃ wS : IotaWitnessS E, l = iotaLhsOfS wS ∧ r = iotaRhsOfS wS := by
    intro l r h; cases h with | of wS => exact ⟨wS, rfl, rfl⟩
  obtain ⟨ht⟩ := derivedIotaT_of_iotaWitness_envWfT hW w
  cases unpack ht with
  | intro wS hpair =>
      have hlhs : iotaLhsOfS wS = iotaLhsOf w := hpair.1.symm
      have hrhs : iotaRhsOfS wS = iotaRhsOf w := hpair.2.symm
      have hs := congrArg appsSpine hlhs
      unfold iotaLhsOfS iotaLhsOf recCall at hs
      rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
      injection hs with hconst hargs
      injection hconst with hrec hls
      have hmemr : wS.recMember = w.recMember := by
        have a := wS.hrec
        have b := w.hrec
        rw [← hrec] at b
        exact Option.some.inj (a.symm.trans b)
      have hpreLen : wS.preMajor.length = w.preMajor.length := by
        have h₁ := wS.hpre
        have h₂ := w.hpre
        have hn₁ := wS.hnmin
        have hn₂ := w.hnmin
        rw [hmemr] at hn₁
        omega
      obtain ⟨hpre, hmajSingleton⟩ := List.append_inj hargs hpreLen
      injection hmajSingleton with hmaj _
      have hsC := congrArg appsSpine hmaj
      unfold ctorMajor ctorSpine at hsC
      rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hsC
      injection hsC with hconstC hargsC
      injection hconstC with hctor hlsC
      have hmemc : wS.ctorMember = w.ctorMember := by
        have a := wS.hctor
        have b := w.hctor
        rw [← hctor] at b
        exact Option.some.inj (a.symm.trans b)
      have hpeelEq : wS.ctorDoms = w.ctorDoms ∧ wS.ctorResult = w.ctorResult := by
        have a := wS.hpeel
        have b := w.hpeel
        rw [wS.hnpar] at a
        rw [w.hnpar, ← hmemc] at b
        have eq := Option.some.inj (a.symm.trans b)
        exact ⟨congrArg Prod.fst eq, congrArg Prod.snd eq⟩
      have hfam : wS.familyRef = w.familyRef := by
        have hf₁ := wS.hfamApp
        have hf₂ := w.hfamApp
        rw [← hpeelEq.2] at hf₂
        unfold isFamilyApp at hf₁ hf₂
        split at hf₁
        · rename_i r ls' args heq
          rw [heq] at hf₂
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hf₁ hf₂
          exact hf₁.1.symm.trans hf₂.1
        · cases hf₁
      have hmemf : wS.famMember = w.famMember := by
        have a := wS.hfam
        have b := w.hfam
        rw [← hfam] at b
        exact Option.some.inj (a.symm.trans b)
      have hnmin : wS.nMinors = w.nMinors := by
        have a := wS.hrecIdx
        have b := w.hrecIdx
        rw [← hrec, ← hfam] at b
        have := a.symm.trans b
        omega
      have hrecBodyEq : wS.recBody = w.recBody := by
        have a := wS.hpeelRec
        have b := w.hpeelRec
        rw [wS.hnmin] at a
        rw [w.hnmin, ← hmemr] at b
        exact congrArg Prod.snd (Option.some.inj (a.symm.trans b))
      have hnidx : wS.nindices = w.nindices := by
        have eq := wS.hrecBody.symm.trans (hrecBodyEq.trans w.hrecBody)
        have s₁ := appsSpine_foldApps
          (.bvar (wS.nMinors + wS.nindices + 1) : Expr Nat)
          ((List.range wS.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++ [Expr.bvar 0])
        have s₂ := appsSpine_foldApps
          (.bvar (w.nMinors + w.nindices + 1) : Expr Nat)
          ((List.range w.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++ [Expr.bvar 0])
        simp only [appsSpine_bvar, List.nil_append] at s₁ s₂
        have hsB := congrArg appsSpine eq
        rw [s₁, s₂] at hsB
        injection hsB with hhead _
        injection hhead with hidxB
        omega
      have hnpar : wS.nparams = w.nparams := by
        have a := wS.hnidx
        have b := w.hnidx
        rw [hmemf] at a
        omega
      have hidx : wS.ctorIdx = w.ctorIdx := by
        have a := wS.hctorIdx
        have b := w.hctorIdx
        rw [← hctor, ← hfam] at b
        have := a.symm.trans b
        omega
      have hcpLen : wS.ctorParams.length = w.ctorParams.length := by
        rw [wS.hctorParams, w.hctorParams, hnpar]
      obtain ⟨hcp, hflds⟩ := List.append_inj hargsC hcpLen
      exact ⟨wS, hrec, hctor, hls, hlsC, hpre, hflds, hcp, hfam, hmemf,
        hnpar, hnidx, hnmin, hidx, hlhs, hrhs⟩

/-- **Compiling `#7670`'s Open Observation on `ApproxDI` (`approxDI_recursor_elim_no_ctor_inv`):**
    In `ApproxDI E ρ`, if a recursor `.const w.recRef ls` is applied to any pre-major spine `pre` of
    length `w.preMajor.length` and a major expression `x` that has no `.spine r args` compact in
    `ApproxDI E ρ x`, then the only compact of `recCall (.const w.recRef ls) pre x` in
    `ApproxDI E ρ` is `.bot`. -/
theorem approxDI_recursor_elim_no_ctor_inv {E : ResolvedEnv} {ρ : EnvI}
    (w : IotaWitnessS E) (ls : List Level) {pre : List (Expr Nat)}
    (hpre : pre.length = w.preMajor.length) {x : Expr Nat}
    (hno : ∀ r args, ¬ ApproxDI E ρ x (.spine r args)) {c : CptI}
    (h : ApproxDI E ρ (recCall (.const w.recRef ls) pre x) c) :
    c = .bot := by
  unfold recCall at h
  rw [approxDI_foldApps_iff] at h
  obtain ⟨d, hd, hfold⟩ := h
  rcases approxDI_recursor_const_inv w.hrec w.hrecK hd with
    rfl | ⟨w', us_pre, us_fields, c₀, hrecEq, hpreLen, _, _, rfl⟩
  · exact foldAppCpt_bot_inv hfold
  · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
    have htotLen : (us_pre ++ [ctorDemand w'.ctorRef w'.nparams us_fields]).length =
        (pre ++ [x]).length := by
      simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq, hpre]
    rcases (foldAppCpt_curryStep_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
    · rfl
    · obtain ⟨us_pre', us_maj', hsplitEq, hpreArgs, hmajArgs⟩ :=
        (ApproxArgsDemand.append_iff pre [x] _).mp hargs
      have hlenPre : us_pre.length = us_pre'.length := by
        rw [hpreArgs.length_eq, hpreLen, hpreLenEq, hpre]
      obtain ⟨rfl, hmajEq⟩ := List.append_inj hsplitEq hlenPre
      cases hmajArgs with
      | cons hmaj _ =>
          cases hmajEq
          have hsp := hmaj
            (.spine w'.ctorRef (List.replicate w'.nparams .bot ++ List.replicate us_fields.length .bot))
            (List.mem_cons_self _ _)
          exact (hno _ _ hsp).elim

/-- At `EnvI.bot`, any recursor elimination `recCall (.const w.recRef ls) pre (.bvar i)` at a bound
    variable major `.bvar i` has only `.bot` in `ApproxDI E EnvI.bot`. -/
theorem approxDI_recursor_elim_bvar_bot_inv {E : ResolvedEnv} (w : IotaWitnessS E)
    (ls : List Level) {pre : List (Expr Nat)} (hpre : pre.length = w.preMajor.length)
    (i : Nat) {c : CptI}
    (h : ApproxDI E EnvI.bot (recCall (.const w.recRef ls) pre (.bvar i)) c) :
    c = .bot :=
  approxDI_recursor_elim_no_ctor_inv w ls hpre
    (fun _ _ hsp => CptI.noConfusion (approxDI_bot_bvar_inv hsp)) h

/-- The `True.rec.{2}` eliminator applied to its motive `λ _ : True. Sort 1` and minor `Sort 0` in
    `trueEnvU`. -/
def trueEnvU_kRecElim : Expr Nat :=
  foldApps (.const 2 [.succ (.succ .zero)]) wTrueRecU.preMajor

/-- `True.rec.{2} (λ _ : True. Sort 1) (Sort 0) (.bvar 0)` at an open proof variable major in
    `trueEnvU`. -/
def trueEnvU_kRecVar : Expr Nat :=
  recCall (.const 2 [.succ (.succ .zero)]) wTrueRecU.preMajor (.bvar 0)

/-- `True.rec.{2} (λ _ : True. Sort 1) (Sort 0) ((λ y : True. y) True.intro)` at a closed
    β-redex proof major in `trueEnvU`. -/
def trueEnvU_kRecIdTt : Expr Nat :=
  recCall (.const 2 [.succ (.succ .zero)]) wTrueRecU.preMajor
    (.app (.lam (.const 0 []) (.bvar 0)) (.const 1 []))

/-- The let-free single-assumption context `[h : True]` in `trueEnvU`. -/
def trueEnvU_kVarCtx : LCtx :=
  [.assumption (.const 0 [])]

/-- `trueEnvU_kVarCtx` is let-free. -/
theorem letFreeCtx_trueEnvU_kVarCtx : LetFreeCtx trueEnvU_kVarCtx :=
  letFreeCtx_assumption letFreeCtx_nil

/-- `mixAndCtx` is let-free. -/
theorem letFreeCtx_mixAndCtx : LetFreeCtx mixAndCtx :=
  letFreeCtx_assumption (letFreeCtx_assumption (letFreeCtx_assumption
    (letFreeCtx_assumption (letFreeCtx_assumption letFreeCtx_nil))))

/-- In `ApproxDI trueEnvU EnvI.bot`, `trueEnvU_kRecVar` has only `.bot` as compact. -/
theorem approxDI_trueEnvU_kRecVar_bot_inv {c : CptI}
    (h : ApproxDI trueEnvU EnvI.bot trueEnvU_kRecVar c) : c = .bot := by
  obtain ⟨wS, hrec, _, _, _, hpre, _⟩ :=
    iotaWitnessS_of_iotaWitness_envWfT trueEnvUWfT wTrueRecU
  have h' : ApproxDI trueEnvU EnvI.bot
      (recCall (.const wS.recRef [.succ (.succ .zero)]) wTrueRecU.preMajor (.bvar 0)) c := by
    rw [hrec]
    exact h
  exact approxDI_recursor_elim_bvar_bot_inv wS [.succ (.succ .zero)] (by rw [hpre]) 0 h'

/-- `ApproxDI trueEnvU EnvI.bot trueEnvU_kRecVar .sort` is false (`W-K` in `ApproxDI` at `EnvI.bot`). -/
theorem not_approxDI_trueEnvU_kRecVar_sort :
    ¬ ApproxDI trueEnvU EnvI.bot trueEnvU_kRecVar .sort :=
  fun h => CptI.noConfusion (approxDI_trueEnvU_kRecVar_bot_inv h)

/-- `SemEqDI trueEnvU EnvI.bot trueEnvU_kRecVar (.sort .zero)` is false. -/
theorem not_semEqDI_trueEnvU_kRecVar_sort :
    ¬ SemEqDI trueEnvU EnvI.bot trueEnvU_kRecVar (.sort .zero) :=
  fun h => not_approxDI_trueEnvU_kRecVar_sort ((h .sort).mpr (.sort _ _))

/-- `PEqDI trueEnvU EnvI.bot (.sort (.succ .zero)) trueEnvU_kRecVar (.sort .zero)` is false. -/
theorem not_pEqDI_trueEnvU_kRecVar_sort :
    ¬ PEqDI trueEnvU EnvI.bot (.sort (.succ .zero)) trueEnvU_kRecVar (.sort .zero) := by
  intro h
  have hr : tprojI trueEnvU (denDI trueEnvU EnvI.bot (.sort (.succ .zero)))
      (denDI trueEnvU EnvI.bot (.sort .zero)) .sort :=
    ⟨.sort _ _, .sort, .sort _ _, .univ .sort⟩
  obtain ⟨hl, _⟩ := (h .sort).mpr hr
  exact not_approxDI_trueEnvU_kRecVar_sort hl

/-- `MajorStableDI` is refuted at `EnvI.bot` on `trueEnvU_kRecElim` in `trueEnvU`. -/
theorem not_majorStableDI_trueEnvU :
    ¬ MajorStableDI trueEnvU EnvI.bot (.const 0 []) (.sort (.succ .zero)) trueEnvU_kRecElim := by
  intro hstab
  have hP : IsPropIdealI trueEnvU (denDI trueEnvU EnvI.bot (.const 0 [])) := by
    intro a ha
    have hrigid : RigidConst trueEnvU 0 :=
      rigidConst_of_body_none (m := trueFamMember) rfl rfl (by decide)
    rcases approxDI_rigid_const_inv hrigid ha with rfl | rfl
    · exact .bot
    · exact .spine (m := trueFamMember) rfl rfl
  have hirr : PEqDI trueEnvU EnvI.bot (.const 0 []) (.bvar 0) (.const 1 []) :=
    pEqDI_irr hP (.bvar 0) (.const 1 [])
  have hstep : PEqDI trueEnvU EnvI.bot (.sort (.succ .zero))
      trueEnvU_kRecVar (iotaLhsOf wTrueRecU) :=
    hstab (.bvar 0) (.const 1 []) hirr
  have hι : PEqDI trueEnvU EnvI.bot (.sort (.succ .zero))
      (iotaLhsOf wTrueRecU) (.sort .zero) :=
    pEqDI_of_semEqDI (approxDI_iota_of_envWfT trueEnvUWfT wTrueRecU EnvI.bot)
  exact not_pEqDI_trueEnvU_kRecVar_sort (hstep.trans hι)

/-- `DomTyped` is refuted at `EnvI.bot` on `trueEnvU_kRecElim` in `trueEnvU` (because
    `ApproxDI.recursor` puts `ctorDemand 1 0 [] = [.spine 1 []]` at the major position). -/
theorem not_domTyped_trueEnvU_recElim :
    ¬ DomTyped trueEnvU (denDI trueEnvU EnvI.bot (.const 0 []))
        (denDI trueEnvU EnvI.bot trueEnvU_kRecElim) := by
  intro hdom
  obtain ⟨wS, hrec, _, _, _, hpre, _⟩ :=
    iotaWitnessS_of_iotaWitness_envWfT trueEnvUWfT wTrueRecU
  have hP : IsPropIdealI trueEnvU (denDI trueEnvU EnvI.bot (.const 0 [])) := by
    intro a ha
    have hrigid : RigidConst trueEnvU 0 :=
      rigidConst_of_body_none (m := trueFamMember) rfl rfl (by decide)
    rcases approxDI_rigid_const_inv hrigid ha with rfl | rfl
    · exact .bot
    · exact .spine (m := trueFamMember) rfl rfl
  have hns : NoSpine (denDI trueEnvU EnvI.bot trueEnvU_kRecElim) := by
    have hns0 := noSpine_recursor_prefix_approxDI wS [.succ (.succ .zero)] EnvI.bot
      wTrueRecU.preMajor (by rw [hpre]; exact Nat.le_refl _)
    rwa [hrec] at hns0
  exact not_majorStableDI_trueEnvU (majorStableDI_of_domTyped hP hdom hns)

/-- In `ApproxDI andEnvU EnvI.bot`, `mixAndRedex` has only `.bot` as compact. -/
theorem approxDI_andEnvU_mixAndRedex_bot_inv {c : CptI}
    (h : ApproxDI andEnvU EnvI.bot mixAndRedex c) : c = .bot := by
  obtain ⟨wS, hrec, _, _, _, hpre, _⟩ :=
    iotaWitnessS_of_iotaWitness_envWfT andEnvUWfT mixAndW
  have h' : ApproxDI andEnvU EnvI.bot
      (recCall (.const wS.recRef [.succ (.succ .zero)]) mixAndW.preMajor (.bvar 0)) c := by
    rw [hrec]
    exact h
  exact approxDI_recursor_elim_bvar_bot_inv wS [.succ (.succ .zero)] (by rw [hpre]) 0 h'

/-- `ApproxDI andEnvU EnvI.bot mixAndRedex (.pi .bot [])` is false (`W-K` fieldful in `ApproxDI`). -/
theorem not_approxDI_andEnvU_mixAndRedex_pi :
    ¬ ApproxDI andEnvU EnvI.bot mixAndRedex (.pi .bot []) :=
  fun h => CptI.noConfusion (approxDI_andEnvU_mixAndRedex_bot_inv h)

/-- `SemEqDI andEnvU EnvI.bot mixAndRedex mixPi` is false. -/
theorem not_semEqDI_andEnvU_mixAndRedex_mixPi :
    ¬ SemEqDI andEnvU EnvI.bot mixAndRedex mixPi :=
  fun h => not_approxDI_andEnvU_mixAndRedex_pi ((h (.pi .bot [])).mpr (approxDI_pi_bot_nil _ _ _ _))

/-- **Positive `ApproxDI` Evaluation at Closed β-Redex Proof Major (`semEqDI_trueEnvU_kRecIdTt`):**
    Whereas syntactic `WhRed trueEnvU` is stuck on `trueEnvU_kRecIdTt` (because `WhStep` does not
    reduce inside the major argument of a recursor), `ApproxDI` is β-sound on arguments
    (`approxDI_beta`) and ι-sound (`approxDI_iota_of_envWfT`), so `trueEnvU_kRecIdTt` is
    semantically equal to `.sort .zero` at **every** valuation `ρ : EnvI`! -/
theorem semEqDI_trueEnvU_kRecIdTt (ρ : EnvI) :
    SemEqDI trueEnvU ρ trueEnvU_kRecIdTt (.sort .zero) := by
  have hβ : SemEqDI trueEnvU ρ (.app (.lam (.const 0 []) (.bvar 0)) (.const 1 [])) (.const 1 []) :=
    fun c => approxDI_beta trueEnvU ρ (.const 0 []) (.bvar 0) (.const 1 []) c
  have hcong : SemEqDI trueEnvU ρ trueEnvU_kRecIdTt (iotaLhsOf wTrueRecU) :=
    semEqDI_app (semEqDI_refl trueEnvU ρ _) hβ
  exact semEqDI_trans hcong (approxDI_iota_of_envWfT trueEnvUWfT wTrueRecU ρ)

/-- **Positive `ApproxDI` Evaluation of `trueEnvU_kRecVar` Under the Canonical-Constructor Valuation
    (`semEqDI_trueEnvU_kRecVar_canonEnv`):**
    When variable `0` (`h : True`) is interpreted by `denDI trueEnvU EnvI.bot (.const 1 [])`,
    existing `ApproxDI` evaluates `trueEnvU_kRecVar` to `.sort .zero`. -/
theorem semEqDI_trueEnvU_kRecVar_canonEnv :
    SemEqDI trueEnvU (EnvI.cons (denDI trueEnvU EnvI.bot (.const 1 [])) EnvI.bot)
      trueEnvU_kRecVar (.sort .zero) := by
  intro c
  have hinst := (approxDI_subst_iff trueEnvU EnvI.bot 0 (.const 1 []) trueEnvU_kRecVar c).symm
  rw [EnvI.insert_zero, EnvI.drop_zero, lift_zero_idx] at hinst
  have hι := approxDI_iota_of_envWfT trueEnvUWfT wTrueRecU EnvI.bot c
  have hcl : ApproxDI trueEnvU EnvI.bot (.sort .zero) c ↔
      ApproxDI trueEnvU (EnvI.cons (denDI trueEnvU EnvI.bot (.const 1 [])) EnvI.bot) (.sort .zero) c :=
    ⟨approxDI_closed0_env _ _ (e := .sort .zero) rfl, approxDI_closed0_env _ _ (e := .sort .zero) rfl⟩
  exact hinst.trans (hι.trans hcl)

/-- `mixAndRhs` weak-head reduces in two `WhStep.beta` steps to `mixPi`. -/
theorem whRed_andEnvU_mixAndRhs_mixPi : WhRed andEnvU mixAndRhs mixPi :=
  .step (.appHead (.beta (.bvar 4) (.lam (.bvar 4) mixPi) (.bvar 2)))
    (.step (.beta (.bvar 3) mixPi (.bvar 1)) (.refl mixPi))

/-- **Positive `ApproxDI` Evaluation of `mixAndRedex` Under the Canonical-Constructor Valuation
    (`semEqDI_andEnvU_mixAndRedex_canonEnv`):**
    When variable `0` (`h : And a b`) in `mixAndCtx` is interpreted by
    `denDI andEnvU EnvI.bot mixAndMkApp`, existing `ApproxDI` evaluates `mixAndRedex` to `mixPi`. -/
theorem semEqDI_andEnvU_mixAndRedex_canonEnv :
    SemEqDI andEnvU (EnvI.cons (denDI andEnvU EnvI.bot mixAndMkApp) EnvI.bot)
      mixAndRedex mixPi := by
  let ρ₁ : EnvI := EnvI.cons (denDI andEnvU EnvI.bot mixAndMkApp) EnvI.bot
  have hbvar : ∀ k : Nat, SemEqDI andEnvU ρ₁ (.bvar (k + 1)) (.bvar (k + 2)) := by
    intro k c
    constructor <;> intro h
    · rcases approxDI_bvar_inv h with rfl | h0
      · exact .bot _ _
      · have hbot : c = .bot := h0
        subst hbot; exact .bot _ _
    · rcases approxDI_bvar_inv h with rfl | h0
      · exact .bot _ _
      · have hbot : c = .bot := h0
        subst hbot; exact .bot _ _
  intro c
  have hinst := (approxDI_subst_iff andEnvU EnvI.bot 0 mixAndMkApp
    (.app (foldApps (.const 2 [.succ (.succ .zero)])
      [.bvar 5, .bvar 4, .lam (andApp (.bvar 5) (.bvar 4)) (.sort (.succ .zero)),
       .lam (.bvar 5) (.lam (.bvar 5) mixPi)]) (.bvar 0)) c).symm
  rw [EnvI.insert_zero, EnvI.drop_zero, lift_zero_idx] at hinst
  have hrecEq : SemEqDI andEnvU ρ₁ mixAndRec
      (foldApps (.const 2 [.succ (.succ .zero)])
        [.bvar 5, .bvar 4, .lam (andApp (.bvar 5) (.bvar 4)) (.sort (.succ .zero)),
         .lam (.bvar 5) (.lam (.bvar 5) mixPi)]) := by
    refine semEqDI_app (semEqDI_app (semEqDI_app (semEqDI_app
      (semEqDI_refl _ _ _) (hbvar 3)) (hbvar 2)) ?_) ?_
    · exact semEqDI_lam _ _ (fun _ => semEqDI_refl _ _ _)
    · exact semEqDI_lam _ _ (fun _ => semEqDI_lam _ _ (fun _ => semEqDI_refl _ _ _))
  have hsub : ApproxDI andEnvU ρ₁ mixAndRedex c ↔ ApproxDI andEnvU EnvI.bot mixAndLhs c :=
    (semEqDI_app hrecEq (semEqDI_refl _ _ _) c).trans hinst
  have hι := (semEqDI_trans (approxDI_iota_of_envWfT andEnvUWfT mixAndW EnvI.bot)
    (semEqDI_whRed andEnvUWfT whRed_andEnvU_mixAndRhs_mixPi EnvI.bot)) c
  have hcl : ApproxDI andEnvU EnvI.bot mixPi c ↔ ApproxDI andEnvU ρ₁ mixPi c :=
    ⟨approxDI_closed0_env _ _ (e := mixPi) rfl, approxDI_closed0_env _ _ (e := mixPi) rfl⟩
  exact hsub.trans (hι.trans hcl)

private theorem list_eq_nil_or_snoc {α : Type} :
    (xs : List α) → xs = [] ∨ ∃ (pre : List α) (x : α), xs = pre ++ [x]
  | [] => Or.inl rfl
  | x :: xs =>
      match list_eq_nil_or_snoc xs with
      | Or.inl h => Or.inr ⟨[], x, by rw [h]; rfl⟩
      | Or.inr ⟨pre, y, h⟩ => Or.inr ⟨x :: pre, y, by rw [h]; rfl⟩

/-- Auxiliary lemma: no `WhStep E a e` can step a spine `foldApps (.const r ls) xs` when `r` has
    `m.body = none` and no argument `x ∈ xs` is a constant-headed spine. -/
theorem whStep_constSpine_no_ctor_false_aux {E : ResolvedEnv} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hm : E.members r = some m) (hbody : m.body = none)
    {a e : Expr Nat} (h : WhStep E a e) :
    ∀ (xs : List (Expr Nat)),
      (∀ x ∈ xs, ∀ (c : Nat) (us : List Level) (ys : List (Expr Nat)),
        x ≠ foldApps (.const c us) ys) →
      a = foldApps (.const r ls) xs → False := by
  induction h with
  | beta A b arg =>
      intro xs _ heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hf _
        exact F8EtaK.foldApps_const_ne_lam_any hf.symm
  | zeta A v b =>
      intro xs _ heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | delta hres hbody' =>
      intro xs _ heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · injection heq with hr _
        subst hr
        rw [hm] at hres
        injection hres with hm'
        subst hm'
        rw [hbody] at hbody'
        exact Option.noConfusion hbody'
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | iota hI =>
      intro xs hxs heq
      cases hI with
      | ofU w =>
          have hs := congrArg appsSpine heq
          unfold iotaLhsOf recCall at hs
          rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
          injection hs with _ hxs_eq
          have hmem : ctorMajor w ∈ xs := by
            subst hxs_eq
            exact List.mem_append_right _ (List.mem_singleton_self _)
          exact hxs (ctorMajor w) hmem w.ctorRef w.lsC (w.ctorParams ++ w.fields) rfl
      | ofUS w =>
          have hs := congrArg appsSpine heq
          unfold iotaLhsOfS recCall at hs
          rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
          injection hs with _ hxs_eq
          have hmem : foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields) ∈ xs := by
            subst hxs_eq
            exact List.mem_append_right _ (List.mem_singleton_self _)
          exact hxs _ hmem w.ctorRef w.lsC (w.ctorParams ++ w.fields) rfl
  | lit t =>
      intro xs _ heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | appHead _ ih =>
      intro xs hxs heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hpre _
        exact ih pre (fun y hy c us ys h' => hxs y (List.mem_append_left _ hy) c us ys h') hpre

/-- Any constant-headed spine `foldApps (.const r ls) xs` whose head has `m.body = none` and none
    of whose arguments is a constant-headed spine is `WhStep`-normal. -/
theorem whStep_constSpine_no_ctor_false {E : ResolvedEnv} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hm : E.members r = some m) (hbody : m.body = none)
    {xs : List (Expr Nat)}
    (hxs : ∀ x ∈ xs, ∀ (c : Nat) (us : List Level) (ys : List (Expr Nat)),
      x ≠ foldApps (.const c us) ys)
    {e : Expr Nat} (h : WhStep E (foldApps (.const r ls) xs) e) : False :=
  whStep_constSpine_no_ctor_false_aux hm hbody h xs hxs rfl

/-- `WhRed E` on such a spine is reflexive. -/
theorem whRed_constSpine_no_ctor_eq {E : ResolvedEnv} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hm : E.members r = some m) (hbody : m.body = none)
    {xs : List (Expr Nat)}
    (hxs : ∀ x ∈ xs, ∀ (c : Nat) (us : List Level) (ys : List (Expr Nat)),
      x ≠ foldApps (.const c us) ys)
    {e : Expr Nat} (h : WhRed E (foldApps (.const r ls) xs) e) :
    e = foldApps (.const r ls) xs := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStep_constSpine_no_ctor_false hm hbody hxs hs).elim

/-- `trueEnvU_kRecVar` is stuck for `WhRed trueEnvU`. -/
theorem whRed_trueEnvU_kRecVar_eq {e : Expr Nat}
    (h : WhRed trueEnvU trueEnvU_kRecVar e) : e = trueEnvU_kRecVar := by
  refine whRed_constSpine_no_ctor_eq (m := trueRecMemberU)
    (xs := [.lam (.const 0 []) (.sort (.succ .zero)), .sort .zero, .bvar 0]) rfl rfl ?_ h
  intro x hx c us ys heq
  have hx' : x = .lam (.const 0 []) (.sort (.succ .zero)) ∨ x = .sort .zero ∨ x = .bvar 0 := by
    simpa using hx
  rcases hx' with rfl | rfl | rfl
  · exact F8EtaK.foldApps_const_ne_lam_any heq.symm
  · have hs := congrArg appsSpine heq
    rw [appsSpine_foldApps_const] at hs
    exact Expr.noConfusion (congrArg Prod.fst hs)
  · have hs := congrArg appsSpine heq
    rw [appsSpine_foldApps_const] at hs
    exact Expr.noConfusion (congrArg Prod.fst hs)

/-- `mixAndRedex` is stuck for `WhRed andEnvU`. -/
theorem whRed_andEnvU_mixAndRedex_eq {e : Expr Nat}
    (h : WhRed andEnvU mixAndRedex e) : e = mixAndRedex := by
  refine whRed_constSpine_no_ctor_eq (m := andRecMemberU)
    (xs := [.bvar 4, .bvar 3, mixAndMot, mixAndMin, .bvar 0]) rfl rfl ?_ h
  intro x hx c us ys heq
  have hx' : x = .bvar 4 ∨ x = .bvar 3 ∨ x = mixAndMot ∨ x = mixAndMin ∨ x = .bvar 0 := by
    simpa using hx
  rcases hx' with rfl | rfl | rfl | rfl | rfl
  · have hs := congrArg appsSpine heq
    rw [appsSpine_foldApps_const] at hs
    exact Expr.noConfusion (congrArg Prod.fst hs)
  · have hs := congrArg appsSpine heq
    rw [appsSpine_foldApps_const] at hs
    exact Expr.noConfusion (congrArg Prod.fst hs)
  · exact F8EtaK.foldApps_const_ne_lam_any heq.symm
  · exact F8EtaK.foldApps_const_ne_lam_any heq.symm
  · have hs := congrArg appsSpine heq
    rw [appsSpine_foldApps_const] at hs
    exact Expr.noConfusion (congrArg Prod.fst hs)

/-- `trueEnvU_kVarCtx` is well-formed (`CtxWfT trueEnvU n trueEnvU_kVarCtx`). -/
def ctxWfT_trueEnvU_kVarCtx (n : Nat) : CtxWfT trueEnvU n trueEnvU_kVarCtx :=
  .assumption [] (.const 0 []) .zero .nil trueEnvUF_ty

/-- `ConvT trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar (.sort (.succ .zero))`
    by `ConvT.iota` at `True.intro` + `ConvT.irr` at `True : Sort 0`. -/
def convT_trueEnvU_kRecVar_sort (n : Nat) :
    ConvT trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar (.sort (.succ .zero)) :=
  let hhead : HasTyT trueEnvU n trueEnvU_kVarCtx trueEnvU_kRecElim
      (.pi (.const 0 []) (.app (.lam (.const 0 []) (.sort (.succ .zero))) (.bvar 0))) :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.const _ 2 [.succ (.succ .zero)] trueRecMemberU rfl rfl rfl)
        trueEnvUM_ty)
      trueEnvUS0_ty
  let hvar : HasTyT trueEnvU n trueEnvU_kVarCtx (.bvar 0) (.const 0 []) :=
    .bvar _ 0 _ rfl
  .trans _ _ _ _ _ (.symm _ _ _ _ trueEnvU_ci)
    (.tyConv _ _ _ _ _ _
      (.app _ _ _ _ _ _ _
        (.refl _ _ _ hhead)
        (.irr _ _ _ _ trueEnvUF_ty trueEnvUtt_ty hvar))
      trueEnvU_betaK)

/-- `TyConvT trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar`. -/
def tyConvT_trueEnvU_kRecVar_sort (n : Nat) :
    TyConvT trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar :=
  .of _ _ _ _ (convT_trueEnvU_kRecVar_sort n)

/-- `LRTypeINBiDI trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar` is false. -/
theorem not_lrTypeINBiDI_trueEnvU_kRecVar (n : Nat) :
    ¬ LRTypeINBiDI trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar := by
  intro h
  have hs := h .sort BotPiCpt.sort (Or.inl (.sort _ _))
  cases hs with
  | sort _ hR => exact Expr.noConfusion (whRed_trueEnvU_kRecVar_eq hR)

/-- `LRTermD trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar (.sort (.succ .zero)) .sort`
    is false. -/
theorem not_lrTermD_trueEnvU_kRecVar (n : Nat) :
    ¬ LRTermD trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar
        (.sort (.succ .zero)) .sort := by
  intro h
  have hLR := lrTypeIN_of_lrTermD_sort .sort h
  cases hLR with
  | sort _ hR => exact Expr.noConfusion (whRed_trueEnvU_kRecVar_eq hR)

/-- `LRTermDBiDI trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar (.sort (.succ .zero))`
    is false. -/
theorem not_lrTermDBiDI_trueEnvU_kRecVar (n : Nat) :
    ¬ LRTermDBiDI trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar
        (.sort (.succ .zero)) :=
  fun h => not_lrTermD_trueEnvU_kRecVar n (h .sort BotPiCpt.sort (Or.inl (.sort _ _)))

/-- `LRTermDSub trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar (.sort (.succ .zero)) .sort`
    is false. -/
theorem not_lrTermDSub_trueEnvU_kRecVar (n : Nat) :
    ¬ LRTermDSub trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar
        (.sort (.succ .zero)) .sort := by
  intro h
  rcases h with hP | hcore
  · exact not_isPropTyI_sort trueEnvU n trueEnvU_kVarCtx (.succ .zero) hP
  · rw [lrTermDSubCore_sort_iff] at hcore
    cases hcore.2 with
    | sort _ hR => exact Expr.noConfusion (whRed_trueEnvU_kRecVar_eq hR)

/-- **Admitted Obstruction (`W-K` at `trueEnvU` refutes `FundamentalLRINBotDI_letFree`):**
    Because `trueEnvU_kVarCtx` is let-free and `.sort` is `BotPiCpt`, `W-K` refutes
    `FundamentalLRINBotDI_letFree trueEnvU n` for every `n : Nat`. -/
theorem not_fundamentalLRINBotDI_letFree_trueEnvU (n : Nat) :
    ¬ FundamentalLRINBotDI_letFree trueEnvU n := by
  intro hF
  have h := hF letFreeCtx_trueEnvU_kVarCtx (ctxWfT_trueEnvU_kVarCtx n)
    (.sort _ .zero) (tyConvT_trueEnvU_kRecVar_sort n) .sort BotPiCpt.sort (.sort _ _)
  cases h with
  | sort _ hR => exact Expr.noConfusion (whRed_trueEnvU_kRecVar_eq hR)

/-- `W-K` at `trueEnvU` refutes `FundamentalTermBotDI_letFree trueEnvU n` for every `n : Nat`. -/
theorem not_fundamentalTermBotDI_letFree_trueEnvU (n : Nat) :
    ¬ FundamentalTermBotDI_letFree trueEnvU n :=
  fun hF => not_fundamentalLRINBotDI_letFree_trueEnvU n
    (fundamentalLRINBotDI_letFree_of_termBotDI_letFree trueEnvUWfT hF)

/-- `W-K` at `trueEnvU` refutes `FundamentalTermBiBotDI_letFree trueEnvU n` for every `n : Nat`. -/
theorem not_fundamentalTermBiBotDI_letFree_trueEnvU (n : Nat) :
    ¬ FundamentalTermBiBotDI_letFree trueEnvU n :=
  fun hF => not_fundamentalTermBotDI_letFree_trueEnvU n
    (fundamentalTermBotDI_letFree_of_biBotDI_letFree hF)

/-- `W-K` at `trueEnvU` refutes `FundamentalTermDSubBotDI_letFree trueEnvU n` for every `n : Nat`. -/
theorem not_fundamentalTermDSubBotDI_letFree_trueEnvU (n : Nat) :
    ¬ FundamentalTermDSubBotDI_letFree trueEnvU n := by
  intro hF
  have hconv := convT_trueEnvU_kRecVar_sort n
  have ends := convEnds trueEnvUWfT (ctxWfT_trueEnvU_kVarCtx n) hconv
  exact not_lrTermDSub_trueEnvU_kRecVar n
    (hF.2 (ctxWfT_trueEnvU_kVarCtx n) letFreeCtx_trueEnvU_kVarCtx
      ends.1 ends.2.1 hconv .sort BotPiCpt.sort (.sort _ _))

/-- `LRTypeIN andEnvU 0 mixAndCtx mixPi mixAndRedex (.pi .bot [])` is false. -/
theorem not_lrTypeIN_andEnvU_mixAnd :
    ¬ LRTypeIN andEnvU 0 mixAndCtx mixPi mixAndRedex (.pi .bot []) := by
  intro h
  cases h with
  | pi _ hR _ _ _ _ _ => exact Expr.noConfusion (whRed_andEnvU_mixAndRedex_eq hR)

/-- `LRTypeINBiDI andEnvU 0 mixAndCtx mixPi mixAndRedex` is false. -/
theorem not_lrTypeINBiDI_andEnvU_mixAnd :
    ¬ LRTypeINBiDI andEnvU 0 mixAndCtx mixPi mixAndRedex :=
  fun h => not_lrTypeIN_andEnvU_mixAnd
    (h (.pi .bot []) botPiCpt_pi_bot_nil (Or.inl (approxDI_pi_bot_nil _ _ _ _)))

/-- `LRTermD andEnvU 0 mixAndCtx mixPi mixAndRedex (.sort (.succ .zero)) (.pi .bot [])` is false. -/
theorem not_lrTermD_andEnvU_mixAnd :
    ¬ LRTermD andEnvU 0 mixAndCtx mixPi mixAndRedex (.sort (.succ .zero)) (.pi .bot []) :=
  fun h => not_lrTypeIN_andEnvU_mixAnd (lrTypeIN_of_lrTermD_sort (.pi .bot []) h)

/-- `LRTermDBiDI andEnvU 0 mixAndCtx mixPi mixAndRedex (.sort (.succ .zero))` is false. -/
theorem not_lrTermDBiDI_andEnvU_mixAnd :
    ¬ LRTermDBiDI andEnvU 0 mixAndCtx mixPi mixAndRedex (.sort (.succ .zero)) :=
  fun h => not_lrTermD_andEnvU_mixAnd
    (h (.pi .bot []) botPiCpt_pi_bot_nil (Or.inl (approxDI_pi_bot_nil _ _ _ _)))

/-- `LRTermDSub andEnvU 0 mixAndCtx mixPi mixAndRedex (.sort (.succ .zero)) (.pi .bot [])` is false. -/
theorem not_lrTermDSub_andEnvU_mixAnd :
    ¬ LRTermDSub andEnvU 0 mixAndCtx mixPi mixAndRedex (.sort (.succ .zero)) (.pi .bot []) :=
  fun h => not_lrTypeIN_andEnvU_mixAnd (lrTypeIN_pi_bot_nil_of_lrTermDSub h)

/-- **Admitted Obstruction (`W-K` fieldful at `andEnvU` refutes `FundamentalLRINBotDI_letFree`):**
    At `andEnvU` in the let-free context `mixAndCtx`, `mixAnd_conv` refutes
    `FundamentalLRINBotDI_letFree andEnvU 0` at `.pi .bot []` (`botPiCpt_pi_bot_nil`). -/
theorem not_fundamentalLRINBotDI_letFree_andEnvU :
    ¬ FundamentalLRINBotDI_letFree andEnvU 0 := by
  intro hF
  refine mixAnd_conv.elim fun hconv => ?_
  have ends := convEnds andEnvUWfT Rcic.Domain.Model.PiInversion.mixAndCtx_wf hconv
  exact not_lrTypeIN_andEnvU_mixAnd
    (hF letFreeCtx_mixAndCtx Rcic.Domain.Model.PiInversion.mixAndCtx_wf ends.2.1
      (.of _ _ _ _ (.symm _ _ _ _ hconv)) (.pi .bot []) botPiCpt_pi_bot_nil
      (approxDI_pi_bot_nil _ _ _ _))

/-- `W-K` fieldful at `andEnvU` refutes `FundamentalTermBotDI_letFree andEnvU 0`. -/
theorem not_fundamentalTermBotDI_letFree_andEnvU :
    ¬ FundamentalTermBotDI_letFree andEnvU 0 :=
  fun hF => not_fundamentalLRINBotDI_letFree_andEnvU
    (fundamentalLRINBotDI_letFree_of_termBotDI_letFree andEnvUWfT hF)

/-- `W-K` fieldful at `andEnvU` refutes `FundamentalTermBiBotDI_letFree andEnvU 0`. -/
theorem not_fundamentalTermBiBotDI_letFree_andEnvU :
    ¬ FundamentalTermBiBotDI_letFree andEnvU 0 :=
  fun hF => not_fundamentalTermBotDI_letFree_andEnvU
    (fundamentalTermBotDI_letFree_of_biBotDI_letFree hF)

/-- `W-K` fieldful at `andEnvU` refutes `FundamentalTermDSubBotDI_letFree andEnvU 0`. -/
theorem not_fundamentalTermDSubBotDI_letFree_andEnvU :
    ¬ FundamentalTermDSubBotDI_letFree andEnvU 0 := by
  intro hF
  refine mixAnd_conv.elim fun hconv => ?_
  have ends := convEnds andEnvUWfT Rcic.Domain.Model.PiInversion.mixAndCtx_wf hconv
  exact not_lrTypeIN_andEnvU_mixAnd
    (lrTypeIN_pi_bot_nil_of_lrTermDSub
      (hF.2 Rcic.Domain.Model.PiInversion.mixAndCtx_wf letFreeCtx_mixAndCtx
        ends.2.1 ends.1 (.symm _ _ _ _ hconv) (.pi .bot []) botPiCpt_pi_bot_nil
        (approxDI_pi_bot_nil _ _ _ _)))

/-! ## §10. Concrete K-Aware Lower-Ideal Model `ApproxDIK` and Readback `WhStepPiK` / `WhRedPiK`
    Repairing `W-K` at Both `trueEnvU` (0-Field) and `andEnvU` (Fieldful `mixAndRedex`)

We now repair the `W-K` obstructions of §9 with concrete constructions (zero `structure`/`class`
declarations):
1. **Compiled Proof-Irrelevant Major Conversion (`convT_iotaS_of_propMajor_eq`,
   `convT_iotaS_of_propMajor_tyConv`)**: compiles the syntactic `ConvT.irr` + `ConvT.app` +
   `ConvT.iota` derivation (`recCall (.const w.recRef w.ls) w.preMajor x ≡ iotaRhsOf w`) that was
   left commented out in `#7670` (`RcicNativeFamModelK.lean`).
2. **Concrete K-Aware Lower-Ideal Model (`ApproxDIK`, `denDIK`, `SemEqDIK`, `PEqDIK`)**: adds the
   concrete `recursorK` constructor for single-constructor `Prop` inductives
   (`piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1`), firing on any `⊥`-only major demand
   `u_maj` (`∀ u ∈ u_maj, u = .bot`) with empty field demands `List.replicate w.fields.length []`.
   - Preserves **unconditional canonical ι soundness** (`approxDIK_iotaS : SemEqDIK E ρ
     (iotaLhsOfS w) (iotaRhsOfS w)`) for **every** `w : IotaWitnessS E`, because in the `recursorK`
     inversion branch `iotaWitnessS_unique_of_nMinors_one` forces `w'.ctorRef = w.ctorRef` and
     `w'.schema = w.schema`, and `List.replicate w.fields.length []` is vacuously satisfied by
     `w.fields`.
   - Proves **unconditional 0-field K soundness** (`semEqDIK_k_zeroFields : SemEqDIK E ρ
     (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w)`) for **every** 0-field
     single-constructor `Prop` witness `w`, **every** `ρ : EnvI`, and **every** `x : Expr Nat`
     (in particular `semEqDIK_trueEnvU_kRec_all` at `trueEnvU`).
   - Proves **unconditional fieldful K soundness** (`semEqDIK_k_botFields : SemEqDIK E ρ
     (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w)`) whenever `w.fields` have
     `⊥`-only approximations at `ρ` and `x` has no `.spine w.ctorRef args` approximation at `ρ`
     (in particular `semEqDIK_andEnvU_mixAndRedex_mixPi` at `andEnvU`). -/

/-! ### §10.1. Compiled Syntactic `ConvT` Derivation for Proposition-Major Elimination -/

/-- Compiled syntactic `ConvT` derivation for eliminating a proposition-major recursor at an
    arbitrary proof `x : U` when the motive is definitionally constant across `x` and
    `ctorMajor w` (`instantiate0 x motive = instantiate0 (ctorMajor w) motive`):
    chains `ConvT.irr` (`x ≡ ctorMajor w : U`), `ConvT.app`, and `ConvT.iota`. -/
def convT_iotaS_of_propMajor_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {x U motive : Expr Nat}
    (hhead : HasTyT E n Γ (foldApps (.const w.recRef w.ls) w.preMajor) (.pi U motive))
    (hU : HasTyT E n Γ U (.sort .zero))
    (hx : HasTyT E n Γ x U)
    (hc : HasTyT E n Γ (ctorMajor w) U)
    (hrhs : HasTyT E n Γ (iotaRhsOf w) (instantiate0 (ctorMajor w) motive))
    (hmot : instantiate0 x motive = instantiate0 (ctorMajor w) motive) :
    ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w)
      (instantiate0 x motive) := by
  have hirr : ConvT E n Γ x (ctorMajor w) U := .irr Γ U x (ctorMajor w) hU hx hc
  have happ0 : ConvT E n Γ (.app (foldApps (.const w.recRef w.ls) w.preMajor) x)
      (.app (foldApps (.const w.recRef w.ls) w.preMajor) (ctorMajor w))
      (instantiate0 x motive) :=
    .app Γ _ _ x (ctorMajor w) U motive (.refl Γ _ (.pi U motive) hhead) hirr
  have happ : ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaLhsOf w)
      (instantiate0 x motive) := by
    unfold iotaLhsOf recCall
    rw [foldApps_snoc, foldApps_snoc]
    exact happ0
  have hlhsC0 : HasTyT E n Γ (.app (foldApps (.const w.recRef w.ls) w.preMajor) (ctorMajor w))
      (instantiate0 (ctorMajor w) motive) :=
    .app Γ _ (ctorMajor w) U motive hhead hc
  have hlhsC : HasTyT E n Γ (iotaLhsOf w) (instantiate0 (ctorMajor w) motive) := by
    unfold iotaLhsOf recCall
    rw [foldApps_snoc]
    exact hlhsC0
  have hiota : ConvT E n Γ (iotaLhsOf w) (iotaRhsOf w) (instantiate0 (ctorMajor w) motive) :=
    .iota Γ (iotaLhsOf w) (iotaRhsOf w) _ (.of w) hlhsC hrhs
  exact .trans Γ _ (iotaLhsOf w) (iotaRhsOf w) _ happ (hmot ▸ hiota)

/-- Compiled syntactic `ConvT` derivation for eliminating a proposition-major recursor at an
    arbitrary proof `x : U` with general `ConvT`-convertible motive instances:
    chains `ConvT.irr`, `ConvT.app`, and `ConvT.tyConv` around `ConvT.iota`. -/
def convT_iotaS_of_propMajor_tyConv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {x U motive : Expr Nat} {u : Level}
    (hhead : HasTyT E n Γ (foldApps (.const w.recRef w.ls) w.preMajor) (.pi U motive))
    (hU : HasTyT E n Γ U (.sort .zero))
    (hx : HasTyT E n Γ x U)
    (hc : HasTyT E n Γ (ctorMajor w) U)
    (hrhs : HasTyT E n Γ (iotaRhsOf w) (instantiate0 (ctorMajor w) motive))
    (hmot : ConvT E n Γ (instantiate0 (ctorMajor w) motive) (instantiate0 x motive) (.sort u)) :
    ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w)
      (instantiate0 x motive) := by
  have hirr : ConvT E n Γ x (ctorMajor w) U := .irr Γ U x (ctorMajor w) hU hx hc
  have happ0 : ConvT E n Γ (.app (foldApps (.const w.recRef w.ls) w.preMajor) x)
      (.app (foldApps (.const w.recRef w.ls) w.preMajor) (ctorMajor w))
      (instantiate0 x motive) :=
    .app Γ _ _ x (ctorMajor w) U motive (.refl Γ _ (.pi U motive) hhead) hirr
  have happ : ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaLhsOf w)
      (instantiate0 x motive) := by
    unfold iotaLhsOf recCall
    rw [foldApps_snoc, foldApps_snoc]
    exact happ0
  have hlhsC0 : HasTyT E n Γ (.app (foldApps (.const w.recRef w.ls) w.preMajor) (ctorMajor w))
      (instantiate0 (ctorMajor w) motive) :=
    .app Γ _ (ctorMajor w) U motive hhead hc
  have hlhsC : HasTyT E n Γ (iotaLhsOf w) (instantiate0 (ctorMajor w) motive) := by
    unfold iotaLhsOf recCall
    rw [foldApps_snoc]
    exact hlhsC0
  have hiota : ConvT E n Γ (iotaLhsOf w) (iotaRhsOf w) (instantiate0 (ctorMajor w) motive) :=
    .iota Γ (iotaLhsOf w) (iotaRhsOf w) _ (.of w) hlhsC hrhs
  exact .trans Γ _ (iotaLhsOf w) (iotaRhsOf w) _ happ
    (.tyConv Γ _ _ _ (instantiate0 x motive) u hiota hmot)

/-! ### §10.2. Concrete K-Aware Lower-Ideal Approximation `ApproxDIK` -/

/-- `ApproxDIK E ρ e c`: concrete lower-ideal approximation relation extending `ApproxDI` with the
    K-aware recursor clause `recursorK` for single-constructor `Prop` inductives
    (`piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1`). -/
inductive ApproxDIK (E : ResolvedEnv) : EnvI → Expr Nat → CptI → Prop
  | bot (ρ : EnvI) (e : Expr Nat) : ApproxDIK E ρ e .bot
  | bvar {ρ : EnvI} {i : Nat} {c : CptI} (h : ρ i c) : ApproxDIK E ρ (.bvar i) c
  | sort (ρ : EnvI) (l : Level) : ApproxDIK E ρ (.sort l) .sort
  | pi {ρ : EnvI} {A B : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (hA : ApproxDIK E ρ A a)
      (hB : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) ρ) B s.2) :
      ApproxDIK E ρ (.pi A B) (.pi a f)
  | lam {ρ : EnvI} {A b : Expr Nat} {f : List (List CptI × CptI)}
      (hb : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) ρ) b s.2) :
      ApproxDIK E ρ (.lam A b) (.lam f)
  | app {ρ : EnvI} {f a : Expr Nat} {g : List (List CptI × CptI)} {s : List CptI × CptI}
      (hf : ApproxDIK E ρ f (.lam g)) (hs : s ∈ g) (ha : ∀ u ∈ s.1, ApproxDIK E ρ a u) :
      ApproxDIK E ρ (.app f a) s.2
  | const (ρ : EnvI) (r : Nat) (ls : List Level) (hrigid : RigidConst E r) :
      ApproxDIK E ρ (.const r ls) (.spine r [])
  | delta {ρ : EnvI} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat} {c : CptI}
      (hdelta : DeltaConst E r m b)
      (h : ApproxDIK E EnvI.bot (instantiateLevels ls b) c) :
      ApproxDIK E ρ (.const r ls) c
  | recursor {ρ : EnvI} {w : IotaWitnessS E} (ls : List Level)
      {us_pre : List (List CptI)} {us_fields : List (List CptI)} {c : CptI}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxDIK E (EnvI.pushArgs ((us_pre ++ us_fields).map demand) EnvI.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxDIK E ρ (.const w.recRef ls)
        (curryStep (us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields]) c)
  | recursorK {ρ : EnvI} {w : IotaWitnessS E} (ls : List Level)
      {us_pre : List (List CptI)} {u_maj : List CptI} {c : CptI}
      (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
      (hpre : us_pre.length = w.preMajor.length)
      (hmaj : ∀ u ∈ u_maj, u = .bot)
      (h : ApproxDIK E
        (EnvI.pushArgs ((us_pre ++ List.replicate w.fields.length []).map demand) EnvI.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxDIK E ρ (.const w.recRef ls)
        (curryStep (us_pre ++ [u_maj]) c)
  | appSpine {ρ : EnvI} {f a : Expr Nat} {r : Nat} {args : List CptI} {u : CptI}
      (hf : ApproxDIK E ρ f (.spine r args)) (ha : ApproxDIK E ρ a u) :
      ApproxDIK E ρ (.app f a) (.spine r (args ++ [u]))
  | letE {ρ : EnvI} {A v b : Expr Nat} {c : CptI}
      (h : ApproxDIK E ρ (.app (.lam A b) v) c) :
      ApproxDIK E ρ (.letE A v b) c
  | lit {ρ : EnvI} {t : Nat} {c : CptI}
      (h : ApproxDIK E ρ (natExpand t) c) :
      ApproxDIK E ρ (.lit t) c

/-- The δ/ι/K lower-ideal denotation of `e` at environment `E` and variable valuation `ρ`. -/
def denDIK (E : ResolvedEnv) (ρ : EnvI) (e : Expr Nat) : CptI → Prop :=
  fun c => ApproxDIK E ρ e c

/-- Semantic equality in the δ/ι/K lower-ideal model `ApproxDIK`. -/
def SemEqDIK (E : ResolvedEnv) (ρ : EnvI) (a b : Expr Nat) : Prop :=
  ∀ c, ApproxDIK E ρ a c ↔ ApproxDIK E ρ b c

/-- Non-`⊥` overlap (`PEqI` counterpart) in `ApproxDIK`. -/
def PEqDIK (E : ResolvedEnv) (ρ : EnvI) (a b : Expr Nat) : Prop :=
  ∃ c, c ≠ .bot ∧ ApproxDIK E ρ a c ∧ ApproxDIK E ρ b c

theorem semEqDIK_refl (E : ResolvedEnv) (ρ : EnvI) (a : Expr Nat) : SemEqDIK E ρ a a :=
  fun _ => Iff.rfl

theorem semEqDIK_symm {E : ResolvedEnv} {ρ : EnvI} {a b : Expr Nat}
    (h : SemEqDIK E ρ a b) : SemEqDIK E ρ b a :=
  fun c => (h c).symm

theorem semEqDIK_trans {E : ResolvedEnv} {ρ : EnvI} {a b d : Expr Nat}
    (h₁ : SemEqDIK E ρ a b) (h₂ : SemEqDIK E ρ b d) : SemEqDIK E ρ a d :=
  fun c => (h₁ c).trans (h₂ c)

/-- Every `ApproxDI` approximation embeds conservatively into `ApproxDIK`. -/
theorem approxDIK_of_approxDI {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDI E ρ e c) : ApproxDIK E ρ e c := by
  induction h with
  | bot => exact .bot _ _
  | bvar h => exact .bvar h
  | sort => exact .sort _ _
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | lam _ ihb => exact .lam ihb
  | app _ hs _ ihf iha => exact .app ihf hs iha
  | const _ r ls hrig => exact .const _ r ls hrig
  | delta hdelta _ ih => exact .delta hdelta ih
  | recursor ls hpre hflds _ ih => exact .recursor ls hpre hflds ih
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih

theorem approxDIK_const_env {E : ResolvedEnv} (ρ ρ' : EnvI) {r : Nat} {ls : List Level} {c : CptI}
    (h : ApproxDIK E ρ (.const r ls) c) : ApproxDIK E ρ' (.const r ls) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hrigid => exact .const _ _ _ hrigid
  | delta hdelta h => exact .delta hdelta h
  | recursor ls hpre hflds h => exact .recursor ls hpre hflds h
  | recursorK ls hk hpre hmaj h => exact .recursorK ls hk hpre hmaj h

theorem approxDIK_mono_env {E : ResolvedEnv} {ρ ρ' : EnvI} (hle : EnvI.le ρ ρ')
    {e : Expr Nat} {c : CptI} (h : ApproxDIK E ρ e c) : ApproxDIK E ρ' e c := by
  induction h generalizing ρ' with
  | bot => exact .bot _ _
  | bvar h => exact .bvar (hle _ _ h)
  | sort => exact .sort _ _
  | pi _ _ ihA ihB => exact .pi (ihA hle) (fun s hs => ihB s hs (EnvI.le_cons hle _))
  | lam _ ihb => exact .lam (fun s hs => ihb s hs (EnvI.le_cons hle _))
  | app _ hs _ ihf iha => exact .app (ihf hle) hs (fun u hu => iha u hu hle)
  | const _ _ _ hrigid => exact .const _ _ _ hrigid
  | delta hdelta h => exact .delta hdelta h
  | recursor ls hpre hflds h => exact .recursor ls hpre hflds h
  | recursorK ls hk hpre hmaj h => exact .recursorK ls hk hpre hmaj h
  | appSpine _ _ ihf iha => exact .appSpine (ihf hle) (iha hle)
  | letE _ ih => exact .letE (ih hle)
  | lit _ ih => exact .lit (ih hle)

theorem approxDIK_mono_env_nonbot {E : ResolvedEnv} {ρ ρ' : EnvI}
    (hle : ∀ i c, c ≠ .bot → ρ i c → ρ' i c) {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ e c) : ApproxDIK E ρ' e c := by
  induction h generalizing ρ' with
  | bot => exact .bot _ _
  | @bvar ρ i c h =>
      cases c with
      | bot => exact .bot _ _
      | sort => exact .bvar (hle i .sort (fun h => nomatch h) h)
      | pi a f => exact .bvar (hle i (.pi a f) (fun h => nomatch h) h)
      | spine r args => exact .bvar (hle i (.spine r args) (fun h => nomatch h) h)
      | lam g => exact .bvar (hle i (.lam g) (fun h => nomatch h) h)
  | sort => exact .sort _ _
  | pi _ _ ihA ihB =>
      refine .pi (ihA hle) (fun s hs => ihB s hs ?_)
      intro i c hc
      cases i with
      | zero => exact id
      | succ i => exact hle i c hc
  | lam _ ihb =>
      refine .lam (fun s hs => ihb s hs ?_)
      intro i c hc
      cases i with
      | zero => exact id
      | succ i => exact hle i c hc
  | app _ hs _ ihf iha =>
      exact .app (ihf hle) hs (fun u hu => iha u hu hle)
  | const _ _ _ hrig => exact .const _ _ _ hrig
  | delta hd h => exact .delta hd h
  | recursor ls hpre hflds h => exact .recursor ls hpre hflds h
  | recursorK ls hk hpre hmaj h => exact .recursorK ls hk hpre hmaj h
  | appSpine _ _ ihf iha => exact .appSpine (ihf hle) (iha hle)
  | letE _ ih => exact .letE (ih hle)
  | lit _ ih => exact .lit (ih hle)

theorem approxDIK_cons_botDemand_iff {E : ResolvedEnv} {ρ : EnvI} {us : List CptI}
    (h : BotDemand us) (e : Expr Nat) (c : CptI) :
    ApproxDIK E (EnvI.cons (demand us) ρ) e c ↔ ApproxDIK E (EnvI.cons (EnvI.bot 0) ρ) e c := by
  constructor
  · refine approxDIK_mono_env_nonbot (fun i u hne => ?_)
    cases i with
    | zero => intro hu; exact (hne (h u hu)).elim
    | succ i => exact id
  · refine approxDIK_mono_env_nonbot (fun i u hne => ?_)
    cases i with
    | zero => intro hu; exact (hne hu).elim
    | succ i => exact id

theorem approxDIK_cons_botDemand_bot_iff {E : ResolvedEnv} {us : List CptI}
    (h : BotDemand us) (e : Expr Nat) (c : CptI) :
    ApproxDIK E (EnvI.cons (demand us) EnvI.bot) e c ↔ ApproxDIK E EnvI.bot e c := by
  refine (approxDIK_cons_botDemand_iff h e c).trans ⟨approxDIK_mono_env ?_, approxDIK_mono_env ?_⟩
  · intro i u; cases i <;> exact id
  · intro i u; cases i <;> exact id

theorem approxDIK_bvar_inv {E : ResolvedEnv} {ρ : EnvI} {i : Nat} {c : CptI}
    (h : ApproxDIK E ρ (.bvar i) c) : c = .bot ∨ ρ i c := by
  cases h with
  | bot => exact Or.inl rfl
  | bvar h => exact Or.inr h

theorem approxDIK_sort_inv {E : ResolvedEnv} {ρ : EnvI} {l : Level} {c : CptI}
    (h : ApproxDIK E ρ (.sort l) c) : c = .bot ∨ c = .sort := by
  cases h with
  | bot => exact Or.inl rfl
  | sort => exact Or.inr rfl

theorem approxDIK_rigid_const_inv {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    (hrigid : RigidConst E r) {c : CptI} (h : ApproxDIK E ρ (.const r ls) c) :
    c = .bot ∨ c = .spine r [] := by
  cases h with
  | bot => exact Or.inl rfl
  | const => exact Or.inr rfl
  | delta hdelta => exact (not_rigidConst_of_deltaConst hdelta hrigid).elim
  | @recursor _ w => exact (not_rigidConst_of_recursor w hrigid).elim
  | @recursorK _ w => exact (not_rigidConst_of_recursor w hrigid).elim

theorem approxDIK_delta_const_inv {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hdelta : DeltaConst E r m b) {c : CptI}
    (h : ApproxDIK E ρ (.const r ls) c) :
    ApproxDIK E EnvI.bot (instantiateLevels ls b) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hrigid => exact (not_rigidConst_of_deltaConst hdelta hrigid).elim
  | delta hdelta' h' =>
      have hm : m = _ := Option.some.inj (hdelta.1.symm.trans hdelta'.1)
      subst hm
      have hb : b = _ := Option.some.inj (hdelta.2.1.symm.trans hdelta'.2.1)
      subst hb
      exact h'
  | @recursor _ w => exact (not_deltaConst_of_recursor w hdelta).elim
  | @recursorK _ w => exact (not_deltaConst_of_recursor w hdelta).elim

theorem approxDIK_recursor_const_inv {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hrec : E.members r = some m) (hrecK : m.mclass = .recursorM) {c : CptI}
    (h : ApproxDIK E ρ (.const r ls) c) :
    c = .bot ∨
      (∃ (w : IotaWitnessS E) (us_pre us_fields : List (List CptI)) (c₀ : CptI),
        w.recRef = r ∧ us_pre.length = w.preMajor.length ∧ us_fields.length = w.fields.length ∧
        ApproxDIK E (EnvI.pushArgs ((us_pre ++ us_fields).map demand) EnvI.bot)
          (instantiateLevels ls w.schema) c₀ ∧
        c = curryStep (us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields]) c₀) ∨
      (∃ (w : IotaWitnessS E) (us_pre : List (List CptI)) (u_maj : List CptI) (c₀ : CptI),
        w.recRef = r ∧
        (piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1) ∧
        us_pre.length = w.preMajor.length ∧
        (∀ u ∈ u_maj, u = .bot) ∧
        ApproxDIK E
          (EnvI.pushArgs ((us_pre ++ List.replicate w.fields.length []).map demand) EnvI.bot)
          (instantiateLevels ls w.schema) c₀ ∧
        c = curryStep (us_pre ++ [u_maj]) c₀) := by
  cases h with
  | bot => exact Or.inl rfl
  | const _ _ _ hrigid => exact ((hrigid m hrec).2 hrecK).elim
  | delta hdelta =>
      have hm : m = _ := Option.some.inj (hrec.symm.trans hdelta.1)
      subst hm
      exact (hdelta.2.2.1 hrecK).elim
  | @recursor _ w _ us_pre us_fields c₀ hpre hflds h' =>
      exact Or.inr (Or.inl ⟨w, us_pre, us_fields, c₀, rfl, hpre, hflds, h', rfl⟩)
  | @recursorK _ w _ us_pre u_maj c₀ hk hpre hmaj h' =>
      exact Or.inr (Or.inr ⟨w, us_pre, u_maj, c₀, rfl, hk, hpre, hmaj, h', rfl⟩)

theorem approxDIK_pi_inv {E : ResolvedEnv} {ρ : EnvI} {A B : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ (.pi A B) c) :
    c = .bot ∨ ∃ a f, c = .pi a f ∧ ApproxDIK E ρ A a ∧
      ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) ρ) B s.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | pi hA hB => exact Or.inr ⟨_, _, rfl, hA, hB⟩

theorem approxDIK_lam_inv {E : ResolvedEnv} {ρ : EnvI} {A b : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ (.lam A b) c) :
    c = .bot ∨ ∃ f, c = .lam f ∧ ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) ρ) b s.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | lam hb => exact Or.inr ⟨_, rfl, hb⟩

theorem approxDIK_app_inv {E : ResolvedEnv} {ρ : EnvI} {f a : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ (.app f a) c) :
    c = .bot ∨
      (∃ g s, c = s.2 ∧ ApproxDIK E ρ f (.lam g) ∧ s ∈ g ∧ ∀ u ∈ s.1, ApproxDIK E ρ a u) ∨
      (∃ r args u, c = .spine r (args ++ [u]) ∧ ApproxDIK E ρ f (.spine r args) ∧ ApproxDIK E ρ a u) := by
  cases h with
  | bot => exact Or.inl rfl
  | app hf hs ha => exact Or.inr (Or.inl ⟨_, _, rfl, hf, hs, ha⟩)
  | appSpine hf ha => exact Or.inr (Or.inr ⟨_, _, _, rfl, hf, ha⟩)

theorem approxDIK_letE_inv {E : ResolvedEnv} {ρ : EnvI} {A v b : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ (.letE A v b) c) :
    c = .bot ∨ ApproxDIK E ρ (.app (.lam A b) v) c := by
  cases h with
  | bot => exact Or.inl rfl
  | letE h => exact Or.inr h

theorem approxDIK_lit_inv {E : ResolvedEnv} {ρ : EnvI} {t : Nat} {c : CptI}
    (h : ApproxDIK E ρ (.lit t) c) :
    c = .bot ∨ ApproxDIK E ρ (natExpand t) c := by
  cases h with
  | bot => exact Or.inl rfl
  | lit h => exact Or.inr h

theorem approxDIK_closedAt_env {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ e c) :
    ∀ {k : Nat} {ρ' : EnvI}, exprClosedAt k e = true → (∀ i < k, ρ i = ρ' i) →
      ApproxDIK E ρ' e c := by
  induction h with
  | bot => intro _ _ _ _; exact .bot _ _
  | @bvar ρ i c h =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, decide_eq_true_eq] at hcl
      exact .bvar (heq i hcl ▸ h)
  | sort => intro _ _ _ _; exact .sort _ _
  | pi _ _ ihA ihB =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .pi (ihA hcl.1 heq) (fun s hs => ihB s hs hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | lam _ ihb =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .lam (fun s hs => ihb s hs hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | app _ hs _ ihf iha =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      exact .app (ihf hcl.1 heq) hs (fun u hu => iha u hu hcl.2 heq)
  | const _ _ _ hrigid => intro _ _ _ _; exact .const _ _ _ hrigid
  | delta hdelta h => intro _ _ _ _; exact .delta hdelta h
  | recursor ls hpre hflds h => intro _ _ _ _; exact .recursor ls hpre hflds h
  | recursorK ls hk hpre hmaj h => intro _ _ _ _; exact .recursorK ls hk hpre hmaj h
  | appSpine _ _ ihf iha =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      exact .appSpine (ihf hcl.1 heq) (iha hcl.2 heq)
  | @letE _ A v b _ _ ih =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      have hcl' : exprClosedAt k (.app (.lam A b) v) = true := by
        simp only [exprClosedAt, Bool.and_eq_true]
        exact ⟨⟨hcl.1.1, hcl.2⟩, hcl.1.2⟩
      exact .letE (ih hcl' heq)
  | @lit _ t _ _ ih =>
      intro k ρ' _ heq
      exact .lit (ih (exprClosedAt_natExpand k t) heq)

theorem approxDIK_closed0_env {E : ResolvedEnv} (ρ ρ' : EnvI) {e : Expr Nat}
    (hcl : exprClosedAt 0 e = true) {c : CptI}
    (h : ApproxDIK E ρ e c) : ApproxDIK E ρ' e c :=
  approxDIK_closedAt_env h hcl (fun _ hi => (Nat.not_lt_zero _ hi).elim)

theorem approxDIK_natExpand_env {E : ResolvedEnv} (ρ ρ' : EnvI) (t : Nat) {c : CptI}
    (h : ApproxDIK E ρ (natExpand t) c) : ApproxDIK E ρ' (natExpand t) c :=
  approxDIK_closed0_env ρ ρ' (exprClosedAt_natExpand 0 t) h

theorem approxDIK_mono_update {E : ResolvedEnv} {ρ : EnvI} {j : Nat} {e : Expr Nat} {c : CptI}
    (us us' : List CptI) (hsub : ∀ u ∈ us, u ∈ us')
    (h : ApproxDIK E (EnvI.update ρ j (demand us)) e c) :
    ApproxDIK E (EnvI.update ρ j (demand us')) e c :=
  approxDIK_mono_env (fun i d hd => by
    by_cases hij : i = j
    · subst hij
      rw [EnvI.update_self] at hd ⊢
      exact hsub d hd
    · rw [EnvI.update_ne _ hij] at hd ⊢
      exact hd) h

theorem approxDIK_factor_list {E : ResolvedEnv} {ρ : EnvI} {j : Nat} {B : Expr Nat} :
    (f : List (List CptI × CptI)) →
    (∀ s ∈ f, ∃ us : List CptI, (∀ u ∈ us, ρ j u) ∧
      ApproxDIK E (EnvI.cons (demand s.1) (EnvI.update ρ j (demand us))) B s.2) →
    ∃ us : List CptI, (∀ u ∈ us, ρ j u) ∧
      ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) (EnvI.update ρ j (demand us))) B s.2
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | s :: rest, ih => by
      obtain ⟨us₁, h₁, hs⟩ := ih s (List.mem_cons_self _ _)
      obtain ⟨us₂, h₂, hrest⟩ :=
        approxDIK_factor_list rest (fun s' hs' => ih s' (List.mem_cons_of_mem _ hs'))
      refine ⟨us₁ ++ us₂, fun u hu => ?_, fun s' hs' => ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact h₁ u hu
        · exact h₂ u hu
      · cases List.mem_cons.mp hs' with
        | inl heq =>
            subst heq
            rw [EnvI.cons_update] at hs ⊢
            exact approxDIK_mono_update us₁ _ (fun u hu => List.mem_append.mpr (Or.inl hu)) hs
        | inr hs'' =>
            have := hrest s' hs''
            rw [EnvI.cons_update] at this ⊢
            exact approxDIK_mono_update us₂ _ (fun u hu => List.mem_append.mpr (Or.inr hu)) this

theorem approxDIK_factor_args {E : ResolvedEnv} {ρ : EnvI} {j : Nat} {a : Expr Nat} :
    (us0 : List CptI) →
    (∀ u ∈ us0, ∃ us : List CptI, (∀ w ∈ us, ρ j w) ∧
      ApproxDIK E (EnvI.update ρ j (demand us)) a u) →
    ∃ us : List CptI, (∀ w ∈ us, ρ j w) ∧
      ∀ u ∈ us0, ApproxDIK E (EnvI.update ρ j (demand us)) a u
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | u :: rest, ih => by
      obtain ⟨us₁, h₁, hu⟩ := ih u (List.mem_cons_self _ _)
      obtain ⟨us₂, h₂, hrest⟩ :=
        approxDIK_factor_args rest (fun u' hu' => ih u' (List.mem_cons_of_mem _ hu'))
      refine ⟨us₁ ++ us₂, fun w hw => ?_, fun u' hu' => ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact h₁ w hw
        · exact h₂ w hw
      · cases List.mem_cons.mp hu' with
        | inl heq =>
            subst heq
            exact approxDIK_mono_update us₁ _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hu
        | inr hu'' =>
            exact approxDIK_mono_update us₂ _ (fun w hw => List.mem_append.mpr (Or.inr hw))
              (hrest u' hu'')

theorem approxDIK_factor {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ e c) (j : Nat) :
    ∃ us : List CptI, (∀ u ∈ us, ρ j u) ∧ ApproxDIK E (EnvI.update ρ j (demand us)) e c := by
  induction h generalizing j with
  | bot => exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .bot _ _⟩
  | @bvar ρ i c h =>
      by_cases hij : i = j
      · subst hij
        refine ⟨[c], fun u hu => ?_, .bvar ?_⟩
        · have heq := List.mem_singleton.mp hu; subst heq; exact h
        · rw [EnvI.update_self]; exact List.mem_singleton.mpr rfl
      · exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim,
          .bvar (by rw [EnvI.update_ne _ hij]; exact h)⟩
  | sort => exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .sort _ _⟩
  | @pi ρ A B a f _ _ ihA ihB =>
      obtain ⟨usA, hA₁, hA₂⟩ := ihA j
      obtain ⟨usB, hB₁, hB₂⟩ := approxDIK_factor_list f (fun s hs => by
        obtain ⟨us, h₁, h₂⟩ := ihB s hs (j + 1)
        exact ⟨us, h₁, by rw [EnvI.cons_update]; exact h₂⟩)
      refine ⟨usA ++ usB, fun u hu => ?_, .pi ?_ ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hA₁ u hu
        · exact hB₁ u hu
      · exact approxDIK_mono_update usA _ (fun u hu => List.mem_append.mpr (Or.inl hu)) hA₂
      · intro s hs
        have := hB₂ s hs
        rw [EnvI.cons_update] at this ⊢
        exact approxDIK_mono_update usB _ (fun u hu => List.mem_append.mpr (Or.inr hu)) this
  | @lam ρ A b f _ ihb =>
      obtain ⟨usb, hb₁, hb₂⟩ := approxDIK_factor_list f (fun s hs => by
        obtain ⟨us, h₁, h₂⟩ := ihb s hs (j + 1)
        exact ⟨us, h₁, by rw [EnvI.cons_update]; exact h₂⟩)
      exact ⟨usb, hb₁, .lam hb₂⟩
  | @app ρ f a g s _ hs _ ihf iha =>
      obtain ⟨usf, hf₁, hf₂⟩ := ihf j
      obtain ⟨usa, ha₁, ha₂⟩ := approxDIK_factor_args s.1 (fun u hu => iha u hu j)
      refine ⟨usf ++ usa, fun w hw => ?_, .app ?_ hs ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact hf₁ w hw
        · exact ha₁ w hw
      · exact approxDIK_mono_update usf _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hf₂
      · exact fun u hu => approxDIK_mono_update usa _
          (fun w hw => List.mem_append.mpr (Or.inr hw)) (ha₂ u hu)
  | const _ _ _ hrigid =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .const _ _ _ hrigid⟩
  | delta hdelta h =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .delta hdelta h⟩
  | recursor ls hpre hflds h =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .recursor ls hpre hflds h⟩
  | recursorK ls hk hpre hmaj h =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .recursorK ls hk hpre hmaj h⟩
  | appSpine _ _ ihf iha =>
      obtain ⟨usf, hf₁, hf₂⟩ := ihf j
      obtain ⟨usa, ha₁, ha₂⟩ := iha j
      refine ⟨usf ++ usa, fun w hw => ?_, .appSpine ?_ ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact hf₁ w hw
        · exact ha₁ w hw
      · exact approxDIK_mono_update usf _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hf₂
      · exact approxDIK_mono_update usa _ (fun w hw => List.mem_append.mpr (Or.inr hw)) ha₂
  | letE _ ih =>
      obtain ⟨us, h₁, h₂⟩ := ih j
      exact ⟨us, h₁, .letE h₂⟩
  | lit _ ih =>
      obtain ⟨us, h₁, h₂⟩ := ih j
      exact ⟨us, h₁, .lit h₂⟩

theorem approxDIK_lift_intro {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ e c) :
    ∀ (k : Nat) (S : CptI → Prop), ApproxDIK E (EnvI.insert ρ k S) (lift k 1 e) c := by
  induction h with
  | bot => intro k S; exact .bot _ _
  | @bvar ρ i c h =>
      intro k S
      simp only [lift]
      by_cases hk : k ≤ i
      · rw [if_pos hk]
        exact .bvar (by rw [EnvI.insert_gt _ (Nat.lt_succ_of_le hk)]; simpa using h)
      · rw [if_neg hk]
        exact .bvar (by rw [EnvI.insert_lt _ (Nat.lt_of_not_le hk)]; exact h)
  | sort => intro k S; exact .sort _ _
  | pi _ _ ihA ihB =>
      intro k S
      simp only [lift]
      exact .pi (ihA k S) (fun s hs => by rw [EnvI.cons_insert]; exact ihB s hs (k + 1) S)
  | lam _ ihb =>
      intro k S
      simp only [lift]
      exact .lam (fun s hs => by rw [EnvI.cons_insert]; exact ihb s hs (k + 1) S)
  | app _ hs _ ihf iha =>
      intro k S
      simp only [lift]
      exact .app (ihf k S) hs (fun u hu => iha u hu k S)
  | const _ _ _ hrigid => intro k S; exact .const _ _ _ hrigid
  | delta hdelta h => intro k S; exact .delta hdelta h
  | recursor ls hpre hflds h => intro k S; exact .recursor ls hpre hflds h
  | recursorK ls hk hpre hmaj h => intro k S; exact .recursorK ls hk hpre hmaj h
  | appSpine _ _ ihf iha =>
      intro k S
      simp only [lift]
      exact .appSpine (ihf k S) (iha k S)
  | letE _ ih =>
      intro k S
      simp only [lift]
      exact .letE (ih k S)
  | lit _ ih =>
      intro k S
      simp only [lift]
      exact .lit (by have := ih k S; rwa [natExpand_lift] at this)

theorem approxDIK_lift_elim {E : ResolvedEnv} :
    (e : Expr Nat) → ∀ {ρ : EnvI} {k : Nat} {S : CptI → Prop} {c : CptI},
      ApproxDIK E (EnvI.insert ρ k S) (lift k 1 e) c → ApproxDIK E ρ e c
  | .bvar i, ρ, k, S, c, h => by
      simp only [lift] at h
      by_cases hk : k ≤ i
      · rw [if_pos hk] at h
        rcases approxDIK_bvar_inv h with h0 | h0
        · subst h0; exact .bot _ _
        · rw [EnvI.insert_gt _ (Nat.lt_succ_of_le hk)] at h0
          exact .bvar (by simpa using h0)
      · rw [if_neg hk] at h
        rcases approxDIK_bvar_inv h with h0 | h0
        · subst h0; exact .bot _ _
        · rw [EnvI.insert_lt _ (Nat.lt_of_not_le hk)] at h0
          exact .bvar h0
  | .sort l, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDIK_sort_inv h with h0 | h0 <;> subst h0
      · exact .bot _ _
      · exact .sort _ _
  | .const r ls, ρ, k, S, c, h => by
      simp only [lift] at h
      exact approxDIK_const_env (EnvI.insert ρ k S) ρ h
  | .app f a, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDIK_app_inv h with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨r, args, u, heq, hf, ha⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .app (approxDIK_lift_elim f hf) hs (fun u hu => approxDIK_lift_elim a (ha u hu))
      · subst heq
        exact .appSpine (approxDIK_lift_elim f hf) (approxDIK_lift_elim a ha)
  | .lam A b, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDIK_lam_inv h with h0 | ⟨f, heq, hb⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .lam (fun s hs => approxDIK_lift_elim b (by
          have := hb s hs; rw [EnvI.cons_insert] at this; exact this))
  | .pi A B, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDIK_pi_inv h with h0 | ⟨a, f, heq, hA, hB⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .pi (approxDIK_lift_elim A hA) (fun s hs => approxDIK_lift_elim B (by
          have := hB s hs; rw [EnvI.cons_insert] at this; exact this))
  | .letE A v b, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDIK_letE_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · rcases approxDIK_app_inv h' with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨r, args, u, heq, hf, ha⟩
        · subst h0; exact .letE (.bot _ _)
        · subst heq
          rcases approxDIK_lam_inv hf with h1 | ⟨f', heq', hb⟩
          · cases h1
          · cases heq'
            exact .letE (.app (.lam (fun s' hs' => approxDIK_lift_elim b (by
              have := hb s' hs'; rw [EnvI.cons_insert] at this; exact this))) hs
              (fun u hu => approxDIK_lift_elim v (ha u hu)))
        · rcases approxDIK_lam_inv hf with h1 | ⟨f', heq', _⟩
          · cases h1
          · cases heq'
  | .lit t, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxDIK_lit_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · exact .lit (approxDIK_natExpand_env _ _ t h')

theorem approxDIK_liftN_intro {E : ResolvedEnv} {e : Expr Nat} {c : CptI} :
    ∀ (ρ : EnvI) (j : Nat), ApproxDIK E (EnvI.drop ρ j) e c → ApproxDIK E ρ (lift 0 j e) c
  | ρ, 0, h => by rw [EnvI.drop_zero] at h; rw [lift_zero_idx]; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx]
      rw [EnvI.drop_succ] at h
      have := approxDIK_lift_intro (approxDIK_liftN_intro (EnvI.drop ρ 1) j h) 0 (ρ 0)
      rwa [EnvI.insert_drop_one] at this

theorem approxDIK_liftN_elim {E : ResolvedEnv} {e : Expr Nat} {c : CptI} :
    ∀ (ρ : EnvI) (j : Nat), ApproxDIK E ρ (lift 0 j e) c → ApproxDIK E (EnvI.drop ρ j) e c
  | ρ, 0, h => by rw [EnvI.drop_zero]; rw [lift_zero_idx] at h; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx] at h
      rw [EnvI.drop_succ]
      have h' : ApproxDIK E (EnvI.insert (EnvI.drop ρ 1) 0 (ρ 0)) (lift 0 1 (lift 0 j e)) c := by
        rwa [EnvI.insert_drop_one]
      exact approxDIK_liftN_elim (EnvI.drop ρ 1) j (approxDIK_lift_elim (lift 0 j e) h')

theorem approxDIK_subst_intro {E : ResolvedEnv} {ρ' : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ' e c) :
    ∀ (ρ : EnvI) (j : Nat) (r : Expr Nat),
      ρ' = EnvI.insert ρ j (denDIK E (EnvI.drop ρ j) r) →
      ApproxDIK E ρ (instantiate j (lift 0 j r) e) c := by
  induction h with
  | bot => intro ρ j r _; exact .bot _ _
  | @bvar ρ' i c h =>
      intro ρ j r hρ
      subst hρ
      simp only [instantiate]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        rw [EnvI.insert_self] at h
        exact approxDIK_liftN_intro ρ i h
      · rw [if_neg hij]
        by_cases hlt : j < i
        · rw [if_pos hlt]
          rw [EnvI.insert_gt _ hlt] at h
          exact .bvar h
        · rw [if_neg hlt]
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rw [EnvI.insert_lt _ hil] at h
          exact .bvar h
  | sort => intro ρ j r _; exact .sort _ _
  | pi _ _ ihA ihB =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .pi (ihA ρ j r hρ) (fun s hs => ihB s hs _ (j + 1) r
        (by rw [hρ, EnvI.cons_insert, EnvI.drop_cons]))
  | lam _ ihb =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .lam (fun s hs => ihb s hs _ (j + 1) r (by rw [hρ, EnvI.cons_insert, EnvI.drop_cons]))
  | app _ hs _ ihf iha =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .app (ihf ρ j r hρ) hs (fun u hu => iha u hu ρ j r hρ)
  | const _ _ _ hrigid => intro _ _ _ _; exact .const _ _ _ hrigid
  | delta hdelta h => intro _ _ _ _; exact .delta hdelta h
  | recursor ls hpre hflds h => intro _ _ _ _; exact .recursor ls hpre hflds h
  | recursorK ls hk hpre hmaj h => intro _ _ _ _; exact .recursorK ls hk hpre hmaj h
  | appSpine _ _ ihf iha =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .appSpine (ihf ρ j r hρ) (iha ρ j r hρ)
  | letE _ ih =>
      intro ρ j r hρ
      have := ih ρ j r hρ
      simp only [instantiate] at this ⊢
      exact .letE this
  | lit _ ih =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .lit (by have := ih ρ j r hρ; rwa [natExpand_instantiate] at this)

theorem approxDIK_subst_elim {E : ResolvedEnv} :
    (e : Expr Nat) → ∀ {ρ : EnvI} {j : Nat} {r : Expr Nat} {c : CptI},
      ApproxDIK E ρ (instantiate j (lift 0 j r) e) c →
      ApproxDIK E (EnvI.insert ρ j (denDIK E (EnvI.drop ρ j) r)) e c
  | .bvar i, ρ, j, r, c, h => by
      simp only [instantiate] at h
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at h
        exact .bvar (by rw [EnvI.insert_self]; exact approxDIK_liftN_elim ρ i h)
      · rw [if_neg hij] at h
        by_cases hlt : j < i
        · rw [if_pos hlt] at h
          rcases approxDIK_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [EnvI.insert_gt _ hlt]; exact h0)
        · rw [if_neg hlt] at h
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rcases approxDIK_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [EnvI.insert_lt _ hil]; exact h0)
  | .sort l, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxDIK_sort_inv h with h0 | h0 <;> subst h0
      · exact .bot _ _
      · exact .sort _ _
  | .const k ls, ρ, j, r, c, h => by
      simp only [instantiate] at h
      exact approxDIK_const_env ρ _ h
  | .app f a, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxDIK_app_inv h with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨k, args, u, heq, hf, ha⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .app (approxDIK_subst_elim f hf) hs (fun u hu => approxDIK_subst_elim a (ha u hu))
      · subst heq
        exact .appSpine (approxDIK_subst_elim f hf) (approxDIK_subst_elim a ha)
  | .lam A b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxDIK_lam_inv h with h0 | ⟨f, heq, hb⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .lam (fun s hs => by
          rw [EnvI.cons_insert, ← EnvI.drop_cons (demand s.1) ρ j]
          exact approxDIK_subst_elim b (hb s hs))
  | .pi A B, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxDIK_pi_inv h with h0 | ⟨a, f, heq, hA, hB⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .pi (approxDIK_subst_elim A hA) (fun s hs => by
          rw [EnvI.cons_insert, ← EnvI.drop_cons (demand s.1) ρ j]
          exact approxDIK_subst_elim B (hB s hs))
  | .letE A v b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxDIK_letE_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · rcases approxDIK_app_inv h' with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨k, args, u, heq, hf, ha⟩
        · subst h0; exact .letE (.bot _ _)
        · subst heq
          rcases approxDIK_lam_inv hf with h1 | ⟨f', heq', hb⟩
          · cases h1
          · cases heq'
            rw [lift_shift_comp_idx] at hb
            exact .letE (.app (.lam (fun s' hs' => by
              rw [EnvI.cons_insert, ← EnvI.drop_cons (demand s'.1) ρ j]
              exact approxDIK_subst_elim b (hb s' hs'))) hs
              (fun u hu => approxDIK_subst_elim v (ha u hu)))
        · rcases approxDIK_lam_inv hf with h1 | ⟨f', heq', _⟩
          · cases h1
          · cases heq'
  | .lit t, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxDIK_lit_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · exact .lit (approxDIK_natExpand_env _ _ t h')

theorem approxDIK_subst_iff (E : ResolvedEnv) (ρ : EnvI) (j : Nat) (a e : Expr Nat) (c : CptI) :
    ApproxDIK E ρ (instantiate j (lift 0 j a) e) c ↔
      ApproxDIK E (EnvI.insert ρ j (denDIK E (EnvI.drop ρ j) a)) e c :=
  ⟨approxDIK_subst_elim e, fun h => approxDIK_subst_intro h ρ j a rfl⟩

theorem approxDIK_subst_demand_iff (E : ResolvedEnv) (ρ : EnvI) (j : Nat) (a e : Expr Nat)
    (c : CptI) :
    ApproxDIK E ρ (instantiate j (lift 0 j a) e) c ↔
      ∃ us : List CptI, (∀ u ∈ us, ApproxDIK E (EnvI.drop ρ j) a u) ∧
        ApproxDIK E (EnvI.insert ρ j (demand us)) e c := by
  rw [approxDIK_subst_iff]
  constructor
  · intro h
    obtain ⟨us, hus, hup⟩ := approxDIK_factor h j
    rw [EnvI.update_insert_self] at hup
    exact ⟨us, fun u hu => by have := hus u hu; rwa [EnvI.insert_self] at this, hup⟩
  · rintro ⟨us, hus, hins⟩
    refine approxDIK_mono_env (fun i d hd => ?_) hins
    by_cases hij : i = j
    · subst hij
      rw [EnvI.insert_self] at hd ⊢
      exact hus d hd
    · by_cases hlt : i < j
      · rw [EnvI.insert_lt _ hlt] at hd ⊢; exact hd
      · have hgt : j < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (Ne.symm hij)
        rw [EnvI.insert_gt _ hgt] at hd ⊢; exact hd

/-- Pointwise finite-demand approximation of a list of arguments `args` in `ApproxDIK`. -/
inductive ApproxArgsDemandK (E : ResolvedEnv) (ρ : EnvI) :
    List (Expr Nat) → List (List CptI) → Prop
  | nil : ApproxArgsDemandK E ρ [] []
  | cons {a : Expr Nat} {as : List (Expr Nat)} {us : List CptI} {uss : List (List CptI)}
      (ha : ∀ u ∈ us, ApproxDIK E ρ a u)
      (has : ApproxArgsDemandK E ρ as uss) :
      ApproxArgsDemandK E ρ (a :: as) (us :: uss)

theorem ApproxArgsDemandK.length_eq {E : ResolvedEnv} {ρ : EnvI}
    {args : List (Expr Nat)} {uss : List (List CptI)}
    (h : ApproxArgsDemandK E ρ args uss) : uss.length = args.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem ApproxArgsDemandK.append_iff {E : ResolvedEnv} {ρ : EnvI}
    (xs ys : List (Expr Nat)) (uss : List (List CptI)) :
    ApproxArgsDemandK E ρ (xs ++ ys) uss ↔
      ∃ uss₁ uss₂, uss = uss₁ ++ uss₂ ∧
        ApproxArgsDemandK E ρ xs uss₁ ∧ ApproxArgsDemandK E ρ ys uss₂ := by
  induction xs generalizing uss with
  | nil =>
      simp only [List.nil_append]
      constructor
      · intro h; exact ⟨[], uss, rfl, .nil, h⟩
      · rintro ⟨uss₁, uss₂, rfl, h₁, h₂⟩
        cases h₁
        exact h₂
  | cons x xs ih =>
      simp only [List.cons_append]
      constructor
      · intro h
        cases h with
        | cons hx hrest =>
            obtain ⟨uss₁, uss₂, rfl, h₁, h₂⟩ := (ih _).mp hrest
            exact ⟨_ :: uss₁, uss₂, rfl, .cons hx h₁, h₂⟩
      · rintro ⟨uss₁, uss₂, rfl, h₁, h₂⟩
        cases h₁ with
        | cons hx h₁' =>
            exact .cons hx ((ih _).mpr ⟨_, _, rfl, h₁', h₂⟩)

theorem approxArgsDemandK_replicate_nil {E : ResolvedEnv} {ρ : EnvI} :
    (xs : List (Expr Nat)) → ApproxArgsDemandK E ρ xs (List.replicate xs.length [])
  | [] => .nil
  | _ :: xs => .cons (fun _ h => (List.not_mem_nil _ h).elim) (approxArgsDemandK_replicate_nil xs)

theorem approxDIK_instPrefix_demand_iff (E : ResolvedEnv) (ρ : EnvI)
    (args : List (Expr Nat)) (e : Expr Nat) (c : CptI) :
    ApproxDIK E ρ (instPrefix args e) c ↔
      ∃ uss, ApproxArgsDemandK E ρ args uss ∧
        ApproxDIK E (EnvI.pushArgs (uss.map demand) ρ) e c := by
  induction args generalizing e with
  | nil =>
      simp only [instPrefix]
      constructor
      · intro h; exact ⟨[], .nil, h⟩
      · rintro ⟨uss, hargs, h⟩
        cases hargs
        exact h
  | cons a as ih =>
      simp only [instPrefix]
      rw [ih]
      constructor
      · rintro ⟨uss, has, hsub⟩
        have hlen : (uss.map demand).length = as.length := by
          rw [List.length_map, has.length_eq]
        rw [← hlen, approxDIK_subst_demand_iff, EnvI.drop_pushArgs_self] at hsub
        obtain ⟨us, ha, he⟩ := hsub
        rw [EnvI.insert_pushArgs_self] at he
        exact ⟨us :: uss, .cons ha has, he⟩
      · rintro ⟨uss₀, hargs, he⟩
        cases hargs with
        | @cons _ _ us uss ha has =>
            refine ⟨uss, has, ?_⟩
            have hlen : (uss.map demand).length = as.length := by
              rw [List.length_map, has.length_eq]
            rw [← hlen, approxDIK_subst_demand_iff, EnvI.drop_pushArgs_self]
            refine ⟨us, ha, ?_⟩
            rw [EnvI.insert_pushArgs_self]
            exact he

theorem approxDIK_instPrefix_closed_iff (E : ResolvedEnv) (ρ : EnvI)
    (args : List (Expr Nat)) (e : Expr Nat) (hcl : exprClosedAt args.length e = true)
    (c : CptI) :
    ApproxDIK E ρ (instPrefix args e) c ↔
      ∃ uss, ApproxArgsDemandK E ρ args uss ∧
        ApproxDIK E (EnvI.pushArgs (uss.map demand) EnvI.bot) e c := by
  rw [approxDIK_instPrefix_demand_iff]
  constructor
  · rintro ⟨uss, hargs, h⟩
    have hcl' : exprClosedAt (uss.map demand).length e = true := by
      rwa [List.length_map, hargs.length_eq]
    exact ⟨uss, hargs,
      approxDIK_closedAt_env h hcl' (fun i hi => EnvI.pushArgs_lt _ ρ EnvI.bot hi)⟩
  · rintro ⟨uss, hargs, h⟩
    have hcl' : exprClosedAt (uss.map demand).length e = true := by
      rwa [List.length_map, hargs.length_eq]
    exact ⟨uss, hargs,
      approxDIK_closedAt_env h hcl' (fun i hi => EnvI.pushArgs_lt _ EnvI.bot ρ hi)⟩

theorem approxDIK_beta (E : ResolvedEnv) (ρ : EnvI) (A b a : Expr Nat) :
    SemEqDIK E ρ (.app (.lam A b) a) (instantiate0 a b) := by
  intro c
  constructor
  · intro h
    rcases approxDIK_app_inv h with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨k, args, u, heq, hf, ha⟩
    · subst h0; exact .bot _ _
    · subst heq
      rcases approxDIK_lam_inv hf with h1 | ⟨f', heq', hb⟩
      · cases h1
      · cases heq'
        have h₁ : ApproxDIK E (EnvI.cons (denDIK E ρ a) ρ) b s.2 :=
          approxDIK_mono_env (fun i d hd => by
            cases i with
            | zero => exact ha d hd
            | succ i => exact hd) (hb s hs)
        have h₂ := approxDIK_subst_intro h₁ ρ 0 a (by rw [EnvI.insert_zero, EnvI.drop_zero])
        rwa [lift_zero_idx] at h₂
    · rcases approxDIK_lam_inv hf with h1 | ⟨f', heq', _⟩
      · cases h1
      · cases heq'
  · intro h
    have h₁ : ApproxDIK E ρ (instantiate 0 (lift 0 0 a) b) c := by rwa [lift_zero_idx]
    have h₂ := approxDIK_subst_elim b h₁
    rw [EnvI.insert_zero, EnvI.drop_zero] at h₂
    obtain ⟨us, hus, h₃⟩ := approxDIK_factor h₂ 0
    have h₄ : ApproxDIK E (EnvI.cons (demand us) ρ) b c := by
      refine approxDIK_mono_env (fun i d hd => ?_) h₃
      cases i with
      | zero => rw [EnvI.update_self] at hd; exact hd
      | succ i => rw [EnvI.update_ne _ (Nat.succ_ne_zero i)] at hd; exact hd
    exact .app (s := (us, c)) (.lam (f := [(us, c)]) (fun s hs => by
      have heq := List.mem_singleton.mp hs
      subst heq
      exact h₄)) (List.mem_singleton.mpr rfl)
      (fun u hu => hus u hu)

theorem approxDIK_zeta (E : ResolvedEnv) (ρ : EnvI) (A v b : Expr Nat) :
    SemEqDIK E ρ (.letE A v b) (instantiate0 v b) := by
  intro c
  constructor
  · intro h
    rcases approxDIK_letE_inv h with h0 | h'
    · subst h0; exact .bot _ _
    · exact (approxDIK_beta E ρ A b v c).mp h'
  · intro h
    exact .letE ((approxDIK_beta E ρ A b v c).mpr h)

theorem approxDIK_lit (E : ResolvedEnv) (ρ : EnvI) (t : Nat) :
    SemEqDIK E ρ (.lit t) (natExpand t) := by
  intro c
  constructor
  · intro h
    rcases approxDIK_lit_inv h with h0 | h'
    · subst h0; exact .bot _ _
    · exact h'
  · intro h
    exact .lit h

theorem approxDIK_delta_bot {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hdelta : DeltaConst E r m b) (c : CptI) :
    ApproxDIK E ρ (.const r ls) c ↔ ApproxDIK E EnvI.bot (instantiateLevels ls b) c :=
  ⟨approxDIK_delta_const_inv hdelta, .delta hdelta⟩

theorem semEqDIK_delta {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hdelta : DeltaConst E r m b)
    (hcl : exprClosedAt 0 b = true) :
    SemEqDIK E ρ (.const r ls) (instantiateLevels ls b) := by
  intro c
  have hcl_inst : exprClosedAt 0 (instantiateLevels ls b) = true := by
    rw [exprClosedAt_instantiateLevels]; exact hcl
  rw [approxDIK_delta_bot hdelta]
  exact ⟨approxDIK_closed0_env EnvI.bot ρ hcl_inst, approxDIK_closed0_env ρ EnvI.bot hcl_inst⟩

theorem semEqDIK_of_whStep_delta {E : ResolvedEnv} (hW : EnvWfT E)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b) (ρ : EnvI) :
    SemEqDIK E ρ (.const r ls) (instantiateLevels ls b) := by
  obtain ⟨hd, hcl⟩ := envWfT_member_body_closed hW r m b hres hbody
  exact semEqDIK_delta hd hcl

/-! ### §10.3. Unconditional Canonical ι Soundness (`approxDIK_iotaS`) and K Soundness
    (`semEqDIK_k_botFields`, `semEqDIK_k_zeroFields`) -/

inductive AppCptK (E : ResolvedEnv) (ρ : EnvI) : CptI → Expr Nat → CptI → Prop
  | bot (d : CptI) (x : Expr Nat) : AppCptK E ρ d x .bot
  | app {g : List (List CptI × CptI)} {s : List CptI × CptI} {x : Expr Nat}
      (hs : s ∈ g) (hx : ∀ u ∈ s.1, ApproxDIK E ρ x u) :
      AppCptK E ρ (.lam g) x s.2
  | appSpine {r : Nat} {args : List CptI} {x : Expr Nat} {u : CptI}
      (hx : ApproxDIK E ρ x u) :
      AppCptK E ρ (.spine r args) x (.spine r (args ++ [u]))

theorem approxDIK_app_iff_appCptK (E : ResolvedEnv) (ρ : EnvI) (f x : Expr Nat) (c : CptI) :
    ApproxDIK E ρ (.app f x) c ↔ ∃ d, ApproxDIK E ρ f d ∧ AppCptK E ρ d x c := by
  constructor
  · intro h
    rcases approxDIK_app_inv h with rfl | ⟨g, s, rfl, hf, hs, hx⟩ | ⟨r, args, u, rfl, hf, hx⟩
    · exact ⟨.bot, .bot ρ f, .bot .bot x⟩
    · exact ⟨.lam g, hf, .app hs hx⟩
    · exact ⟨.spine r args, hf, .appSpine hx⟩
  · rintro ⟨d, hf, hstep⟩
    cases hstep with
    | bot => exact .bot ρ (.app f x)
    | app hs hx => exact .app hf hs hx
    | appSpine hx => exact .appSpine hf hx

inductive FoldAppCptK (E : ResolvedEnv) (ρ : EnvI) : CptI → List (Expr Nat) → CptI → Prop
  | bot (d : CptI) (xs : List (Expr Nat)) : FoldAppCptK E ρ d xs .bot
  | nil (c : CptI) : FoldAppCptK E ρ c [] c
  | cons {d d' c : CptI} {x : Expr Nat} {xs : List (Expr Nat)}
      (hstep : AppCptK E ρ d x d') (hrest : FoldAppCptK E ρ d' xs c) :
      FoldAppCptK E ρ d (x :: xs) c

theorem approxDIK_foldApps_iff (E : ResolvedEnv) (ρ : EnvI) (f : Expr Nat)
    (xs : List (Expr Nat)) (c : CptI) :
    ApproxDIK E ρ (foldApps f xs) c ↔ ∃ d, ApproxDIK E ρ f d ∧ FoldAppCptK E ρ d xs c := by
  induction xs generalizing f with
  | nil =>
      simp only [foldApps]
      constructor
      · intro h; exact ⟨c, h, .nil c⟩
      · rintro ⟨d, hd, hfold⟩
        cases hfold with
        | bot => exact .bot ρ f
        | nil => exact hd
  | cons x xs ih =>
      simp only [foldApps]
      rw [ih]
      constructor
      · rintro ⟨d', hfx, hrest⟩
        rw [approxDIK_app_iff_appCptK] at hfx
        obtain ⟨d, hf, hstep⟩ := hfx
        exact ⟨d, hf, .cons hstep hrest⟩
      · rintro ⟨d, hf, hfold⟩
        cases hfold with
        | bot => exact ⟨.bot, .bot ρ (.app f x), .bot .bot xs⟩
        | cons hstep hrest =>
            exact ⟨_, (approxDIK_app_iff_appCptK E ρ f x _).mpr ⟨d, hf, hstep⟩, hrest⟩

theorem foldAppCptK_bot_inv {E : ResolvedEnv} {ρ : EnvI} {xs : List (Expr Nat)} {c : CptI}
    (h : FoldAppCptK E ρ .bot xs c) : c = .bot := by
  induction xs with
  | nil => cases h <;> rfl
  | cons x xs ih =>
      cases h with
      | bot => rfl
      | cons hstep hrest =>
          cases hstep with
          | bot => exact ih hrest

theorem foldAppCptK_curryStep_iff {E : ResolvedEnv} {ρ : EnvI}
    {uss : List (List CptI)} {xs : List (Expr Nat)}
    (hlen : uss.length = xs.length) {c₀ c : CptI} :
    FoldAppCptK E ρ (curryStep uss c₀) xs c ↔
      c = .bot ∨ (ApproxArgsDemandK E ρ xs uss ∧ c = c₀) := by
  induction uss generalizing xs c₀ c with
  | nil =>
      cases xs with
      | nil =>
          simp only [curryStep]
          constructor
          · intro h
            cases h with
            | bot => exact Or.inl rfl
            | nil => exact Or.inr ⟨.nil, rfl⟩
          · rintro (rfl | ⟨_, rfl⟩)
            · exact .bot _ []
            · exact .nil _
      | cons _ _ => cases hlen
  | cons us uss ih =>
      cases xs with
      | nil => cases hlen
      | cons x xs =>
          simp only [List.length_cons] at hlen
          simp only [curryStep]
          constructor
          · intro h
            cases h with
            | bot => exact Or.inl rfl
            | cons hstep hrest =>
                cases hstep with
                | bot => exact Or.inl (foldAppCptK_bot_inv hrest)
                | app hs hx =>
                    have hs' : _ = (us, curryStep uss c₀) := List.mem_singleton.mp hs
                    cases hs'
                    rcases (ih (Nat.succ.inj hlen)).mp hrest with rfl | ⟨hxs, rfl⟩
                    · exact Or.inl rfl
                    · exact Or.inr ⟨.cons hx hxs, rfl⟩
          · rintro (rfl | ⟨hargs, rfl⟩)
            · exact .bot _ _
            · cases hargs with
              | cons hx hxs =>
                  exact .cons (.app (List.mem_singleton.mpr rfl) hx)
                    ((ih (Nat.succ.inj hlen)).mpr (Or.inr ⟨hxs, rfl⟩))

inductive ApproxSpineArgsK (E : ResolvedEnv) (ρ : EnvI) :
    List (Expr Nat) → List CptI → Prop
  | nil : ApproxSpineArgsK E ρ [] []
  | cons {x : Expr Nat} {xs : List (Expr Nat)} {u : CptI} {us : List CptI}
      (hx : ApproxDIK E ρ x u) (hxs : ApproxSpineArgsK E ρ xs us) :
      ApproxSpineArgsK E ρ (x :: xs) (u :: us)

theorem approxSpineArgsK_cons_iff {E : ResolvedEnv} {ρ : EnvI}
    (x : Expr Nat) (xs : List (Expr Nat)) (u : CptI) (us : List CptI) :
    ApproxSpineArgsK E ρ (x :: xs) (u :: us) ↔
      ApproxDIK E ρ x u ∧ ApproxSpineArgsK E ρ xs us := by
  constructor
  · intro h; cases h with | cons hx hxs => exact ⟨hx, hxs⟩
  · rintro ⟨hx, hxs⟩; exact .cons hx hxs

theorem approxSpineArgsK_replicate_bot {E : ResolvedEnv} {ρ : EnvI} :
    (xs : List (Expr Nat)) → ApproxSpineArgsK E ρ xs (List.replicate xs.length .bot)
  | [] => .nil
  | x :: xs => .cons (.bot ρ x) (approxSpineArgsK_replicate_bot xs)

theorem approxSpineArgsK_append_iff {E : ResolvedEnv} {ρ : EnvI} :
    (xs ys : List (Expr Nat)) → (us vs : List CptI) →
    xs.length = us.length →
    (ApproxSpineArgsK E ρ (xs ++ ys) (us ++ vs) ↔
      ApproxSpineArgsK E ρ xs us ∧ ApproxSpineArgsK E ρ ys vs)
  | [], ys, [], vs, _ => by
      simp only [List.nil_append]
      exact ⟨fun h => ⟨.nil, h⟩, fun h => h.2⟩
  | [], _, _ :: _, _, hlen => by cases hlen
  | _ :: _, _, [], _, hlen => by cases hlen
  | x :: xs, ys, u :: us, vs, hlen => by
      simp only [List.length_cons] at hlen
      simp only [List.cons_append, approxSpineArgsK_cons_iff]
      rw [approxSpineArgsK_append_iff xs ys us vs (Nat.succ.inj hlen)]
      exact ⟨fun ⟨hx, hxs, hys⟩ => ⟨⟨hx, hxs⟩, hys⟩,
        fun ⟨⟨hx, hxs⟩, hys⟩ => ⟨hx, hxs, hys⟩⟩

theorem foldAppCptK_spine_iff {E : ResolvedEnv} {ρ : EnvI} (r : Nat) :
    (xs : List (Expr Nat)) → (args : List CptI) → (c : CptI) →
    (FoldAppCptK E ρ (.spine r args) xs c ↔
      c = .bot ∨ ∃ us, ApproxSpineArgsK E ρ xs us ∧ c = .spine r (args ++ us))
  | [], args, c => by
      constructor
      · intro h
        cases h with
        | bot => exact Or.inl rfl
        | nil => exact Or.inr ⟨[], .nil, by simp⟩
      · rintro (rfl | ⟨us, hus, rfl⟩)
        · exact .bot _ _
        · cases hus
          simp only [List.append_nil]
          exact .nil _
  | x :: xs, args, c => by
      constructor
      · intro h
        cases h with
        | bot => exact Or.inl rfl
        | cons hstep hrest =>
            cases hstep with
            | bot => exact Or.inl (foldAppCptK_bot_inv hrest)
            | @appSpine _ _ _ u hx =>
                rcases (foldAppCptK_spine_iff r xs (args ++ [u]) c).mp hrest with
                  rfl | ⟨us, hxs, rfl⟩
                · exact Or.inl rfl
                · rw [List.append_assoc]
                  exact Or.inr ⟨u :: us, .cons hx hxs, rfl⟩
      · rintro (rfl | ⟨us₀, hus, rfl⟩)
        · exact .bot _ _
        · cases hus with
          | @cons _ _ u us hx hxs =>
              refine .cons (.appSpine hx) ((foldAppCptK_spine_iff r xs (args ++ [u]) _).mpr ?_)
              refine Or.inr ⟨us, hxs, ?_⟩
              simp [List.append_assoc]

theorem approxDIK_foldApps_rigid_iff {E : ResolvedEnv} {ρ : EnvI} {r : Nat} (ls : List Level)
    (hrigid : RigidConst E r) (xs : List (Expr Nat)) (c : CptI) :
    ApproxDIK E ρ (foldApps (.const r ls) xs) c ↔
      c = .bot ∨ ∃ us, ApproxSpineArgsK E ρ xs us ∧ c = .spine r us := by
  rw [approxDIK_foldApps_iff]
  constructor
  · rintro ⟨d, hd, hfold⟩
    rcases approxDIK_rigid_const_inv hrigid hd with rfl | rfl
    · exact Or.inl (foldAppCptK_bot_inv hfold)
    · simpa using (foldAppCptK_spine_iff r xs [] c).mp hfold
  · rintro (rfl | ⟨us, hus, rfl⟩)
    · exact ⟨.bot, .bot ρ (.const r ls), .bot .bot xs⟩
    · refine ⟨.spine r [], .const ρ r ls hrigid, ?_⟩
      exact (foldAppCptK_spine_iff r xs [] (.spine r us)).mpr (Or.inr ⟨us, hus, rfl⟩)

theorem forall_fieldDemandVectorsK_iff {E : ResolvedEnv} {ρ : EnvI} :
    (fields : List (Expr Nat)) → (us_fields : List (List CptI)) →
    fields.length = us_fields.length →
    ((∀ vec ∈ fieldDemandVectors us_fields, ApproxSpineArgsK E ρ fields vec) ↔
      ApproxArgsDemandK E ρ fields us_fields)
  | [], [], _ => by
      simp only [fieldDemandVectors]
      exact ⟨fun _ => .nil, fun _ _ h => (List.not_mem_nil _ h).elim⟩
  | [], _ :: _, hlen => by cases hlen
  | _ :: _, [], hlen => by cases hlen
  | f :: fs, us :: uss, hlen => by
      simp only [List.length_cons] at hlen
      have hlen' : fs.length = uss.length := Nat.succ.inj hlen
      simp only [fieldDemandVectors, List.mem_append, List.mem_map]
      constructor
      · intro hall
        refine .cons (fun u hu => ?_)
          ((forall_fieldDemandVectorsK_iff fs uss hlen').mp (fun vec hvec => ?_))
        · have h := hall (u :: List.replicate uss.length .bot) (Or.inl ⟨u, hu, rfl⟩)
          exact ((approxSpineArgsK_cons_iff f fs u _).mp h).1
        · have h := hall (.bot :: vec) (Or.inr ⟨vec, hvec, rfl⟩)
          exact ((approxSpineArgsK_cons_iff f fs .bot vec).mp h).2
      · intro hargs vec hmem
        cases hargs with
        | cons hf hfs =>
            rcases hmem with ⟨u, hu, rfl⟩ | ⟨vec', hvec', rfl⟩
            · rw [← hlen']
              exact .cons (hf u hu) (approxSpineArgsK_replicate_bot fs)
            · exact .cons (.bot ρ f)
                ((forall_fieldDemandVectorsK_iff fs uss hlen').mpr hfs vec' hvec')

theorem ctorDemandK_intro {E : ResolvedEnv} {ρ : EnvI} {ctorRef : Nat} (lsC : List Level)
    (hrigid : RigidConst E ctorRef) {ctorParams fields : List (Expr Nat)} {nparams : Nat}
    (hparams : ctorParams.length = nparams) {us_fields : List (List CptI)}
    (hflds : ApproxArgsDemandK E ρ fields us_fields) :
    ∀ v ∈ ctorDemand ctorRef nparams us_fields,
      ApproxDIK E ρ (foldApps (.const ctorRef lsC) (ctorParams ++ fields)) v := by
  have hflen : fields.length = us_fields.length := hflds.length_eq.symm
  have hrepP : ApproxSpineArgsK E ρ ctorParams (List.replicate nparams .bot) := by
    rw [← hparams]; exact approxSpineArgsK_replicate_bot ctorParams
  intro v hv
  simp only [ctorDemand, List.mem_cons, List.mem_map] at hv
  rw [approxDIK_foldApps_rigid_iff lsC hrigid]
  rcases hv with rfl | ⟨vec, hvec, rfl⟩
  · refine Or.inr ⟨_, ?_, rfl⟩
    rw [approxSpineArgsK_append_iff ctorParams fields _ _ (by simp [hparams])]
    refine ⟨hrepP, ?_⟩
    rw [← hflen]
    exact approxSpineArgsK_replicate_bot fields
  · refine Or.inr ⟨_, ?_, rfl⟩
    rw [approxSpineArgsK_append_iff ctorParams fields _ _ (by simp [hparams])]
    exact ⟨hrepP, (forall_fieldDemandVectorsK_iff fields us_fields hflen).mpr hflds vec hvec⟩

theorem ctorDemandK_inv {E : ResolvedEnv} {ρ : EnvI} {ctorRef ctorRef' nparams : Nat}
    {lsC : List Level} (hrigid : RigidConst E ctorRef') {ctorParams fields : List (Expr Nat)}
    {us_fields : List (List CptI)}
    (h : ∀ v ∈ ctorDemand ctorRef nparams us_fields,
      ApproxDIK E ρ (foldApps (.const ctorRef' lsC) (ctorParams ++ fields)) v) :
    ctorRef = ctorRef' ∧
      (ctorParams.length = nparams → fields.length = us_fields.length →
        ApproxArgsDemandK E ρ fields us_fields) := by
  have htag := h (.spine ctorRef (List.replicate nparams .bot ++ List.replicate us_fields.length .bot))
    (List.mem_cons_self _ _)
  rw [approxDIK_foldApps_rigid_iff lsC hrigid] at htag
  rcases htag with hbot | ⟨us₀, _, heq⟩
  · cases hbot
  · injection heq with hctor _
    refine ⟨hctor, fun hparams hflen => ?_⟩
    apply (forall_fieldDemandVectorsK_iff fields us_fields hflen).mp
    intro vec hvec
    have hv := h (.spine ctorRef (List.replicate nparams .bot ++ vec))
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨vec, hvec, rfl⟩))
    rw [approxDIK_foldApps_rigid_iff lsC hrigid] at hv
    rcases hv with hbot | ⟨us, hus, heq'⟩
    · cases hbot
    · injection heq' with _ husEq
      subst husEq
      exact ((approxSpineArgsK_append_iff ctorParams fields _ _ (by simp [hparams])).mp hus).2

/-- **Unconditional Canonical ι Soundness in `ApproxDIK`**: for **every** `E : ResolvedEnv`,
    **every** shape witness `w : IotaWitnessS E` (both `Prop` and `Type`, both 0-field and
    fieldful, both single-constructor and multi-constructor), and **every** `ρ : EnvI`,
    `SemEqDIK E ρ (iotaLhsOfS w) (iotaRhsOfS w)` holds. -/
theorem approxDIK_iotaS {E : ResolvedEnv} (w : IotaWitnessS E) (ρ : EnvI) :
    SemEqDIK E ρ (iotaLhsOfS w) (iotaRhsOfS w) := by
  have hclSchema : exprClosedAt (w.preMajor ++ w.fields).length
      (instantiateLevels w.ls w.schema) = true := by
    rw [exprClosedAt_instantiateLevels, List.length_append, w.hpre]
    exact w.hschemaScope
  have hrigidCtor : RigidConst E w.ctorRef := rigidConst_of_ctor w.hctor w.hctorK
  intro c
  constructor
  · intro hlhs
    unfold iotaLhsOfS recCall at hlhs
    rw [approxDIK_foldApps_iff] at hlhs
    obtain ⟨d, hd, hfold⟩ := hlhs
    rcases approxDIK_recursor_const_inv w.hrec w.hrecK hd with
      rfl |
      ⟨w', us_pre, us_fields, c₀, hrecEq, hpreLen, hfldsLen, hschema', rfl⟩ |
      ⟨w', us_pre, u_maj, c₀, hrecEq, hk', hpreLen, _, hschema', rfl⟩
    · rw [foldAppCptK_bot_inv hfold]
      exact .bot ρ (iotaRhsOfS w)
    · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
      have htotLen : (us_pre ++ [ctorDemand w'.ctorRef w'.nparams us_fields]).length =
          (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)]).length := by
        simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq]
      rcases (foldAppCptK_curryStep_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
      · exact .bot ρ (iotaRhsOfS w)
      · obtain ⟨us_pre', us_maj', hsplitEq, hpreArgs, hmajArgs⟩ :=
          (ApproxArgsDemandK.append_iff w.preMajor _ _).mp hargs
        have hlenPre : us_pre.length = us_pre'.length := by
          rw [hpreArgs.length_eq, hpreLen, hpreLenEq]
        obtain ⟨rfl, hmajEq⟩ := List.append_inj hsplitEq hlenPre
        cases hmajArgs with
        | cons hmaj _ =>
            cases hmajEq
            obtain ⟨hctorEq, hfldsFn⟩ := ctorDemandK_inv hrigidCtor hmaj
            obtain ⟨hnparEq, _, _, _, _, hfldsLenEq, _, hschemaEq⟩ :=
              iotaWitnessS_same_branch w' w hrecEq hctorEq
            have hfldsArgs : ApproxArgsDemandK E ρ w.fields us_fields :=
              hfldsFn (w.hctorParams.trans hnparEq.symm) (hfldsLenEq.symm.trans hfldsLen.symm)
            rw [hschemaEq] at hschema'
            unfold iotaRhsOfS
            rw [approxDIK_instPrefix_closed_iff E ρ _ _ hclSchema]
            exact ⟨us_pre ++ us_fields,
              (ApproxArgsDemandK.append_iff _ _ _).mpr ⟨us_pre, us_fields, rfl, hpreArgs, hfldsArgs⟩,
              hschema'⟩
    · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
      have htotLen : (us_pre ++ [u_maj]).length =
          (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)]).length := by
        simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq]
      rcases (foldAppCptK_curryStep_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
      · exact .bot ρ (iotaRhsOfS w)
      · obtain ⟨us_pre', us_maj', hsplitEq, hpreArgs, _⟩ :=
          (ApproxArgsDemandK.append_iff w.preMajor _ _).mp hargs
        have hlenPre : us_pre.length = us_pre'.length := by
          rw [hpreArgs.length_eq, hpreLen, hpreLenEq]
        obtain ⟨rfl, _⟩ := List.append_inj hsplitEq hlenPre
        obtain ⟨_, _, _, hfldsLenEq, _, hschemaEq⟩ :=
          iotaWitnessS_unique_of_nMinors_one w' w hrecEq hk'.2
        rw [hfldsLenEq, hschemaEq] at hschema'
        unfold iotaRhsOfS
        rw [approxDIK_instPrefix_closed_iff E ρ _ _ hclSchema]
        exact ⟨us_pre ++ List.replicate w.fields.length [],
          (ApproxArgsDemandK.append_iff _ _ _).mpr
            ⟨us_pre, List.replicate w.fields.length [], rfl, hpreArgs,
              approxArgsDemandK_replicate_nil w.fields⟩,
          hschema'⟩
  · intro hrhs
    unfold iotaRhsOfS at hrhs
    rw [approxDIK_instPrefix_closed_iff E ρ _ _ hclSchema] at hrhs
    obtain ⟨uss, hargs, hschema⟩ := hrhs
    obtain ⟨us_pre, us_fields, rfl, hpreArgs, hfldsArgs⟩ :=
      (ApproxArgsDemandK.append_iff w.preMajor w.fields uss).mp hargs
    have hrecHead : ApproxDIK E ρ (.const w.recRef w.ls)
        (curryStep (us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields]) c) :=
      .recursor w.ls hpreArgs.length_eq hfldsArgs.length_eq hschema
    have hmaj : ∀ v ∈ ctorDemand w.ctorRef w.nparams us_fields,
        ApproxDIK E ρ (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) v :=
      ctorDemandK_intro w.lsC hrigidCtor w.hctorParams hfldsArgs
    have htotArgs : ApproxArgsDemandK E ρ
        (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)])
        (us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields]) :=
      (ApproxArgsDemandK.append_iff _ _ _).mpr
        ⟨us_pre, [ctorDemand w.ctorRef w.nparams us_fields], rfl, hpreArgs, .cons hmaj .nil⟩
    unfold iotaLhsOfS recCall
    rw [approxDIK_foldApps_iff]
    exact ⟨_, hrecHead,
      (foldAppCptK_curryStep_iff htotArgs.length_eq).mpr (Or.inr ⟨htotArgs, rfl⟩)⟩

theorem approxDIK_iotaT {E : ResolvedEnv} {lhs rhs : Expr Nat} (h : DerivedIotaT E lhs rhs)
    (ρ : EnvI) : SemEqDIK E ρ lhs rhs := by
  cases h with
  | of w => exact approxDIK_iotaS w ρ

theorem approxDIK_iota_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) (w : IotaWitness E)
    (ρ : EnvI) : SemEqDIK E ρ (iotaLhsOf w) (iotaRhsOf w) := by
  obtain ⟨ht⟩ := derivedIotaT_of_iotaWitness_envWfT hW w
  exact approxDIK_iotaT ht ρ

theorem approxDIK_iotaU_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {lhs rhs : Expr Nat}
    (h : DerivedIotaU E lhs rhs) (ρ : EnvI) : SemEqDIK E ρ lhs rhs := by
  obtain ⟨ht⟩ := derivedIotaT_of_derivedIotaU_envWfT hW h
  exact approxDIK_iotaT ht ρ

theorem semEqDIK_of_convT_iota {E : ResolvedEnv} (hW : EnvWfT E) {lhs rhs : Expr Nat}
    (h : DerivedIota E lhs rhs) (ρ : EnvI) : SemEqDIK E ρ lhs rhs := by
  obtain ⟨ht⟩ := derivedIotaT_of_derivedIota_envWfT hW h
  exact approxDIK_iotaT ht ρ

/-- List of demand lists in which every demand list is a `BotDemand` (`∀ u ∈ us, u = .bot`). -/
inductive BotDemandList : List (List CptI) → Prop
  | nil : BotDemandList []
  | cons {us : List CptI} {uss : List (List CptI)}
      (hus : BotDemand us) (huss : BotDemandList uss) :
      BotDemandList (us :: uss)

theorem botDemandList_of_approxArgsDemandK {E : ResolvedEnv} {ρ : EnvI}
    {fields : List (Expr Nat)} {us_fields : List (List CptI)}
    (hflds : ∀ f ∈ fields, ∀ u, ApproxDIK E ρ f u → u = .bot)
    (hargs : ApproxArgsDemandK E ρ fields us_fields) :
    BotDemandList us_fields := by
  induction hargs with
  | nil => exact .nil
  | @cons f fs us uss ha _ ih =>
      refine .cons (fun u hu => hflds f (List.mem_cons_self _ _) u (ha u hu))
        (ih (fun f' hf' => hflds f' (List.mem_cons_of_mem _ hf')))

theorem pushArgs_botDemandList_nonbot_le {us_fields : List (List CptI)}
    (hbd : BotDemandList us_fields) :
    ∀ {ρ₁ ρ₂ : EnvI}, (∀ i c, c ≠ .bot → ρ₁ i c → ρ₂ i c) →
      ∀ i c, c ≠ .bot →
        EnvI.pushArgs (us_fields.map demand) ρ₁ i c →
        EnvI.pushArgs ((List.replicate us_fields.length []).map demand) ρ₂ i c := by
  induction hbd with
  | nil =>
      intro ρ₁ ρ₂ hρ i c hne h
      exact hρ i c hne h
  | @cons us uss hus _ ih =>
      intro ρ₁ ρ₂ hρ i c hne h
      simp only [List.length_cons, List.replicate_succ, List.map_cons, EnvI.pushArgs] at h ⊢
      refine ih (fun j d hd => ?_) i c hne h
      cases j with
      | zero =>
          intro hdem
          exact (hd (hus d hdem)).elim
      | succ j =>
          exact hρ j d hd

/-- **Unconditional Fieldful K Soundness (`semEqDIK_k_botFields`)**: for any single-constructor
    `Prop` witness `w : IotaWitnessS E` (`piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1`),
    any valuation `ρ : EnvI` at which `w.fields` have only `.bot` approximations, and any major
    expression `x : Expr Nat` having no `.spine w.ctorRef args` approximation at `ρ`,
    `SemEqDIK E ρ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w)` holds. -/
theorem semEqDIK_k_botFields {E : ResolvedEnv} (w : IotaWitnessS E)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    {ρ : EnvI} {x : Expr Nat}
    (hflds : ∀ f ∈ w.fields, ∀ u, ApproxDIK E ρ f u → u = .bot)
    (hx : ∀ args, ¬ ApproxDIK E ρ x (.spine w.ctorRef args)) :
    SemEqDIK E ρ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w) := by
  have hclSchema : exprClosedAt (w.preMajor ++ w.fields).length
      (instantiateLevels w.ls w.schema) = true := by
    rw [exprClosedAt_instantiateLevels, List.length_append, w.hpre]
    exact w.hschemaScope
  intro c
  constructor
  · intro hlhs
    unfold recCall at hlhs
    rw [approxDIK_foldApps_iff] at hlhs
    obtain ⟨d, hd, hfold⟩ := hlhs
    rcases approxDIK_recursor_const_inv w.hrec w.hrecK hd with
      rfl |
      ⟨w', us_pre, us_fields, c₀, hrecEq, hpreLen, _, _, rfl⟩ |
      ⟨w', us_pre, u_maj, c₀, hrecEq, hk', hpreLen, _, hschema', rfl⟩
    · rw [foldAppCptK_bot_inv hfold]
      exact .bot ρ (iotaRhsOfS w)
    · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
      have htotLen : (us_pre ++ [ctorDemand w'.ctorRef w'.nparams us_fields]).length =
          (w.preMajor ++ [x]).length := by
        simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq]
      rcases (foldAppCptK_curryStep_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
      · exact .bot ρ (iotaRhsOfS w)
      · obtain ⟨us_pre', us_maj', hsplitEq, hpreArgs, hmajArgs⟩ :=
          (ApproxArgsDemandK.append_iff w.preMajor [x] _).mp hargs
        have hlenPre : us_pre.length = us_pre'.length := by
          rw [hpreArgs.length_eq, hpreLen, hpreLenEq]
        obtain ⟨rfl, hmajEq⟩ := List.append_inj hsplitEq hlenPre
        cases hmajArgs with
        | cons hmaj _ =>
            cases hmajEq
            obtain ⟨_, hctorEq, _, _, _, _⟩ :=
              iotaWitnessS_unique_of_nMinors_one w w' hrecEq.symm hk.2
            have htag := hmaj
              (.spine w'.ctorRef (List.replicate w'.nparams .bot ++ List.replicate us_fields.length .bot))
              (List.mem_cons_self _ _)
            rw [← hctorEq] at htag
            exact (hx _ htag).elim
    · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
      have htotLen : (us_pre ++ [u_maj]).length = (w.preMajor ++ [x]).length := by
        simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq]
      rcases (foldAppCptK_curryStep_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
      · exact .bot ρ (iotaRhsOfS w)
      · obtain ⟨us_pre', us_maj', hsplitEq, hpreArgs, _⟩ :=
          (ApproxArgsDemandK.append_iff w.preMajor [x] _).mp hargs
        have hlenPre : us_pre.length = us_pre'.length := by
          rw [hpreArgs.length_eq, hpreLen, hpreLenEq]
        obtain ⟨rfl, _⟩ := List.append_inj hsplitEq hlenPre
        obtain ⟨_, _, _, hfldsLenEq, _, hschemaEq⟩ :=
          iotaWitnessS_unique_of_nMinors_one w' w hrecEq hk'.2
        rw [hfldsLenEq, hschemaEq] at hschema'
        unfold iotaRhsOfS
        rw [approxDIK_instPrefix_closed_iff E ρ _ _ hclSchema]
        exact ⟨us_pre ++ List.replicate w.fields.length [],
          (ApproxArgsDemandK.append_iff _ _ _).mpr
            ⟨us_pre, List.replicate w.fields.length [], rfl, hpreArgs,
              approxArgsDemandK_replicate_nil w.fields⟩,
          hschema'⟩
  · intro hrhs
    unfold iotaRhsOfS at hrhs
    rw [approxDIK_instPrefix_closed_iff E ρ _ _ hclSchema] at hrhs
    obtain ⟨uss, hargs, hschema⟩ := hrhs
    obtain ⟨us_pre, us_fields, rfl, hpreArgs, hfldsArgs⟩ :=
      (ApproxArgsDemandK.append_iff w.preMajor w.fields uss).mp hargs
    have hbd : BotDemandList us_fields := botDemandList_of_approxArgsDemandK hflds hfldsArgs
    have hschemaK : ApproxDIK E
        (EnvI.pushArgs ((us_pre ++ List.replicate w.fields.length []).map demand) EnvI.bot)
        (instantiateLevels w.ls w.schema) c := by
      rw [← hfldsArgs.length_eq]
      rw [List.map_append, EnvI.pushArgs_append] at hschema ⊢
      exact approxDIK_mono_env_nonbot
        (pushArgs_botDemandList_nonbot_le hbd (fun _ _ _ => id)) hschema
    have hrecHead : ApproxDIK E ρ (.const w.recRef w.ls)
        (curryStep (us_pre ++ [[]]) c) :=
      .recursorK w.ls hk hpreArgs.length_eq (fun _ h => (List.not_mem_nil _ h).elim) hschemaK
    have htotArgs : ApproxArgsDemandK E ρ (w.preMajor ++ [x]) (us_pre ++ [[]]) :=
      (ApproxArgsDemandK.append_iff _ _ _).mpr
        ⟨us_pre, [[]], rfl, hpreArgs, .cons (fun _ h => (List.not_mem_nil _ h).elim) .nil⟩
    unfold recCall
    rw [approxDIK_foldApps_iff]
    exact ⟨_, hrecHead,
      (foldAppCptK_curryStep_iff htotArgs.length_eq).mpr (Or.inr ⟨htotArgs, rfl⟩)⟩

/-- **Unconditional 0-Field K Soundness (`semEqDIK_k_zeroFields`)**: for any 0-field
    single-constructor `Prop` witness `w : IotaWitnessS E` (`piBody w.famMember.mtype = .sort .zero
    ∧ w.nMinors = 1` and `w.fields = []`), **every** valuation `ρ : EnvI`, and **every** major
    expression `x : Expr Nat` (with **zero** side conditions on `x` or `ρ`),
    `SemEqDIK E ρ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w)` holds. -/
theorem semEqDIK_k_zeroFields {E : ResolvedEnv} (w : IotaWitnessS E)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    (hzero : w.fields = []) (ρ : EnvI) (x : Expr Nat) :
    SemEqDIK E ρ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w) := by
  have hclSchema : exprClosedAt (w.preMajor ++ w.fields).length
      (instantiateLevels w.ls w.schema) = true := by
    rw [exprClosedAt_instantiateLevels, List.length_append, w.hpre]
    exact w.hschemaScope
  intro c
  constructor
  · intro hlhs
    unfold recCall at hlhs
    rw [approxDIK_foldApps_iff] at hlhs
    obtain ⟨d, hd, hfold⟩ := hlhs
    rcases approxDIK_recursor_const_inv w.hrec w.hrecK hd with
      rfl |
      ⟨w', us_pre, us_fields, c₀, hrecEq, hpreLen, hfldsLen, hschema', rfl⟩ |
      ⟨w', us_pre, u_maj, c₀, hrecEq, hk', hpreLen, _, hschema', rfl⟩
    · rw [foldAppCptK_bot_inv hfold]
      exact .bot ρ (iotaRhsOfS w)
    · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
      have htotLen : (us_pre ++ [ctorDemand w'.ctorRef w'.nparams us_fields]).length =
          (w.preMajor ++ [x]).length := by
        simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq]
      rcases (foldAppCptK_curryStep_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
      · exact .bot ρ (iotaRhsOfS w)
      · obtain ⟨us_pre', _, hsplitEq, hpreArgs, _⟩ :=
          (ApproxArgsDemandK.append_iff w.preMajor [x] _).mp hargs
        have hlenPre : us_pre.length = us_pre'.length := by
          rw [hpreArgs.length_eq, hpreLen, hpreLenEq]
        obtain ⟨rfl, _⟩ := List.append_inj hsplitEq hlenPre
        obtain ⟨_, _, _, hfldsLenEq, _, hschemaEq⟩ :=
          iotaWitnessS_unique_of_nMinors_one w w' hrecEq.symm hk.2
        have husNil : us_fields = [] :=
          List.eq_nil_of_length_eq_zero (hfldsLen.trans (hfldsLenEq.symm.trans (by simp [hzero])))
        subst husNil
        rw [← hschemaEq] at hschema'
        unfold iotaRhsOfS
        rw [approxDIK_instPrefix_closed_iff E ρ _ _ hclSchema]
        refine ⟨us_pre ++ [], (ApproxArgsDemandK.append_iff _ _ _).mpr
          ⟨us_pre, [], rfl, hpreArgs, ?_⟩, hschema'⟩
        rw [hzero]
        exact .nil
    · obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w' w hrecEq
      have htotLen : (us_pre ++ [u_maj]).length = (w.preMajor ++ [x]).length := by
        simp only [List.length_append, List.length_singleton, hpreLen, hpreLenEq]
      rcases (foldAppCptK_curryStep_iff htotLen).mp hfold with rfl | ⟨hargs, rfl⟩
      · exact .bot ρ (iotaRhsOfS w)
      · obtain ⟨us_pre', _, hsplitEq, hpreArgs, _⟩ :=
          (ApproxArgsDemandK.append_iff w.preMajor [x] _).mp hargs
        have hlenPre : us_pre.length = us_pre'.length := by
          rw [hpreArgs.length_eq, hpreLen, hpreLenEq]
        obtain ⟨rfl, _⟩ := List.append_inj hsplitEq hlenPre
        obtain ⟨_, _, _, hfldsLenEq, _, hschemaEq⟩ :=
          iotaWitnessS_unique_of_nMinors_one w' w hrecEq hk'.2
        rw [hfldsLenEq, hschemaEq] at hschema'
        unfold iotaRhsOfS
        rw [approxDIK_instPrefix_closed_iff E ρ _ _ hclSchema]
        exact ⟨us_pre ++ List.replicate w.fields.length [],
          (ApproxArgsDemandK.append_iff _ _ _).mpr
            ⟨us_pre, List.replicate w.fields.length [], rfl, hpreArgs,
              approxArgsDemandK_replicate_nil w.fields⟩,
          hschema'⟩
  · intro hrhs
    unfold iotaRhsOfS at hrhs
    rw [approxDIK_instPrefix_closed_iff E ρ _ _ hclSchema] at hrhs
    obtain ⟨uss, hargs, hschema⟩ := hrhs
    obtain ⟨us_pre, us_fields, rfl, hpreArgs, hfldsArgs⟩ :=
      (ApproxArgsDemandK.append_iff w.preMajor w.fields uss).mp hargs
    have husNil : us_fields = List.replicate w.fields.length [] := by
      have h0 : us_fields.length = 0 := hfldsArgs.length_eq.trans (by simp [hzero])
      rw [List.eq_nil_of_length_eq_zero h0, hzero]
      rfl
    rw [husNil] at hschema
    have hrecHead : ApproxDIK E ρ (.const w.recRef w.ls)
        (curryStep (us_pre ++ [[]]) c) :=
      .recursorK w.ls hk hpreArgs.length_eq (fun _ h => (List.not_mem_nil _ h).elim) hschema
    have htotArgs : ApproxArgsDemandK E ρ (w.preMajor ++ [x]) (us_pre ++ [[]]) :=
      (ApproxArgsDemandK.append_iff _ _ _).mpr
        ⟨us_pre, [[]], rfl, hpreArgs, .cons (fun _ h => (List.not_mem_nil _ h).elim) .nil⟩
    unfold recCall
    rw [approxDIK_foldApps_iff]
    exact ⟨_, hrecHead,
      (foldAppCptK_curryStep_iff htotArgs.length_eq).mpr (Or.inr ⟨htotArgs, rfl⟩)⟩

/-- Unconditional 0-field K soundness for legacy `w : IotaWitness E` at `EnvWfT E`. -/
theorem semEqDIK_k_zeroFields_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) (w : IotaWitness E)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    (hzero : w.fields = []) (ρ : EnvI) (x : Expr Nat) :
    SemEqDIK E ρ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) := by
  obtain ⟨wS, hrec, _, hls, _, hpre, hflds, _, _, hfamM, _, _, hnmin, _, _, hrhs⟩ :=
    iotaWitnessS_of_iotaWitness_envWfT hW w
  have hkS : piBody wS.famMember.mtype = .sort .zero ∧ wS.nMinors = 1 := by
    rw [hfamM, hnmin]; exact hk
  have hzeroS : wS.fields = [] := hflds.trans hzero
  have h := semEqDIK_k_zeroFields wS hkS hzeroS ρ x
  rwa [hrec, hls, hpre, hrhs] at h

/-- Fieldful K soundness for legacy `w : IotaWitness E` at `EnvWfT E`. -/
theorem semEqDIK_k_botFields_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) (w : IotaWitness E)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    {ρ : EnvI} {x : Expr Nat}
    (hflds : ∀ f ∈ w.fields, ∀ u, ApproxDIK E ρ f u → u = .bot)
    (hx : ∀ args, ¬ ApproxDIK E ρ x (.spine w.ctorRef args)) :
    SemEqDIK E ρ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) := by
  obtain ⟨wS, hrec, hctor, hls, _, hpre, hfldsEq, _, _, hfamM, _, _, hnmin, _, _, hrhs⟩ :=
    iotaWitnessS_of_iotaWitness_envWfT hW w
  have hkS : piBody wS.famMember.mtype = .sort .zero ∧ wS.nMinors = 1 := by
    rw [hfamM, hnmin]; exact hk
  have hfldsS : ∀ f ∈ wS.fields, ∀ u, ApproxDIK E ρ f u → u = .bot := by
    rw [hfldsEq]; exact hflds
  have hxS : ∀ args, ¬ ApproxDIK E ρ x (.spine wS.ctorRef args) := by
    rw [hctor]; exact hx
  have h := semEqDIK_k_botFields wS hkS hfldsS hxS
  rwa [hrec, hls, hpre, hrhs] at h

/-- **Positive `W-K` Repair at `trueEnvU`**: for **every** valuation `ρ : EnvI` and **every**
    major expression `x : Expr Nat`, `.app trueEnvU_kRecElim x` and `.sort .zero` are semantically
    equal in `ApproxDIK` (`SemEqDIK trueEnvU ρ (.app trueEnvU_kRecElim x) (.sort .zero)`). -/
theorem semEqDIK_trueEnvU_kRec_all (ρ : EnvI) (x : Expr Nat) :
    SemEqDIK trueEnvU ρ (.app trueEnvU_kRecElim x) (.sort .zero) :=
  semEqDIK_k_zeroFields_of_envWfT trueEnvUWfT wTrueRecU ⟨rfl, rfl⟩ rfl ρ x

/-- In `ApproxDIK`, `trueEnvU_kRecVar` and `.sort .zero` are semantically equal at every `ρ`. -/
theorem semEqDIK_trueEnvU_kRecVar_sort (ρ : EnvI) :
    SemEqDIK trueEnvU ρ trueEnvU_kRecVar (.sort .zero) :=
  semEqDIK_trueEnvU_kRec_all ρ (.bvar 0)

/-- In `ApproxDIK`, `trueEnvU_kRecIdTt` and `.sort .zero` are semantically equal at every `ρ`. -/
theorem semEqDIK_trueEnvU_kRecIdTt_sort (ρ : EnvI) :
    SemEqDIK trueEnvU ρ trueEnvU_kRecIdTt (.sort .zero) :=
  semEqDIK_trueEnvU_kRec_all ρ (.app (.lam (.const 0 []) (.bvar 0)) (.const 1 []))

/-- In `ApproxDIK`, `.sort` approximates `trueEnvU_kRecVar` at every valuation `ρ`. -/
theorem approxDIK_trueEnvU_kRecVar_sort (ρ : EnvI) :
    ApproxDIK trueEnvU ρ trueEnvU_kRecVar .sort :=
  (semEqDIK_trueEnvU_kRecVar_sort ρ .sort).mpr (.sort ρ .zero)

/-- In `ApproxDIK`, `mixAndRedex` and `mixAndRhs` are semantically equal at `EnvI.bot`. -/
theorem semEqDIK_andEnvU_mixAndRedex_mixAndRhs :
    SemEqDIK andEnvU EnvI.bot mixAndRedex mixAndRhs :=
  semEqDIK_k_botFields_of_envWfT andEnvUWfT mixAndW ⟨rfl, rfl⟩
    (fun f hf u hu => by
      simp only [mixAndW, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;>
        (rcases approxDIK_bvar_inv hu with rfl | h0; rfl; exact h0))
    (fun args hsp => by
      rcases approxDIK_bvar_inv hsp with h0 | h0 <;> cases h0)

/-! ### §10.4. `SemEqDIK` Congruences, K-Aware Readback `WhStepPiK` / `WhRedPiK`, and
    Logical Relation `LRTypeINPiK` / `LRTypeINBiDIK` -/

theorem semEqDIK_sorts (E : ResolvedEnv) (ρ : EnvI) (l₁ l₂ : Level) :
    SemEqDIK E ρ (.sort l₁) (.sort l₂) := by
  intro c
  constructor <;>
    (intro h; rcases approxDIK_sort_inv h with rfl | rfl; exact .bot _ _; exact .sort _ _)

theorem semEqDIK_app {E : ResolvedEnv} {ρ : EnvI} {f f' a a' : Expr Nat}
    (hf : SemEqDIK E ρ f f') (ha : SemEqDIK E ρ a a') :
    SemEqDIK E ρ (.app f a) (.app f' a') := by
  intro c
  constructor
  · intro h
    rcases approxDIK_app_inv h with rfl | ⟨g, s, rfl, hfg, hs, hax⟩ | ⟨r, args, u, rfl, hfs, hau⟩
    · exact .bot _ _
    · exact .app ((hf (.lam g)).mp hfg) hs (fun u hu => (ha u).mp (hax u hu))
    · exact .appSpine ((hf (.spine r args)).mp hfs) ((ha u).mp hau)
  · intro h
    rcases approxDIK_app_inv h with rfl | ⟨g, s, rfl, hfg, hs, hax⟩ | ⟨r, args, u, rfl, hfs, hau⟩
    · exact .bot _ _
    · exact .app ((hf (.lam g)).mpr hfg) hs (fun u hu => (ha u).mpr (hax u hu))
    · exact .appSpine ((hf (.spine r args)).mpr hfs) ((ha u).mpr hau)

theorem semEqDIK_lam {E : ResolvedEnv} {ρ : EnvI} (A A' : Expr Nat) {b b' : Expr Nat}
    (hb : ∀ us, SemEqDIK E (EnvI.cons (demand us) ρ) b b') :
    SemEqDIK E ρ (.lam A b) (.lam A' b') := by
  intro c
  constructor
  · intro h
    rcases approxDIK_lam_inv h with rfl | ⟨f, rfl, hbf⟩
    · exact .bot _ _
    · exact .lam (fun s hs => (hb s.1 s.2).mp (hbf s hs))
  · intro h
    rcases approxDIK_lam_inv h with rfl | ⟨f, rfl, hbf⟩
    · exact .bot _ _
    · exact .lam (fun s hs => (hb s.1 s.2).mpr (hbf s hs))

theorem semEqDIK_pi {E : ResolvedEnv} {ρ : EnvI} {A A' B B' : Expr Nat}
    (hA : SemEqDIK E ρ A A') (hB : ∀ us, SemEqDIK E (EnvI.cons (demand us) ρ) B B') :
    SemEqDIK E ρ (.pi A B) (.pi A' B') := by
  intro c
  constructor
  · intro h
    rcases approxDIK_pi_inv h with rfl | ⟨a, f, rfl, hAa, hBf⟩
    · exact .bot _ _
    · exact .pi ((hA a).mp hAa) (fun s hs => (hB s.1 s.2).mp (hBf s hs))
  · intro h
    rcases approxDIK_pi_inv h with rfl | ⟨a, f, rfl, hAa, hBf⟩
    · exact .bot _ _
    · exact .pi ((hA a).mpr hAa) (fun s hs => (hB s.1 s.2).mpr (hBf s hs))

theorem semEqDIK_letE {E : ResolvedEnv} {ρ : EnvI} (A A' : Expr Nat) {v v' b b' : Expr Nat}
    (hv : SemEqDIK E ρ v v') (hb : ∀ us, SemEqDIK E (EnvI.cons (demand us) ρ) b b') :
    SemEqDIK E ρ (.letE A v b) (.letE A' v' b') := by
  have happ : SemEqDIK E ρ (.app (.lam A b) v) (.app (.lam A' b') v') :=
    semEqDIK_app (semEqDIK_lam A A' hb) hv
  intro c
  constructor
  · intro h
    rcases approxDIK_letE_inv h with rfl | h'
    · exact .bot _ _
    · exact .letE ((happ c).mp h')
  · intro h
    rcases approxDIK_letE_inv h with rfl | h'
    · exact .bot _ _
    · exact .letE ((happ c).mpr h')

/-- Soundness of every weak-head step (`WhStep E a b`) in `ApproxDIK` at every `EnvWfT E` and
    every valuation `ρ : EnvI`. -/
theorem semEqDIK_whStep {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hs : WhStep E a b) (ρ : EnvI) : SemEqDIK E ρ a b := by
  induction hs with
  | beta A body arg => exact approxDIK_beta E ρ A body arg
  | zeta A v body => exact approxDIK_zeta E ρ A v body
  | delta hres hbody => exact semEqDIK_of_whStep_delta hW hres hbody ρ
  | iota h => exact approxDIK_iotaU_of_envWfT hW h ρ
  | lit t => exact approxDIK_lit E ρ t
  | @appHead f f' arg _ ih => exact semEqDIK_app ih (semEqDIK_refl E ρ arg)

/-- Soundness of multi-step weak-head reduction (`WhRed E a b`) in `ApproxDIK` at every `EnvWfT E`
    and every valuation `ρ : EnvI`. -/
theorem semEqDIK_whRed {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hr : WhRed E a b) (ρ : EnvI) : SemEqDIK E ρ a b := by
  induction hr with
  | refl e => exact semEqDIK_refl E ρ e
  | step hs _ ih => exact semEqDIK_trans (semEqDIK_whStep hW hs ρ) ih

/-- Model Π-injectivity for `SemEqDIK`: on domains, and on codomains at every finite demand. -/
theorem semEqDIK_pi_inj {E : ResolvedEnv} {ρ : EnvI} {A B A' B' : Expr Nat}
    (h : SemEqDIK E ρ (.pi A B) (.pi A' B')) :
    SemEqDIK E ρ A A' ∧ ∀ us, SemEqDIK E (EnvI.cons (demand us) ρ) B B' := by
  refine ⟨fun a => ⟨fun hA => ?_, fun hA' => ?_⟩, fun us v => ⟨fun hB => ?_, fun hB' => ?_⟩⟩
  · have := (h (.pi a [])).mp (.pi hA (fun _ hs => (List.not_mem_nil _ hs).elim))
    rcases approxDIK_pi_inv this with h0 | ⟨_, _, heq, hA', _⟩
    · cases h0
    · cases heq; exact hA'
  · have := (h (.pi a [])).mpr (.pi hA' (fun _ hs => (List.not_mem_nil _ hs).elim))
    rcases approxDIK_pi_inv this with h0 | ⟨_, _, heq, hA, _⟩
    · cases h0
    · cases heq; exact hA
  · have := (h (.pi .bot [(us, v)])).mp (.pi (.bot ρ A) (fun s hs => by
      have heq := List.mem_singleton.mp hs; subst heq; exact hB))
    rcases approxDIK_pi_inv this with h0 | ⟨_, _, heq, _, hB'⟩
    · cases h0
    · cases heq; exact hB' (us, v) (List.mem_singleton.mpr rfl)
  · have := (h (.pi .bot [(us, v)])).mpr (.pi (.bot ρ A') (fun s hs => by
      have heq := List.mem_singleton.mp hs; subst heq; exact hB'))
    rcases approxDIK_pi_inv this with h0 | ⟨_, _, heq, _, hB⟩
    · cases h0
    · cases heq; exact hB (us, v) (List.mem_singleton.mpr rfl)

/-- Π-types and sorts are disjoint in `SemEqDIK`. -/
theorem semEqDIK_pi_sort_disjoint {E : ResolvedEnv} {ρ : EnvI} {A B : Expr Nat} {l : Level}
    (h : SemEqDIK E ρ (.pi A B) (.sort l)) : False := by
  have := (h (.pi .bot [])).mp (.pi (.bot ρ A) (fun _ hs => (List.not_mem_nil _ hs).elim))
  rcases approxDIK_sort_inv this with h0 | h0 <;> cases h0

/-- `.pi .bot []` approximates every Π-type in `ApproxDIK`. -/
theorem approxDIK_pi_bot_nil (E : ResolvedEnv) (ρ : EnvI) (A B : Expr Nat) :
    ApproxDIK E ρ (.pi A B) (.pi .bot []) :=
  .pi (.bot ρ A) (fun _ hs => (List.not_mem_nil _ hs).elim)

/-- **Positive `W-K` Repair at `andEnvU` (`semEqDIK_andEnvU_mixAndRedex_mixPi`)**: in `ApproxDIK`,
    `mixAndRedex` and `mixPi` have the exact same approximations at `EnvI.bot`
    (repairing `not_semEqDI_andEnvU_mixAndRedex_mixPi` from §9.2). -/
theorem semEqDIK_andEnvU_mixAndRedex_mixPi :
    SemEqDIK andEnvU EnvI.bot mixAndRedex mixPi :=
  semEqDIK_trans semEqDIK_andEnvU_mixAndRedex_mixAndRhs
    (semEqDIK_whRed andEnvUWfT whRed_andEnvU_mixAndRhs_mixPi EnvI.bot)

/-- In `ApproxDIK`, `.pi .bot []` approximates `mixAndRedex` at `EnvI.bot`
    (repairing `not_approxDI_andEnvU_mixAndRedex_pi` from §9.2). -/
theorem approxDIK_andEnvU_mixAndRedex_pi :
    ApproxDIK andEnvU EnvI.bot mixAndRedex (.pi .bot []) :=
  (semEqDIK_andEnvU_mixAndRedex_mixPi (.pi .bot [])).mpr
    (approxDIK_pi_bot_nil andEnvU EnvI.bot (.sort .zero) (.sort .zero))

/-- K-aware weak-head step relation `WhStepPiK E a b`: extends `WhStep E` with `iotaK` for
    single-constructor `Prop` recursors (`piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1`)
    whose fields have `⊥`-only approximations at `EnvI.bot` and whose major premise `x` has no
    `.spine w.ctorRef args` approximation at `EnvI.bot`. -/
inductive WhStepPiK (E : ResolvedEnv) : Expr Nat → Expr Nat → Prop
  | of_whStep {a b : Expr Nat} (h : WhStep E a b) : WhStepPiK E a b
  | iotaK (w : IotaWitnessS E) (x : Expr Nat)
      (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
      (hflds : ∀ f ∈ w.fields, ∀ u, ApproxDIK E EnvI.bot f u → u = .bot)
      (hx : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w.ctorRef args)) :
      WhStepPiK E (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w)
  | appHead {f f' arg : Expr Nat} (h : WhStepPiK E f f') :
      WhStepPiK E (.app f arg) (.app f' arg)

/-- Reflexive-transitive closure of `WhStepPiK`. -/
inductive WhRedPiK (E : ResolvedEnv) : Expr Nat → Expr Nat → Prop
  | refl (a : Expr Nat) : WhRedPiK E a a
  | step {a b c : Expr Nat} (hs : WhStepPiK E a b) (hr : WhRedPiK E b c) :
      WhRedPiK E a c

theorem whRedPiK_trans {E : ResolvedEnv} {a b c : Expr Nat}
    (h₁ : WhRedPiK E a b) (h₂ : WhRedPiK E b c) : WhRedPiK E a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem whRedPiK_of_whRed {E : ResolvedEnv} {a b : Expr Nat}
    (h : WhRed E a b) : WhRedPiK E a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step (.of_whStep hs) ih

/-- Every `WhStepPiK` step is sound in `ApproxDIK E EnvI.bot` at `EnvWfT E`. -/
theorem semEqDIK_whStepPiK {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hs : WhStepPiK E a b) : SemEqDIK E EnvI.bot a b := by
  induction hs with
  | of_whStep h => exact semEqDIK_whStep hW h EnvI.bot
  | iotaK w x hk hflds hx => exact semEqDIK_k_botFields w hk hflds hx
  | @appHead f f' arg _ ih => exact semEqDIK_app ih (semEqDIK_refl E EnvI.bot arg)

/-- Multi-step `WhRedPiK` reduction is sound in `ApproxDIK E EnvI.bot` at `EnvWfT E`. -/
theorem semEqDIK_whRedPiK {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hr : WhRedPiK E a b) : SemEqDIK E EnvI.bot a b := by
  induction hr with
  | refl e => exact semEqDIK_refl E EnvI.bot e
  | step hs _ ih => exact semEqDIK_trans (semEqDIK_whStepPiK hW hs) ih

theorem approxDIK_whRedPiK_back {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hr : WhRedPiK E a b) {c : CptI} (hb : ApproxDIK E EnvI.bot b c) :
    ApproxDIK E EnvI.bot a c :=
  (semEqDIK_whRedPiK hW hr c).mpr hb

theorem approxDIK_sort_of_whRedPiK {E : ResolvedEnv} (hW : EnvWfT E) {a : Expr Nat} {l : Level}
    (hr : WhRedPiK E a (.sort l)) : ApproxDIK E EnvI.bot a .sort :=
  approxDIK_whRedPiK_back hW hr (.sort EnvI.bot l)

theorem whStepPiK_sort_false {E : ResolvedEnv} {l : Level} {e : Expr Nat}
    (h : WhStepPiK E (.sort l) e) : False := by
  generalize ha : (Expr.sort l : Expr Nat) = a at h
  cases h with
  | of_whStep hs =>
      subst ha
      exact whStep_sort_false hs
  | iotaK w x _ _ _ =>
      have hs := congrArg appsSpine ha
      unfold recCall at hs
      rw [appsSpine_foldApps_const] at hs
      exact Expr.noConfusion (congrArg Prod.fst hs)
  | appHead _ =>
      exact Expr.noConfusion ha

theorem whStepPiK_pi_false {E : ResolvedEnv} {A B e : Expr Nat}
    (h : WhStepPiK E (.pi A B) e) : False := by
  generalize ha : (Expr.pi A B : Expr Nat) = a at h
  cases h with
  | of_whStep hs =>
      subst ha
      exact whStep_pi_false hs
  | iotaK w x _ _ _ =>
      have hs := congrArg appsSpine ha
      unfold recCall at hs
      rw [appsSpine_foldApps_const] at hs
      exact Expr.noConfusion (congrArg Prod.fst hs)
  | appHead _ =>
      exact Expr.noConfusion ha

theorem whRedPiK_sort_eq {E : ResolvedEnv} {l : Level} {e : Expr Nat}
    (h : WhRedPiK E (.sort l) e) : e = .sort l := by
  cases h with
  | refl => rfl
  | step hs => exact (whStepPiK_sort_false hs).elim

theorem whRedPiK_pi_eq {E : ResolvedEnv} {A B e : Expr Nat}
    (h : WhRedPiK E (.pi A B) e) : e = .pi A B := by
  cases h with
  | refl => rfl
  | step hs => exact (whStepPiK_pi_false hs).elim

/-- `WhStepPiK.iotaK` for legacy `w : IotaWitness E` at `EnvWfT E`. -/
theorem whStepPiK_iotaK_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) (x : Expr Nat)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    (hflds : ∀ f ∈ w.fields, ∀ u, ApproxDIK E EnvI.bot f u → u = .bot)
    (hx : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w.ctorRef args)) :
    WhStepPiK E (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) := by
  obtain ⟨wS, hrec, hctor, hls, _, hpre, hfldsEq, _, _, hfamM, _, _, hnmin, _, _, hrhs⟩ :=
    iotaWitnessS_of_iotaWitness_envWfT hW w
  have hkS : piBody wS.famMember.mtype = .sort .zero ∧ wS.nMinors = 1 := by
    rw [hfamM, hnmin]; exact hk
  have hfldsS : ∀ f ∈ wS.fields, ∀ u, ApproxDIK E EnvI.bot f u → u = .bot := by
    rw [hfldsEq]; exact hflds
  have hxS : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine wS.ctorRef args) := by
    rw [hctor]; exact hx
  have hs := WhStepPiK.iotaK wS x hkS hfldsS hxS
  rwa [hrec, hls, hpre, hrhs] at hs

/-- In `WhRedPiK`, `trueEnvU_kRecVar` reduces in 1 `iotaK` step to `.sort .zero`. -/
theorem whRedPiK_trueEnvU_kRecVar_sort :
    WhRedPiK trueEnvU trueEnvU_kRecVar (.sort .zero) :=
  .step (whStepPiK_iotaK_of_envWfT trueEnvUWfT wTrueRecU (.bvar 0) ⟨rfl, rfl⟩
    (fun f hf => (List.not_mem_nil _ hf).elim)
    (fun args hsp => by rcases approxDIK_bvar_inv hsp with h0 | h0 <;> cases h0)) (.refl _)

/-- In `WhRedPiK`, `mixAndRedex` reduces via 1 `iotaK` step (`mixAndRedex ↦ mixAndRhs`) followed
    by 2 β steps (`mixAndRhs ↦* mixPi`) to `mixPi = .pi (.sort .zero) (.sort .zero)`. -/
theorem whRedPiK_andEnvU_mixAndRedex_mixPi :
    WhRedPiK andEnvU mixAndRedex mixPi :=
  .step (whStepPiK_iotaK_of_envWfT andEnvUWfT mixAndW (.bvar 0) ⟨rfl, rfl⟩
    (fun f hf u hu => by
      simp only [mixAndW, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;>
        (rcases approxDIK_bvar_inv hu with rfl | h0; rfl; exact h0))
    (fun args hsp => by rcases approxDIK_bvar_inv hsp with h0 | h0 <;> cases h0))
    (whRedPiK_of_whRed whRed_andEnvU_mixAndRhs_mixPi)

/-- Compact-indexed type logical relation `LRTypeINPiK` over `WhRedPiK`. -/
inductive LRTypeINPiK (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → CptI → Prop
  | bot (Γ : LCtx) (A B : Expr Nat) : LRTypeINPiK E n Γ A B .bot
  | sort {Γ : LCtx} {A B : Expr Nat} {l₁ l₂ : Level}
      (hA : WhRedPiK E A (.sort l₁)) (hB : WhRedPiK E B (.sort l₂)) :
      LRTypeINPiK E n Γ A B .sort
  | pi {Γ : LCtx} {A B A₁ B₁ A₂ B₂ : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (hA : WhRedPiK E A (.pi A₁ B₁)) (hB : WhRedPiK E B (.pi A₂ B₂))
      (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
      (hdom : TyConvT E n Γ A₁ A₂)
      (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
      (ra : LRTypeINPiK E n Γ A₁ A₂ a)
      (rf : ∀ s ∈ f, LRTypeINPiK E n (.assumption A₁ :: Γ) B₁ B₂ s.2) :
      LRTypeINPiK E n Γ A B (.pi a f)
  | spine {Γ : LCtx} {A B X X' : Expr Nat} {r : Nat} {args : List CptI}
      (hA : WhRedPiK E A X) (hB : WhRedPiK E B X')
      (hX : WhNormal E X) (hX' : WhNormal E X')
      (hc : TyConvT E n Γ X X') :
      LRTypeINPiK E n Γ A B (.spine r args)

/-- Every `LRTypeIN` witness embeds conservatively into `LRTypeINPiK`. -/
theorem lrTypeINPiK_of_lrTypeIN {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {c : CptI}
    (h : LRTypeIN E n Γ A B c) : LRTypeINPiK E n Γ A B c := by
  induction h with
  | bot => exact .bot _ _ _
  | sort hA hB => exact .sort (whRedPiK_of_whRed hA) (whRedPiK_of_whRed hB)
  | pi hA hB hΓ₁ hdom hcod _ _ iha ihf =>
      exact .pi (whRedPiK_of_whRed hA) (whRedPiK_of_whRed hB) hΓ₁ hdom hcod iha ihf
  | spine hA hB hX hX' hc =>
      exact .spine (whRedPiK_of_whRed hA) (whRedPiK_of_whRed hB) hX hX' hc

/-- **Soundness-Free Reverse Adequacy of `LRTypeINPiK` on `BotPiCpt`:** at every `EnvWfT E`,
    `LRTypeINPiK E n Γ A B c` on a `BotPiCpt c` implies **both** `ApproxDIK E EnvI.bot A c` and
    `ApproxDIK E EnvI.bot B c` (eliminating `TypeSoundness` from `TyConvT.trans` on `BotPiCpt`). -/
theorem approxDIK_of_lrTypeINPiK_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A B : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (h : LRTypeINPiK E n Γ A B c) :
    ApproxDIK E EnvI.bot A c ∧ ApproxDIK E EnvI.bot B c := by
  induction h with
  | bot => exact ⟨.bot _ _, .bot _ _⟩
  | sort hA hB =>
      exact ⟨approxDIK_sort_of_whRedPiK hW hA, approxDIK_sort_of_whRedPiK hW hB⟩
  | @pi Γ A B A₁ B₁ A₂ B₂ a f hA hB _ _ _ _ _ iha ihf =>
      cases hc with
      | pi ha hbd hf =>
          obtain ⟨ha₁, ha₂⟩ := iha ha
          have hf₁ : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) EnvI.bot) B₁ s.2 :=
            fun s hs =>
              (approxDIK_cons_botDemand_bot_iff (hbd s hs) B₁ s.2).mpr (ihf s hs (hf s hs)).1
          have hf₂ : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) EnvI.bot) B₂ s.2 :=
            fun s hs =>
              (approxDIK_cons_botDemand_bot_iff (hbd s hs) B₂ s.2).mpr (ihf s hs (hf s hs)).2
          exact ⟨approxDIK_whRedPiK_back hW hA (.pi ha₁ hf₁),
                 approxDIK_whRedPiK_back hW hB (.pi ha₂ hf₂)⟩
  | spine => cases hc

/-- Bidirectional `BotPiCpt`-restricted type logical relation over `ApproxDIK E EnvI.bot` and
    `LRTypeINPiK`. -/
def LRTypeINBiDIK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B : Expr Nat) : Prop :=
  ∀ c, BotPiCpt c →
    (ApproxDIK E EnvI.bot A c ∨ ApproxDIK E EnvI.bot B c) →
    LRTypeINPiK E n Γ A B c

theorem lrTypeINBiDIK_sorts (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l₁ l₂ : Level) :
    LRTypeINBiDIK E n Γ (.sort l₁) (.sort l₂) := by
  intro c _ h
  rcases h with h | h
  · rcases approxDIK_sort_inv h with rfl | rfl
    · exact .bot _ _ _
    · exact .sort (.refl _) (.refl _)
  · rcases approxDIK_sort_inv h with rfl | rfl
    · exact .bot _ _ _
    · exact .sort (.refl _) (.refl _)

theorem lrTypeINBiDIK_sort_diag (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level) :
    LRTypeINBiDIK E n Γ (.sort l) (.sort l) :=
  lrTypeINBiDIK_sorts E n Γ l l

theorem lrTypeINBiDIK_bvar_diag (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (i : Nat) :
    LRTypeINBiDIK E n Γ (.bvar i) (.bvar i) := by
  intro c _ h
  rcases approxDIK_bvar_inv (h.elim id id) with rfl | h0
  · exact .bot _ _ _
  · cases h0; exact .bot _ _ _

theorem lrTypeINBiDIK_pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₁ B₁ A₂ B₂ : Expr Nat}
    (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
    (hdom : TyConvT E n Γ A₁ A₂)
    (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
    (ihA : LRTypeINBiDIK E n Γ A₁ A₂)
    (ihB : LRTypeINBiDIK E n (.assumption A₁ :: Γ) B₁ B₂) :
    LRTypeINBiDIK E n Γ (.pi A₁ B₁) (.pi A₂ B₂) := by
  intro c hc h
  rcases h with h₁ | h₂
  · rcases approxDIK_pi_inv h₁ with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact .bot _ _ _
    · cases hc with
      | pi hca hbd hcf =>
          refine .pi (.refl _) (.refl _) hΓ₁ hdom hcod (ihA a hca (Or.inl ha)) (fun s hs => ?_)
          have hb := (approxDIK_cons_botDemand_bot_iff (hbd s hs) B₁ s.2).mp (hf s hs)
          exact ihB s.2 (hcf s hs) (Or.inl hb)
  · rcases approxDIK_pi_inv h₂ with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact .bot _ _ _
    · cases hc with
      | pi hca hbd hcf =>
          refine .pi (.refl _) (.refl _) hΓ₁ hdom hcod (ihA a hca (Or.inr ha)) (fun s hs => ?_)
          have hb := (approxDIK_cons_botDemand_bot_iff (hbd s hs) B₂ s.2).mp (hf s hs)
          exact ihB s.2 (hcf s hs) (Or.inr hb)

theorem lrTypeINPiK_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat}
    (hA : WhRedPiK E A A') (hB : WhRedPiK E B B') {c : CptI}
    (h : LRTypeINPiK E n Γ A' B' c) : LRTypeINPiK E n Γ A B c := by
  cases h with
  | bot => exact .bot _ _ _
  | sort hA' hB' => exact .sort (whRedPiK_trans hA hA') (whRedPiK_trans hB hB')
  | pi hA' hB' hΓ₁ hdom hcod ra rf =>
      exact .pi (whRedPiK_trans hA hA') (whRedPiK_trans hB hB') hΓ₁ hdom hcod ra rf
  | spine hA' hB' hX hX' hc =>
      exact .spine (whRedPiK_trans hA hA') (whRedPiK_trans hB hB') hX hX' hc

theorem lrTypeINBiDIK_of_whRedPiK {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {M M' : Expr Nat} (hr : WhRedPiK E M M')
    (hdiag : LRTypeINBiDIK E n Γ M' M') :
    LRTypeINBiDIK E n Γ M M' := by
  intro c hc h
  have hM' : ApproxDIK E EnvI.bot M' c :=
    h.elim (fun hM => (semEqDIK_whRedPiK hW hr c).mp hM) id
  exact lrTypeINPiK_expand hr (.refl _) (hdiag c hc (Or.inl hM'))

/-- **Positive `W-K` Repair in `LRTypeINBiDIK` at `trueEnvU`**:
    `LRTypeINBiDIK trueEnvU 0 trueEnvU_kVarCtx trueEnvU_kRecVar (.sort .zero)` holds
    (repairing `not_lrTypeINBiDI_trueEnvU_kRecVar` from §9.4). -/
theorem lrTypeINBiDIK_trueEnvU_kRecVar_sort :
    LRTypeINBiDIK trueEnvU 0 trueEnvU_kVarCtx trueEnvU_kRecVar (.sort .zero) :=
  lrTypeINBiDIK_of_whRedPiK trueEnvUWfT whRedPiK_trueEnvU_kRecVar_sort
    (lrTypeINBiDIK_sort_diag trueEnvU 0 trueEnvU_kVarCtx .zero)

/-- **Positive `W-K` Repair in `LRTypeINBiDIK` at `andEnvU`**:
    `LRTypeINBiDIK andEnvU 0 mixAndCtx mixAndRedex mixPi` holds
    (repairing `not_lrTypeIN_andEnvU_mixAnd` and `not_lrTypeINBiDI_andEnvU_mixAnd` from §9.5). -/
theorem lrTypeINBiDIK_andEnvU_mixAndRedex_mixPi :
    LRTypeINBiDIK andEnvU 0 mixAndCtx mixAndRedex mixPi := by
  have hΓ₁ : CtxWfT andEnvU 0 (.assumption (.sort .zero) :: mixAndCtx) :=
    .assumption mixAndCtx (.sort .zero) (.succ .zero)
      Rcic.Domain.Model.PiInversion.mixAndCtx_wf (.sort mixAndCtx .zero)
  exact lrTypeINBiDIK_of_whRedPiK andEnvUWfT whRedPiK_andEnvU_mixAndRedex_mixPi
    (lrTypeINBiDIK_pi hΓ₁ (.refl _ _) (.refl _ _)
      (lrTypeINBiDIK_sort_diag andEnvU 0 mixAndCtx .zero)
      (lrTypeINBiDIK_sort_diag andEnvU 0 (.assumption (.sort .zero) :: mixAndCtx) .zero))

/-- Named `LetFreeCtx`-restricted fundamental supply for `LRTypeINPiK` over `ApproxDIK E EnvI.bot`:
    not refuted by `W-ZetaLocal` (`letFreeCtx`), `W-IrrPi` (`BotPiCpt`), or `W-K` at `trueEnvU`
    and `andEnvU` (`lrTypeINBiDIK_trueEnvU_kRecVar_sort`, `lrTypeINBiDIK_andEnvU_mixAndRedex_mixPi`). -/
def FundamentalLRINBotDIK_letFree (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {A B : Expr Nat}, TyConvT E n Γ A B →
      ∀ c, BotPiCpt c → ApproxDIK E EnvI.bot A c → LRTypeINPiK E n Γ A B c

/-- Projection from `FundamentalLRINBotDIK_letFree E n` to `LetFreeCtx`-restricted `piRow`. -/
theorem piRow_letFree_of_fundamentalLRINBotDIK_letFree {E : ResolvedEnv} {n : Nat}
    (hF : FundamentalLRINBotDIK_letFree E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hlf : LetFreeCtx Γ)
    {A₁ B₁ A₂ B₂ : Expr Nat}
    (h : TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  have hlr : LRTypeINPiK E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.pi .bot []) :=
    hF hΓ hlf h (.pi .bot []) botPiCpt_pi_bot_nil (approxDIK_pi_bot_nil E EnvI.bot A₁ B₁)
  cases hlr with
  | pi hA hB _ hdom hcod _ _ =>
      have e₁ := whRedPiK_pi_eq hA
      have e₂ := whRedPiK_pi_eq hB
      injection e₁ with eA₁ eB₁
      injection e₂ with eA₂ eB₂
      subst eA₁; subst eB₁; subst eA₂; subst eB₂
      exact ⟨⟨hdom⟩, ⟨hcod⟩⟩

theorem piRow_of_fundamentalLRINBotDIK_letFree {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hF : FundamentalLRINBotDIK_letFree E n) : PiRowField E n :=
  fun {_} hΓ {_ _ _ _} h =>
    piRow_of_letFree_piRow hW
      (fun {_} hlf' hΓ' {_ _ _ _} h' =>
        piRow_letFree_of_fundamentalLRINBotDIK_letFree hF hΓ' hlf' h')
      hΓ h

/-! ## §11. `lift 0 1` Invariance & Context-Aware `ctxEnvDIK`, `LRTypeINPiK` Symmetry,
Canonical Deterministic K-Readback `WhStepPiKCanon` / `WhRedPiKCanon` (`whDetPiKCanon_of_envWfT`),
and `LRTypeINPiKCanon` / `LRTypeINBiDIKCanon` Transitivity & Chain Closure -/

/-! ### §11.1. `lift 0 1` Invariance in `ApproxDIK` and Context-Aware Valuation `ctxEnvDIK` -/

/-- Exact `lift 0 1` invariance of `ApproxDIK` under `EnvI.cons S ρ`. -/
theorem approxDIK_lift0_one_iff {E : ResolvedEnv} (ρ : EnvI) (S : CptI → Prop)
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E (EnvI.cons S ρ) (lift 0 1 e) c ↔ ApproxDIK E ρ e c := by
  constructor
  · intro h
    exact approxDIK_lift_elim e (by rwa [EnvI.insert_zero])
  · intro h
    have := approxDIK_lift_intro h 0 S
    rwa [EnvI.insert_zero] at this

theorem denDIK_lift0_one_eq {E : ResolvedEnv} (ρ : EnvI) (S : CptI → Prop) (e : Expr Nat) :
    denDIK E (EnvI.cons S ρ) (lift 0 1 e) = denDIK E ρ e := by
  funext c
  exact propext (approxDIK_lift0_one_iff ρ S e c)

theorem semEqDIK_lift0_one_iff {E : ResolvedEnv} (ρ : EnvI) (S : CptI → Prop)
    (a b : Expr Nat) :
    SemEqDIK E (EnvI.cons S ρ) (lift 0 1 a) (lift 0 1 b) ↔ SemEqDIK E ρ a b := by
  constructor
  · intro h c
    exact (approxDIK_lift0_one_iff ρ S a c).symm.trans
      ((h c).trans (approxDIK_lift0_one_iff ρ S b c))
  · intro h c
    exact (approxDIK_lift0_one_iff ρ S a c).trans
      ((h c).trans (approxDIK_lift0_one_iff ρ S b c).symm)

/-- Context-aware K-model valuation `ctxEnvDIK E Γ`: maps `.assumption` entries to `{.bot}` and
    `.letBinding _ v :: Γ` entries to `denDIK E (ctxEnvDIK E Γ) v`. -/
def ctxEnvDIK (E : ResolvedEnv) : LCtx → EnvI
  | [] => EnvI.bot
  | .assumption _ :: Γ => EnvI.cons (fun c => c = .bot) (ctxEnvDIK E Γ)
  | .letBinding _ v :: Γ => EnvI.cons (denDIK E (ctxEnvDIK E Γ) v) (ctxEnvDIK E Γ)

/-- `EnvI.bot` is below `ctxEnvDIK E Γ` for every context `Γ : LCtx`. -/
theorem bot_le_ctxEnvDIK (E : ResolvedEnv) :
    ∀ (Γ : LCtx), EnvI.le EnvI.bot (ctxEnvDIK E Γ)
  | [] => fun _ _ h => h
  | .assumption _ :: Γ => by
      intro i c hc
      cases hc
      cases i with
      | zero => rfl
      | succ i => exact bot_le_ctxEnvDIK E Γ i .bot rfl
  | .letBinding _ v :: Γ => by
      intro i c hc
      cases hc
      cases i with
      | zero => exact .bot (ctxEnvDIK E Γ) v
      | succ i => exact bot_le_ctxEnvDIK E Γ i .bot rfl

/-- At any assumption-bound (or out-of-range) index `lookupValue Γ i = none`, `ctxEnvDIK E Γ i`
    contains only `.bot`. -/
theorem ctxEnvDIK_none_bot (E : ResolvedEnv) :
    ∀ (Γ : LCtx) (i : Nat), lookupValue Γ i = none →
      ∀ c, ctxEnvDIK E Γ i c → c = .bot
  | [], _, _, _, h => h
  | .assumption _ :: Γ, 0, _, _, h => h
  | .assumption _ :: Γ, i + 1, h0, c, h => by
      apply ctxEnvDIK_none_bot E Γ i _ c h
      rw [lookupValue_cons_succ] at h0
      cases hv : lookupValue Γ i with
      | none => rfl
      | some v => rw [hv] at h0; exact Option.noConfusion h0
  | .letBinding _ _ :: Γ, 0, h0, _, _ => Option.noConfusion h0
  | .letBinding _ _ :: Γ, i + 1, h0, c, h => by
      apply ctxEnvDIK_none_bot E Γ i _ c h
      rw [lookupValue_cons_succ] at h0
      cases hv : lookupValue Γ i with
      | none => rfl
      | some v => rw [hv] at h0; exact Option.noConfusion h0

/-- On any `LetFreeCtx Γ`, `ctxEnvDIK E Γ` is pointwise below `EnvI.bot`. -/
theorem ctxEnvDIK_letFree_le_bot {E : ResolvedEnv} {Γ : LCtx} (hlf : LetFreeCtx Γ) :
    EnvI.le (ctxEnvDIK E Γ) EnvI.bot :=
  fun i c hc => ctxEnvDIK_none_bot E Γ i (hlf i) c hc

/-- Monotonicity from `EnvI.bot` to `ctxEnvDIK E Γ` for any context `Γ`. -/
theorem approxDIK_of_bot_to_ctxEnvDIK {E : ResolvedEnv} (Γ : LCtx) {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E EnvI.bot e c) : ApproxDIK E (ctxEnvDIK E Γ) e c :=
  approxDIK_mono_env (bot_le_ctxEnvDIK E Γ) h

/-- On any `LetFreeCtx Γ`, `ApproxDIK E (ctxEnvDIK E Γ)` and `ApproxDIK E EnvI.bot` coincide. -/
theorem approxDIK_ctxEnvDIK_letFree_iff {E : ResolvedEnv} {Γ : LCtx} (hlf : LetFreeCtx Γ)
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E (ctxEnvDIK E Γ) e c ↔ ApproxDIK E EnvI.bot e c :=
  ⟨approxDIK_mono_env (ctxEnvDIK_letFree_le_bot hlf), approxDIK_of_bot_to_ctxEnvDIK Γ⟩

/-- **Unconditional `ConvT.zetaLocal` Soundness in `ctxEnvDIK` (`semEqDIK_ctxEnvDIK_zetaLocal`):**
    for **every** `E : ResolvedEnv`, `Γ : LCtx`, `i : Nat`, and `v : Expr Nat`,
    `lookupValue Γ i = some v → SemEqDIK E (ctxEnvDIK E Γ) (.bvar i) v`. -/
theorem semEqDIK_ctxEnvDIK_zetaLocal (E : ResolvedEnv) :
    ∀ (Γ : LCtx) {i : Nat} {v : Expr Nat},
      lookupValue Γ i = some v →
      SemEqDIK E (ctxEnvDIK E Γ) (.bvar i) v
  | [], _, _, hv => Option.noConfusion hv
  | .assumption A :: Γ, 0, _, hv => Option.noConfusion hv
  | .assumption A :: Γ, i + 1, v, hv => by
      rw [lookupValue_cons_succ] at hv
      cases hli : lookupValue Γ i with
      | none => rw [hli] at hv; exact Option.noConfusion hv
      | some w =>
          rw [hli] at hv
          injection hv with hv'
          subst hv'
          have ih := semEqDIK_ctxEnvDIK_zetaLocal E Γ hli
          intro c
          have hbvar : ApproxDIK E (ctxEnvDIK E (.assumption A :: Γ)) (.bvar (i + 1)) c ↔
              ApproxDIK E (ctxEnvDIK E Γ) (.bvar i) c := by
            constructor <;>
              (intro h; rcases approxDIK_bvar_inv h with rfl | h0; exact .bot _ _; exact .bvar h0)
          exact hbvar.trans
            ((ih c).trans (approxDIK_lift0_one_iff (ctxEnvDIK E Γ) (fun c => c = .bot) w c).symm)
  | .letBinding A w :: Γ, 0, v, hv => by
      injection hv with hv'
      subst hv'
      intro c
      have hbvar : ApproxDIK E (ctxEnvDIK E (.letBinding A w :: Γ)) (.bvar 0) c ↔
          ApproxDIK E (ctxEnvDIK E Γ) w c := by
        constructor
        · intro h
          rcases approxDIK_bvar_inv h with rfl | h0
          · exact .bot _ _
          · exact h0
        · intro h
          exact .bvar h
      exact hbvar.trans
        (approxDIK_lift0_one_iff (ctxEnvDIK E Γ) (denDIK E (ctxEnvDIK E Γ) w) w c).symm
  | .letBinding A u :: Γ, i + 1, v, hv => by
      rw [lookupValue_cons_succ] at hv
      cases hli : lookupValue Γ i with
      | none => rw [hli] at hv; exact Option.noConfusion hv
      | some w =>
          rw [hli] at hv
          injection hv with hv'
          subst hv'
          have ih := semEqDIK_ctxEnvDIK_zetaLocal E Γ hli
          intro c
          have hbvar : ApproxDIK E (ctxEnvDIK E (.letBinding A u :: Γ)) (.bvar (i + 1)) c ↔
              ApproxDIK E (ctxEnvDIK E Γ) (.bvar i) c := by
            constructor <;>
              (intro h; rcases approxDIK_bvar_inv h with rfl | h0; exact .bot _ _; exact .bvar h0)
          exact hbvar.trans
            ((ih c).trans
              (approxDIK_lift0_one_iff (ctxEnvDIK E Γ) (denDIK E (ctxEnvDIK E Γ) u) w c).symm)

/-- Positive pin on `zetaLocalSortCtx = [.letBinding (.sort (.succ .zero)) (.sort .zero)]`:
    under `ctxEnvDIK E zetaLocalSortCtx`, `.bvar 0` and `.sort .zero` are semantically equal. -/
theorem semEqDIK_ctxEnvDIK_zetaLocalSortCtx (E : ResolvedEnv) :
    SemEqDIK E (ctxEnvDIK E zetaLocalSortCtx) (.bvar 0) (.sort .zero) :=
  semEqDIK_ctxEnvDIK_zetaLocal E zetaLocalSortCtx rfl

theorem approxDIK_ctxEnvDIK_zetaLocalSortCtx_sort (E : ResolvedEnv) :
    ApproxDIK E (ctxEnvDIK E zetaLocalSortCtx) (.bvar 0) .sort :=
  (semEqDIK_ctxEnvDIK_zetaLocalSortCtx E .sort).mpr (.sort _ _)

/-! ### §11.2. `Sort`/`Pi` Disjointness (`not_whRedPiK_sort_and_pi`), Context Conversion, and
Full Symmetry (`lrTypeINPiK_symm`, `lrTypeINBiDIK_symm`) for `LRTypeINPiK` -/

/-- No term `A` can `WhRedPiK`-reduce to both `.sort l` and `.pi A₁ B₁` in any `EnvWfT E`
    (proved directly from `semEqDIK_whRedPiK` and `semEqDIK_pi_sort_disjoint`, without determinism). -/
theorem not_whRedPiK_sort_and_pi {E : ResolvedEnv} (hW : EnvWfT E)
    {A A₁ B₁ : Expr Nat} {l : Level}
    (hs : WhRedPiK E A (.sort l)) (hp : WhRedPiK E A (.pi A₁ B₁)) : False :=
  semEqDIK_pi_sort_disjoint
    (semEqDIK_trans (semEqDIK_symm (semEqDIK_whRedPiK hW hp)) (semEqDIK_whRedPiK hW hs))

/-- Context transport of `LRTypeINPiK` along any `CtxConvT E n Γ Γ'` across all compacts `c : CptI`. -/
theorem lrTypeINPiK_ctx {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ Γ' : LCtx}
    (hctx : CtxConvT E n Γ Γ') (hΓ' : CtxWfT E n Γ') {A A' : Expr Nat} {c : CptI}
    (h : LRTypeINPiK E n Γ A A' c) : LRTypeINPiK E n Γ' A A' c := by
  have hcl := envClosed_of_envWfT hW
  induction h generalizing Γ' with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort h h'
  | @pi Γ A A' A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      cases hΓ₁ with
      | assumption _ _ u _ hA₁ =>
          have hA₁' : HasTyT E n Γ' A₁ (.sort u) := hasTyT_ctx hcl hctx hA₁
          have hΓ₁' : CtxWfT E n (.assumption A₁ :: Γ') := .assumption Γ' A₁ u hΓ' hA₁'
          exact .pi h h' hΓ₁' (tyConvT_ctx hcl hctx hdom)
            (tyConvT_ctx hcl (.same (.assumption A₁) hctx) hcod)
            (iha hctx hΓ')
            (fun s hs => ihf s hs (.same (.assumption A₁) hctx) hΓ₁')
  | spine h h' hn hn' hc => exact .spine h h' hn hn' (tyConvT_ctx hcl hctx hc)

/-- Head-assumption domain transport for `LRTypeINPiK` along a `TyConvT` chain. -/
theorem lrTypeINPiK_assump_dom {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) :
    {A₁ A₂ : Expr Nat} → TyConvT E n Γ A₁ A₂ → {u : Level} → HasTyT E n Γ A₁ (.sort u) →
    ∀ {B B' : Expr Nat} {c : CptI},
      LRTypeINPiK E n (.assumption A₂ :: Γ) B B' c →
      LRTypeINPiK E n (.assumption A₁ :: Γ) B B' c
  | _, _, .refl _ _, _, _, _, _, _, h => h
  | _, _, .of _ A₁ A₂ _ hc, _, hA₁, _, _, _, h =>
      let ends := convEnds hW hΓ hc
      lrTypeINPiK_ctx hW
        (.assumption (ctxConvT_refl Γ) ends.2.1 ends.1 (.symm _ _ _ _ hc))
        (.assumption Γ A₁ _ hΓ hA₁) h
  | _, _, .trans _ A₁ _ A₂ c₁ c₂, _, hA₁, _, _, _, h =>
      let ⟨_, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA₁
      lrTypeINPiK_assump_dom hW hΓ c₁ hA₁ (lrTypeINPiK_assump_dom hW hΓ c₂ hM h)

/-- Full symmetry of `LRTypeINPiK` across all compacts `c : CptI` at `EnvWfT E`
    (requiring **zero** `WhDet` or `TypeSoundness` hypotheses). -/
theorem lrTypeINPiK_symm {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ : LCtx}
    {A A' : Expr Nat} {c : CptI} (h : LRTypeINPiK E n Γ A A' c) :
    LRTypeINPiK E n Γ A' A c := by
  induction h with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort h' h
  | @pi Γ A A' A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      cases hΓ₁ with
      | assumption _ _ _ hΓ hA₁ =>
          obtain ⟨v, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          have hΓ₂ : CtxWfT E n (.assumption A₂ :: Γ) := .assumption Γ A₂ v hΓ hA₂
          exact .pi h' h hΓ₂ hdom.symmT (tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT) iha
            (fun s hs => lrTypeINPiK_assump_dom hW hΓ hdom.symmT hA₂ (ihf s hs))
  | spine h h' hn hn' hc => exact .spine h' h hn' hn hc.symmT

/-- Symmetry of `LRTypeINBiDIK` at `EnvWfT E`. -/
theorem lrTypeINBiDIK_symm {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A B : Expr Nat} (h : LRTypeINBiDIK E n Γ A B) :
    LRTypeINBiDIK E n Γ B A :=
  fun c hc hBA => lrTypeINPiK_symm hW (h c hc hBA.symm)

/-! ### §11.3. Canonical Deterministic K-Aware Weak-Head Reduction `WhStepPiKCanon` / `WhRedPiKCanon`
and Exact Single-Step Determinism (`whDetPiKCanon_of_envWfT`) -/

/-- **Canonical Deterministic K-Aware Weak-Head Step (`WhStepPiKCanon E a b`):**
    Refines `WhStepPiK` by fixing the dummy field terms in `iotaKCanon` to
    `w.fields = List.replicate w.fields.length (.bvar 0)`. Because `iotaWitnessS_unique_of_nMinors_one`
    uniquely determines `w.fields.length` and `w.schema` from `w.recRef` and `w.nMinors = 1`, fixing
    `w.fields = List.replicate w.fields.length (.bvar 0)` makes the contractum `iotaRhsOfS w`
    **100% single-step deterministic** (`whDetPiKCanon_of_envWfT`) while still reducing both
    0-field `trueEnvU_kRecVar` and fieldful `mixAndRedex`! -/
inductive WhStepPiKCanon (E : ResolvedEnv) : Expr Nat → Expr Nat → Prop
  | of_whStep {a b : Expr Nat} (h : WhStep E a b) : WhStepPiKCanon E a b
  | iotaKCanon (w : IotaWitnessS E) (x : Expr Nat)
      (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
      (hflds : w.fields = List.replicate w.fields.length (.bvar 0))
      (hx : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w.ctorRef args)) :
      WhStepPiKCanon E (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w)
  | appHead {f f' arg : Expr Nat} (h : WhStepPiKCanon E f f') :
      WhStepPiKCanon E (.app f arg) (.app f' arg)

/-- Every `WhStepPiKCanon` step embeds into `WhStepPiK` (since every element of
    `List.replicate k (.bvar 0)` is `.bvar 0`, which has `⊥`-only approximations at `EnvI.bot`). -/
theorem whStepPiK_of_whStepPiKCanon {E : ResolvedEnv} {a b : Expr Nat}
    (h : WhStepPiKCanon E a b) : WhStepPiK E a b := by
  induction h with
  | of_whStep hs => exact .of_whStep hs
  | iotaKCanon w x hk hflds hx =>
      refine .iotaK w x hk (fun f hf u hu => ?_) hx
      rw [hflds] at hf
      have hfEq : f = .bvar 0 := List.eq_of_mem_replicate hf
      subst hfEq
      rcases approxDIK_bvar_inv hu with rfl | h0
      · rfl
      · exact h0
  | @appHead _ _ _ _ ih => exact .appHead ih

/-- Reflexive-transitive closure of `WhStepPiKCanon`. -/
inductive WhRedPiKCanon (E : ResolvedEnv) : Expr Nat → Expr Nat → Prop
  | refl (a : Expr Nat) : WhRedPiKCanon E a a
  | step {a b c : Expr Nat} (hs : WhStepPiKCanon E a b) (hr : WhRedPiKCanon E b c) :
      WhRedPiKCanon E a c

theorem whRedPiKCanon_trans {E : ResolvedEnv} {a b c : Expr Nat}
    (h₁ : WhRedPiKCanon E a b) (h₂ : WhRedPiKCanon E b c) : WhRedPiKCanon E a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem whRedPiKCanon_of_whRed {E : ResolvedEnv} {a b : Expr Nat}
    (h : WhRed E a b) : WhRedPiKCanon E a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step (.of_whStep hs) ih

theorem whRedPiK_of_whRedPiKCanon {E : ResolvedEnv} {a b : Expr Nat}
    (h : WhRedPiKCanon E a b) : WhRedPiK E a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step (whStepPiK_of_whStepPiKCanon hs) ih

theorem whRedPiKCanon_appHead {E : ResolvedEnv} {f f' arg : Expr Nat}
    (h : WhRedPiKCanon E f f') : WhRedPiKCanon E (.app f arg) (.app f' arg) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.appHead hs) ih

/-- Every `WhStepPiKCanon` step is sound in `ApproxDIK E EnvI.bot` at `EnvWfT E`. -/
theorem semEqDIK_whStepPiKCanon {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hs : WhStepPiKCanon E a b) : SemEqDIK E EnvI.bot a b :=
  semEqDIK_whStepPiK hW (whStepPiK_of_whStepPiKCanon hs)

/-- Multi-step `WhRedPiKCanon` reduction is sound in `ApproxDIK E EnvI.bot` at `EnvWfT E`. -/
theorem semEqDIK_whRedPiKCanon {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hr : WhRedPiKCanon E a b) : SemEqDIK E EnvI.bot a b :=
  semEqDIK_whRedPiK hW (whRedPiK_of_whRedPiKCanon hr)

theorem approxDIK_whRedPiKCanon_back {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hr : WhRedPiKCanon E a b) {c : CptI} (hb : ApproxDIK E EnvI.bot b c) :
    ApproxDIK E EnvI.bot a c :=
  (semEqDIK_whRedPiKCanon hW hr c).mpr hb

theorem approxDIK_sort_of_whRedPiKCanon {E : ResolvedEnv} (hW : EnvWfT E) {a : Expr Nat} {l : Level}
    (hr : WhRedPiKCanon E a (.sort l)) : ApproxDIK E EnvI.bot a .sort :=
  approxDIK_whRedPiKCanon_back hW hr (.sort EnvI.bot l)

theorem whStepPiKCanon_sort_false {E : ResolvedEnv} {l : Level} {e : Expr Nat}
    (h : WhStepPiKCanon E (.sort l) e) : False :=
  whStepPiK_sort_false (whStepPiK_of_whStepPiKCanon h)

theorem whStepPiKCanon_pi_false {E : ResolvedEnv} {A B e : Expr Nat}
    (h : WhStepPiKCanon E (.pi A B) e) : False :=
  whStepPiK_pi_false (whStepPiK_of_whStepPiKCanon h)

theorem whRedPiKCanon_sort_eq {E : ResolvedEnv} {l : Level} {e : Expr Nat}
    (h : WhRedPiKCanon E (.sort l) e) : e = .sort l :=
  whRedPiK_sort_eq (whRedPiK_of_whRedPiKCanon h)

theorem whRedPiKCanon_pi_eq {E : ResolvedEnv} {A B e : Expr Nat}
    (h : WhRedPiKCanon E (.pi A B) e) : e = .pi A B :=
  whRedPiK_pi_eq (whRedPiK_of_whRedPiKCanon h)

theorem whStepPiK_lam_false {E : ResolvedEnv} {A b e : Expr Nat}
    (h : WhStepPiK E (.lam A b) e) : False := by
  generalize ha : (Expr.lam A b : Expr Nat) = a at h
  cases h with
  | of_whStep hs =>
      subst ha
      exact whStep_lam_false hs
  | iotaK w x _ _ _ =>
      have hs := congrArg appsSpine ha
      unfold recCall at hs
      rw [appsSpine_foldApps_const] at hs
      exact Expr.noConfusion (congrArg Prod.fst hs)
  | appHead _ =>
      exact Expr.noConfusion ha

theorem whStepPiKCanon_lam_false {E : ResolvedEnv} {A b e : Expr Nat}
    (h : WhStepPiKCanon E (.lam A b) e) : False :=
  whStepPiK_lam_false (whStepPiK_of_whStepPiKCanon h)

/-- No partial application `foldApps (.const w.recRef ls) xs` with `xs.length ≤ w.preMajor.length`
    takes a `WhStepPiK` step in any `EnvWfT E`. -/
theorem not_whStepPiK_recursor_prefix {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitnessS E) (ls : List Level) (xs : List (Expr Nat))
    (hlen : xs.length ≤ w.preMajor.length) {e : Expr Nat}
    (hs : WhStepPiK E (foldApps (.const w.recRef ls) xs) e) : False := by
  have key : ∀ {f e : Expr Nat} (ys : List (Expr Nat)),
      WhStepPiK E f e → f = foldApps (.const w.recRef ls) ys →
      ys.length ≤ w.preMajor.length → False := by
    intro f e ys hstep
    induction hstep generalizing ys with
    | of_whStep hs₀ =>
        intro hf hlen'
        subst hf
        exact not_whStep_recursor_prefix hW w ls ys hlen' hs₀
    | iotaK w' x _ _ _ =>
        intro hf hlen'
        have hsp := congrArg appsSpine hf
        unfold recCall at hsp
        rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hsp
        injection hsp with hhead hargs
        injection hhead with hrec _
        have hpreLen := (iotaWitnessS_preMajor_length_eq w w' hrec.symm).2
        have hlenEq := congrArg List.length hargs
        simp only [List.length_append, List.length_singleton] at hlenEq
        omega
    | @appHead f₀ f₀' a _ ih =>
        intro hf hlen'
        rcases list_eq_nil_or_snoc ys with rfl | ⟨pre, y, rfl⟩
        · exact Expr.noConfusion hf
        · rw [foldApps_snoc] at hf
          injection hf with hf₀ _
          simp only [List.length_append, List.length_singleton] at hlen'
          exact ih pre hf₀ (by omega)
  exact key xs hs rfl hlen

theorem not_whStepPiKCanon_recursor_prefix {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitnessS E) (ls : List Level) (xs : List (Expr Nat))
    (hlen : xs.length ≤ w.preMajor.length) {e : Expr Nat}
    (hs : WhStepPiKCanon E (foldApps (.const w.recRef ls) xs) e) : False :=
  not_whStepPiK_recursor_prefix hW w ls xs hlen (whStepPiK_of_whStepPiKCanon hs)

/-- In `ApproxDIK E EnvI.bot`, every constructor application `foldApps (.const cRef lsC) args`
    has the spine compact `.spine cRef (List.replicate args.length .bot)`. -/
theorem approxDIK_ctor_spine_bot {E : ResolvedEnv} (_ : EnvWfT E)
    {cRef : Nat} {cm : CheckedMember} (hctor : E.members cRef = some cm)
    (hctorK : cm.mclass = .constructorM) (lsC : List Level) (args : List (Expr Nat)) :
    ApproxDIK E EnvI.bot (foldApps (.const cRef lsC) args)
      (.spine cRef (List.replicate args.length .bot)) := by
  have hrig : RigidConst E cRef := rigidConst_of_ctor hctor hctorK
  exact (approxDIK_foldApps_rigid_iff lsC hrig args (.spine cRef (List.replicate args.length .bot))).mpr
    (Or.inr ⟨List.replicate args.length .bot, approxSpineArgsK_replicate_bot args, rfl⟩)

/-- Mutual exclusion of `WhStep` and `iotaK`: if `x` has no `.spine w.ctorRef _` compact in
    `ApproxDIK E EnvI.bot`, then `recCall (.const w.recRef w.ls) w.preMajor x` cannot step by
    `WhStep E`. -/
theorem not_whStep_and_iotaK {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitnessS E) (x : Expr Nat)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    (hx : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w.ctorRef args))
    {b : Expr Nat} (hs : WhStep E (recCall (.const w.recRef w.ls) w.preMajor x) b) : False := by
  have hrecEq : recCall (.const w.recRef w.ls) w.preMajor x =
      .app (foldApps (.const w.recRef w.ls) w.preMajor) x := by
    unfold recCall
    rw [foldApps_snoc]
  rw [hrecEq] at hs
  generalize ha : Expr.app (foldApps (.const w.recRef w.ls) w.preMajor) x = a₀ at hs
  cases hs with
  | beta A body arg =>
      injection ha with hf _
      exact F8EtaK.foldApps_const_ne_lam_any hf
  | zeta => exact Expr.noConfusion ha
  | delta => exact Expr.noConfusion ha
  | lit => exact Expr.noConfusion ha
  | iota hI =>
      obtain ⟨hT⟩ := derivedIotaT_of_derivedIotaU_envWfT hW hI
      cases hT with
      | of w' =>
          have hsp := congrArg appsSpine ha
          unfold iotaLhsOfS recCall at hsp
          rw [← foldApps_snoc] at hsp
          rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hsp
          injection hsp with hhead hargs
          injection hhead with hrec _
          obtain ⟨_, hctorEq, _, _, _, _⟩ :=
            iotaWitnessS_unique_of_nMinors_one w w' hrec hk.2
          obtain ⟨_, hpreLenEq⟩ := iotaWitnessS_preMajor_length_eq w w' hrec
          obtain ⟨_, hxEq⟩ := List.append_inj hargs hpreLenEq
          injection hxEq with hx'
          have hxCtor : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w'.ctorRef args) :=
            hctorEq ▸ hx
          subst hx'
          exact hxCtor _ (approxDIK_ctor_spine_bot hW w'.hctor w'.hctorK w'.lsC
            (w'.ctorParams ++ w'.fields))
  | appHead hf =>
      injection ha with hfEq _
      subst hfEq
      exact not_whStep_recursor_prefix hW w w.ls w.preMajor (Nat.le_refl _) hf

/-- Uniqueness of the `iotaKCanon` contractum from the redex expression alone. -/
theorem iotaKCanon_det {E : ResolvedEnv} (w₁ w₂ : IotaWitnessS E) (x₁ x₂ : Expr Nat)
    (hk₁ : piBody w₁.famMember.mtype = .sort .zero ∧ w₁.nMinors = 1)
    (hflds₁ : w₁.fields = List.replicate w₁.fields.length (.bvar 0))
    (hflds₂ : w₂.fields = List.replicate w₂.fields.length (.bvar 0))
    (heq : recCall (.const w₁.recRef w₁.ls) w₁.preMajor x₁ =
      recCall (.const w₂.recRef w₂.ls) w₂.preMajor x₂) :
    iotaRhsOfS w₁ = iotaRhsOfS w₂ := by
  have hsp := congrArg appsSpine heq
  unfold recCall at hsp
  rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hsp
  injection hsp with hhead hargs
  injection hhead with hrec hls
  obtain ⟨_, _, _, hfldsLenEq, _, hschemaEq⟩ :=
    iotaWitnessS_unique_of_nMinors_one w₁ w₂ hrec hk₁.2
  obtain ⟨hpreEq, _⟩ := List.append_inj hargs (by rw [(iotaWitnessS_preMajor_length_eq w₁ w₂ hrec).2])
  have hfldsEq : w₁.fields = w₂.fields := by
    rw [hflds₁, hflds₂, hfldsLenEq]
  unfold iotaRhsOfS
  rw [hpreEq, hfldsEq, hls, hschemaEq]

/-- Deterministic agreement when the left step is `WhStep E` and the right step is
    `WhStepPiKCanon E`. -/
theorem whStep_and_whStepPiKCanon_det {E : ResolvedEnv} (hW : EnvWfT E)
    {a b c : Expr Nat} (h₁ : WhStep E a b) (h₂ : WhStepPiKCanon E a c) :
    b = c := by
  induction h₂ generalizing b with
  | of_whStep hs₂ =>
      exact whDet_of_envWfT hW h₁ hs₂
  | iotaKCanon w₂ x₂ hk₂ _ hx₂ =>
      exact (not_whStep_and_iotaK hW w₂ x₂ hk₂ hx₂ h₁).elim
  | @appHead f f' arg hf₂ ih =>
      generalize ha : Expr.app f arg = a₀ at h₁
      cases h₁ with
      | beta A body arg' =>
          injection ha with hfEq _
          subst hfEq
          exact (whStepPiKCanon_lam_false hf₂).elim
      | zeta => exact Expr.noConfusion ha
      | delta => exact Expr.noConfusion ha
      | lit => exact Expr.noConfusion ha
      | iota hI =>
          obtain ⟨hT⟩ := derivedIotaT_of_derivedIotaU_envWfT hW hI
          cases hT with
          | of w₁ =>
              unfold iotaLhsOfS recCall at ha
              rw [foldApps_snoc] at ha
              injection ha with hfEq _
              subst hfEq
              exact (not_whStepPiKCanon_recursor_prefix hW w₁ w₁.ls w₁.preMajor (Nat.le_refl _) hf₂).elim
      | appHead hs₁ =>
          injection ha with hfEq hargEq
          subst hfEq; subst hargEq
          exact congrArg (fun t => Expr.app t arg) (ih hs₁)

/-- **Exact Single-Step Determinism of `WhStepPiKCanon` (`whDetPiKCanon_of_envWfT`):**
    At every `EnvWfT E`, `WhStepPiKCanon E` is 100% single-step deterministic! -/
theorem whDetPiKCanon_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {a b c : Expr Nat} (h₁ : WhStepPiKCanon E a b) (h₂ : WhStepPiKCanon E a c) :
    b = c := by
  induction h₁ generalizing c with
  | of_whStep hs₁ =>
      exact whStep_and_whStepPiKCanon_det hW hs₁ h₂
  | iotaKCanon w₁ x₁ hk₁ hflds₁ hx₁ =>
      generalize ha : recCall (.const w₁.recRef w₁.ls) w₁.preMajor x₁ = a₀ at h₂
      cases h₂ with
      | of_whStep hs₂ =>
          subst ha
          exact (not_whStep_and_iotaK hW w₁ x₁ hk₁ hx₁ hs₂).elim
      | iotaKCanon w₂ x₂ _ hflds₂ _ =>
          exact iotaKCanon_det w₁ w₂ x₁ x₂ hk₁ hflds₁ hflds₂ ha
      | appHead hf₂ =>
          unfold recCall at ha
          rw [foldApps_snoc] at ha
          injection ha with hfEq _
          subst hfEq
          exact (not_whStepPiKCanon_recursor_prefix hW w₁ w₁.ls w₁.preMajor (Nat.le_refl _) hf₂).elim
  | @appHead f f' arg hf₁ ih =>
      generalize ha : Expr.app f arg = a₀ at h₂
      cases h₂ with
      | of_whStep hs₂ =>
          subst ha
          exact (whStep_and_whStepPiKCanon_det hW hs₂ (.appHead hf₁)).symm
      | iotaKCanon w₂ x₂ _ _ _ =>
          unfold recCall at ha
          rw [foldApps_snoc] at ha
          injection ha with hfEq _
          subst hfEq
          exact (not_whStepPiKCanon_recursor_prefix hW w₂ w₂.ls w₂.preMajor (Nat.le_refl _) hf₁).elim
      | appHead hf₂ =>
          injection ha with hfEq hargEq
          subst hfEq; subst hargEq
          exact congrArg (fun t => Expr.app t arg) (ih hf₂)

/-- Normal forms of `WhStepPiKCanon E`. -/
def WhNormalPiKCanon (E : ResolvedEnv) (a : Expr Nat) : Prop :=
  ∀ b, ¬ WhStepPiKCanon E a b

theorem whNormalPiKCanon_sort (E : ResolvedEnv) (l : Level) :
    WhNormalPiKCanon E (.sort l) :=
  fun _ h => whStepPiKCanon_sort_false h

theorem whNormalPiKCanon_pi (E : ResolvedEnv) (A B : Expr Nat) :
    WhNormalPiKCanon E (.pi A B) :=
  fun _ h => whStepPiKCanon_pi_false h

theorem whNormalPiKCanon_lam (E : ResolvedEnv) (A b : Expr Nat) :
    WhNormalPiKCanon E (.lam A b) :=
  fun _ h => whStepPiKCanon_lam_false h

theorem whRedPiKCanon_of_normal {E : ResolvedEnv} {X Y : Expr Nat}
    (hX : WhNormalPiKCanon E X) (h : WhRedPiKCanon E X Y) : Y = X := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hX _ hs).elim

/-- **Unconditional Normal-Form Uniqueness for `WhRedPiKCanon` (`whRedPiKCanon_normal_unique_of_envWfT`):**
    At every `EnvWfT E`, any two `WhNormalPiKCanon E` reducts of the same expression `a` are equal. -/
theorem whRedPiKCanon_normal_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {a X Y : Expr Nat} (h₁ : WhRedPiKCanon E a X) (hX : WhNormalPiKCanon E X)
    (h₂ : WhRedPiKCanon E a Y) (hY : WhNormalPiKCanon E Y) : X = Y := by
  induction h₁ with
  | refl => exact (whRedPiKCanon_of_normal hX h₂).symm
  | step hs₁ _ ih =>
      cases h₂ with
      | refl => exact (hY _ hs₁).elim
      | step hs₂ hr₂ =>
          have e := whDetPiKCanon_of_envWfT hW hs₁ hs₂
          subst e
          exact ih hX hr₂

theorem whRedPiKCanon_pi_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {a A₁ B₁ A₂ B₂ : Expr Nat}
    (h₁ : WhRedPiKCanon E a (.pi A₁ B₁)) (h₂ : WhRedPiKCanon E a (.pi A₂ B₂)) :
    A₁ = A₂ ∧ B₁ = B₂ := by
  have e := whRedPiKCanon_normal_unique_of_envWfT hW h₁ (whNormalPiKCanon_pi E A₁ B₁)
    h₂ (whNormalPiKCanon_pi E A₂ B₂)
  injection e with eA eB
  exact ⟨eA, eB⟩

theorem whRedPiKCanon_sort_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {a : Expr Nat} {l₁ l₂ : Level}
    (h₁ : WhRedPiKCanon E a (.sort l₁)) (h₂ : WhRedPiKCanon E a (.sort l₂)) :
    l₁ = l₂ := by
  have e := whRedPiKCanon_normal_unique_of_envWfT hW h₁ (whNormalPiKCanon_sort E l₁)
    h₂ (whNormalPiKCanon_sort E l₂)
  injection e

/-- `WhStepPiKCanon.iotaKCanon` for legacy `w : IotaWitness E` at `EnvWfT E`. -/
theorem whStepPiKCanon_iotaKCanon_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) (x : Expr Nat)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    (hflds : w.fields = List.replicate w.fields.length (.bvar 0))
    (hx : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w.ctorRef args)) :
    WhStepPiKCanon E (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) := by
  obtain ⟨wS, hrec, hctor, hls, _, hpre, hfldsEq, _, _, hfamM, _, _, hnmin, _, _, hrhs⟩ :=
    iotaWitnessS_of_iotaWitness_envWfT hW w
  have hkS : piBody wS.famMember.mtype = .sort .zero ∧ wS.nMinors = 1 := by
    rw [hfamM, hnmin]; exact hk
  have hfldsS : wS.fields = List.replicate wS.fields.length (.bvar 0) := by
    rw [hfldsEq]; exact hflds
  have hxS : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine wS.ctorRef args) := by
    rw [hctor]; exact hx
  have hs := WhStepPiKCanon.iotaKCanon wS x hkS hfldsS hxS
  rwa [hrec, hls, hpre, hrhs] at hs

/-- In `WhRedPiKCanon`, `trueEnvU_kRecVar` reduces in 1 `iotaKCanon` step to `.sort .zero`. -/
theorem whRedPiKCanon_trueEnvU_kRecVar_sort :
    WhRedPiKCanon trueEnvU trueEnvU_kRecVar (.sort .zero) :=
  .step (whStepPiKCanon_iotaKCanon_of_envWfT trueEnvUWfT wTrueRecU (.bvar 0) ⟨rfl, rfl⟩ rfl
    (fun args hsp => by rcases approxDIK_bvar_inv hsp with h0 | h0 <;> cases h0)) (.refl _)

/-- Canonical-field witness `mixAndWCanon : IotaWitness andEnvU` with
    `fields = [.bvar 0, .bvar 0] = List.replicate 2 (.bvar 0)`. -/
def mixAndWCanon : IotaWitness andEnvU :=
  { mixAndW with
    fields := [.bvar 0, .bvar 0]
    hlen := rfl
    hnpar := rfl }

/-- `iotaRhsOf mixAndWCanon = .app (.app mixAndMin (.bvar 0)) (.bvar 0)` reduces in two
    `WhStep.beta` steps to `mixPi = .pi (.sort .zero) (.sort .zero)`. -/
theorem whRed_andEnvU_mixAndCanonRhs_mixPi :
    WhRed andEnvU (iotaRhsOf mixAndWCanon) mixPi :=
  .step (.appHead (.beta (.bvar 4) (.lam (.bvar 4) mixPi) (.bvar 0)))
    (.step (.beta (.bvar 3) mixPi (.bvar 0)) (.refl mixPi))

/-- **Fieldful `W-K` Reduction in Deterministic `WhRedPiKCanon` (`whRedPiKCanon_andEnvU_mixAndRedex_mixPi`):**
    Whereas `WhStepCK` (`w.fields = []`) is stuck on `mixAndRedex`, deterministic `WhRedPiKCanon`
    reduces `mixAndRedex` via `mixAndWCanon` (`fields = [.bvar 0, .bvar 0]`) and 2 β-steps to `mixPi`! -/
theorem whRedPiKCanon_andEnvU_mixAndRedex_mixPi :
    WhRedPiKCanon andEnvU mixAndRedex mixPi :=
  .step (whStepPiKCanon_iotaKCanon_of_envWfT andEnvUWfT mixAndWCanon (.bvar 0) ⟨rfl, rfl⟩ rfl
    (fun args hsp => by rcases approxDIK_bvar_inv hsp with h0 | h0 <;> cases h0))
    (whRedPiKCanon_of_whRed whRed_andEnvU_mixAndCanonRhs_mixPi)

/-! ### §11.4. `LRTypeINPiKCanon` & `LRTypeINBiDIKCanon`: Unconditional Symmetry, Transitivity Across All
Compacts (`lrTypeINPiKCanon_trans_of_envWfT`), and Chain Closure (`fundamentalLRINBotDIKCanon_letFree_of_links`) -/

/-- Compact-indexed type logical relation `LRTypeINPiKCanon` over deterministic `WhRedPiKCanon`
    and `WhNormalPiKCanon`. -/
inductive LRTypeINPiKCanon (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → CptI → Prop
  | bot (Γ : LCtx) (A B : Expr Nat) : LRTypeINPiKCanon E n Γ A B .bot
  | sort {Γ : LCtx} {A B : Expr Nat} {l₁ l₂ : Level}
      (hA : WhRedPiKCanon E A (.sort l₁)) (hB : WhRedPiKCanon E B (.sort l₂)) :
      LRTypeINPiKCanon E n Γ A B .sort
  | pi {Γ : LCtx} {A B A₁ B₁ A₂ B₂ : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (hA : WhRedPiKCanon E A (.pi A₁ B₁)) (hB : WhRedPiKCanon E B (.pi A₂ B₂))
      (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
      (hdom : TyConvT E n Γ A₁ A₂)
      (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
      (ra : LRTypeINPiKCanon E n Γ A₁ A₂ a)
      (rf : ∀ s ∈ f, LRTypeINPiKCanon E n (.assumption A₁ :: Γ) B₁ B₂ s.2) :
      LRTypeINPiKCanon E n Γ A B (.pi a f)
  | spine {Γ : LCtx} {A B X X' : Expr Nat} {r : Nat} {args : List CptI}
      (hA : WhRedPiKCanon E A X) (hB : WhRedPiKCanon E B X')
      (hX : WhNormalPiKCanon E X) (hX' : WhNormalPiKCanon E X')
      (hc : TyConvT E n Γ X X') :
      LRTypeINPiKCanon E n Γ A B (.spine r args)

/-- Soundness-free reverse adequacy of `LRTypeINPiKCanon` on `BotPiCpt`: implies both
    `ApproxDIK E EnvI.bot A c` and `ApproxDIK E EnvI.bot B c` at `EnvWfT E`. -/
theorem approxDIK_of_lrTypeINPiKCanon_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A B : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (h : LRTypeINPiKCanon E n Γ A B c) :
    ApproxDIK E EnvI.bot A c ∧ ApproxDIK E EnvI.bot B c := by
  induction h with
  | bot => exact ⟨.bot _ _, .bot _ _⟩
  | sort hA hB =>
      exact ⟨approxDIK_sort_of_whRedPiKCanon hW hA, approxDIK_sort_of_whRedPiKCanon hW hB⟩
  | @pi Γ A B A₁ B₁ A₂ B₂ a f hA hB _ _ _ _ _ iha ihf =>
      cases hc with
      | pi ha hbd hf =>
          obtain ⟨ha₁, ha₂⟩ := iha ha
          have hf₁ : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) EnvI.bot) B₁ s.2 :=
            fun s hs =>
              (approxDIK_cons_botDemand_bot_iff (hbd s hs) B₁ s.2).mpr (ihf s hs (hf s hs)).1
          have hf₂ : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) EnvI.bot) B₂ s.2 :=
            fun s hs =>
              (approxDIK_cons_botDemand_bot_iff (hbd s hs) B₂ s.2).mpr (ihf s hs (hf s hs)).2
          exact ⟨approxDIK_whRedPiKCanon_back hW hA (.pi ha₁ hf₁),
                 approxDIK_whRedPiKCanon_back hW hB (.pi ha₂ hf₂)⟩
  | spine => cases hc

theorem lrTypeINPiKCanon_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat}
    (hA : WhRedPiKCanon E A A') (hB : WhRedPiKCanon E B B') {c : CptI}
    (h : LRTypeINPiKCanon E n Γ A' B' c) : LRTypeINPiKCanon E n Γ A B c := by
  cases h with
  | bot => exact .bot _ _ _
  | sort hA' hB' => exact .sort (whRedPiKCanon_trans hA hA') (whRedPiKCanon_trans hB hB')
  | pi hA' hB' hΓ₁ hdom hcod ra rf =>
      exact .pi (whRedPiKCanon_trans hA hA') (whRedPiKCanon_trans hB hB') hΓ₁ hdom hcod ra rf
  | spine hA' hB' hX hX' hc =>
      exact .spine (whRedPiKCanon_trans hA hA') (whRedPiKCanon_trans hB hB') hX hX' hc

theorem lrTypeINPiKCanon_ctx {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ Γ' : LCtx}
    (hctx : CtxConvT E n Γ Γ') (hΓ' : CtxWfT E n Γ') {A A' : Expr Nat} {c : CptI}
    (h : LRTypeINPiKCanon E n Γ A A' c) : LRTypeINPiKCanon E n Γ' A A' c := by
  have hcl := envClosed_of_envWfT hW
  induction h generalizing Γ' with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort h h'
  | @pi Γ A A' A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      cases hΓ₁ with
      | assumption _ _ u _ hA₁ =>
          have hA₁' : HasTyT E n Γ' A₁ (.sort u) := hasTyT_ctx hcl hctx hA₁
          have hΓ₁' : CtxWfT E n (.assumption A₁ :: Γ') := .assumption Γ' A₁ u hΓ' hA₁'
          exact .pi h h' hΓ₁' (tyConvT_ctx hcl hctx hdom)
            (tyConvT_ctx hcl (.same (.assumption A₁) hctx) hcod)
            (iha hctx hΓ')
            (fun s hs => ihf s hs (.same (.assumption A₁) hctx) hΓ₁')
  | spine h h' hn hn' hc => exact .spine h h' hn hn' (tyConvT_ctx hcl hctx hc)

theorem lrTypeINPiKCanon_assump_dom {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) :
    {A₁ A₂ : Expr Nat} → TyConvT E n Γ A₁ A₂ → {u : Level} → HasTyT E n Γ A₁ (.sort u) →
    ∀ {B B' : Expr Nat} {c : CptI},
      LRTypeINPiKCanon E n (.assumption A₂ :: Γ) B B' c →
      LRTypeINPiKCanon E n (.assumption A₁ :: Γ) B B' c
  | _, _, .refl _ _, _, _, _, _, _, h => h
  | _, _, .of _ A₁ A₂ _ hc, _, hA₁, _, _, _, h =>
      let ends := convEnds hW hΓ hc
      lrTypeINPiKCanon_ctx hW
        (.assumption (ctxConvT_refl Γ) ends.2.1 ends.1 (.symm _ _ _ _ hc))
        (.assumption Γ A₁ _ hΓ hA₁) h
  | _, _, .trans _ A₁ _ A₂ c₁ c₂, _, hA₁, _, _, _, h =>
      let ⟨_, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA₁
      lrTypeINPiKCanon_assump_dom hW hΓ c₁ hA₁ (lrTypeINPiKCanon_assump_dom hW hΓ c₂ hM h)

/-- Full symmetry of `LRTypeINPiKCanon` across all compacts `c : CptI` at `EnvWfT E`. -/
theorem lrTypeINPiKCanon_symm {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ : LCtx}
    {A A' : Expr Nat} {c : CptI} (h : LRTypeINPiKCanon E n Γ A A' c) :
    LRTypeINPiKCanon E n Γ A' A c := by
  induction h with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort h' h
  | @pi Γ A A' A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      cases hΓ₁ with
      | assumption _ _ _ hΓ hA₁ =>
          obtain ⟨v, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          have hΓ₂ : CtxWfT E n (.assumption A₂ :: Γ) := .assumption Γ A₂ v hΓ hA₂
          exact .pi h' h hΓ₂ hdom.symmT (tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT) iha
            (fun s hs => lrTypeINPiKCanon_assump_dom hW hΓ hdom.symmT hA₂ (ihf s hs))
  | spine h h' hn hn' hc => exact .spine h' h hn' hn hc.symmT

/-- **Full Transitivity of `LRTypeINPiKCanon` Across All Compacts (`lrTypeINPiKCanon_trans_of_envWfT`):**
    At every `EnvWfT E`, `LRTypeINPiKCanon` is transitive across **all** compacts `c : CptI`
    (including `.pi a f` and `.spine r args`), proved directly from `whRedPiKCanon_normal_unique_of_envWfT`
    with **zero** external `WhDet`, `TypeSoundness`, or `Diamond` hypotheses! -/
theorem lrTypeINPiKCanon_trans_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ : LCtx}
    {A B : Expr Nat} {c : CptI} (h₁ : LRTypeINPiKCanon E n Γ A B c) :
    ∀ {C : Expr Nat}, LRTypeINPiKCanon E n Γ B C c → LRTypeINPiKCanon E n Γ A C c := by
  induction h₁ with
  | bot => intro C _; exact .bot _ _ _
  | sort h _ =>
      intro C h₂
      cases h₂ with
      | sort _ hC => exact .sort h hC
  | @pi Γ A B A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      intro C h₂
      cases h₂ with
      | pi hB hC _ hdom' hcod' ra' rf' =>
          obtain ⟨eA, eB⟩ := whRedPiKCanon_pi_unique_of_envWfT hW h' hB
          subst eA; subst eB
          cases hΓ₁ with
          | assumption _ _ u hΓ hA₁ =>
              exact .pi h hC (.assumption Γ A₁ u hΓ hA₁) (.trans _ _ _ _ hdom hdom')
                (.trans _ _ _ _ hcod (tyConvT_assump_dom hW hΓ hdom hcod'))
                (iha ra')
                (fun s hs => ihf s hs (lrTypeINPiKCanon_assump_dom hW hΓ hdom hA₁ (rf' s hs)))
  | spine h h' hn hn' hc =>
      intro C h₂
      cases h₂ with
      | spine hB hC hY hY' hc' =>
          have e := whRedPiKCanon_normal_unique_of_envWfT hW h' hn' hB hY
          subst e
          exact .spine h hC hn hY' (.trans _ _ _ _ hc hc')

/-- Bidirectional `BotPiCpt`-restricted type logical relation over `ApproxDIK E EnvI.bot` and
    `LRTypeINPiKCanon`. -/
def LRTypeINBiDIKCanon (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B : Expr Nat) : Prop :=
  ∀ c, BotPiCpt c →
    (ApproxDIK E EnvI.bot A c ∨ ApproxDIK E EnvI.bot B c) →
    LRTypeINPiKCanon E n Γ A B c

theorem lrTypeINBiDIKCanon_symm {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A B : Expr Nat} (h : LRTypeINBiDIKCanon E n Γ A B) :
    LRTypeINBiDIKCanon E n Γ B A :=
  fun c hc hBA => lrTypeINPiKCanon_symm hW (h c hc hBA.symm)

/-- **Unconditional Transitivity of `LRTypeINBiDIKCanon` (`lrTypeINBiDIKCanon_trans`):**
    At every `EnvWfT E`, `LRTypeINBiDIKCanon` is transitive with **zero** `WhDet`, `TypeSoundness`,
    or `Diamond` hypotheses (using `approxDIK_of_lrTypeINPiKCanon_botPiCpt` and
    `lrTypeINPiKCanon_trans_of_envWfT`). -/
theorem lrTypeINBiDIKCanon_trans {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A B C : Expr Nat}
    (h₁ : LRTypeINBiDIKCanon E n Γ A B) (h₂ : LRTypeINBiDIKCanon E n Γ B C) :
    LRTypeINBiDIKCanon E n Γ A C := by
  intro c hc hAC
  rcases hAC with hA | hC
  · have r₁ := h₁ c hc (Or.inl hA)
    have hB := (approxDIK_of_lrTypeINPiKCanon_botPiCpt hW hc r₁).2
    exact lrTypeINPiKCanon_trans_of_envWfT hW r₁ (h₂ c hc (Or.inl hB))
  · have r₂ := h₂ c hc (Or.inr hC)
    have hB := (approxDIK_of_lrTypeINPiKCanon_botPiCpt hW hc r₂).1
    exact lrTypeINPiKCanon_trans_of_envWfT hW (h₁ c hc (Or.inr hB)) r₂

theorem lrTypeINBiDIKCanon_sorts (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l₁ l₂ : Level) :
    LRTypeINBiDIKCanon E n Γ (.sort l₁) (.sort l₂) := by
  intro c _ h
  rcases h with h | h
  · rcases approxDIK_sort_inv h with rfl | rfl
    · exact .bot _ _ _
    · exact .sort (.refl _) (.refl _)
  · rcases approxDIK_sort_inv h with rfl | rfl
    · exact .bot _ _ _
    · exact .sort (.refl _) (.refl _)

theorem lrTypeINBiDIKCanon_sort_diag (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level) :
    LRTypeINBiDIKCanon E n Γ (.sort l) (.sort l) :=
  lrTypeINBiDIKCanon_sorts E n Γ l l

theorem lrTypeINBiDIKCanon_bvar_diag (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (i : Nat) :
    LRTypeINBiDIKCanon E n Γ (.bvar i) (.bvar i) := by
  intro c _ h
  rcases approxDIK_bvar_inv (h.elim id id) with rfl | h0
  · exact .bot _ _ _
  · cases h0; exact .bot _ _ _

theorem lrTypeINBiDIKCanon_pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₁ B₁ A₂ B₂ : Expr Nat}
    (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
    (hdom : TyConvT E n Γ A₁ A₂)
    (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
    (ihA : LRTypeINBiDIKCanon E n Γ A₁ A₂)
    (ihB : LRTypeINBiDIKCanon E n (.assumption A₁ :: Γ) B₁ B₂) :
    LRTypeINBiDIKCanon E n Γ (.pi A₁ B₁) (.pi A₂ B₂) := by
  intro c hc h
  rcases h with h₁ | h₂
  · rcases approxDIK_pi_inv h₁ with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact .bot _ _ _
    · cases hc with
      | pi hca hbd hcf =>
          refine .pi (.refl _) (.refl _) hΓ₁ hdom hcod (ihA a hca (Or.inl ha)) (fun s hs => ?_)
          have hb := (approxDIK_cons_botDemand_bot_iff (hbd s hs) B₁ s.2).mp (hf s hs)
          exact ihB s.2 (hcf s hs) (Or.inl hb)
  · rcases approxDIK_pi_inv h₂ with rfl | ⟨a, f, rfl, ha, hf⟩
    · exact .bot _ _ _
    · cases hc with
      | pi hca hbd hcf =>
          refine .pi (.refl _) (.refl _) hΓ₁ hdom hcod (ihA a hca (Or.inr ha)) (fun s hs => ?_)
          have hb := (approxDIK_cons_botDemand_bot_iff (hbd s hs) B₂ s.2).mp (hf s hs)
          exact ihB s.2 (hcf s hs) (Or.inr hb)

theorem lrTypeINBiDIKCanon_pi_diag {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    (hΓ₁ : CtxWfT E n (.assumption A :: Γ))
    (ihA : LRTypeINBiDIKCanon E n Γ A A)
    (ihB : LRTypeINBiDIKCanon E n (.assumption A :: Γ) B B) :
    LRTypeINBiDIKCanon E n Γ (.pi A B) (.pi A B) :=
  lrTypeINBiDIKCanon_pi hΓ₁ (.refl Γ A) (.refl (.assumption A :: Γ) B) ihA ihB

theorem lrTypeINBiDIKCanon_of_whRedPiKCanon {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {M M' : Expr Nat} (hr : WhRedPiKCanon E M M')
    (hdiag : LRTypeINBiDIKCanon E n Γ M' M') :
    LRTypeINBiDIKCanon E n Γ M M' := by
  intro c hc h
  have hM' : ApproxDIK E EnvI.bot M' c :=
    h.elim (fun hM => (semEqDIK_whRedPiKCanon hW hr c).mp hM) id
  exact lrTypeINPiKCanon_expand hr (.refl _) (hdiag c hc (Or.inl hM'))

theorem lrTypeINBiDIKCanon_of_whStepPiKCanon {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {M M' : Expr Nat} (hs : WhStepPiKCanon E M M')
    (hdiag : LRTypeINBiDIKCanon E n Γ M' M') :
    LRTypeINBiDIKCanon E n Γ M M' :=
  lrTypeINBiDIKCanon_of_whRedPiKCanon hW (.step hs (.refl _)) hdiag

theorem lrTypeINBiDIKCanon_beta {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (A b a : Expr Nat)
    (hdiag : LRTypeINBiDIKCanon E n Γ (instantiate 0 a b) (instantiate 0 a b)) :
    LRTypeINBiDIKCanon E n Γ (.app (.lam A b) a) (instantiate 0 a b) :=
  lrTypeINBiDIKCanon_of_whStepPiKCanon hW (.of_whStep (.beta A b a)) hdiag

theorem lrTypeINBiDIKCanon_zeta {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (A v b : Expr Nat)
    (hdiag : LRTypeINBiDIKCanon E n Γ (instantiate 0 v b) (instantiate 0 v b)) :
    LRTypeINBiDIKCanon E n Γ (.letE A v b) (instantiate 0 v b) :=
  lrTypeINBiDIKCanon_of_whStepPiKCanon hW (.of_whStep (.zeta A v b)) hdiag

theorem lrTypeINBiDIKCanon_delta {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hdiag : LRTypeINBiDIKCanon E n Γ (instantiateLevels ls b) (instantiateLevels ls b)) :
    LRTypeINBiDIKCanon E n Γ (.const r ls) (instantiateLevels ls b) :=
  lrTypeINBiDIKCanon_of_whStepPiKCanon hW (.of_whStep (.delta hres hbody)) hdiag

theorem lrTypeINBiDIKCanon_iota {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {lhs rhs : Expr Nat} (hI : DerivedIotaU E lhs rhs)
    (hdiag : LRTypeINBiDIKCanon E n Γ rhs rhs) :
    LRTypeINBiDIKCanon E n Γ lhs rhs :=
  lrTypeINBiDIKCanon_of_whStepPiKCanon hW (.of_whStep (.iota hI)) hdiag

theorem lrTypeINBiDIKCanon_lit {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (t : Nat)
    (hdiag : LRTypeINBiDIKCanon E n Γ (natExpand t) (natExpand t)) :
    LRTypeINBiDIKCanon E n Γ (.lit t) (natExpand t) :=
  lrTypeINBiDIKCanon_of_whStepPiKCanon hW (.of_whStep (.lit t)) hdiag

theorem lrTypeINBiDIKCanon_iotaKCanon {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (w : IotaWitnessS E) (x : Expr Nat)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    (hflds : w.fields = List.replicate w.fields.length (.bvar 0))
    (hx : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w.ctorRef args))
    (hdiag : LRTypeINBiDIKCanon E n Γ (iotaRhsOfS w) (iotaRhsOfS w)) :
    LRTypeINBiDIKCanon E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w) :=
  lrTypeINBiDIKCanon_of_whStepPiKCanon hW (.iotaKCanon w x hk hflds hx) hdiag

theorem lrTypeINBiDIKCanon_zetaLocal_letFree {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (hlf : LetFreeCtx Γ) {i : Nat} {v : Expr Nat}
    (hv : lookupValue Γ i = some v) :
    LRTypeINBiDIKCanon E n Γ (.bvar i) v := by
  rw [hlf i] at hv
  exact Option.noConfusion hv

/-- Positive satisfaction on `idPiProp` (`W-DEMAND`) in `LRTypeINBiDIKCanon`. -/
theorem lrTypeINBiDIKCanon_idPiProp (E : ResolvedEnv) (n : Nat) :
    LRTypeINBiDIKCanon E n [] idPiProp idPiProp :=
  lrTypeINBiDIKCanon_pi_diag
    (.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero))
    (lrTypeINBiDIKCanon_sort_diag E n [] .zero)
    (lrTypeINBiDIKCanon_bvar_diag E n [.assumption (.sort .zero)] 0)

/-- Positive satisfaction on `closedIrrPi` (`W-IrrPi`) in `LRTypeINBiDIKCanon`. -/
theorem lrTypeINBiDIKCanon_closedIrrPi (E : ResolvedEnv) (n : Nat) :
    LRTypeINBiDIKCanon E n [] closedIrrPiL closedIrrPiR := by
  let Γ₁ : LCtx := [.assumption (.sort .zero)]
  let Γ₂ : LCtx := .assumption (.pi (.bvar 0) (.sort .zero)) :: Γ₁
  let Γ₃ : LCtx := .assumption (.bvar 1) :: Γ₂
  let Γ₄ : LCtx := .assumption (.bvar 2) :: Γ₃
  have hΓ₁ : CtxWfT E n Γ₁ := .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)
  have hA₁ : HasTyT E n Γ₁ (.pi (.bvar 0) (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ₁ (.bvar 0) .zero (.sort .zero) (.succ .zero)
      (.bvar Γ₁ 0 (.sort .zero) rfl) (.sort _ .zero)
  have hΓ₂ : CtxWfT E n Γ₂ := .assumption Γ₁ _ _ hΓ₁ hA₁
  have hΓ₃ : CtxWfT E n Γ₃ := .assumption Γ₂ (.bvar 1) .zero hΓ₂ (.bvar Γ₂ 1 (.sort .zero) rfl)
  have hΓ₄ : CtxWfT E n Γ₄ := .assumption Γ₃ (.bvar 2) .zero hΓ₃ (.bvar Γ₃ 2 (.sort .zero) rfl)
  have hP : HasTyT E n Γ₄ (.bvar 3) (.sort .zero) := .bvar Γ₄ 3 (.sort .zero) rfl
  have hF : HasTyT E n Γ₄ (.bvar 2) (.pi (.bvar 3) (.sort .zero)) :=
    .bvar Γ₄ 2 (.pi (.bvar 3) (.sort .zero)) rfl
  have hp : HasTyT E n Γ₄ (.bvar 1) (.bvar 3) := .bvar Γ₄ 1 (.bvar 3) rfl
  have hq : HasTyT E n Γ₄ (.bvar 0) (.bvar 3) := .bvar Γ₄ 0 (.bvar 3) rfl
  have hbodyConv : ConvT E n Γ₄ (.app (.bvar 2) (.bvar 1)) (.app (.bvar 2) (.bvar 0)) (.sort .zero) :=
    .app Γ₄ (.bvar 2) (.bvar 2) (.bvar 1) (.bvar 0) (.bvar 3) (.sort .zero)
      (.refl Γ₄ (.bvar 2) _ hF) (.irr Γ₄ (.bvar 3) (.bvar 1) (.bvar 0) hP hp hq)
  have hcod₃ : ConvT E n Γ₃ (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1)))
      (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0))) (.sort (.imax .zero .zero)) :=
    .pi Γ₃ _ _ _ _ .zero .zero (.refl Γ₃ _ _ (.bvar Γ₃ 2 (.sort .zero) rfl)) hbodyConv
  have hcod₂ : ConvT E n Γ₂ (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1))))
      (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0))))
      (.sort (.imax .zero (.imax .zero .zero))) :=
    .pi Γ₂ _ _ _ _ .zero _ (.refl Γ₂ _ _ (.bvar Γ₂ 1 (.sort .zero) rfl)) hcod₃
  have hcod₁ : ConvT E n Γ₁
      (.pi (.pi (.bvar 0) (.sort .zero)) (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1)))))
      (.pi (.pi (.bvar 0) (.sort .zero)) (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0)))))
      (.sort (.imax (.imax .zero (.succ .zero)) (.imax .zero (.imax .zero .zero)))) :=
    .pi Γ₁ _ _ _ _ _ _ (.refl Γ₁ _ _ hA₁) hcod₂
  have hinner : LRTypeINBiDIKCanon E n Γ₄ (.app (.bvar 2) (.bvar 1)) (.app (.bvar 2) (.bvar 0)) := by
    intro c _ h
    rcases h with h | h
    · rcases approxDIK_app_inv h with rfl | ⟨_, _, _, hf, _, _⟩ | ⟨_, _, _, _, hf, _⟩
      · exact .bot _ _ _
      · rcases approxDIK_bvar_inv hf with h0 | h0 <;> cases h0
      · rcases approxDIK_bvar_inv hf with h0 | h0 <;> cases h0
    · rcases approxDIK_app_inv h with rfl | ⟨_, _, _, hf, _, _⟩ | ⟨_, _, _, _, hf, _⟩
      · exact .bot _ _ _
      · rcases approxDIK_bvar_inv hf with h0 | h0 <;> cases h0
      · rcases approxDIK_bvar_inv hf with h0 | h0 <;> cases h0
  exact lrTypeINBiDIKCanon_pi hΓ₁ (.refl [] _) (.of Γ₁ _ _ _ hcod₁)
    (lrTypeINBiDIKCanon_sort_diag E n [] .zero)
    (lrTypeINBiDIKCanon_pi hΓ₂ (.refl Γ₁ _) (.of Γ₂ _ _ _ hcod₂)
      (lrTypeINBiDIKCanon_pi_diag
        (.assumption Γ₁ (.bvar 0) .zero hΓ₁ (.bvar Γ₁ 0 (.sort .zero) rfl))
        (lrTypeINBiDIKCanon_bvar_diag E n Γ₁ 0)
        (lrTypeINBiDIKCanon_sort_diag E n (.assumption (.bvar 0) :: Γ₁) .zero))
      (lrTypeINBiDIKCanon_pi hΓ₃ (.refl Γ₂ _) (.of Γ₃ _ _ _ hcod₃)
        (lrTypeINBiDIKCanon_bvar_diag E n Γ₂ 1)
        (lrTypeINBiDIKCanon_pi hΓ₄ (.refl Γ₃ _) (.of Γ₄ _ _ _ hbodyConv)
          (lrTypeINBiDIKCanon_bvar_diag E n Γ₃ 2) hinner)))

/-- Positive satisfaction on 0-field `trueEnvU_kRecVar` (`W-K`) in `LRTypeINBiDIKCanon`. -/
theorem lrTypeINBiDIKCanon_trueEnvU_kRecVar_sort :
    LRTypeINBiDIKCanon trueEnvU 0 trueEnvU_kVarCtx trueEnvU_kRecVar (.sort .zero) :=
  lrTypeINBiDIKCanon_of_whRedPiKCanon trueEnvUWfT whRedPiKCanon_trueEnvU_kRecVar_sort
    (lrTypeINBiDIKCanon_sort_diag trueEnvU 0 trueEnvU_kVarCtx .zero)

/-- Positive satisfaction on fieldful `mixAndRedex` (`W-K` at `andEnvU`) in `LRTypeINBiDIKCanon`. -/
theorem lrTypeINBiDIKCanon_andEnvU_mixAndRedex_mixPi :
    LRTypeINBiDIKCanon andEnvU 0 mixAndCtx mixAndRedex mixPi := by
  have hΓ₁ : CtxWfT andEnvU 0 (.assumption (.sort .zero) :: mixAndCtx) :=
    .assumption mixAndCtx (.sort .zero) (.succ .zero)
      Rcic.Domain.Model.PiInversion.mixAndCtx_wf (.sort mixAndCtx .zero)
  exact lrTypeINBiDIKCanon_of_whRedPiKCanon andEnvUWfT whRedPiKCanon_andEnvU_mixAndRedex_mixPi
    (lrTypeINBiDIKCanon_pi hΓ₁ (.refl _ _) (.refl _ _)
      (lrTypeINBiDIKCanon_sort_diag andEnvU 0 mixAndCtx .zero)
      (lrTypeINBiDIKCanon_sort_diag andEnvU 0 (.assumption (.sort .zero) :: mixAndCtx) .zero))

/-- Named `LetFreeCtx`-restricted fundamental supply for `LRTypeINPiKCanon` over `ApproxDIK E EnvI.bot`. -/
def FundamentalLRINBotDIKCanon_letFree (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {A B : Expr Nat}, TyConvT E n Γ A B →
      ∀ c, BotPiCpt c → ApproxDIK E EnvI.bot A c → LRTypeINPiKCanon E n Γ A B c

/-- **Chain Closure for `FundamentalLRINBotDIKCanon_letFree` (`fundamentalLRINBotDIKCanon_letFree_of_links`):**
    Closes `TyConvT.refl` and `TyConvT.trans` from diagonal and single-link `LRTypeINBiDIKCanon`
    supplies at `EnvWfT E`, with **zero** external `WhDet`, `TypeSoundness`, or `Diamond` hypotheses! -/
theorem fundamentalLRINBotDIKCanon_letFree_of_links {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ → ∀ A : Expr Nat, LRTypeINBiDIKCanon E n Γ A A)
    (hlink : ∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
      ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) → LRTypeINBiDIKCanon E n Γ A B) :
    FundamentalLRINBotDIKCanon_letFree E n := by
  have hbi : ∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
      ∀ {A B : Expr Nat}, TyConvT E n Γ A B → LRTypeINBiDIKCanon E n Γ A B := by
    intro Γ hΓ hlf A B hc
    induction hc with
    | refl A => exact hdiag hΓ hlf A
    | of A B _ h => exact hlink hΓ hlf h
    | trans A B C _ _ ih₁ ih₂ => exact lrTypeINBiDIKCanon_trans hW ih₁ ih₂
  intro Γ hΓ hlf A B hc c hbc hA
  exact hbi hΓ hlf hc c hbc (Or.inl hA)

theorem piRow_letFree_of_fundamentalLRINBotDIKCanon_letFree {E : ResolvedEnv} {n : Nat}
    (hF : FundamentalLRINBotDIKCanon_letFree E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hlf : LetFreeCtx Γ)
    {A₁ B₁ A₂ B₂ : Expr Nat}
    (h : TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  have hlr : LRTypeINPiKCanon E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.pi .bot []) :=
    hF hΓ hlf h (.pi .bot []) botPiCpt_pi_bot_nil (approxDIK_pi_bot_nil E EnvI.bot A₁ B₁)
  cases hlr with
  | pi hA hB _ hdom hcod _ _ =>
      have e₁ := whRedPiKCanon_pi_eq hA
      have e₂ := whRedPiKCanon_pi_eq hB
      injection e₁ with eA₁ eB₁
      injection e₂ with eA₂ eB₂
      subst eA₁; subst eB₁; subst eA₂; subst eB₂
      exact ⟨⟨hdom⟩, ⟨hcod⟩⟩

/-- **Full `PiRowField E n` from `FundamentalLRINBotDIKCanon_letFree`:** lifts let-free `piRow`
    across all `CtxWfT E n Γ` (including contexts with `letBinding`s) via `piRow_of_letFree_piRow`. -/
theorem piRow_of_fundamentalLRINBotDIKCanon_letFree {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hF : FundamentalLRINBotDIKCanon_letFree E n) : PiRowField E n :=
  fun {_} hΓ {_ _ _ _} h =>
    piRow_of_letFree_piRow hW
      (fun {_} hlf' hΓ' {_ _ _ _} h' =>
        piRow_letFree_of_fundamentalLRINBotDIKCanon_letFree hF hΓ' hlf' h')
      hΓ h

/-! ## §12. K-Aware `ConvT`-Guarded Substitution-Style Term Logical Relation `LRTermDSubKCore` /
`LRTermDSubK` Over `WhRedPiKCanon` and `ApproxDIK` -/

/-! ### §12.1. Definition, Unfolding, and Weak-Head Expansion of `LRTermDSubKCore` and `LRTermDSubK` -/

/-- **K-Aware `ConvT`-Guarded Substitution-Style Term Logical Relation (`LRTermDSubKCore`):**
    Combines the `ConvT E n Γ N N' A₁`-guarded substitution-style codomain instantiation of
    `LRTermDSubCore` (§7–§8) with the canonical deterministic K-aware readback `WhRedPiKCanon`
    and `LRTypeINPiKCanon` (§11.3–§11.4). -/
def LRTermDSubKCore (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : CptI → Prop
  | .bot => True
  | .sort => (∃ l, WhRedPiKCanon E A (.sort l)) ∧ LRTypeINPiKCanon E n Γ M M' .sort
  | .pi a f =>
      (∃ l, WhRedPiKCanon E A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ u₁ w₁,
        WhRedPiKCanon E M (.pi A₁ B₁) ∧
        WhRedPiKCanon E M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧
        Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        Nonempty (HasTyT E n Γ A₁ (.sort u₁)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁)) ∧
        LRTermDSubKCore E n Γ A₁ A₂ (.sort u₁) a ∧
        ∀ s ∈ f, ∀ N N' : Expr Nat,
          HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ → ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKCore E n Γ N N' A₁ u) →
          LRTermDSubKCore E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁) s.2
  | .spine r args =>
      ((∃ l, WhRedPiKCanon E A (.sort l)) ∧ LRTypeINPiKCanon E n Γ M M' (.spine r args)) ∨
      (∃ ls₁ ls₂ args₁ args₂,
        WhRedPiKCanon E M (foldApps (.const r ls₁) args₁) ∧
        WhRedPiKCanon E M' (foldApps (.const r ls₂) args₂) ∧
        WhNormalPiKCanon E (foldApps (.const r ls₁) args₁) ∧
        WhNormalPiKCanon E (foldApps (.const r ls₂) args₂) ∧
        Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
          (foldApps (.const r ls₂) args₂) A) ∧
        args.length ≤ args₁.length ∧ args.length ≤ args₂.length)
  | .lam g =>
      ∃ A₁ B₁ w, WhRedPiKCanon E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat,
          HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ → ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKCore E n Γ N N' A₁ u) →
          (IsPropTyI E n Γ (instantiate0 N B₁) ∨
            LRTermDSubKCore E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  · omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have h₃ := sizeOfD_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
    have h₃ := sizeOfD_snd_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have h₃ := sizeOfD_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOfD_snd_lt s
    omega

/-- Proposition-collapsed wrapper `LRTermDSubK` over `LRTermDSubKCore`. -/
def LRTermDSubK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (u : CptI) : Prop :=
  IsPropTyI E n Γ A ∨ LRTermDSubKCore E n Γ M M' A u

theorem lrTermDSubKCore_bot_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermDSubKCore E n Γ M M' A .bot ↔ True := by
  rw [LRTermDSubKCore.eq_def]

theorem lrTermDSubKCore_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermDSubKCore E n Γ M M' A .sort ↔
      (∃ l, WhRedPiKCanon E A (.sort l)) ∧ LRTypeINPiKCanon E n Γ M M' .sort := by
  rw [LRTermDSubKCore.eq_def]

theorem lrTermDSubKCore_pi_iff (Γ : LCtx) (M M' A : Expr Nat) (a : CptI)
    (f : List (List CptI × CptI)) :
    LRTermDSubKCore E n Γ M M' A (.pi a f) ↔
      (∃ l, WhRedPiKCanon E A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ u₁ w₁,
        WhRedPiKCanon E M (.pi A₁ B₁) ∧
        WhRedPiKCanon E M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧
        Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        Nonempty (HasTyT E n Γ A₁ (.sort u₁)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁)) ∧
        LRTermDSubKCore E n Γ A₁ A₂ (.sort u₁) a ∧
        ∀ s ∈ f, ∀ N N' : Expr Nat,
          HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ → ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKCore E n Γ N N' A₁ u) →
          LRTermDSubKCore E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁) s.2 := by
  rw [LRTermDSubKCore.eq_def]

theorem lrTermDSubKCore_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptI) :
    LRTermDSubKCore E n Γ M M' A (.spine r args) ↔
      ((∃ l, WhRedPiKCanon E A (.sort l)) ∧ LRTypeINPiKCanon E n Γ M M' (.spine r args)) ∨
      (∃ ls₁ ls₂ args₁ args₂,
        WhRedPiKCanon E M (foldApps (.const r ls₁) args₁) ∧
        WhRedPiKCanon E M' (foldApps (.const r ls₂) args₂) ∧
        WhNormalPiKCanon E (foldApps (.const r ls₁) args₁) ∧
        WhNormalPiKCanon E (foldApps (.const r ls₂) args₂) ∧
        Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
          (foldApps (.const r ls₂) args₂) A) ∧
        args.length ≤ args₁.length ∧ args.length ≤ args₂.length) := by
  rw [LRTermDSubKCore.eq_def]

theorem lrTermDSubKCore_lam_iff (Γ : LCtx) (M M' A : Expr Nat)
    (g : List (List CptI × CptI)) :
    LRTermDSubKCore E n Γ M M' A (.lam g) ↔
      ∃ A₁ B₁ w, WhRedPiKCanon E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat,
          HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ → ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKCore E n Γ N N' A₁ u) →
          (IsPropTyI E n Γ (instantiate0 N B₁) ∨
            LRTermDSubKCore E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2) := by
  rw [LRTermDSubKCore.eq_def]

/-- Weak-head expansion under `WhRedPiKCanon` on both sides for `LRTermDSubKCore`. -/
theorem lrTermDSubKCore_whRedPiKCanon_expand {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRedPiKCanon E M X) (hX' : WhRedPiKCanon E M' X') :
    (u : CptI) → LRTermDSubKCore E n Γ X X' A u → LRTermDSubKCore E n Γ M M' A u
  | .bot, _ => by rw [lrTermDSubKCore_bot_iff]; trivial
  | .sort, h => by
      rw [lrTermDSubKCore_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeINPiKCanon_expand hX hX' h.2⟩
  | .pi a f, h => by
      rw [lrTermDSubKCore_pi_iff] at h ⊢
      rcases h with ⟨hl, A₁, B₁, A₂, B₂, u₁, w₁, h1, h2, hΓ₁, hcA, hcB, hA₁, hB₁, ha, hf⟩
      exact ⟨hl, A₁, B₁, A₂, B₂, u₁, w₁,
        whRedPiKCanon_trans hX h1, whRedPiKCanon_trans hX' h2, hΓ₁, hcA, hcB, hA₁, hB₁, ha, hf⟩
  | .spine r args, h => by
      rw [lrTermDSubKCore_spine_iff] at h ⊢
      rcases h with ⟨hl, hLR⟩ | ⟨ls₁, ls₂, args₁, args₂, h1, h2, hn1, hn2, hc, hl1, hl2⟩
      · exact Or.inl ⟨hl, lrTypeINPiKCanon_expand hX hX' hLR⟩
      · exact Or.inr ⟨ls₁, ls₂, args₁, args₂,
          whRedPiKCanon_trans hX h1, whRedPiKCanon_trans hX' h2, hn1, hn2, hc, hl1, hl2⟩
  | .lam g, h => by
      rw [lrTermDSubKCore_lam_iff] at h ⊢
      rcases h with ⟨A₁, B₁, w, hA, hΓ₁, hB₁, hf⟩
      refine ⟨A₁, B₁, w, hA, hΓ₁, hB₁, fun s hs N N' hN hN' hconv hrel => ?_⟩
      rcases hf s hs N N' hN hN' hconv hrel with hP | hcore
      · exact Or.inl hP
      · exact Or.inr (lrTermDSubKCore_whRedPiKCanon_expand
          (whRedPiKCanon_appHead hX) (whRedPiKCanon_appHead hX') s.2 hcore)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOfD_snd_lt s
  omega

/-- Weak-head expansion under `WhRedPiKCanon` on both sides for `LRTermDSubK`. -/
theorem lrTermDSubK_whRedPiKCanon_expand {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRedPiKCanon E M X) (hX' : WhRedPiKCanon E M' X') (u : CptI)
    (h : LRTermDSubK E n Γ X X' A u) : LRTermDSubK E n Γ M M' A u := by
  rcases h with hP | hcore
  · exact Or.inl hP
  · exact Or.inr (lrTermDSubKCore_whRedPiKCanon_expand hX hX' u hcore)

/-! ### §12.2. Simultaneous Positive Satisfaction of `LRTermDSubKCore` and `LRTermDSubK` Across
All Four Concrete Obstructions (`idPiProp`, `closedIrrPi`, `trueEnvU_kRecVar`, `mixAndRedex`) -/

/-- **1. `W-DEMAND` Resolved Across All Compacts (`lrTermDSubKCore_idPiProp_all`):**
    For **every** `E, n, Γ` (`CtxWfT E n Γ`) and **every** compact `c : CptI` approximating
    `idPiProp = .pi (.sort .zero) (.bvar 0)` in `ApproxDIK E EnvI.bot` (including
    `idPiPropSortStep = .pi .bot [([.sort], .sort)]`), `LRTermDSubKCore` holds unconditionally! -/
theorem lrTermDSubKCore_idPiProp_all {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level)
    {c : CptI} (h : ApproxDIK E EnvI.bot idPiProp c) :
    LRTermDSubKCore E n Γ idPiProp idPiProp (.sort w) c := by
  rcases approxDIK_pi_inv h with rfl | ⟨a, f, rfl, ha, hf⟩
  · rw [lrTermDSubKCore_bot_iff]; trivial
  · rw [lrTermDSubKCore_pi_iff]
    refine ⟨⟨w, .refl _⟩, .sort .zero, .bvar 0, .sort .zero, .bvar 0, .succ .zero, .zero,
      .refl _, .refl _,
      ⟨.assumption Γ (.sort .zero) (.succ .zero) hΓ (.sort Γ .zero)⟩,
      ⟨.refl _ _⟩, ⟨.refl _ _⟩,
      ⟨.sort Γ .zero⟩,
      ⟨.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl⟩, ?_, ?_⟩
    · rcases approxDIK_sort_inv ha with rfl | rfl
      · rw [lrTermDSubKCore_bot_iff]; trivial
      · rw [lrTermDSubKCore_sort_iff]
        exact ⟨⟨.succ .zero, .refl _⟩, .sort (.refl _) (.refl _)⟩
    · intro s hs N N' _ _ _ hrel
      rcases approxDIK_bvar_inv (hf s hs) with hbot | hmem
      · rw [hbot, lrTermDSubKCore_bot_iff]; trivial
      · rcases hrel s.2 hmem with hP | hsub
        · exact (not_isPropTyI_sort E n Γ .zero hP).elim
        · exact hsub

theorem lrTermDSubKCore_idPiProp_sortStep {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level) :
    LRTermDSubKCore E n Γ idPiProp idPiProp (.sort w) idPiPropSortStep :=
  lrTermDSubKCore_idPiProp_all hΓ w (approxDIK_of_approxDI (approxDI_idPiProp_sortStep E))

theorem lrTermDSubK_idPiProp_all {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level)
    {c : CptI} (h : ApproxDIK E EnvI.bot idPiProp c) :
    LRTermDSubK E n Γ idPiProp idPiProp (.sort w) c :=
  Or.inr (lrTermDSubKCore_idPiProp_all hΓ w h)

theorem lrTermDSubKCore_polyPiType_of_envWfT (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (w : Level) :
    LRTermDSubKCore E n Γ polyPiType polyPiType (.sort w) polyPiTypeCpt := by
  have hcl := envClosed_of_envWfT hW
  unfold polyPiTypeCpt
  rw [lrTermDSubKCore_pi_iff]
  refine ⟨⟨w, .refl _⟩, .sort (.succ .zero), .pi (.bvar 0) (.bvar 1),
    .sort (.succ .zero), .pi (.bvar 0) (.bvar 1),
    .succ (.succ .zero), .imax (.succ .zero) (.succ .zero),
    .refl _, .refl _,
    ⟨.assumption Γ (.sort (.succ .zero)) (.succ (.succ .zero)) hΓ (.sort Γ (.succ .zero))⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩,
    ⟨.sort Γ (.succ .zero)⟩,
    ⟨.pi (.assumption (.sort (.succ .zero)) :: Γ) (.bvar 0) (.succ .zero) (.bvar 1) (.succ .zero)
      (.bvar (.assumption (.sort (.succ .zero)) :: Γ) 0 (.sort (.succ .zero)) rfl)
      (.bvar (.assumption (.bvar 0) :: .assumption (.sort (.succ .zero)) :: Γ) 1
        (.sort (.succ .zero)) rfl)⟩,
    by rw [lrTermDSubKCore_bot_iff]; trivial, ?_⟩
  intro s hs N N' hN _ hconv _
  rcases List.mem_singleton.mp hs with rfl
  change LRTermDSubKCore E n Γ (.pi N (lift 0 1 N)) (.pi N' (lift 0 1 N'))
    (.sort (.imax (.succ .zero) (.succ .zero))) (.pi .bot [])
  rw [lrTermDSubKCore_pi_iff]
  refine ⟨⟨.imax (.succ .zero) (.succ .zero), .refl _⟩,
    N, lift 0 1 N, N', lift 0 1 N', .succ .zero, .succ .zero,
    .refl _, .refl _,
    ⟨.assumption Γ N (.succ .zero) hΓ hN⟩,
    ⟨.of _ _ _ (.succ .zero) hconv⟩,
    ⟨.of _ _ _ (.succ .zero) (convTWeaken (.assumption N) hcl (c := 0) hconv)⟩,
    ⟨hN⟩,
    ⟨hasTyTWeaken (.assumption N) hcl (c := 0) hN⟩,
    by rw [lrTermDSubKCore_bot_iff]; trivial,
    fun _ hs' => (List.not_mem_nil _ hs').elim⟩

/-- **2. `W-IrrPi` Resolved at `closedIrrPiCpt` (`lrTermDSubKCore_closedIrrPi_of_sortRow`):**
    `LRTermDSubKCore` positively satisfies `closedIrrPiL` vs `closedIrrPiR` at `closedIrrPiCpt`
    in every `EnvWfT E` and `CtxWfT E n Γ` under universe consistency (`hSort`)! -/
theorem lrTermDSubKCore_closedIrrPi_of_sortRow (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level) :
    LRTermDSubKCore E n Γ closedIrrPiL closedIrrPiR (.sort w) closedIrrPiCpt := by
  have hcl := envClosed_of_envWfT hW
  unfold closedIrrPiCpt closedIrrPiL closedIrrPiR
  rw [lrTermDSubKCore_pi_iff]
  let Γ₀ : LCtx := .assumption (.sort .zero) :: Γ
  have hΓ₀ : CtxWfT E n Γ₀ :=
    .assumption Γ (.sort .zero) (.succ .zero) hΓ (.sort Γ .zero)
  have hbP : HasTyT E n Γ₀ (.bvar 0) (.sort .zero) := .bvar Γ₀ 0 (.sort .zero) rfl
  rcases convT_closedIrrPi1_cod hcl hbP (.refl Γ₀ (.bvar 0) (.sort .zero) hbP) with ⟨⟨hcod₁⟩, ⟨hconv₁⟩⟩
  have hdom₀ : HasTyT E n Γ₀ (.pi (.bvar 0) (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ₀ (.bvar 0) .zero (.sort .zero) (.succ .zero) hbP (.sort _ .zero)
  refine ⟨⟨w, .refl _⟩,
    .sort .zero,
    .pi (.pi (.bvar 0) (.sort .zero)) (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 1)))),
    .sort .zero,
    .pi (.pi (.bvar 0) (.sort .zero)) (.pi (.bvar 1) (.pi (.bvar 2) (.app (.bvar 2) (.bvar 0)))),
    .succ .zero,
    .imax (.imax .zero (.succ .zero)) (.imax .zero (.imax .zero .zero)),
    .refl _, .refl _, ⟨hΓ₀⟩, ⟨.refl _ _⟩,
    ⟨.of _ _ _ _ (.pi Γ₀ _ _ _ _ _ _ (.refl Γ₀ _ _ hdom₀) hconv₁)⟩,
    ⟨.sort Γ .zero⟩,
    ⟨.pi Γ₀ _ _ _ _ hdom₀ hcod₁⟩,
    by rw [lrTermDSubKCore_bot_iff]; trivial, ?_⟩
  intro s₁ hs₁ P P' hP _ hPP' _
  rcases List.mem_singleton.mp hs₁ with rfl
  rw [instantiate0_closedIrrPiL, instantiate0_closedIrrPiR]
  unfold closedIrrPi1L closedIrrPi1R
  rw [lrTermDSubKCore_pi_iff]
  have hdom₁ : HasTyT E n Γ (.pi P (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ P .zero (.sort .zero) (.succ .zero) hP (.sort _ .zero)
  have hdom₁_conv : ConvT E n Γ (.pi P (.sort .zero)) (.pi P' (.sort .zero))
      (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ P P' (.sort .zero) (.sort .zero) .zero (.succ .zero) hPP'
      (.refl _ (.sort .zero) (.sort (.succ .zero)) (.sort _ .zero))
  rcases convT_closedIrrPi1_cod hcl hP hPP' with ⟨⟨hcod_stage1⟩, ⟨hconv_stage1⟩⟩
  refine ⟨⟨_, .refl _⟩,
    .pi P (.sort .zero),
    .pi (lift 0 1 P) (.pi (lift 0 1 (lift 0 1 P)) (.app (.bvar 2) (.bvar 1))),
    .pi P' (.sort .zero),
    .pi (lift 0 1 P') (.pi (lift 0 1 (lift 0 1 P')) (.app (.bvar 2) (.bvar 0))),
    .imax .zero (.succ .zero),
    .imax .zero (.imax .zero .zero),
    .refl _, .refl _,
    ⟨.assumption Γ (.pi P (.sort .zero)) (.imax .zero (.succ .zero)) hΓ hdom₁⟩,
    ⟨.of _ _ _ _ hdom₁_conv⟩,
    ⟨.of _ _ _ _ hconv_stage1⟩,
    ⟨hdom₁⟩,
    ⟨hcod_stage1⟩,
    by rw [lrTermDSubKCore_bot_iff]; trivial, ?_⟩
  intro s₂ hs₂ F F' hF _ hFF' hFrel
  rcases List.mem_singleton.mp hs₂ with rfl
  rw [instantiate0_closedIrrPi1L, instantiate0_closedIrrPi1R]
  unfold closedIrrPi2L closedIrrPi2R
  rw [lrTermDSubKCore_pi_iff]
  rcases convT_closedIrrPi2_cod hcl hP hPP' hF hFF' with ⟨⟨hcod_stage2⟩, ⟨hconv_stage2⟩⟩
  refine ⟨⟨_, .refl _⟩,
    P, .pi (lift 0 1 P) (.app (lift 0 1 (lift 0 1 F)) (.bvar 1)),
    P', .pi (lift 0 1 P') (.app (lift 0 1 (lift 0 1 F')) (.bvar 0)),
    .zero, .imax .zero .zero,
    .refl _, .refl _,
    ⟨.assumption Γ P .zero hΓ hP⟩,
    ⟨.of _ _ _ .zero hPP'⟩,
    ⟨.of _ _ _ _ hconv_stage2⟩,
    ⟨hP⟩,
    ⟨hcod_stage2⟩,
    by rw [lrTermDSubKCore_bot_iff]; trivial, ?_⟩
  intro s₃ hs₃ p p' hp _ _ _
  rcases List.mem_singleton.mp hs₃ with rfl
  rw [instantiate0_closedIrrPi2L, instantiate0_closedIrrPi2R]
  unfold closedIrrPi3L closedIrrPi3R
  rw [lrTermDSubKCore_pi_iff]
  rcases convT_closedIrrPi3_cod hcl hP hF hFF' hp with ⟨⟨hcod_stage3⟩, ⟨hconv_stage3⟩⟩
  refine ⟨⟨_, .refl _⟩,
    P, .app (lift 0 1 F) (lift 0 1 p),
    P', .app (lift 0 1 F') (.bvar 0),
    .zero, .zero,
    .refl _, .refl _,
    ⟨.assumption Γ P .zero hΓ hP⟩,
    ⟨.of _ _ _ .zero hPP'⟩,
    ⟨.of _ _ _ .zero hconv_stage3⟩,
    ⟨hP⟩,
    ⟨hcod_stage3⟩,
    by rw [lrTermDSubKCore_bot_iff]; trivial, ?_⟩
  intro s₄ hs₄ q q' _ hq' _ _
  rcases List.mem_singleton.mp hs₄ with rfl
  rw [instantiate0_closedIrrPi3L, instantiate0_closedIrrPi3R]
  have hF_notProp : ¬ IsPropTyI E n Γ (.pi P (.sort .zero)) :=
    not_isPropTyI_pi_sort hSort Γ P .zero
  have hFlam : LRTermDSubKCore E n Γ F F' (.pi P (.sort .zero)) (.lam [([.sort], .sort)]) := by
    rcases hFrel (.lam [([.sort], .sort)]) (List.mem_singleton.mpr rfl) with hProp | hcore
    · exact (hF_notProp hProp).elim
    · exact hcore
  rw [lrTermDSubKCore_lam_iff] at hFlam
  rcases hFlam with ⟨A₁, B₁, _, hpiRed, _, _, happ⟩
  have hpiEq := (whRedPiKCanon_pi_eq hpiRed).symm
  injection hpiEq with hA₁eq hB₁eq
  subst hA₁eq; subst hB₁eq
  have hpq' : ConvT E n Γ p q' P := .irr Γ P p q' hP hp hq'
  have hP_prop : IsPropTyI E n Γ P := isPropTyI_of_hasTyT_sort_zero hSort hP
  have hstep := happ ([.sort], .sort) (List.mem_singleton.mpr rfl) p q' hp hq' hpq'
    (fun _ _ => Or.inl hP_prop)
  change IsPropTyI E n Γ (.sort .zero) ∨
    LRTermDSubKCore E n Γ (.app F p) (.app F' q') (.sort .zero) .sort at hstep
  rcases hstep with hSortProp | hcore
  · exact (not_isPropTyI_sort E n Γ .zero hSortProp).elim
  · exact hcore

theorem lrTermDSubK_closedIrrPi_of_sortRow (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : Level) :
    LRTermDSubK E n Γ closedIrrPiL closedIrrPiR (.sort w) closedIrrPiCpt :=
  Or.inr (lrTermDSubKCore_closedIrrPi_of_sortRow hW hSort hΓ w)

/-- **3. `W-K` 0-Field Resolved at `trueEnvU` (`lrTermDSubKCore_trueEnvU_kRecVar_sort`):**
    Whereas `LRTermDSub` over `WhRed` is refuted on `trueEnvU_kRecVar`
    (`not_lrTermDSub_trueEnvU_kRecVar`), `LRTermDSubKCore` and `LRTermDSubK` positively satisfy
    `(.sort .zero)` vs `trueEnvU_kRecVar` across all compacts in `ApproxDIK trueEnvU EnvI.bot`! -/
theorem lrTermDSubKCore_trueEnvU_kRecVar_sort (n : Nat) :
    LRTermDSubKCore trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar
      (.sort (.succ .zero)) .sort := by
  rw [lrTermDSubKCore_sort_iff]
  exact ⟨⟨.succ .zero, .refl _⟩, .sort (.refl _) whRedPiKCanon_trueEnvU_kRecVar_sort⟩

theorem lrTermDSubK_trueEnvU_kRecVar_sort (n : Nat) :
    LRTermDSubK trueEnvU n trueEnvU_kVarCtx (.sort .zero) trueEnvU_kRecVar
      (.sort (.succ .zero)) .sort :=
  Or.inr (lrTermDSubKCore_trueEnvU_kRecVar_sort n)

/-- **4. `W-K` Fieldful Resolved at `andEnvU` (`lrTermDSubKCore_andEnvU_mixAndRedex_mixPi`):**
    Whereas `LRTermDSub` over `WhRed` is refuted on `mixAndRedex`
    (`not_lrTermDSub_andEnvU_mixAnd`) and `WhStepCK` (`w.fields = []`) is stuck on `mixAndRedex`,
    `LRTermDSubKCore` and `LRTermDSubK` positively satisfy `mixPi` vs `mixAndRedex` at `.pi .bot []`! -/
theorem lrTermDSubKCore_andEnvU_mixAndRedex_mixPi :
    LRTermDSubKCore andEnvU 0 mixAndCtx mixPi mixAndRedex
      (.sort (.succ .zero)) (.pi .bot []) := by
  rw [lrTermDSubKCore_pi_iff]
  refine ⟨⟨.succ .zero, .refl _⟩,
    .sort .zero, .sort .zero, .sort .zero, .sort .zero, .succ .zero, .succ .zero,
    .refl _, whRedPiKCanon_andEnvU_mixAndRedex_mixPi,
    ⟨.assumption mixAndCtx (.sort .zero) (.succ .zero)
      Rcic.Domain.Model.PiInversion.mixAndCtx_wf (.sort mixAndCtx .zero)⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩,
    ⟨.sort mixAndCtx .zero⟩,
    ⟨.sort (.assumption (.sort .zero) :: mixAndCtx) .zero⟩,
    by rw [lrTermDSubKCore_bot_iff]; trivial,
    fun _ hs => (List.not_mem_nil _ hs).elim⟩

theorem lrTermDSubK_andEnvU_mixAndRedex_mixPi :
    LRTermDSubK andEnvU 0 mixAndCtx mixPi mixAndRedex
      (.sort (.succ .zero)) (.pi .bot []) :=
  Or.inr lrTermDSubKCore_andEnvU_mixAndRedex_mixPi

/-! ### §12.3. Head-Step `ConvT` Clauses for `LRTermDSubK` Over `ApproxDIK`, `LRTypeINPiKCanon`
Extraction, and Lifting Let-Free `FundamentalTermDSubKBotDIK_letFree` to All `CtxWfT E n Γ` -/

theorem fundConvDSubK_of_whRedPiKCanon (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (hr : WhRedPiKCanon E M M')
    (hdiag : ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot M' u → LRTermDSubK E n Γ M' M' A u) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot M u → LRTermDSubK E n Γ M M' A u := by
  intro u hbu hMu
  exact lrTermDSubK_whRedPiKCanon_expand hr (.refl _) u
    (hdiag u hbu ((semEqDIK_whRedPiKCanon hW hr u).mp hMu))

theorem fundConvDSubK_of_whStepPiKCanon (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (hs : WhStepPiKCanon E M M')
    (hdiag : ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot M' u → LRTermDSubK E n Γ M' M' A u) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot M u → LRTermDSubK E n Γ M M' A u :=
  fundConvDSubK_of_whRedPiKCanon hW (.step hs (.refl _)) hdiag

theorem fundConvDSubK_beta (hW : EnvWfT E) {Γ : LCtx} (A b a T : Expr Nat)
    (hdiag : ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (instantiate 0 a b) u →
      LRTermDSubK E n Γ (instantiate 0 a b) (instantiate 0 a b) T u) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (.app (.lam A b) a) u →
      LRTermDSubK E n Γ (.app (.lam A b) a) (instantiate 0 a b) T u :=
  fundConvDSubK_of_whStepPiKCanon hW (.of_whStep (.beta A b a)) hdiag

theorem fundConvDSubK_zeta (hW : EnvWfT E) {Γ : LCtx} (A v b T : Expr Nat)
    (hdiag : ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (instantiate 0 v b) u →
      LRTermDSubK E n Γ (instantiate 0 v b) (instantiate 0 v b) T u) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (.letE A v b) u →
      LRTermDSubK E n Γ (.letE A v b) (instantiate 0 v b) T u :=
  fundConvDSubK_of_whStepPiKCanon hW (.of_whStep (.zeta A v b)) hdiag

theorem fundConvDSubK_delta (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b T : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hdiag : ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (instantiateLevels ls b) u →
      LRTermDSubK E n Γ (instantiateLevels ls b) (instantiateLevels ls b) T u) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (.const r ls) u →
      LRTermDSubK E n Γ (.const r ls) (instantiateLevels ls b) T u :=
  fundConvDSubK_of_whStepPiKCanon hW (.of_whStep (.delta hres hbody)) hdiag

theorem fundConvDSubK_iota (hW : EnvWfT E) {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hI : DerivedIotaU E lhs rhs)
    (hdiag : ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot rhs u → LRTermDSubK E n Γ rhs rhs T u) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot lhs u → LRTermDSubK E n Γ lhs rhs T u :=
  fundConvDSubK_of_whStepPiKCanon hW (.of_whStep (.iota hI)) hdiag

theorem fundConvDSubK_lit (hW : EnvWfT E) {Γ : LCtx} (t : Nat) (T : Expr Nat)
    (hdiag : ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (natExpand t) u →
      LRTermDSubK E n Γ (natExpand t) (natExpand t) T u) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (.lit t) u →
      LRTermDSubK E n Γ (.lit t) (natExpand t) T u :=
  fundConvDSubK_of_whStepPiKCanon hW (.of_whStep (.lit t)) hdiag

theorem fundConvDSubK_iotaKCanon (hW : EnvWfT E) {Γ : LCtx}
    (w : IotaWitnessS E) (x T : Expr Nat)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    (hflds : w.fields = List.replicate w.fields.length (.bvar 0))
    (hx : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w.ctorRef args))
    (hdiag : ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (iotaRhsOfS w) u →
      LRTermDSubK E n Γ (iotaRhsOfS w) (iotaRhsOfS w) T u) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (recCall (.const w.recRef w.ls) w.preMajor x) u →
      LRTermDSubK E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w) T u :=
  fundConvDSubK_of_whStepPiKCanon hW (.iotaKCanon w x hk hflds hx) hdiag

theorem fundConvDSubK_zetaLocal_letFree {Γ : LCtx} (hlf : LetFreeCtx Γ)
    {i : Nat} {v T : Expr Nat} (hv : lookupValue Γ i = some v) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (.bvar i) u → LRTermDSubK E n Γ (.bvar i) v T u := by
  rw [hlf i] at hv
  exact Option.noConfusion hv

theorem fundConvDSubK_sorts (Γ : LCtx) (l₁ l₂ : Level) :
    ∀ u, BotPiCpt u → ApproxDIK E EnvI.bot (.sort l₁) u →
      LRTermDSubK E n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) u := by
  intro u _ hu
  rcases approxDIK_sort_inv hu with rfl | rfl
  · exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)
  · refine Or.inr ?_
    rw [lrTermDSubKCore_sort_iff]
    exact ⟨⟨.succ l₁, .refl _⟩, .sort (.refl _) (.refl _)⟩

theorem fundConvDSubK_irr_of_sortRow
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero)) :
    ∀ u, LRTermDSubK E n Γ p q P u :=
  fun _ => Or.inl (isPropTyI_of_hasTyT_sort_zero hSort hP)

/-- Extracting `LRTypeINPiKCanon E n Γ A B (.pi .bot [])` from
    `LRTermDSubKCore E n Γ A B (.sort u) (.pi .bot [])`. -/
theorem lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubKCore {Γ : LCtx} {A B : Expr Nat} {u : Level}
    (h : LRTermDSubKCore E n Γ A B (.sort u) (.pi .bot [])) :
    LRTypeINPiKCanon E n Γ A B (.pi .bot []) := by
  rw [lrTermDSubKCore_pi_iff] at h
  rcases h with ⟨_, A₁, B₁, A₂, B₂, _, _, h1, h2, ⟨hΓ₁⟩, ⟨hcA⟩, ⟨hcB⟩, _, _, _, _⟩
  exact .pi h1 h2 hΓ₁ hcA hcB (.bot Γ A₁ A₂) (fun _ hs => (List.not_mem_nil _ hs).elim)

/-- Extracting `LRTypeINPiKCanon E n Γ A B (.pi .bot [])` from
    `LRTermDSubK E n Γ A B (.sort u) (.pi .bot [])`. -/
theorem lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubK {Γ : LCtx} {A B : Expr Nat} {u : Level}
    (h : LRTermDSubK E n Γ A B (.sort u) (.pi .bot [])) :
    LRTypeINPiKCanon E n Γ A B (.pi .bot []) := by
  rcases h with hProp | hcore
  · exact (not_isPropTyI_sort E n Γ u hProp).elim
  · exact lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubKCore hcore

/-- Named `LetFreeCtx` + `BotPiCpt` fundamental supply for `LRTermDSubK` over `ApproxDIK E EnvI.bot`:
    not refuted by `W-DELTA`/`W-IOTA` (`ApproxDIK`), `W-DEMAND` (`lrTermDSubK_idPiProp_all`),
    `W-IrrPi` (`lrTermDSubK_closedIrrPi_of_sortRow`), `W-K` (`lrTermDSubK_trueEnvU_kRecVar_sort`,
    `lrTermDSubK_andEnvU_mixAndRedex_mixPi`), or `W-ZETALOCAL` (`LetFreeCtx`). -/
def FundamentalTermDSubKBotDIK_letFree (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
      ∀ c, BotPiCpt c → ApproxDIK E EnvI.bot M c → LRTermDSubK E n Γ M M A c) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {M M' A : Expr Nat},
      HasTyT E n Γ M A → HasTyT E n Γ M' A → ConvT E n Γ M M' A →
      ∀ c, BotPiCpt c → ApproxDIK E EnvI.bot M c → LRTermDSubK E n Γ M M' A c)

/-- Projection from `FundamentalTermDSubKBotDIK_letFree` to `LetFreeCtx`-restricted `piRow`
    (closing `TyConvT.trans` via `lrTypeINPiKCanon_trans_of_envWfT` and
    `approxDIK_of_lrTypeINPiKCanon_botPiCpt` with **zero** `TypeSoundness` or `Diamond` hypotheses). -/
theorem piRow_letFree_of_fundamentalTermDSubKBotDIK_letFree (hW : EnvWfT E)
    (hF : FundamentalTermDSubKBotDIK_letFree E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hlf : LetFreeCtx Γ)
    {A₁ B₁ A₂ B₂ : Expr Nat}
    (h : TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  have hwalk : ∀ {X Y : Expr Nat} {u : Level},
      HasTyT E n Γ X (.sort u) → TyConvT E n Γ X Y →
      ApproxDIK E EnvI.bot X (.pi .bot []) → LRTypeINPiKCanon E n Γ X Y (.pi .bot []) := by
    intro X Y u hX htc
    revert u
    induction htc with
    | refl X =>
        intro u hX hAc
        exact lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubK
          (hF.1 hΓ hlf hX (.pi .bot []) botPiCpt_pi_bot_nil hAc)
    | of X Y v hc =>
        intro _ _ hAc
        exact lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubK
          (hF.2 hΓ hlf (convEnds hW hΓ hc).1 (convEnds hW hΓ hc).2.1 hc
            (.pi .bot []) botPiCpt_pi_bot_nil hAc)
    | trans X M Y c₁ c₂ ih₁ ih₂ =>
        intro u hX hAc
        obtain ⟨v, hM⟩ := tyConvT_endTyped hW hΓ c₁ hX
        have r₁ := ih₁ hX hAc
        have hcM := (approxDIK_of_lrTypeINPiKCanon_botPiCpt hW botPiCpt_pi_bot_nil r₁).2
        exact lrTypeINPiKCanon_trans_of_envWfT hW r₁ (ih₂ hM hcM)
  rcases tyConvT_firstOf_data h with heq | ⟨_, u, hc₀, _⟩
  · injection heq with eA eB
    subst eA; subst eB
    exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  · have hpi : HasTyT E n Γ (.pi A₁ B₁) (.sort u) := (convEnds hW hΓ hc₀).1
    have hlr := hwalk hpi h (approxDIK_pi_bot_nil E EnvI.bot A₁ B₁)
    cases hlr with
    | pi hA hB _ hdom hcod _ _ =>
        have e₁ := whRedPiKCanon_pi_eq hA
        have e₂ := whRedPiKCanon_pi_eq hB
        injection e₁ with eA₁ eB₁
        injection e₂ with eA₂ eB₂
        subst eA₁; subst eB₁; subst eA₂; subst eB₂
        exact ⟨⟨hdom⟩, ⟨hcod⟩⟩

/-- **Full `PiRowField E n` from `FundamentalTermDSubKBotDIK_letFree`:**
    Combines `piRow_letFree_of_fundamentalTermDSubKBotDIK_letFree` with the telescope let-expansion
    engine `piRow_of_letFree_piRow` (§6.3) to yield unrestricted `PiRowField E n` on **all**
    `CtxWfT E n Γ` (including contexts with `letBinding`s). -/
theorem piRow_of_fundamentalTermDSubKBotDIK_letFree (hW : EnvWfT E)
    (hF : FundamentalTermDSubKBotDIK_letFree E n) : PiRowField E n :=
  fun {_} hΓ {_ _ _ _} h =>
    piRow_of_letFree_piRow hW
      (fun {_} hlf' hΓ' {_ _ _ _} h' =>
        piRow_letFree_of_fundamentalTermDSubKBotDIK_letFree hW hF hΓ' hlf' h')
      hΓ h


#print axioms defIdMember
#print axioms defIdEnv
#print axioms defIdEnvWfT
#print axioms hasTyT_defIdEnv_const0
#print axioms whStep_defIdEnv_const0
#print axioms not_whNormal_defIdEnv_const0
#print axioms whStep_defIdEnv_const0_unique
#print axioms whRed_defIdEnv_const0_inv
#print axioms not_whRed_whNormal_foldApps_defIdEnv_const0
#print axioms not_lrTermDCore_defIdEnv_const0_spine0
#print axioms not_lrTermS_defIdEnv_const0_spine0
#print axioms not_lrTermD_defIdEnv_const0_spine0_of_not_pi_sort
#print axioms rigidConst_body_none_of_envWfT
#print axioms ctor_body_none_of_envWfT
#print axioms whNormal_const_of_rigidConst
#print axioms rigidConst_of_body_none
#print axioms envWfT_member_trichotomy
#print axioms lrTermDCore_rigidConst_consts
#print axioms lrTermDCore_rigidConst_diag
#print axioms lrTermD_rigidConst_consts
#print axioms lrTermD_rigidConst_diag
#print axioms lrTermSDI_rigidConst_consts
#print axioms lrTermSDI_rigidConst_diag
#print axioms deltaConst_defIdEnv_const0
#print axioms approxDI_defIdEnv_const0_iff
#print axioms not_approxDI_defIdEnv_const0_spine0
#print axioms lrTermDCore_defIdEnv_const0_lam_nil
#print axioms lrTermD_weaken_botPiCpt
#print axioms lrTermD_weaken0_botPiCpt
#print axioms lrTermD_subst_botPiCpt_of_sortRow
#print axioms lrTermD_subst0_botPiCpt_of_sortRow
#print axioms lrTermD_subst_botPiCpt_of_botDI
#print axioms lrTermD_subst0_botPiCpt_of_botDI
#print axioms lrTermS_substLet_botPiCpt
#print axioms lrTermS_substLet0_botPiCpt
#print axioms lrTermSDI_substLet_botPiCpt
#print axioms lrTermSDI_substLet0_botPiCpt
#print axioms lrTermDCore_substLet_botPiCpt
#print axioms lrTermDCore_substLet0_botPiCpt
#print axioms lrTermD_substLet_botPiCpt_of_sortRow
#print axioms lrTermD_substLet0_botPiCpt_of_sortRow
#print axioms lrTermD_substLet_botPiCpt_of_botDI
#print axioms lrTermD_substLet0_botPiCpt_of_botDI
#print axioms lrTermDCore_sort_subst_of_envClosed
#print axioms fundamentalTermDIS_of_envClosed
#print axioms fundamentalTermDIS_typed_of_sortRow
#print axioms not_botPiCpt_curryStep
#print axioms approxDI_lam_botPiCpt_eq_bot
#print axioms approxDI_rigidConst_botPiCpt_eq_bot
#print axioms approxDI_recursor_botPiCpt_eq_bot
#print axioms approxDI_const_body_none_botPiCpt_eq_bot
#print axioms lrTermDCore_botPiCpt_forces_sort
#print axioms approxDI_of_lrTermDCore_botPiCpt
#print axioms not_lrTermDCore_at_pi_of_botPiCpt_ne_bot
#print axioms lrTermD_at_pi_of_botPiCpt
#print axioms fundTermBotDI_sort
#print axioms fundTermBotDI_bvar
#print axioms fundTermBotDI_lam
#print axioms fundTermBotDI_const_of_body_none
#print axioms fundTermBotDI_rigidConst
#print axioms fundTermBotDI_recursor
#print axioms fundTermBotDI_deltaConst
#print axioms fundTermBotDI_pi
#print axioms fundTermBotDI_lit
#print axioms fundTermBotDI_letE
#print axioms fundTermBotDI_conv
#print axioms fundConvBotDI_refl
#print axioms fundConvBotDI_trans
#print axioms fundConvBotDI_beta
#print axioms fundConvBotDI_zeta
#print axioms fundConvBotDI_zetaLocal
#print axioms fundConvBotDI_delta
#print axioms fundConvBotDI_delta_of_deltaConst
#print axioms fundConvBotDI_iota
#print axioms fundConvBotDI_lit
#print axioms fundConvBotDI_lam
#print axioms fundConvBotDI_pi
#print axioms fundConvBotDI_letE
#print axioms fundConvBotDI_sorts
#print axioms fundConvBotDI_consts_of_body_none
#print axioms fundConvBotDI_rigidConsts
#print axioms fundConvBotDI_recursorConsts
#print axioms fundConvBotDI_deltaConsts
#print axioms fundConvBotDI_eta
#print axioms fundConvBotDI_irr_of_sortRow
#print axioms fundConvBotDI_irr_of_botDI
#print axioms LRTermDBiDI
#print axioms lrTermDBiDI_symm
#print axioms lrTermDBiDI_trans
#print axioms lrTermDBiDI_sorts
#print axioms lrTermDBiDI_sort_diag
#print axioms lrTermDBiDI_bvar_diag
#print axioms lrTermDBiDI_lam
#print axioms lrTermDBiDI_consts_of_body_none
#print axioms lrTermDBiDI_pi
#print axioms lrTermDBiDI_eta
#print axioms lrTermDBiDI_irr_of_sortRow
#print axioms lrTermDBiDI_tyConv
#print axioms FundamentalTermBiBotDI
#print axioms fundamentalTermBotDI_of_biBotDI
#print axioms piRow_of_fundamentalTermBiBotDI
#print axioms not_lrTypeIN_zetaLocalSortCtx_symm
#print axioms not_lrTypeINBiDI_zetaLocalSortCtx
#print axioms not_lrTermD_zetaLocalSortCtx_symm
#print axioms not_lrTermDBiDI_zetaLocalSortCtx
#print axioms not_fundamentalLRINBotDI_zetaLocal
#print axioms not_fundamentalTermBotDI_zetaLocal
#print axioms not_fundamentalTermBiBotDI_zetaLocal
#print axioms LetFreeCtx
#print axioms letFreeCtx_nil
#print axioms letFreeCtx_assumption
#print axioms not_letFreeCtx_letBinding
#print axioms letFreeCtx_tail
#print axioms letFreeCtx_substRemove
#print axioms lrTypeINBiDI_zetaLocal_letFree
#print axioms lrTermDBiDI_zetaLocal_letFree
#print axioms FundamentalLRINBotDI_letFree
#print axioms FundamentalTermBotDI_letFree
#print axioms FundamentalTermBiBotDI_letFree
#print axioms fundamentalTermBotDI_letFree_of_biBotDI_letFree
#print axioms fundamentalLRINBotDI_letFree_of_links
#print axioms fundamentalLRINBotDI_letFree_of_termBotDI_letFree
#print axioms piRow_letFree_of_fundamentalLRINBotDI_letFree
#print axioms not_tyConvT_pi_sort_letFree_of_fundamentalLRINBotDI_letFree
#print axioms expandLetAt
#print axioms expandLetAt_sort
#print axioms expandLetAt_const
#print axioms expandLetAt_lit
#print axioms expandLetAt_app
#print axioms expandLetAt_pi
#print axioms expandLetAt_lam
#print axioms expandLetAt_letE
#print axioms expandLetAt_bvar_eq
#print axioms expandLetAt_bvar_ne
#print axioms hasTyT_conv_expandLetAt
#print axioms tyConvT_substLet_of_envWfT
#print axioms letCount
#print axioms FirstLetAt
#print axioms letFree_or_firstLetAt
#print axioms firstLetAt_get?
#print axioms letCount_substRemove_of_firstLetAt
#print axioms ctxWfT_substRemove_of_firstLetAt
#print axioms ctxConvT_insertAt_substRemove_of_firstLetAt
#print axioms tyConvT_of_substRemove_firstLetAt
#print axioms tyConvT_eq_or_both_typed
#print axioms piRow_of_letCount
#print axioms piRow_of_letFree_piRow
#print axioms sortRow_of_letCount
#print axioms sortRow_of_letFree_sortRow
#print axioms piRow_of_fundamentalLRINBotDI_letFree
#print axioms piRow_of_fundamentalTermBotDI_letFree
#print axioms piRow_of_fundamentalTermBiBotDI_letFree
#print axioms polyPiType
#print axioms polyPiTypeCpt
#print axioms botPiCpt_polyPiTypeCpt
#print axioms hasTyT_polyPiType
#print axioms approxDI_polyPiType
#print axioms tyConvT_pi_sort_of_unguarded_pi_polyPiType
#print axioms LRTermDSubCore
#print axioms LRTermDSub
#print axioms lrTermDSubCore_bot_iff
#print axioms lrTermDSubCore_sort_iff
#print axioms lrTermDSubCore_pi_iff
#print axioms lrTermDSubCore_idPiProp_all
#print axioms lrTermDSubCore_idPiProp_sortStep
#print axioms lrTermDSub_idPiProp_all
#print axioms lrTermDSubCore_polyPiType_of_envWfT
#print axioms lrTermDSubCore_spine_iff
#print axioms lrTermDSubCore_lam_iff
#print axioms lrTermDSubCore_whRed_expand
#print axioms lrTermDSub_whRed_expand
#print axioms fundConvDSub_of_whRed
#print axioms fundConvDSub_of_whStep
#print axioms fundConvDSub_beta
#print axioms fundConvDSub_zeta
#print axioms fundConvDSub_delta
#print axioms fundConvDSub_iota
#print axioms fundConvDSub_lit
#print axioms fundConvDSub_zetaLocal_letFree
#print axioms fundConvDSub_irr_of_sortRow
#print axioms convT_instantiate0_sort_of_convT
#print axioms tyConvT_instantiate0_sort_of_convT
#print axioms eval_const_zero_isSome
#print axioms not_isPropTyI_pi_sort
#print axioms instantiate1_lift0_lift0
#print axioms closedIrrPi1L
#print axioms closedIrrPi1R
#print axioms closedIrrPi2L
#print axioms closedIrrPi2R
#print axioms closedIrrPi3L
#print axioms closedIrrPi3R
#print axioms instantiate0_closedIrrPiL
#print axioms instantiate0_closedIrrPiR
#print axioms instantiate0_closedIrrPi1L
#print axioms instantiate0_closedIrrPi1R
#print axioms instantiate0_closedIrrPi2L
#print axioms instantiate0_closedIrrPi2R
#print axioms instantiate0_closedIrrPi3L
#print axioms instantiate0_closedIrrPi3R
#print axioms convT_closedIrrPi3_cod
#print axioms convT_closedIrrPi2_cod
#print axioms convT_closedIrrPi1_cod
#print axioms lrTermDSubCore_closedIrrPi_of_sortRow
#print axioms lrTermDSub_closedIrrPi_of_sortRow
#print axioms lrTypeIN_pi_bot_nil_of_lrTermDSubCore
#print axioms lrTypeIN_pi_bot_nil_of_lrTermDSub
#print axioms FundamentalTermDSubBotDI_letFree
#print axioms piRow_letFree_of_fundamentalTermDSubBotDI_letFree
#print axioms piRow_of_fundamentalTermDSubBotDI_letFree
#print axioms iotaWitnessS_same_recRef
#print axioms iotaWitnessS_unique_of_nMinors_one
#print axioms iotaWitnessS_of_iotaWitness_envWfT
#print axioms approxDI_recursor_elim_no_ctor_inv
#print axioms approxDI_recursor_elim_bvar_bot_inv
#print axioms trueEnvU_kRecElim
#print axioms trueEnvU_kRecVar
#print axioms trueEnvU_kRecIdTt
#print axioms trueEnvU_kVarCtx
#print axioms letFreeCtx_trueEnvU_kVarCtx
#print axioms letFreeCtx_mixAndCtx
#print axioms approxDI_trueEnvU_kRecVar_bot_inv
#print axioms not_approxDI_trueEnvU_kRecVar_sort
#print axioms not_semEqDI_trueEnvU_kRecVar_sort
#print axioms not_pEqDI_trueEnvU_kRecVar_sort
#print axioms not_majorStableDI_trueEnvU
#print axioms not_domTyped_trueEnvU_recElim
#print axioms approxDI_andEnvU_mixAndRedex_bot_inv
#print axioms not_approxDI_andEnvU_mixAndRedex_pi
#print axioms not_semEqDI_andEnvU_mixAndRedex_mixPi
#print axioms semEqDI_trueEnvU_kRecIdTt
#print axioms semEqDI_trueEnvU_kRecVar_canonEnv
#print axioms whRed_andEnvU_mixAndRhs_mixPi
#print axioms semEqDI_andEnvU_mixAndRedex_canonEnv
#print axioms whStep_constSpine_no_ctor_false_aux
#print axioms whStep_constSpine_no_ctor_false
#print axioms whRed_constSpine_no_ctor_eq
#print axioms whRed_trueEnvU_kRecVar_eq
#print axioms whRed_andEnvU_mixAndRedex_eq
#print axioms ctxWfT_trueEnvU_kVarCtx
#print axioms convT_trueEnvU_kRecVar_sort
#print axioms tyConvT_trueEnvU_kRecVar_sort
#print axioms not_lrTypeINBiDI_trueEnvU_kRecVar
#print axioms not_lrTermD_trueEnvU_kRecVar
#print axioms not_lrTermDBiDI_trueEnvU_kRecVar
#print axioms not_lrTermDSub_trueEnvU_kRecVar
#print axioms not_fundamentalLRINBotDI_letFree_trueEnvU
#print axioms not_fundamentalTermBotDI_letFree_trueEnvU
#print axioms not_fundamentalTermBiBotDI_letFree_trueEnvU
#print axioms not_fundamentalTermDSubBotDI_letFree_trueEnvU
#print axioms not_lrTypeIN_andEnvU_mixAnd
#print axioms not_lrTypeINBiDI_andEnvU_mixAnd
#print axioms not_lrTermD_andEnvU_mixAnd
#print axioms not_lrTermDBiDI_andEnvU_mixAnd
#print axioms not_lrTermDSub_andEnvU_mixAnd
#print axioms not_fundamentalLRINBotDI_letFree_andEnvU
#print axioms not_fundamentalTermBotDI_letFree_andEnvU
#print axioms not_fundamentalTermBiBotDI_letFree_andEnvU
#print axioms not_fundamentalTermDSubBotDI_letFree_andEnvU
#print axioms convT_iotaS_of_propMajor_eq
#print axioms convT_iotaS_of_propMajor_tyConv
#print axioms ApproxDIK
#print axioms denDIK
#print axioms SemEqDIK
#print axioms PEqDIK
#print axioms semEqDIK_refl
#print axioms semEqDIK_symm
#print axioms semEqDIK_trans
#print axioms approxDIK_of_approxDI
#print axioms approxDIK_const_env
#print axioms approxDIK_mono_env
#print axioms approxDIK_mono_env_nonbot
#print axioms approxDIK_cons_botDemand_iff
#print axioms approxDIK_cons_botDemand_bot_iff
#print axioms approxDIK_bvar_inv
#print axioms approxDIK_sort_inv
#print axioms approxDIK_rigid_const_inv
#print axioms approxDIK_delta_const_inv
#print axioms approxDIK_recursor_const_inv
#print axioms approxDIK_pi_inv
#print axioms approxDIK_lam_inv
#print axioms approxDIK_app_inv
#print axioms approxDIK_letE_inv
#print axioms approxDIK_lit_inv
#print axioms approxDIK_closedAt_env
#print axioms approxDIK_closed0_env
#print axioms approxDIK_natExpand_env
#print axioms approxDIK_mono_update
#print axioms approxDIK_factor_list
#print axioms approxDIK_factor_args
#print axioms approxDIK_factor
#print axioms approxDIK_lift_intro
#print axioms approxDIK_lift_elim
#print axioms approxDIK_liftN_intro
#print axioms approxDIK_liftN_elim
#print axioms approxDIK_subst_intro
#print axioms approxDIK_subst_elim
#print axioms approxDIK_subst_iff
#print axioms approxDIK_subst_demand_iff
#print axioms ApproxArgsDemandK
#print axioms ApproxArgsDemandK.length_eq
#print axioms ApproxArgsDemandK.append_iff
#print axioms approxArgsDemandK_replicate_nil
#print axioms approxDIK_instPrefix_demand_iff
#print axioms approxDIK_instPrefix_closed_iff
#print axioms approxDIK_beta
#print axioms approxDIK_zeta
#print axioms approxDIK_lit
#print axioms approxDIK_delta_bot
#print axioms semEqDIK_delta
#print axioms semEqDIK_of_whStep_delta
#print axioms AppCptK
#print axioms approxDIK_app_iff_appCptK
#print axioms FoldAppCptK
#print axioms approxDIK_foldApps_iff
#print axioms foldAppCptK_bot_inv
#print axioms foldAppCptK_curryStep_iff
#print axioms ApproxSpineArgsK
#print axioms approxSpineArgsK_cons_iff
#print axioms approxSpineArgsK_replicate_bot
#print axioms approxSpineArgsK_append_iff
#print axioms foldAppCptK_spine_iff
#print axioms approxDIK_foldApps_rigid_iff
#print axioms forall_fieldDemandVectorsK_iff
#print axioms ctorDemandK_intro
#print axioms ctorDemandK_inv
#print axioms approxDIK_iotaS
#print axioms approxDIK_iotaT
#print axioms approxDIK_iota_of_envWfT
#print axioms approxDIK_iotaU_of_envWfT
#print axioms semEqDIK_of_convT_iota
#print axioms BotDemandList
#print axioms botDemandList_of_approxArgsDemandK
#print axioms pushArgs_botDemandList_nonbot_le
#print axioms semEqDIK_k_botFields
#print axioms semEqDIK_k_zeroFields
#print axioms semEqDIK_k_zeroFields_of_envWfT
#print axioms semEqDIK_k_botFields_of_envWfT
#print axioms semEqDIK_trueEnvU_kRec_all
#print axioms semEqDIK_trueEnvU_kRecVar_sort
#print axioms semEqDIK_trueEnvU_kRecIdTt_sort
#print axioms approxDIK_trueEnvU_kRecVar_sort
#print axioms semEqDIK_andEnvU_mixAndRedex_mixAndRhs
#print axioms semEqDIK_sorts
#print axioms semEqDIK_app
#print axioms semEqDIK_lam
#print axioms semEqDIK_pi
#print axioms semEqDIK_letE
#print axioms semEqDIK_whStep
#print axioms semEqDIK_whRed
#print axioms semEqDIK_pi_inj
#print axioms semEqDIK_pi_sort_disjoint
#print axioms approxDIK_pi_bot_nil
#print axioms semEqDIK_andEnvU_mixAndRedex_mixPi
#print axioms approxDIK_andEnvU_mixAndRedex_pi
#print axioms WhStepPiK
#print axioms WhRedPiK
#print axioms whRedPiK_trans
#print axioms whRedPiK_of_whRed
#print axioms semEqDIK_whStepPiK
#print axioms semEqDIK_whRedPiK
#print axioms approxDIK_whRedPiK_back
#print axioms approxDIK_sort_of_whRedPiK
#print axioms whStepPiK_sort_false
#print axioms whStepPiK_pi_false
#print axioms whRedPiK_sort_eq
#print axioms whRedPiK_pi_eq
#print axioms whStepPiK_iotaK_of_envWfT
#print axioms whRedPiK_trueEnvU_kRecVar_sort
#print axioms whRedPiK_andEnvU_mixAndRedex_mixPi
#print axioms LRTypeINPiK
#print axioms lrTypeINPiK_of_lrTypeIN
#print axioms approxDIK_of_lrTypeINPiK_botPiCpt
#print axioms LRTypeINBiDIK
#print axioms lrTypeINBiDIK_sorts
#print axioms lrTypeINBiDIK_sort_diag
#print axioms lrTypeINBiDIK_bvar_diag
#print axioms lrTypeINBiDIK_pi
#print axioms lrTypeINPiK_expand
#print axioms lrTypeINBiDIK_of_whRedPiK
#print axioms lrTypeINBiDIK_trueEnvU_kRecVar_sort
#print axioms lrTypeINBiDIK_andEnvU_mixAndRedex_mixPi
#print axioms FundamentalLRINBotDIK_letFree
#print axioms piRow_letFree_of_fundamentalLRINBotDIK_letFree
#print axioms piRow_of_fundamentalLRINBotDIK_letFree
#print axioms approxDIK_lift0_one_iff
#print axioms denDIK_lift0_one_eq
#print axioms semEqDIK_lift0_one_iff
#print axioms ctxEnvDIK
#print axioms bot_le_ctxEnvDIK
#print axioms ctxEnvDIK_none_bot
#print axioms ctxEnvDIK_letFree_le_bot
#print axioms approxDIK_of_bot_to_ctxEnvDIK
#print axioms approxDIK_ctxEnvDIK_letFree_iff
#print axioms semEqDIK_ctxEnvDIK_zetaLocal
#print axioms semEqDIK_ctxEnvDIK_zetaLocalSortCtx
#print axioms approxDIK_ctxEnvDIK_zetaLocalSortCtx_sort
#print axioms not_whRedPiK_sort_and_pi
#print axioms lrTypeINPiK_ctx
#print axioms lrTypeINPiK_assump_dom
#print axioms lrTypeINPiK_symm
#print axioms lrTypeINBiDIK_symm
#print axioms WhStepPiKCanon
#print axioms whStepPiK_of_whStepPiKCanon
#print axioms WhRedPiKCanon
#print axioms whRedPiKCanon_trans
#print axioms whRedPiKCanon_of_whRed
#print axioms whRedPiK_of_whRedPiKCanon
#print axioms whRedPiKCanon_appHead
#print axioms semEqDIK_whStepPiKCanon
#print axioms semEqDIK_whRedPiKCanon
#print axioms approxDIK_whRedPiKCanon_back
#print axioms approxDIK_sort_of_whRedPiKCanon
#print axioms whStepPiKCanon_sort_false
#print axioms whStepPiKCanon_pi_false
#print axioms whRedPiKCanon_sort_eq
#print axioms whRedPiKCanon_pi_eq
#print axioms whStepPiK_lam_false
#print axioms whStepPiKCanon_lam_false
#print axioms not_whStepPiK_recursor_prefix
#print axioms not_whStepPiKCanon_recursor_prefix
#print axioms approxDIK_ctor_spine_bot
#print axioms not_whStep_and_iotaK
#print axioms iotaKCanon_det
#print axioms whStep_and_whStepPiKCanon_det
#print axioms whDetPiKCanon_of_envWfT
#print axioms WhNormalPiKCanon
#print axioms whNormalPiKCanon_sort
#print axioms whNormalPiKCanon_pi
#print axioms whNormalPiKCanon_lam
#print axioms whRedPiKCanon_of_normal
#print axioms whRedPiKCanon_normal_unique_of_envWfT
#print axioms whRedPiKCanon_pi_unique_of_envWfT
#print axioms whRedPiKCanon_sort_unique_of_envWfT
#print axioms whStepPiKCanon_iotaKCanon_of_envWfT
#print axioms whRedPiKCanon_trueEnvU_kRecVar_sort
#print axioms mixAndWCanon
#print axioms whRed_andEnvU_mixAndCanonRhs_mixPi
#print axioms whRedPiKCanon_andEnvU_mixAndRedex_mixPi
#print axioms LRTypeINPiKCanon
#print axioms approxDIK_of_lrTypeINPiKCanon_botPiCpt
#print axioms lrTypeINPiKCanon_expand
#print axioms lrTypeINPiKCanon_ctx
#print axioms lrTypeINPiKCanon_assump_dom
#print axioms lrTypeINPiKCanon_symm
#print axioms lrTypeINPiKCanon_trans_of_envWfT
#print axioms LRTypeINBiDIKCanon
#print axioms lrTypeINBiDIKCanon_symm
#print axioms lrTypeINBiDIKCanon_trans
#print axioms lrTypeINBiDIKCanon_sorts
#print axioms lrTypeINBiDIKCanon_sort_diag
#print axioms lrTypeINBiDIKCanon_bvar_diag
#print axioms lrTypeINBiDIKCanon_pi
#print axioms lrTypeINBiDIKCanon_pi_diag
#print axioms lrTypeINBiDIKCanon_of_whRedPiKCanon
#print axioms lrTypeINBiDIKCanon_of_whStepPiKCanon
#print axioms lrTypeINBiDIKCanon_beta
#print axioms lrTypeINBiDIKCanon_zeta
#print axioms lrTypeINBiDIKCanon_delta
#print axioms lrTypeINBiDIKCanon_iota
#print axioms lrTypeINBiDIKCanon_lit
#print axioms lrTypeINBiDIKCanon_iotaKCanon
#print axioms lrTypeINBiDIKCanon_zetaLocal_letFree
#print axioms lrTypeINBiDIKCanon_idPiProp
#print axioms lrTypeINBiDIKCanon_closedIrrPi
#print axioms lrTypeINBiDIKCanon_trueEnvU_kRecVar_sort
#print axioms lrTypeINBiDIKCanon_andEnvU_mixAndRedex_mixPi
#print axioms FundamentalLRINBotDIKCanon_letFree
#print axioms fundamentalLRINBotDIKCanon_letFree_of_links
#print axioms piRow_letFree_of_fundamentalLRINBotDIKCanon_letFree
#print axioms piRow_of_fundamentalLRINBotDIKCanon_letFree
#print axioms LRTermDSubKCore
#print axioms LRTermDSubK
#print axioms lrTermDSubKCore_bot_iff
#print axioms lrTermDSubKCore_sort_iff
#print axioms lrTermDSubKCore_pi_iff
#print axioms lrTermDSubKCore_spine_iff
#print axioms lrTermDSubKCore_lam_iff
#print axioms lrTermDSubKCore_whRedPiKCanon_expand
#print axioms lrTermDSubK_whRedPiKCanon_expand
#print axioms lrTermDSubKCore_idPiProp_all
#print axioms lrTermDSubKCore_idPiProp_sortStep
#print axioms lrTermDSubK_idPiProp_all
#print axioms lrTermDSubKCore_polyPiType_of_envWfT
#print axioms lrTermDSubKCore_closedIrrPi_of_sortRow
#print axioms lrTermDSubK_closedIrrPi_of_sortRow
#print axioms lrTermDSubKCore_trueEnvU_kRecVar_sort
#print axioms lrTermDSubK_trueEnvU_kRecVar_sort
#print axioms lrTermDSubKCore_andEnvU_mixAndRedex_mixPi
#print axioms lrTermDSubK_andEnvU_mixAndRedex_mixPi
#print axioms fundConvDSubK_of_whRedPiKCanon
#print axioms fundConvDSubK_of_whStepPiKCanon
#print axioms fundConvDSubK_beta
#print axioms fundConvDSubK_zeta
#print axioms fundConvDSubK_delta
#print axioms fundConvDSubK_iota
#print axioms fundConvDSubK_lit
#print axioms fundConvDSubK_iotaKCanon
#print axioms fundConvDSubK_zetaLocal_letFree
#print axioms fundConvDSubK_sorts
#print axioms fundConvDSubK_irr_of_sortRow
#print axioms lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubKCore
#print axioms lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubK
#print axioms FundamentalTermDSubKBotDIK_letFree
#print axioms piRow_letFree_of_fundamentalTermDSubKBotDIK_letFree
#print axioms piRow_of_fundamentalTermDSubKBotDIK_letFree

end Rcic.Declarative.NativeValleys.PiModelDeltaIotaConvAudit
