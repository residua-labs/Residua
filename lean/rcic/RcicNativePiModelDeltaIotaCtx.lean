import rcic.RcicNativePiModelDeltaIotaFund
import rcic.RcicDTMetaTypedSR

/-!
# Context-Aware Deterministic K-Closed Readback (`WhStepPiKClosedCtx` / `WhRedPiKClosedCtx`),
`LRTypeINBiDIKClosedCtx`, `LRTermDSubKClosedCtxBi`, and Unconditional `let` / `zeta` / `zetaLocal` /
`beta` / `bvar` / `const` / `consts` / `tyConv` Closure Across All Contexts `Γ : LCtx`

Builds on `RcicNativePiModelDeltaIotaFund` (#7691) and `RcicNativePiModelDeltaIotaConv` (#7669).

## Contents

1. **§5. Self-Contained `ProbeCpt` Index Transport Without `FundamentalLRINBot`,
   `let`-Substitution for `LRTypeINPiKClosed`, and `LRTermDSubKClosed` / `LRTermDSubKClosedBi`
   Over `WhRedPiKClosed`:**
   * Proves `lrTermDSubKCore_probe_transport_of_bi`, `lrTermDSubK_probe_transport_of_bi`, and
     `lrTermDSubKBi_tyConv_of_bi`, eliminating `FundamentalLRINBotDIKCanon_letFree E n` from the
     27-constructor reduction (`fundamentalTermDSubKBiProbe_letFree_of_supply_noBot`,
     `fundamentalTermDSubKProbe_letFree_of_supply_noBot`, `piRow_of_appLetProbeSupplyDSubKBi_noBot`).
   * Proves `lrTypeINPiKClosed_substLet_botPiCpt`, `lrTypeINPiKClosed_substLet0_botPiCpt`, and
     `lrTypeINBiDIKClosed_substLet0`.
   * Defines `LRTermDSubKClosedCore`, `LRTermDSubKClosed`, and `LRTermDSubKClosedBi` over
     `WhRedPiKClosed`, proving full PER (`lrTermDSubKClosedBi_symm`, `lrTermDSubKClosedBi_trans`),
     all-cutoff weakening (`lrTermDSubKClosedBi_weaken`, `lrTermDSubKClosedBi_weaken0`), and
     assumption/`let`-substitution (`lrTermDSubKClosedBi_subst0`, `lrTermDSubKClosedBi_substLet0`,
     `lrTermDSubKClosedBi_beta_of_botApprox`, `lrTermDSubKClosedBi_zeta_of_botApprox`,
     `lrTermDSubKClosedBi_letE_diag_of_botApprox`).

2. **§6. Context-Aware Deterministic K-Closed Readback `WhStepPiKClosedCtx` / `WhRedPiKClosedCtx`
   Over `ctxEnvDIK` and Unconditional `let`-Substitution Across ALL Let-Values:**
   * Defines `WhStepPiKClosedCtx E Γ` and `WhRedPiKClosedCtx E Γ` combining `WhStep`, `zetaLocal`,
     and fieldful `iotaKClosedCtx` guarded by `ctxEnvDIK E Γ`, proving exact agreement with
     `WhStepPiKClosed E` on `LetFreeCtx Γ` (`whStepPiKClosedCtx_letFree_iff`,
     `whRedPiKClosedCtx_letFree_iff`), unconditional model invariance over `ApproxDIK E (ctxEnvDIK E Γ)`
     (`semEqDIK_ctxEnvDIK_whStepPiKClosedCtx`, `semEqDIK_ctxEnvDIK_whRedPiKClosedCtx`), and
     **exact single-step determinism `whDetPiKClosedCtx_of_envWfT`** (`whRedPiKClosedCtx_normal_unique_of_envWfT`,
     `whRedPiKClosedCtx_pi_unique_of_envWfT`, `whRedPiKClosedCtx_sort_unique_of_envWfT`) across
     **all** contexts `Γ : LCtx`.
   * Proves the exact `EnvI` equalities `ctxEnvDIK_insertAt_eq`, **`ctxEnvDIK_substLet_eq` (valid for
     ALL `w0 : Expr Nat` with ZERO `⊥`-approximation restriction!)**, and `ctxEnvDIK_substAssump_eq`,
     yielding `approxDIK_ctxEnvDIK_insertAt_lift_iff`, `approxDIK_ctxEnvDIK_substLet_iff`,
     `approxDIK_ctxEnvDIK_substLet0_iff`, `whStepPiKClosedCtx_lift_insertAt`,
     `whStepPiKClosedCtx_substLet_of_envClosed`, `whRedPiKClosedCtx_substLet_of_envClosed`, and
     `whRedPiKClosedCtx_substLet0_of_envClosed`.

3. **§7. Context-Aware Type and Term Logical Relations `LRTypeINPiKClosedCtx` /
   `LRTypeINBiDIKClosedCtx` and `LRTermDSubKClosedCtx` / `LRTermDSubKClosedCtxBi` Across ALL
   Contexts `Γ : LCtx`:**
   * Defines `SameLetProfile`, `LRTypeINPiKClosedCtx`, and `LRTypeINBiDIKClosedCtx` across **all**
     contexts `Γ : LCtx` (without `LetFreeCtx Γ`!), proving reverse adequacy
     `approxDIK_of_lrTypeINPiKClosedCtx_botPiCpt`, full symmetry `lrTypeINPiKClosedCtx_symm`,
     transitivity `lrTypeINPiKClosedCtx_trans_of_envWfT`, all-cutoff weakening
     `lrTypeINPiKClosedCtx_weaken_botPiCpt`, **unconditional `let`-substitution across all `w0 : Expr Nat`
     (`lrTypeINPiKClosedCtx_substLet_botPiCpt`, `lrTypeINBiDIKClosedCtx_substLet0`)**,
     `lrTypeINBiDIKClosedCtx_zetaLocal`, `lrTypeINBiDIKClosedCtx_zetaLocalSortCtx`, and direct
     8-line `piRow` projection `piRow_of_fundamentalLRINBotDIKClosedCtx`.
   * Defines `LRTermDSubKClosedCtxCore`, `LRTermDSubKClosedCtx`, and `LRTermDSubKClosedCtxBi` across
     **all** contexts `Γ : LCtx`, proving `lrTermDSubKClosedCtxBi_symm`, `lrTermDSubKClosedCtxBi_trans`,
     **unconditional `let`-substitution `lrTermDSubKClosedCtxBi_substLet0` (for all `w0 : Expr Nat`)**,
     **unconditional `ConvT.zetaLocal` (`lrTermDSubKClosedCtxBi_zetaLocal`), `ConvT.zeta`
     (`lrTermDSubKClosedCtxBi_zeta` from `ih_b` alone!), and `HasTyT.letE`
     (`lrTermDSubKClosedCtxBi_letE_diag` from `ih_b` alone!)**, constructor clauses, simultaneous
     positive satisfaction of all 5 named benchmarks (`lrTermDSubKClosedCtxBi_zetaLocalSortCtx`,
     `lrTermDSubKClosedCtxBi_idPiProp`, `lrTermDSubKClosedCtxBi_closedIrrPi`,
     `lrTermDSubKClosedCtxBi_trueEnvU_kRecVar_sort`, `lrTermDSubKClosedCtxBi_andEnvU_mixAndRedex_mixPi`),
     and direct `piRow` projection `piRow_of_fundamentalTermDSubKClosedCtxBiProbe`.

4. **§8. All-Cutoff Weakening, `CtxBVarOK`, Let-Refinement `CtxRefines`, Unconditional `ConvT.beta`
   Closure Across ALL Arguments, and 27-Constructor Reduction Across ALL Contexts `Γ : LCtx`:**
   * Proves all-cutoff weakening (`lrTermDSubKClosedCtxBi_weaken`, `lrTermDSubKClosedCtxBi_weaken0`,
     `lrTermDSubKClosedCtxBi_closed_weaken_ctx`), assumption-substitution
     (`lrTypeINPiKClosedCtx_substAssump_botPiCpt`, `lrTypeINBiDIKClosedCtx_substAssump0`,
     `lrTermDSubKClosedCtxBi_substAssump0`, `lrTermDSubKClosedCtxBi_beta_of_botApprox`), and
     same-value let-congruence (`lrTermDSubKClosedCtxBi_letE_sameVal`).
   * Defines `CtxBVarOK E n Γ`, proving `ctxBVarOK_nil`, `ctxBVarOK_of_letFree`,
     `ctxBVarOK_cons_assumption`, and `ctxBVarOK_cons_letBinding`.
   * Defines `CtxRefines Γ Γ'` (`nil`, `assumption`, `letBinding`, `assumpToLet`), proving
     `lookupType_of_ctxRefines`, `lookupValue_of_ctxRefines`, `hasTyT_of_ctxRefines`,
     `convT_of_ctxRefines`, `tyConvT_of_ctxRefines`, and **unconditional `ConvT.beta` soundness across
     ALL arguments (`lrTermDSubKClosedCtxBi_beta_via_let`)**.
   * Proves the 27-constructor mutual structural induction (`fundCtxBiProbe_hasTyT`,
     `fundCtxBiProbe_convT`, `ctxBVarOK_of_ctxWfT`, `fundamentalTermDSubKClosedCtxBiProbe_of_supply`,
     `piRow_of_appValCongrSupplyDSubKClosedCtxBi`) across **all** contexts `Γ : LCtx` with **zero**
     `LetFreeCtx Γ` restriction and **zero** `FundamentalLRINBot` premise, closing 25 of 27
     constructors (`HasTyT.sort`, `bvar`, `const`, `pi`, `lam`, `letE`, `lit`, `conv`; `ConvT.refl`,
     `symm`, `trans`, `beta`, `zeta`, `zetaLocal`, `delta`, `iota`, `lit`, `lam`, `pi`, `sorts`,
     `consts`, `eta`, `irr`, `tyConv`, plus `HasTyT.app` via `ConvT.app`) unconditionally.

5. **§9. Unconditional `DeltaConst` Discharge from `EnvWfT E` (`AppLetCongrSupplyDSubKClosedCtxBi`),
   Two-Way Weak-Head Reduction Equivalence (`↔`), and `SemEqDIK` / Neutral-Spine Congruence:**
   * Defines the 2-clause supply `AppLetCongrSupplyDSubKClosedCtxBi E n` (retaining only `ConvT.app`
     congruence and `ConvT.letE` diagonal-body value congruence, with **zero** `DeltaConst` clause),
     proves sub-environment structural induction (`fundCtxBiProbe_sub_hasTyT`,
     `fundCtxBiProbe_sub_convT`) and `EnvWfT` induction (`groupMembersT_members_preserved`,
     `groupMembersT_body_from_base`, `envWfT_deltaConst_sub`), and proves
     **`deltaConst_lrTermDSubKClosedCtxBi_of_envWfT`** and **`appValCongrSupply_of_appLetCongrSupply`**,
     discharging `HasTyT.const` and `ConvT.consts` across **all** constants (both `body = none` and
     `body = some b`) from `EnvWfT E` (`fundamentalTermDSubKClosedCtxBiProbe_of_appLetCongrSupply`,
     `piRow_of_appLetCongrSupplyDSubKClosedCtxBi`).
   * Proves forward-and-backward weak-head reduction equivalence (`↔`) for normal targets
     (`whRedPiKClosedCtx_of_whStepPiKClosedCtx_normal`, `whRedPiKClosedCtx_iff_of_whRedPiKClosedCtx_normal`,
     `whRedPiKClosedCtx_sort_iff_of_whRed`, `whRedPiKClosedCtx_pi_iff_of_whRed`) and for
     `LRTypeINPiKClosedCtx` / `LRTermDSubKClosedCtxBi` (`lrTypeINPiKClosedCtx_whRedPiKClosedCtx_iff`,
     `lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_probe_iff`,
     `lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff`), establishing exact equivalence between
     `ConvT.letE` value congruence and $\beta$/$\zeta$-redex congruence
     (`lrTermDSubKClosedCtxBi_beta_congr_iff_subst0`, `lrTermDSubKClosedCtxBi_zeta_congr_iff_subst0`,
     `lrTermDSubKClosedCtxBi_app_lam_whRed_iff_subst0`, `lrTermDSubKClosedCtxBi_subst0_lift0_one`).
   * Proves `SemEqDIK` substitution congruence (`denDIK_instantiate_eq_of_semEqDIK`,
     `semEqDIK_instantiate_of_semEqDIK`, `semEqDIK_instantiate0_of_semEqDIK`,
     `approxDIK_ctxEnvDIK_instantiate0_iff_of_semEqDIK`,
     `lrTermDSubKClosedCtxBi_subst0_of_semEqDIK_botProbe`) and unconditional application congruence
     on non-`.lam` heads and neutral/constructor/inductive spines (`approxDIK_app_not_lam_of_not_lam`,
     `approxDIK_foldApps_not_lam_of_not_lam`, `approxDIK_app_probeCpt_eq_bot_of_no_lam`,
     `approxDIK_foldApps_probeCpt_eq_bot_of_no_lam`, `approxDIK_ctxEnvDIK_bvar_none_not_lam`,
     `approxDIK_sort_not_lam`, `approxDIK_pi_not_lam`, `approxDIK_rigidConst_not_lam`,
     `lrTermDSubKClosedCtxBi_of_probeCpt_eq_bot`, `lrTermDSubKClosedCtxBi_app_of_no_lam`,
     `lrTermDSubKClosedCtxBi_foldApps_of_no_lam`).

6. **§10. Proposition-Codomain Π-Inversion, Canonical Π-Pruning of `ApproxDIK` (`prunePiCpt`),
   `η`-Application Equivalence, and Reductions Between `AppCongrSupply` & `LetValCongrSupply`:**
   * Proves `eqN_zero_of_imax_zero`, `hasTyT_codomain_sort_zero_of_pi_sort_zero`,
     `isPropTyI_codomain_of_pi`, `isPropTyI_inst0_of_pi`, `lrTermDSubKClosedCtxBi_of_isPropTyI`,
     and **`lrTermDSubKClosedCtxBi_app_of_isPropTyI_pi`** (unconditional application congruence
     whenever `.pi A B` is a proposition).
   * Defines `PrunedPiCpt` and `prunePiCpt` (replacing every `.pi a f` sub-compact anywhere inside a
     compact `c : CptI` by `.pi .bot []`), and proves **`approxDIK_prunePiCpt`**,
     **`approxDIK_bot_prunePiCpt`**, and **`approxDIK_ctxEnvDIK_prunePiCpt`** (`ApproxDIK E (ctxEnvDIK E Γ) e c → ApproxDIK E (ctxEnvDIK E Γ) e (prunePiCpt c)`), establishing that `CptI.pi` domain/codomain parameters are 100% inert across all 13 rules of `ApproxDIK`.
   * Proves `instantiate0_app_lift0_bvar0`, `whStep_app_eta`, `whRedPiKClosedCtx_app_eta`,
     `semEqDIK_app_eta`, and **`lrTermDSubKClosedCtxBi_app_eta_left_iff` / `_right_iff` / `_both_iff`**
     (when applied to an argument, an `η`-expanded function is two-way equivalent `↔` to the
     unexpanded function in both `SemEqDIK` and `LRTermDSubKClosedCtxBi`), plus unconditional
     same-argument `λ`-application congruence **`lrTermDSubKClosedCtxBi_app_lam_same_arg`**,
     reduction of two-sided `λ`-application congruence to `LetValCongrSupply`
     (`lrTermDSubKClosedCtxBi_app_lam_of_letValCongr`), and reduction of `.assumption`-typed
     0-instantiation congruence to `AppCongrSupply` (`lrTermDSubKClosedCtxBi_subst0_of_appCongr`).

`closure_claim = 0`. Zero `sorry`, zero new axioms, zero `structure`/`class` declarations.
-/

namespace Rcic.Declarative.NativeValleys.PiModelDeltaIotaCtxAudit

open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelIrrAudit
open Rcic.Declarative.NativeValleys.PiModelKAudit
open Rcic.Declarative.NativeValleys.PiModelTermAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaTermAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaConvAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaFundAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ## §5. Self-Contained `ProbeCpt` Index Transport Without `FundamentalLRINBot`,
`let`-Substitution for `LRTypeINPiKClosed`, and `LRTermDSubKClosed` / `LRTermDSubKClosedBi`
Over `WhRedPiKClosed` -/

/-! ### §5.1. `hBot`-Free Probe Index Transport (`lrTermDSubKCore_probe_transport_of_bi`) and
27-Constructor Reduction Without `FundamentalLRINBotDIKCanon_letFree` -/

/-- **Self-Contained `ProbeCpt` Index Transport for `LRTermDSubKCore`
    (`lrTermDSubKCore_probe_transport_of_bi`):**
    On any `ProbeCpt` compact `c ∈ {.bot, .sort, .pi .bot []}`, transporting
    `LRTermDSubKCore E n Γ M M' A c` to `LRTermDSubKCore E n Γ M M' B c` requires **only**
    `EnvWfT E` and the bidirectional relation `ih_AB : LRTermDSubKBi E n Γ A B (.sort u)` on the
    converting types (evaluated at `c₀ = .sort`), eliminating the external
    `FundamentalLRINBotDIKCanon_letFree E n` hypothesis! -/
theorem lrTermDSubKCore_probe_transport_of_bi (hW : EnvWfT E)
    {Γ : LCtx} {M M' A B : Expr Nat} {u : Level}
    (ih_AB : LRTermDSubKBi E n Γ A B (.sort u))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKCore E n Γ M M' A c) :
    LRTermDSubKCore E n Γ M M' B c := by
  cases hc with
  | bot => rw [lrTermDSubKCore_bot_iff]; trivial
  | sort =>
      obtain ⟨l, hl⟩ :=
        lrTermDSubKCore_botPiCpt_forces_sort .sort (by intro h0; cases h0) h
      have hAsort : ApproxDIK E EnvI.bot A .sort := approxDIK_sort_of_whRedPiKCanon hW hl
      rcases ih_AB .sort .sort (Or.inl hAsort) with hP | hAB
      · exact (not_isPropTyI_sort E n Γ u hP).elim
      · rw [lrTermDSubKCore_sort_iff] at hAB
        exact lrTermDSubKCore_botPiCpt_transport_of_sort hAB.2 .sort h
  | piBotNil =>
      obtain ⟨l, hl⟩ :=
        lrTermDSubKCore_botPiCpt_forces_sort botPiCpt_pi_bot_nil (by intro h0; cases h0) h
      have hAsort : ApproxDIK E EnvI.bot A .sort := approxDIK_sort_of_whRedPiKCanon hW hl
      rcases ih_AB .sort .sort (Or.inl hAsort) with hP | hAB
      · exact (not_isPropTyI_sort E n Γ u hP).elim
      · rw [lrTermDSubKCore_sort_iff] at hAB
        exact lrTermDSubKCore_botPiCpt_transport_of_sort hAB.2 botPiCpt_pi_bot_nil h

/-- Self-contained `ProbeCpt` index transport for `LRTermDSubK` from `ih_AB : LRTermDSubKBi E n Γ A B (.sort u)`. -/
theorem lrTermDSubK_probe_transport_of_bi (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hcAB : TyConvT E n Γ A B)
    (ih_AB : LRTermDSubKBi E n Γ A B (.sort u))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubK E n Γ M M' A c) :
    LRTermDSubK E n Γ M M' B c := by
  rcases h with hP | hC
  · exact Or.inl (hProp hΓ hA hcAB hP)
  · exact Or.inr (lrTermDSubKCore_probe_transport_of_bi hW ih_AB hc hC)

/-- Bidirectional type-conversion transport `LRTermDSubKBi E n Γ M M' A → LRTermDSubKBi E n Γ M M' B`
    using `ih_AB : LRTermDSubKBi E n Γ A B (.sort u)` instead of `FundamentalLRINBotDIKCanon_letFree E n`. -/
theorem lrTermDSubKBi_tyConv_of_bi (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hcAB : TyConvT E n Γ A B)
    (ih_M : LRTermDSubKBi E n Γ M M' A)
    (ih_AB : LRTermDSubKBi E n Γ A B (.sort u)) :
    LRTermDSubKBi E n Γ M M' B :=
  fun _ hc hor =>
    lrTermDSubK_probe_transport_of_bi hW hProp hΓ hA hcAB ih_AB hc (ih_M _ hc hor)

mutual

private theorem fundBiProbeNoBot_hasTyT (hW : EnvWfT E)
    (hPS : PropTyTransport E n ∧
      (∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂))
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    {Γ : LCtx} → {M A : Expr Nat} → HasTyT E n Γ M A →
      CtxWfT E n Γ → LetFreeCtx Γ → LRTermDSubKBi E n Γ M M A
  | Γ, _, _, .sort _ l, _, _ =>
      lrTermDSubKBi_sort_diag Γ l
  | Γ, _, _, .bvar _ i A _, _, _ =>
      lrTermDSubKBi_bvar_diag Γ i A
  | _, _, _, .const _ r ls m hm _ _, hΓ, hlf => by
      cases hb : m.body with
      | none => exact lrTermDSubKBi_consts_of_body_none ls ls _ hm hb
      | some b =>
          obtain ⟨hdelta, _⟩ := envWfT_member_body_closed hW r m b hm hb
          exact lrTermDSubKBi_deltaConsts hW hdelta (hSup.2.2.2 hΓ hlf hdelta)
  | _, _, _, .pi _ _ _ _ _ hA hB, hΓ, _ =>
      lrTermDSubKBi_pi_diag hΓ hA hB
  | Γ, _, _, .lam _ A _ b B _ _, _, _ =>
      lrTermDSubKBi_lam Γ A A b b B
  | _, _, _, .app _ _ _ _ _ hf ha, hΓ, hlf =>
      hSup.1 hΓ hlf hf ha
        (fundBiProbeNoBot_hasTyT hW hPS hSup hf hΓ hlf)
        (fundBiProbeNoBot_hasTyT hW hPS hSup ha hΓ hlf)
  | _, _, _, .letE _ A _ v B b _ hv _, hΓ, hlf =>
      have hstep : WhRedPiKCanon E (.letE A v b) (instantiate 0 v b) :=
        .step (.of_whStep (.zeta A v b)) (.refl _)
      lrTermDSubKBi_whRedPiKCanon_expand hW hstep hstep
        (hSup.2.2.1 hΓ hlf hv hv (fundBiProbeNoBot_hasTyT hW hPS hSup hv hΓ hlf))
  | _, _, _, .lit _ t _ hexp, hΓ, hlf =>
      have hstep : WhRedPiKCanon E (.lit t) (natExpand t) :=
        .step (.of_whStep (.lit t)) (.refl _)
      lrTermDSubKBi_whRedPiKCanon_expand hW hstep hstep
        (fundBiProbeNoBot_hasTyT hW hPS hSup hexp hΓ hlf)
  | Γ, _, _, .conv _ _ A B u he hc, hΓ, hlf =>
      lrTermDSubKBi_tyConv_of_bi hW hPS.1 hΓ (convEnds hW hΓ hc).1 (.of Γ A B u hc)
        (fundBiProbeNoBot_hasTyT hW hPS hSup he hΓ hlf)
        (fundBiProbeNoBot_convT hW hPS hSup hc hΓ hlf)

private theorem fundBiProbeNoBot_convT (hW : EnvWfT E)
    (hPS : PropTyTransport E n ∧
      (∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂))
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    {Γ : LCtx} → {M M' A : Expr Nat} → ConvT E n Γ M M' A →
      CtxWfT E n Γ → LetFreeCtx Γ → LRTermDSubKBi E n Γ M M' A
  | _, _, _, _, .refl _ _ _ he, hΓ, hlf =>
      fundBiProbeNoBot_hasTyT hW hPS hSup he hΓ hlf
  | _, _, _, _, .symm _ _ _ _ h, hΓ, hlf =>
      lrTermDSubKBi_symm hW (fundBiProbeNoBot_convT hW hPS hSup h hΓ hlf)
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂, hΓ, hlf =>
      lrTermDSubKBi_trans hW
        (fundBiProbeNoBot_convT hW hPS hSup h₁ hΓ hlf)
        (fundBiProbeNoBot_convT hW hPS hSup h₂ hΓ hlf)
  | _, _, _, _, .beta _ A b a _ _ _ _ ha, hΓ, hlf =>
      lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.beta A b a))
        (hSup.2.2.1 hΓ hlf ha ha (fundBiProbeNoBot_hasTyT hW hPS hSup ha hΓ hlf))
  | _, _, _, _, .zeta _ A v b _ _ _ hv _, hΓ, hlf =>
      lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.zeta A v b))
        (hSup.2.2.1 hΓ hlf hv hv (fundBiProbeNoBot_hasTyT hW hPS hSup hv hΓ hlf))
  | _, _, _, _, .zetaLocal _ i _ _ hval _ _, _, hlf => by
      rw [hlf i] at hval
      exact Option.noConfusion hval
  | _, _, _, _, .delta _ _ _ _ _ hres hbody _ _ _ hb, hΓ, hlf =>
      lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.delta hres hbody))
        (fundBiProbeNoBot_hasTyT hW hPS hSup hb hΓ hlf)
  | _, _, _, _, .iota _ _ _ _ hI _ hrhs, hΓ, hlf =>
      lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.iota (derivedIotaU_ofDerivedIota hI)))
        (fundBiProbeNoBot_hasTyT hW hPS hSup hrhs hΓ hlf)
  | _, _, _, _, .lit _ t _ _ hlit hexp, hΓ, hlf => by
      have hexp' := fundBiProbeNoBot_hasTyT hW hPS hSup hexp hΓ hlf
      cases hlit
      exact lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.lit t)) hexp'
  | _, _, _, _, .app _ _ _ _ _ _ _ hf ha, hΓ, hlf =>
      hSup.2.1 hΓ hlf hf ha
        (fundBiProbeNoBot_convT hW hPS hSup hf hΓ hlf)
        (fundBiProbeNoBot_convT hW hPS hSup ha hΓ hlf)
  | Γ, _, _, _, .lam _ A₁ A₂ b₁ b₂ B _ _ _, _, _ =>
      lrTermDSubKBi_lam Γ A₁ A₂ b₁ b₂ B
  | Γ, _, _, _, .pi _ A₁ A₂ B₁ B₂ u v hcA hcB, hΓ, _ =>
      have hA₁ : HasTyT E n Γ A₁ (.sort u) := (convEnds hW hΓ hcA).1
      have hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ) := .assumption Γ A₁ u hΓ hA₁
      have hB₁ : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort v) := (convEnds hW hΓ₁ hcB).1
      lrTermDSubKBi_pi hΓ₁ (.of Γ A₁ A₂ u hcA) (.of _ B₁ B₂ v hcB) hA₁ hB₁
  | Γ, _, _, _, .letE _ A₁ A₂ v₁ v₂ b₁ b₂ _ _ _ hcv _, hΓ, hlf =>
      have hL : WhRedPiKCanon E (.letE A₁ v₁ b₁) (instantiate 0 v₁ b₁) :=
        .step (.of_whStep (.zeta A₁ v₁ b₁)) (.refl _)
      have hR : WhRedPiKCanon E (.letE A₂ v₂ b₂) (instantiate 0 v₂ b₂) :=
        .step (.of_whStep (.zeta A₂ v₂ b₂)) (.refl _)
      have hv₁ : HasTyT E n Γ v₁ A₁ := (convEnds hW hΓ hcv).1
      have hv₂ : HasTyT E n Γ v₂ A₁ := (convEnds hW hΓ hcv).2.1
      lrTermDSubKBi_whRedPiKCanon_expand hW hL hR
        (hSup.2.2.1 hΓ hlf hv₁ hv₂ (fundBiProbeNoBot_convT hW hPS hSup hcv hΓ hlf))
  | Γ, _, _, _, .sorts _ l₁ l₂ _, _, _ =>
      lrTermDSubKBi_sorts Γ l₁ l₂
  | _, _, _, _, .consts _ r ls₁ ls₂ m hm _ _ _ _, hΓ, hlf => by
      cases hb : m.body with
      | none => exact lrTermDSubKBi_consts_of_body_none ls₁ ls₂ _ hm hb
      | some b =>
          obtain ⟨hdelta, _⟩ := envWfT_member_body_closed hW r m b hm hb
          exact lrTermDSubKBi_deltaConsts hW hdelta (hSup.2.2.2 hΓ hlf hdelta)
  | _, _, _, _, .eta _ _ _ _ hf, hΓ, hlf =>
      lrTermDSubKBi_eta (fundBiProbeNoBot_hasTyT hW hPS hSup hf hΓ hlf)
  | _, _, _, _, .irr _ _ _ _ hP _ _, _, _ =>
      lrTermDSubKBi_irr_of_sortRow hPS.2 hP
  | Γ, _, _, _, .tyConv _ _ _ A A' u h hA, hΓ, hlf =>
      lrTermDSubKBi_tyConv_of_bi hW hPS.1 hΓ (convEnds hW hΓ hA).1 (.of Γ A A' u hA)
        (fundBiProbeNoBot_convT hW hPS hSup h hΓ hlf)
        (fundBiProbeNoBot_convT hW hPS hSup hA hΓ hlf)

end

/-- **`hBot`-Free 27-Constructor Reduction (`fundamentalTermDSubKBiProbe_letFree_of_supply_noBot`):**
    By mutual structural induction on `HasTyT` and `ConvT` using `lrTermDSubKBi_tyConv_of_bi`,
    `FundamentalTermDSubKBiProbe_letFree E n` follows from `AppLetProbeSupplyDSubKBi E n` under
    `EnvWfT E`, `PropTyTransport E n`, and `SortRow` alone — with **zero**
    `FundamentalLRINBotDIKCanon_letFree E n` hypothesis! -/
theorem fundamentalTermDSubKBiProbe_letFree_of_supply_noBot (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    FundamentalTermDSubKBiProbe_letFree E n :=
  ⟨fun {_} hΓ hlf {_ _} hM => fundBiProbeNoBot_hasTyT hW ⟨hProp, hSort⟩ hSup hM hΓ hlf,
   fun {_} hΓ hlf {_ _ _} _ _ hconv => fundBiProbeNoBot_convT hW ⟨hProp, hSort⟩ hSup hconv hΓ hlf⟩

theorem fundamentalTermDSubKProbe_letFree_of_supply_noBot (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    FundamentalTermDSubKProbe_letFree E n :=
  fundamentalTermDSubKProbe_letFree_of_biProbe_letFree
    (fundamentalTermDSubKBiProbe_letFree_of_supply_noBot hW hProp hSort hSup)

/-- Direct bridge from `AppLetProbeSupplyDSubKBi E n` to full unrestricted `PiRowField E n`
    without `FundamentalLRINBotDIKCanon_letFree E n`. -/
theorem piRow_of_appLetProbeSupplyDSubKBi_noBot (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    PiRowField E n :=
  piRow_of_fundamentalTermDSubKBiProbe_letFree hW
    (fundamentalTermDSubKBiProbe_letFree_of_supply_noBot hW hProp hSort hSup)

/-! ### §5.2. `let`-Substitution Stability of `LRTypeINPiKClosed` and `LRTypeINBiDIKClosed` -/

/-- **Unconditional `let`-Substitution Stability of `LRTypeINPiKClosed` on `BotPiCpt` for
    `⊥`-Approximated Let-Values (`lrTypeINPiKClosed_substLet_botPiCpt`):** -/
theorem lrTypeINPiKClosed_substLet_botPiCpt {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {w0 : Expr Nat} (hw0 : ∀ u, ApproxDIK E EnvI.bot w0 u → u = .bot) (t : Expr Nat)
    {c : CptI} (hc : BotPiCpt c) :
    ∀ {Γ : LCtx} {A A' : Expr Nat} {j : Nat},
      Γ[j]? = some (.letBinding t w0) →
      HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
      CtxWfT E n (substRemove w0 j Γ) →
      LRTypeINPiKClosed E n Γ A A' c →
      LRTypeINPiKClosed E n (substRemove w0 j Γ)
        (instantiate j (lift 0 j w0) A) (instantiate j (lift 0 j w0) A') c := by
  induction hc with
  | bot =>
      intro Γ A A' j _ _ _ _
      exact .bot _ _ _
  | sort =>
      intro Γ A A' j _ _ _ h
      cases h with
      | sort h₁ h₂ =>
          exact .sort (whRedPiKClosed_instantiate_of_botApprox hcl hw0 h₁ j)
            (whRedPiKClosed_instantiate_of_botApprox hcl hw0 h₂ j)
  | @pi a f _ _ _ iha ihf =>
      intro Γ A A' j hget hvty hΓ' h
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h₁ h₂ hΓ₁ hdom hcod ra rf =>
          have hlift : lift 0 1 (lift 0 j w0) = lift 0 (j + 1) w0 :=
            lift_lift_merge 1 j 0 0 (by omega) (by omega) w0
          have h₁' : WhRedPiKClosed E (instantiate j (lift 0 j w0) A)
              (.pi (instantiate j (lift 0 j w0) A₁) (instantiate (j + 1) (lift 0 (j + 1) w0) B₁)) := by
            have h0 := whRedPiKClosed_instantiate_of_botApprox hcl hw0 h₁ j
            simpa only [instantiate, hlift] using h0
          have h₂' : WhRedPiKClosed E (instantiate j (lift 0 j w0) A')
              (.pi (instantiate j (lift 0 j w0) A₂) (instantiate (j + 1) (lift 0 (j + 1) w0) B₂)) := by
            have h0 := whRedPiKClosed_instantiate_of_botApprox hcl hw0 h₂ j
            simpa only [instantiate, hlift] using h0
          have hA₁ : ∃ u, Nonempty (HasTyT E n Γ A₁ (.sort u)) := by
            cases hΓ₁ with
            | assumption _ _ u _ hA₁ => exact ⟨u, ⟨hA₁⟩⟩
          obtain ⟨u, ⟨hA₁⟩⟩ := hA₁
          have hA₁' : HasTyT E n (substRemove w0 j Γ) (instantiate j (lift 0 j w0) A₁) (.sort u) :=
            hasTyT_substLetS hcl hinst t w0 hA₁ hget hvty
          have hΓ₁'' : CtxWfT E n (.assumption (instantiate j (lift 0 j w0) A₁) :: substRemove w0 j Γ) :=
            .assumption _ _ u hΓ' hA₁'
          have hΓ₁' : CtxWfT E n (substRemove w0 (j + 1) (.assumption A₁ :: Γ)) := by
            simpa only [substRemove_succ_cons, instDecl] using hΓ₁''
          have hget' : (LocalDecl.assumption A₁ :: Γ)[j + 1]? = some (.letBinding t w0) := by
            rw [List.getElem?_cons_succ]; exact hget
          have hvty' : HasTyT E n (substRemove w0 (j + 1) (.assumption A₁ :: Γ))
              (lift 0 (j + 1) w0) (lift 0 (j + 1) t) := by
            have h0 := hasTyTWeaken (instDecl j w0 (.assumption A₁)) hcl (c := 0) hvty
            rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
                lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
            exact h0
          have hdom' : TyConvT E n (substRemove w0 j Γ)
              (instantiate j (lift 0 j w0) A₁) (instantiate j (lift 0 j w0) A₂) :=
            tyConvT_substLetS hcl hinst t w0 hdom hget hvty
          have hcod' : TyConvT E n (.assumption (instantiate j (lift 0 j w0) A₁) :: substRemove w0 j Γ)
              (instantiate (j + 1) (lift 0 (j + 1) w0) B₁)
              (instantiate (j + 1) (lift 0 (j + 1) w0) B₂) := by
            simpa only [substRemove_succ_cons, instDecl] using
              tyConvT_substLetS hcl hinst t w0 (j := j + 1) hcod hget' hvty'
          exact .pi h₁' h₂' hΓ₁'' hdom' hcod'
            (iha hget hvty hΓ' ra)
            (fun s hs => by
              simpa only [substRemove_succ_cons, instDecl] using
                ihf s hs hget' hvty' hΓ₁' (rf s hs))

/-- Head (`j = 0`) specialization of `lrTypeINPiKClosed_substLet_botPiCpt`. -/
theorem lrTypeINPiKClosed_substLet0_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 : Expr Nat}
    (hw0 : ∀ u, ApproxDIK E EnvI.bot w0 u → u = .bot)
    (hw0ty : HasTyT E n Γ w0 t)
    {A A' : Expr Nat} {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeINPiKClosed E n (.letBinding t w0 :: Γ) A A' c) :
    LRTypeINPiKClosed E n Γ (instantiate0 w0 A) (instantiate0 w0 A') c := by
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have h0 := lrTypeINPiKClosed_substLet_botPiCpt
    (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hw0 t hc
    (Γ := .letBinding t w0 :: Γ) (j := 0) hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hw0ty)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- Head `let`-substitution stability of `LRTypeINBiDIKClosed` for `⊥`-approximated let-values. -/
theorem lrTypeINBiDIKClosed_substLet0 {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 : Expr Nat}
    (hw0 : ∀ u, ApproxDIK E EnvI.bot w0 u → u = .bot)
    (hw0ty : HasTyT E n Γ w0 t)
    {A A' : Expr Nat}
    (h : LRTypeINBiDIKClosed E n (.letBinding t w0 :: Γ) A A') :
    LRTypeINBiDIKClosed E n Γ (instantiate0 w0 A) (instantiate0 w0 A') := by
  intro c hc hor
  have hor₀ : ApproxDIK E EnvI.bot A c ∨ ApproxDIK E EnvI.bot A' c :=
    hor.elim (fun hL => Or.inl ((approxDIK_bot_instantiate0_iff hw0 A c).mp hL))
             (fun hR => Or.inr ((approxDIK_bot_instantiate0_iff hw0 A' c).mp hR))
  exact lrTypeINPiKClosed_substLet0_botPiCpt hW hΓ hw0 hw0ty hc (h c hc hor₀)

/-! ### §5.3. `LRTermDSubKClosedCore`, `LRTermDSubKClosed`, and `LRTermDSubKClosedBi` Over `WhRedPiKClosed`
and Exact `ProbeCpt` Equivalence with `LRTypeINPiKClosed` -/

/-- **Closed-Field K-Aware `ConvT`-Guarded Substitution-Style Term Logical Relation (`LRTermDSubKClosedCore`):**
    Built over `WhRedPiKClosed` and `LRTypeINPiKClosed`. Note that in the `.pi a f` branch, the
    codomain sort witness `w₁` is placed inside the step quantifier `∀ s ∈ f` where it is used, so
    at `c = .pi .bot []` (`a = .bot`, `f = []`), `LRTermDSubKClosedCore E n Γ M M' A (.pi .bot [])`
    is **100% equivalent (`↔`)** to `(∃ l, WhRedPiKClosed E A (.sort l)) ∧ LRTypeINPiKClosed E n Γ M M' (.pi .bot [])`! -/
def LRTermDSubKClosedCore (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : CptI → Prop
  | .bot => True
  | .sort => (∃ l, WhRedPiKClosed E A (.sort l)) ∧ LRTypeINPiKClosed E n Γ M M' .sort
  | .pi a f =>
      (∃ l, WhRedPiKClosed E A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ u₁,
        WhRedPiKClosed E M (.pi A₁ B₁) ∧
        WhRedPiKClosed E M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧
        Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        LRTermDSubKClosedCore E n Γ A₁ A₂ (.sort u₁) a ∧
        ∀ s ∈ f, ∃ w₁,
          Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁)) ∧
          ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
            ConvT E n Γ N N' A₁ →
            (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKClosedCore E n Γ N N' A₁ u) →
            IsPropTyI E n Γ (instantiate0 N B₁) ∨
              LRTermDSubKClosedCore E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁) s.2
  | .spine r args =>
      ((∃ l, WhRedPiKClosed E A (.sort l)) ∧ LRTypeINPiKClosed E n Γ M M' (.spine r args)) ∨
      (∃ ls₁ ls₂ : List Level, ∃ args₁ args₂ : List (Expr Nat),
        WhRedPiKClosed E M (foldApps (.const r ls₁) args₁) ∧
        WhRedPiKClosed E M' (foldApps (.const r ls₂) args₂) ∧
        WhNormalPiKClosed E (foldApps (.const r ls₁) args₁) ∧
        WhNormalPiKClosed E (foldApps (.const r ls₂) args₂) ∧
        Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁) (foldApps (.const r ls₂) args₂) A) ∧
        args₁.length = args.length ∧
        args₂.length = args.length)
  | .lam g =>
      ∃ A₁ B₁ : Expr Nat, ∃ w : Level,
        WhRedPiKClosed E A (.pi A₁ B₁) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKClosedCore E n Γ N N' A₁ u) →
          IsPropTyI E n Γ (instantiate0 N B₁) ∨
            LRTermDSubKClosedCore E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
termination_by c => sizeOf c
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

/-- Top-level `IsPropTyI`-collapsed `LRTermDSubKClosed`. -/
def LRTermDSubKClosed (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (u : CptI) : Prop :=
  IsPropTyI E n Γ A ∨ LRTermDSubKClosedCore E n Γ M M' A u

/-- Bidirectional `ProbeCpt`-restricted term logical relation over `ApproxDIK E EnvI.bot` and
    `LRTermDSubKClosed`. -/
def LRTermDSubKClosedBi (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : Prop :=
  ∀ c, ProbeCpt c →
    (ApproxDIK E EnvI.bot M c ∨ ApproxDIK E EnvI.bot M' c) →
    LRTermDSubKClosed E n Γ M M' A c

theorem lrTermDSubKClosedCore_bot_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermDSubKClosedCore E n Γ M M' A .bot ↔ True := by
  rw [LRTermDSubKClosedCore.eq_def]

theorem lrTermDSubKClosedCore_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermDSubKClosedCore E n Γ M M' A .sort ↔
      (∃ l, WhRedPiKClosed E A (.sort l)) ∧ LRTypeINPiKClosed E n Γ M M' .sort := by
  rw [LRTermDSubKClosedCore.eq_def]

theorem lrTermDSubKClosedCore_pi_iff (Γ : LCtx) (M M' A : Expr Nat)
    (a : CptI) (f : List (List CptI × CptI)) :
    LRTermDSubKClosedCore E n Γ M M' A (.pi a f) ↔
      (∃ l, WhRedPiKClosed E A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ u₁,
        WhRedPiKClosed E M (.pi A₁ B₁) ∧
        WhRedPiKClosed E M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧
        Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        LRTermDSubKClosedCore E n Γ A₁ A₂ (.sort u₁) a ∧
        ∀ s ∈ f, ∃ w₁,
          Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁)) ∧
          ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
            ConvT E n Γ N N' A₁ →
            (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKClosedCore E n Γ N N' A₁ u) →
            IsPropTyI E n Γ (instantiate0 N B₁) ∨
              LRTermDSubKClosedCore E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁) s.2 := by
  rw [LRTermDSubKClosedCore.eq_def]

/-- **Exact Non-`⊥` `ProbeCpt` Characterization (`lrTermDSubKClosedCore_probe_nonbot_iff`):**
    For every `ProbeCpt c` with `c ≠ .bot` (`c = .sort` or `c = .pi .bot []`),
    `LRTermDSubKClosedCore E n Γ M M' A c` is **100% equivalent (`↔`)** to
    `(∃ l, WhRedPiKClosed E A (.sort l)) ∧ LRTypeINPiKClosed E n Γ M M' c`! -/
theorem lrTermDSubKClosedCore_probe_nonbot_iff {Γ : LCtx} {M M' A : Expr Nat}
    {c : CptI} (hc : ProbeCpt c) (hne : c ≠ .bot) :
    LRTermDSubKClosedCore E n Γ M M' A c ↔
      (∃ l, WhRedPiKClosed E A (.sort l)) ∧ LRTypeINPiKClosed E n Γ M M' c := by
  cases hc with
  | bot => exact (hne rfl).elim
  | sort => exact lrTermDSubKClosedCore_sort_iff Γ M M' A
  | piBotNil =>
      rw [lrTermDSubKClosedCore_pi_iff]
      constructor
      · rintro ⟨hl, A₁, B₁, A₂, B₂, _, h1, h2, ⟨hΓ₁⟩, ⟨hcA⟩, ⟨hcB⟩, _, _⟩
        exact ⟨hl, .pi h1 h2 hΓ₁ hcA hcB (.bot Γ A₁ A₂) (fun _ hs => (List.not_mem_nil _ hs).elim)⟩
      · rintro ⟨hl, hpi⟩
        cases hpi with
        | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h1 h2 hΓ₁ hcA hcB _ _ =>
            exact ⟨hl, A₁, B₁, A₂, B₂, .zero, h1, h2, ⟨hΓ₁⟩, ⟨hcA⟩, ⟨hcB⟩,
              by rw [lrTermDSubKClosedCore_bot_iff]; trivial,
              fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- **Exact Equivalence of `LRTermDSubKClosed` at `A = .sort w` and `LRTypeINPiKClosed` Across
    ALL `ProbeCpt` Compacts (`lrTermDSubKClosed_probe_sort_iff`):** -/
theorem lrTermDSubKClosed_probe_sort_iff {Γ : LCtx} {M M' : Expr Nat} {w : Level}
    {c : CptI} (hc : ProbeCpt c) :
    LRTermDSubKClosed E n Γ M M' (.sort w) c ↔ LRTypeINPiKClosed E n Γ M M' c := by
  cases hc with
  | bot =>
      constructor
      · intro _; exact .bot Γ M M'
      · intro _; exact Or.inr (by rw [lrTermDSubKClosedCore_bot_iff]; trivial)
  | sort =>
      constructor
      · rintro (hP | hC)
        · exact (not_isPropTyI_sort E n Γ w hP).elim
        · exact ((lrTermDSubKClosedCore_probe_nonbot_iff .sort (by intro h; cases h)).mp hC).2
      · intro hlr
        exact Or.inr ((lrTermDSubKClosedCore_probe_nonbot_iff .sort (by intro h; cases h)).mpr
          ⟨⟨w, .refl _⟩, hlr⟩)
  | piBotNil =>
      constructor
      · rintro (hP | hC)
        · exact (not_isPropTyI_sort E n Γ w hP).elim
        · exact ((lrTermDSubKClosedCore_probe_nonbot_iff .piBotNil (by intro h; cases h)).mp hC).2
      · intro hlr
        exact Or.inr ((lrTermDSubKClosedCore_probe_nonbot_iff .piBotNil (by intro h; cases h)).mpr
          ⟨⟨w, .refl _⟩, hlr⟩)

/-- Projecting `LRTermDSubKClosedCore` on `ProbeCpt` to `LRTypeINPiKClosed`. -/
theorem lrTypeINPiKClosed_of_lrTermDSubKClosedCore_probe {Γ : LCtx} {M M' A : Expr Nat}
    {c : CptI} (hc : ProbeCpt c) (h : LRTermDSubKClosedCore E n Γ M M' A c) :
    LRTypeINPiKClosed E n Γ M M' c := by
  cases hc with
  | bot => exact .bot Γ M M'
  | sort => exact ((lrTermDSubKClosedCore_probe_nonbot_iff .sort (by intro h0; cases h0)).mp h).2
  | piBotNil => exact ((lrTermDSubKClosedCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)).mp h).2

/-- Reverse adequacy on `ProbeCpt` for `LRTermDSubKClosedCore`. -/
theorem approxDIK_of_lrTermDSubKClosedCore_probe (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c) (h : LRTermDSubKClosedCore E n Γ M M' A c) :
    ApproxDIK E EnvI.bot M c ∧ ApproxDIK E EnvI.bot M' c :=
  approxDIK_of_lrTypeINPiKClosed_botPiCpt hW (botPiCpt_of_probeCpt hc)
    (lrTypeINPiKClosed_of_lrTermDSubKClosedCore_probe hc h)

/-- Weak-head expansion of `LRTermDSubKClosedCore` on `ProbeCpt`. -/
theorem lrTermDSubKClosedCore_whRedPiKClosed_expand_probe {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRedPiKClosed E M X) (hX' : WhRedPiKClosed E M' X')
    {c : CptI} (hc : ProbeCpt c) (h : LRTermDSubKClosedCore E n Γ X X' A c) :
    LRTermDSubKClosedCore E n Γ M M' A c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h ⊢
      exact ⟨h.1, lrTypeINPiKClosed_expand hX hX' h.2⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h ⊢
      exact ⟨h.1, lrTypeINPiKClosed_expand hX hX' h.2⟩

theorem lrTermDSubKClosed_whRedPiKClosed_expand_probe {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRedPiKClosed E M X) (hX' : WhRedPiKClosed E M' X')
    {c : CptI} (hc : ProbeCpt c) (h : LRTermDSubKClosed E n Γ X X' A c) :
    LRTermDSubKClosed E n Γ M M' A c := by
  rcases h with hP | hC
  · exact Or.inl hP
  · exact Or.inr (lrTermDSubKClosedCore_whRedPiKClosed_expand_probe hX hX' hc hC)

theorem lrTermDSubKClosedBi_whRedPiKClosed_expand (hW : EnvWfT E)
    {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRedPiKClosed E M X) (hX' : WhRedPiKClosed E M' X')
    (h : LRTermDSubKClosedBi E n Γ X X' A) :
    LRTermDSubKClosedBi E n Γ M M' A := by
  intro c hc hor
  have hor' : ApproxDIK E EnvI.bot X c ∨ ApproxDIK E EnvI.bot X' c :=
    hor.elim (fun hM => Or.inl ((semEqDIK_whRedPiKClosed hW hX c).mp hM))
             (fun hM' => Or.inr ((semEqDIK_whRedPiKClosed hW hX' c).mp hM'))
  exact lrTermDSubKClosed_whRedPiKClosed_expand_probe hX hX' hc (h c hc hor')

theorem lrTermDSubKClosedBi_of_whStepPiKClosed (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat}
    (hs : WhStepPiKClosed E M M') (hdiag : LRTermDSubKClosedBi E n Γ M' M' A) :
    LRTermDSubKClosedBi E n Γ M M' A :=
  lrTermDSubKClosedBi_whRedPiKClosed_expand hW (.step hs (.refl _)) (.refl _) hdiag

/-- Unconditional symmetry of `LRTermDSubKClosedCore` on `ProbeCpt`. -/
theorem lrTermDSubKClosedCore_probe_symm (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c) (h : LRTermDSubKClosedCore E n Γ M M' A c) :
    LRTermDSubKClosedCore E n Γ M' M A c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h ⊢
      exact ⟨h.1, lrTypeINPiKClosed_symm hW h.2⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h ⊢
      exact ⟨h.1, lrTypeINPiKClosed_symm hW h.2⟩

theorem lrTermDSubKClosed_probe_symm (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c) (h : LRTermDSubKClosed E n Γ M M' A c) :
    LRTermDSubKClosed E n Γ M' M A c :=
  h.elim Or.inl (fun hC => Or.inr (lrTermDSubKClosedCore_probe_symm hW hc hC))

theorem lrTermDSubKClosedBi_symm (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat}
    (h : LRTermDSubKClosedBi E n Γ M M' A) :
    LRTermDSubKClosedBi E n Γ M' M A :=
  fun c hc hor => lrTermDSubKClosed_probe_symm hW hc (h c hc hor.symm)

/-- Unconditional transitivity of `LRTermDSubKClosedCore` on `ProbeCpt`. -/
theorem lrTermDSubKClosedCore_probe_trans (hW : EnvWfT E)
    {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c)
    (h₁₂ : LRTermDSubKClosedCore E n Γ M₁ M₂ A c)
    (h₂₃ : LRTermDSubKClosedCore E n Γ M₂ M₃ A c) :
    LRTermDSubKClosedCore E n Γ M₁ M₃ A c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h₁₂ h₂₃ ⊢
      exact ⟨h₁₂.1, lrTypeINPiKClosed_trans_of_envWfT hW h₁₂.2 h₂₃.2⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h₁₂ h₂₃ ⊢
      exact ⟨h₁₂.1, lrTypeINPiKClosed_trans_of_envWfT hW h₁₂.2 h₂₃.2⟩

theorem lrTermDSubKClosed_probe_trans (hW : EnvWfT E)
    {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c)
    (h₁₂ : LRTermDSubKClosed E n Γ M₁ M₂ A c)
    (h₂₃ : LRTermDSubKClosed E n Γ M₂ M₃ A c) :
    LRTermDSubKClosed E n Γ M₁ M₃ A c := by
  rcases h₁₂ with hP | hC₁₂
  · exact Or.inl hP
  · rcases h₂₃ with hP | hC₂₃
    · exact Or.inl hP
    · exact Or.inr (lrTermDSubKClosedCore_probe_trans hW hc hC₁₂ hC₂₃)

theorem lrTermDSubKClosedBi_trans (hW : EnvWfT E)
    {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat}
    (h₁₂ : LRTermDSubKClosedBi E n Γ M₁ M₂ A)
    (h₂₃ : LRTermDSubKClosedBi E n Γ M₂ M₃ A) :
    LRTermDSubKClosedBi E n Γ M₁ M₃ A := by
  intro c hc hor
  rcases hor with h₁ | h₃
  · rcases h₁₂ c hc (Or.inl h₁) with hP | hC₁₂
    · exact Or.inl hP
    · have h₂ : ApproxDIK E EnvI.bot M₂ c :=
        (approxDIK_of_lrTermDSubKClosedCore_probe hW hc hC₁₂).2
      exact lrTermDSubKClosed_probe_trans hW hc (Or.inr hC₁₂) (h₂₃ c hc (Or.inl h₂))
  · rcases h₂₃ c hc (Or.inr h₃) with hP | hC₂₃
    · exact Or.inl hP
    · have h₂ : ApproxDIK E EnvI.bot M₂ c :=
        (approxDIK_of_lrTermDSubKClosedCore_probe hW hc hC₂₃).1
      exact lrTermDSubKClosed_probe_trans hW hc (h₁₂ c hc (Or.inr h₂)) (Or.inr hC₂₃)

/-! ### §5.4. Unconditional All-Cutoff Weakening and `⊥`-Approximated Assumption/`let`-Substitution
for `LRTermDSubKClosed` and `LRTermDSubKClosedBi` on `ProbeCpt` -/

/-- **Unconditional All-Cutoff Weakening (`lift k 1` for ALL `k : Nat`, Including `k = 0`) of
    `LRTermDSubKClosedCore` on `ProbeCpt` (`lrTermDSubKClosedCore_weaken_probe`):** -/
theorem lrTermDSubKClosedCore_weaken_probe (hcl : EnvClosed E)
    {Γ : LCtx} {M M' A : Expr Nat} (d : LocalDecl) (k : Nat)
    (hΓ' : CtxWfT E n (insertAt d k Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCore E n Γ M M' A c) :
    LRTermDSubKClosedCore E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosed_lift_of_envClosed hcl hl k⟩,
        lrTypeINPiKClosed_weaken_botPiCpt hcl .sort d k hΓ' hlr⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosed_lift_of_envClosed hcl hl k⟩,
        lrTypeINPiKClosed_weaken_botPiCpt hcl botPiCpt_pi_bot_nil d k hΓ' hlr⟩

/-- **Unconditional All-Cutoff Weakening of `LRTermDSubKClosed` on `ProbeCpt`
    (`lrTermDSubKClosed_weaken_probe`):** -/
theorem lrTermDSubKClosed_weaken_probe (hcl : EnvClosed E)
    {Γ : LCtx} {M M' A : Expr Nat} (d : LocalDecl) (k : Nat)
    (hΓ' : CtxWfT E n (insertAt d k Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosed E n Γ M M' A c) :
    LRTermDSubKClosed E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) c := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_weaken hcl d (c := k) hP)
  · exact Or.inr (lrTermDSubKClosedCore_weaken_probe hcl d k hΓ' hc hC)

theorem lrTermDSubKClosed_weaken0_probe (hcl : EnvClosed E)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {M M' A : Expr Nat} {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosed E n Γ M M' A c) :
    LRTermDSubKClosed E n (d :: Γ) (lift 0 1 M) (lift 0 1 M') (lift 0 1 A) c :=
  lrTermDSubKClosed_weaken_probe hcl d 0 hΓ' hc h

/-- **Unconditional All-Cutoff Weakening of `LRTermDSubKClosedBi` (`lrTermDSubKClosedBi_weaken`):** -/
theorem lrTermDSubKClosedBi_weaken (hcl : EnvClosed E)
    {Γ : LCtx} {M M' A : Expr Nat} (d : LocalDecl) (k : Nat)
    (hΓ' : CtxWfT E n (insertAt d k Γ))
    (h : LRTermDSubKClosedBi E n Γ M M' A) :
    LRTermDSubKClosedBi E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) := by
  intro c hc hor
  have hor₀ : ApproxDIK E EnvI.bot M c ∨ ApproxDIK E EnvI.bot M' c :=
    hor.elim (fun hL => Or.inl ((approxDIK_bot_lift_iff E k M c).mp hL))
             (fun hR => Or.inr ((approxDIK_bot_lift_iff E k M' c).mp hR))
  exact lrTermDSubKClosed_weaken_probe hcl d k hΓ' hc (h c hc hor₀)

theorem lrTermDSubKClosedBi_weaken0 (hcl : EnvClosed E)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {M M' A : Expr Nat}
    (h : LRTermDSubKClosedBi E n Γ M M' A) :
    LRTermDSubKClosedBi E n (d :: Γ) (lift 0 1 M) (lift 0 1 M') (lift 0 1 A) :=
  lrTermDSubKClosedBi_weaken hcl d 0 hΓ' h

/-- **Unconditional Assumption-Substitution Stability of `LRTermDSubKClosedCore` on `ProbeCpt`
    for `⊥`-Approximated Substituents (`lrTermDSubKClosedCore_subst_probe`):** -/
theorem lrTermDSubKClosedCore_subst_probe (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {v : Expr Nat} (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot) (t : Expr Nat)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove v j Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCore E n Γ M M' A c) :
    LRTermDSubKClosedCore E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosed_instantiate_of_botApprox hcl hv hl j⟩,
        lrTypeINPiKClosed_subst_botPiCpt hcl hinst hv t .sort hget hvty hΓ' hlr⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosed_instantiate_of_botApprox hcl hv hl j⟩,
        lrTypeINPiKClosed_subst_botPiCpt hcl hinst hv t botPiCpt_pi_bot_nil hget hvty hΓ' hlr⟩

theorem lrTermDSubKClosed_subst_probe (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {v : Expr Nat} (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot) (t : Expr Nat)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove v j Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosed E n Γ M M' A c) :
    LRTermDSubKClosed E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) c := by
  rcases h with hP | hC
  · obtain ⟨⟨hA⟩, _⟩ := hP
    exact Or.inl (isPropTyI_of_hasTyT_sort_zero hSort (hasTyT_substS hcl hinst v t hA hget hvty))
  · exact Or.inr (lrTermDSubKClosedCore_subst_probe hcl hinst hv t hget hvty hΓ' hc hC)

theorem lrTermDSubKClosed_subst0_probe (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t : Expr Nat}
    (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    (hvty : HasTyT E n Γ v t)
    {M M' A : Expr Nat} {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosed E n (.assumption t :: Γ) M M' A c) :
    LRTermDSubKClosed E n Γ (instantiate0 v M) (instantiate0 v M') (instantiate0 v A) c := by
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  have h0 := lrTermDSubKClosed_subst_probe
    (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hSort hv t
    (Γ := .assumption t :: Γ) (j := 0) hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hvty)
    (by simpa only [substRemove_zero_cons] using hΓ) hc h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- **Unconditional Assumption-Substitution of `LRTermDSubKClosedBi` for `⊥`-Approximated
    Substituents (`lrTermDSubKClosedBi_subst0`):** -/
theorem lrTermDSubKClosedBi_subst0 (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t : Expr Nat}
    (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    (hvty : HasTyT E n Γ v t)
    {M M' A : Expr Nat}
    (h : LRTermDSubKClosedBi E n (.assumption t :: Γ) M M' A) :
    LRTermDSubKClosedBi E n Γ (instantiate0 v M) (instantiate0 v M') (instantiate0 v A) := by
  intro c hc hor
  have hor₀ : ApproxDIK E EnvI.bot M c ∨ ApproxDIK E EnvI.bot M' c :=
    hor.elim (fun hL => Or.inl ((approxDIK_bot_instantiate0_iff hv M c).mp hL))
             (fun hR => Or.inr ((approxDIK_bot_instantiate0_iff hv M' c).mp hR))
  exact lrTermDSubKClosed_subst0_probe hW hSort hΓ hv hvty hc (h c hc hor₀)

/-- **Unconditional `let`-Substitution Stability of `LRTermDSubKClosedCore` on `ProbeCpt`
    for `⊥`-Approximated Let-Values (`lrTermDSubKClosedCore_substLet_probe`):** -/
theorem lrTermDSubKClosedCore_substLet_probe (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {w0 : Expr Nat} (hw0 : ∀ u, ApproxDIK E EnvI.bot w0 u → u = .bot) (t : Expr Nat)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.letBinding t w0))
    (hvty : HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove w0 j Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCore E n Γ M M' A c) :
    LRTermDSubKClosedCore E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) M) (instantiate j (lift 0 j w0) M')
      (instantiate j (lift 0 j w0) A) c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosed_instantiate_of_botApprox hcl hw0 hl j⟩,
        lrTypeINPiKClosed_substLet_botPiCpt hcl hinst hw0 t .sort hget hvty hΓ' hlr⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosed_instantiate_of_botApprox hcl hw0 hl j⟩,
        lrTypeINPiKClosed_substLet_botPiCpt hcl hinst hw0 t botPiCpt_pi_bot_nil hget hvty hΓ' hlr⟩

theorem lrTermDSubKClosed_substLet_probe (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {w0 : Expr Nat} (hw0 : ∀ u, ApproxDIK E EnvI.bot w0 u → u = .bot) (t : Expr Nat)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.letBinding t w0))
    (hvty : HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove w0 j Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosed E n Γ M M' A c) :
    LRTermDSubKClosed E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) M) (instantiate j (lift 0 j w0) M')
      (instantiate j (lift 0 j w0) A) c := by
  rcases h with hP | hC
  · obtain ⟨⟨hA⟩, _⟩ := hP
    exact Or.inl (isPropTyI_of_hasTyT_sort_zero hSort (hasTyT_substLetS hcl hinst t w0 hA hget hvty))
  · exact Or.inr (lrTermDSubKClosedCore_substLet_probe hcl hinst hw0 t hget hvty hΓ' hc hC)

theorem lrTermDSubKClosed_substLet0_probe (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 : Expr Nat}
    (hw0 : ∀ u, ApproxDIK E EnvI.bot w0 u → u = .bot)
    (hw0ty : HasTyT E n Γ w0 t)
    {M M' A : Expr Nat} {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosed E n (.letBinding t w0 :: Γ) M M' A c) :
    LRTermDSubKClosed E n Γ (instantiate0 w0 M) (instantiate0 w0 M') (instantiate0 w0 A) c := by
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have h0 := lrTermDSubKClosed_substLet_probe
    (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hSort hw0 t
    (Γ := .letBinding t w0 :: Γ) (j := 0) hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hw0ty)
    (by simpa only [substRemove_zero_cons] using hΓ) hc h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- **Unconditional `let`-Substitution of `LRTermDSubKClosedBi` for `⊥`-Approximated
    Let-Values (`lrTermDSubKClosedBi_substLet0`):** -/
theorem lrTermDSubKClosedBi_substLet0 (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 : Expr Nat}
    (hw0 : ∀ u, ApproxDIK E EnvI.bot w0 u → u = .bot)
    (hw0ty : HasTyT E n Γ w0 t)
    {M M' A : Expr Nat}
    (h : LRTermDSubKClosedBi E n (.letBinding t w0 :: Γ) M M' A) :
    LRTermDSubKClosedBi E n Γ (instantiate0 w0 M) (instantiate0 w0 M') (instantiate0 w0 A) := by
  intro c hc hor
  have hor₀ : ApproxDIK E EnvI.bot M c ∨ ApproxDIK E EnvI.bot M' c :=
    hor.elim (fun hL => Or.inl ((approxDIK_bot_instantiate0_iff hw0 M c).mp hL))
             (fun hR => Or.inr ((approxDIK_bot_instantiate0_iff hw0 M' c).mp hR))
  exact lrTermDSubKClosed_substLet0_probe hW hSort hΓ hw0 hw0ty hc (h c hc hor₀)

/-- Direct closure of `ConvT.beta` in `LRTermDSubKClosedBi` for any `⊥`-approximated argument `a`
    from the body induction hypothesis `ih_b : LRTermDSubKClosedBi E n (.assumption A :: Γ) b b B`. -/
theorem lrTermDSubKClosedBi_beta_of_botApprox (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A b a B : Expr Nat}
    (ha_bot : ∀ u, ApproxDIK E EnvI.bot a u → u = .bot)
    (ha_ty : HasTyT E n Γ a A)
    (ih_b : LRTermDSubKClosedBi E n (.assumption A :: Γ) b b B) :
    LRTermDSubKClosedBi E n Γ (.app (.lam A b) a) (instantiate0 a b) (instantiate0 a B) :=
  lrTermDSubKClosedBi_of_whStepPiKClosed hW (.of_whStep (.beta A b a))
    (lrTermDSubKClosedBi_subst0 hW hSort hΓ ha_bot ha_ty ih_b)

/-- Direct closure of `ConvT.zeta` in `LRTermDSubKClosedBi` for any `⊥`-approximated let-value `v`
    from the body induction hypothesis `ih_b : LRTermDSubKClosedBi E n (.letBinding A v :: Γ) b b B`. -/
theorem lrTermDSubKClosedBi_zeta_of_botApprox (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A v b B : Expr Nat}
    (hv_bot : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    (hv_ty : HasTyT E n Γ v A)
    (ih_b : LRTermDSubKClosedBi E n (.letBinding A v :: Γ) b b B) :
    LRTermDSubKClosedBi E n Γ (.letE A v b) (instantiate0 v b) (instantiate0 v B) :=
  lrTermDSubKClosedBi_of_whStepPiKClosed hW (.of_whStep (.zeta A v b))
    (lrTermDSubKClosedBi_substLet0 hW hSort hΓ hv_bot hv_ty ih_b)

/-- Direct closure of `HasTyT.letE` in `LRTermDSubKClosedBi` for any `⊥`-approximated let-value `v`
    from the body induction hypothesis `ih_b : LRTermDSubKClosedBi E n (.letBinding A v :: Γ) b b B`. -/
theorem lrTermDSubKClosedBi_letE_diag_of_botApprox (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A v b B : Expr Nat}
    (hv_bot : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    (hv_ty : HasTyT E n Γ v A)
    (ih_b : LRTermDSubKClosedBi E n (.letBinding A v :: Γ) b b B) :
    LRTermDSubKClosedBi E n Γ (.letE A v b) (.letE A v b) (instantiate0 v B) :=
  have hstep : WhRedPiKClosed E (.letE A v b) (instantiate0 v b) :=
    .step (.of_whStep (.zeta A v b)) (.refl _)
  lrTermDSubKClosedBi_whRedPiKClosed_expand hW hstep hstep
    (lrTermDSubKClosedBi_substLet0 hW hSort hΓ hv_bot hv_ty ih_b)

/-! ## §6. Context-Aware Deterministic K-Closed Readback `WhStepPiKClosedCtx` / `WhRedPiKClosedCtx`
Over `ctxEnvDIK` and Unconditional `let`-Substitution -/

/-! ### §6.1. `WhStepPiKClosedCtx` and `WhRedPiKClosedCtx`: Unifying `WhStep`, `zetaLocal`, and
Fieldful `iotaKClosedCtx` with Exact Determinism and `ctxEnvDIK` Model Invariance -/

/-- **Context-Aware Closed-Field Deterministic K-Aware Weak-Head Step (`WhStepPiKClosedCtx E Γ a b`):**
    Combines:
    1. `of_whStep`: standard weak-head reduction (`beta`, `zeta`, `delta`, `lit`, `iota`),
    2. `zetaLocal`: context let-unfolding `lookupValue Γ i = some v` (repairing `W-ZETALOCAL`),
    3. `iotaKClosedCtx`: proposition-major reduction for single-constructor `Prop` inductives with
       canonical closed fields `w.fields = List.replicate w.fields.length botClosedExpr` and
       context-aware non-constructor guard `∀ args, ¬ ApproxDIK E (ctxEnvDIK E Γ) x (.spine w.ctorRef args)`
       (repairing both 0-field and fieldful `W-K`),
    4. `appHead`: head congruence on applications. -/
inductive WhStepPiKClosedCtx (E : ResolvedEnv) (Γ : LCtx) : Expr Nat → Expr Nat → Prop
  | of_whStep {a b : Expr Nat} (h : WhStep E a b) : WhStepPiKClosedCtx E Γ a b
  | zetaLocal {i : Nat} {v : Expr Nat} (h : lookupValue Γ i = some v) :
      WhStepPiKClosedCtx E Γ (.bvar i) v
  | iotaKClosedCtx (w : IotaWitnessS E) (x : Expr Nat)
      (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
      (hflds : w.fields = List.replicate w.fields.length botClosedExpr)
      (hx : ∀ args, ¬ ApproxDIK E (ctxEnvDIK E Γ) x (.spine w.ctorRef args)) :
      WhStepPiKClosedCtx E Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w)
  | appHead {f f' arg : Expr Nat} (h : WhStepPiKClosedCtx E Γ f f') :
      WhStepPiKClosedCtx E Γ (.app f arg) (.app f' arg)

/-- Reflexive-transitive closure of `WhStepPiKClosedCtx E Γ`. -/
inductive WhRedPiKClosedCtx (E : ResolvedEnv) (Γ : LCtx) : Expr Nat → Expr Nat → Prop
  | refl (a : Expr Nat) : WhRedPiKClosedCtx E Γ a a
  | step {a b c : Expr Nat} (hs : WhStepPiKClosedCtx E Γ a b) (hr : WhRedPiKClosedCtx E Γ b c) :
      WhRedPiKClosedCtx E Γ a c

theorem whRedPiKClosedCtx_trans {E : ResolvedEnv} {Γ : LCtx} {a b c : Expr Nat}
    (h₁ : WhRedPiKClosedCtx E Γ a b) (h₂ : WhRedPiKClosedCtx E Γ b c) :
    WhRedPiKClosedCtx E Γ a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem whRedPiKClosedCtx_of_whRed {E : ResolvedEnv} {Γ : LCtx} {a b : Expr Nat}
    (h : WhRed E a b) : WhRedPiKClosedCtx E Γ a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step (.of_whStep hs) ih

theorem whRedPiKClosedCtx_appHead {E : ResolvedEnv} {Γ : LCtx} {f f' arg : Expr Nat}
    (h : WhRedPiKClosedCtx E Γ f f') :
    WhRedPiKClosedCtx E Γ (.app f arg) (.app f' arg) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.appHead hs) ih

/-- **Exact Agreement of `WhStepPiKClosedCtx E Γ` and `WhStepPiKClosed E` on `LetFreeCtx Γ`
    (`whStepPiKClosedCtx_letFree_iff`):** -/
theorem whStepPiKClosedCtx_letFree_iff {E : ResolvedEnv} {Γ : LCtx} (hlf : LetFreeCtx Γ)
    {a b : Expr Nat} :
    WhStepPiKClosedCtx E Γ a b ↔ WhStepPiKClosed E a b := by
  constructor
  · intro h
    induction h with
    | of_whStep hs => exact .of_whStep hs
    | @zetaLocal i _ hval =>
        rw [hlf i] at hval
        exact Option.noConfusion hval
    | iotaKClosedCtx w x hk hflds hx =>
        refine .iotaKClosed w x hk hflds (fun args hsp => hx args ?_)
        exact (approxDIK_ctxEnvDIK_letFree_iff hlf x (.spine w.ctorRef args)).mpr hsp
    | @appHead _ _ _ _ ih => exact .appHead ih
  · intro h
    induction h with
    | of_whStep hs => exact .of_whStep hs
    | iotaKClosed w x hk hflds hx =>
        refine .iotaKClosedCtx w x hk hflds (fun args hsp => hx args ?_)
        exact (approxDIK_ctxEnvDIK_letFree_iff hlf x (.spine w.ctorRef args)).mp hsp
    | @appHead _ _ _ _ ih => exact .appHead ih

theorem whRedPiKClosedCtx_letFree_iff {E : ResolvedEnv} {Γ : LCtx} (hlf : LetFreeCtx Γ)
    {a b : Expr Nat} :
    WhRedPiKClosedCtx E Γ a b ↔ WhRedPiKClosed E a b := by
  constructor
  · intro h
    induction h with
    | refl e => exact .refl e
    | step hs _ ih => exact .step ((whStepPiKClosedCtx_letFree_iff hlf).mp hs) ih
  · intro h
    induction h with
    | refl e => exact .refl e
    | step hs _ ih => exact .step ((whStepPiKClosedCtx_letFree_iff hlf).mpr hs) ih

/-- **Unconditional Model Invariance (`ReadbackModelInv`) of `WhStepPiKClosedCtx` Over
    `ApproxDIK E (ctxEnvDIK E Γ)` Across ALL Contexts `Γ : LCtx`
    (`semEqDIK_ctxEnvDIK_whStepPiKClosedCtx`):**
    Whereas `ReadbackModelInv` fails for `WhStepCK` and `WhStepK` over `ApproxI` and `ApproxDI`,
    every step of `WhStepPiKClosedCtx E Γ` (including `zetaLocal` and fieldful `iotaKClosedCtx`) is
    sound in `ApproxDIK E (ctxEnvDIK E Γ)` under `EnvWfT E` alone! -/
theorem semEqDIK_ctxEnvDIK_whStepPiKClosedCtx {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} {a b : Expr Nat}
    (hs : WhStepPiKClosedCtx E Γ a b) :
    SemEqDIK E (ctxEnvDIK E Γ) a b := by
  induction hs with
  | of_whStep hs₀ =>
      exact semEqDIK_whStep hW hs₀ (ctxEnvDIK E Γ)
  | zetaLocal hval =>
      exact semEqDIK_ctxEnvDIK_zetaLocal E Γ hval
  | iotaKClosedCtx w x hk hflds hx =>
      exact semEqDIK_k_botClosedExpr_of_envWfT w hk hflds x hx
  | @appHead _ _ arg _ ih =>
      exact semEqDIK_app ih (semEqDIK_refl E (ctxEnvDIK E Γ) arg)

/-- Multi-step model invariance of `WhRedPiKClosedCtx` over `ApproxDIK E (ctxEnvDIK E Γ)`. -/
theorem semEqDIK_ctxEnvDIK_whRedPiKClosedCtx {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} {a b : Expr Nat}
    (hr : WhRedPiKClosedCtx E Γ a b) :
    SemEqDIK E (ctxEnvDIK E Γ) a b := by
  induction hr with
  | refl e => exact semEqDIK_refl E (ctxEnvDIK E Γ) e
  | step hs _ ih => exact semEqDIK_trans (semEqDIK_ctxEnvDIK_whStepPiKClosedCtx hW hs) ih

theorem approxDIK_ctxEnvDIK_whRedPiKClosedCtx_back {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} {a b : Expr Nat}
    (hr : WhRedPiKClosedCtx E Γ a b) {c : CptI}
    (hb : ApproxDIK E (ctxEnvDIK E Γ) b c) :
    ApproxDIK E (ctxEnvDIK E Γ) a c :=
  (semEqDIK_ctxEnvDIK_whRedPiKClosedCtx hW hr c).mpr hb

theorem approxDIK_ctxEnvDIK_sort_of_whRedPiKClosedCtx {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} {a : Expr Nat} {l : Level}
    (hr : WhRedPiKClosedCtx E Γ a (.sort l)) :
    ApproxDIK E (ctxEnvDIK E Γ) a .sort :=
  approxDIK_ctxEnvDIK_whRedPiKClosedCtx_back hW hr (.sort (ctxEnvDIK E Γ) l)

theorem whStepPiKClosedCtx_sort_false {E : ResolvedEnv} {Γ : LCtx} {l : Level} {e : Expr Nat}
    (h : WhStepPiKClosedCtx E Γ (.sort l) e) : False := by
  generalize ha : (Expr.sort l : Expr Nat) = a at h
  cases h with
  | of_whStep hs => subst ha; exact whStep_sort_false hs
  | zetaLocal _ => exact Expr.noConfusion ha
  | iotaKClosedCtx w x _ _ _ =>
      have hsp := congrArg appsSpine ha
      unfold recCall at hsp
      rw [appsSpine_foldApps_const] at hsp
      exact Expr.noConfusion (congrArg Prod.fst hsp)
  | appHead _ => exact Expr.noConfusion ha

theorem whStepPiKClosedCtx_pi_false {E : ResolvedEnv} {Γ : LCtx} {A B e : Expr Nat}
    (h : WhStepPiKClosedCtx E Γ (.pi A B) e) : False := by
  generalize ha : (Expr.pi A B : Expr Nat) = a at h
  cases h with
  | of_whStep hs => subst ha; exact whStep_pi_false hs
  | zetaLocal _ => exact Expr.noConfusion ha
  | iotaKClosedCtx w x _ _ _ =>
      have hsp := congrArg appsSpine ha
      unfold recCall at hsp
      rw [appsSpine_foldApps_const] at hsp
      exact Expr.noConfusion (congrArg Prod.fst hsp)
  | appHead _ => exact Expr.noConfusion ha

theorem whStepPiKClosedCtx_lam_false {E : ResolvedEnv} {Γ : LCtx} {A b e : Expr Nat}
    (h : WhStepPiKClosedCtx E Γ (.lam A b) e) : False := by
  generalize ha : (Expr.lam A b : Expr Nat) = a at h
  cases h with
  | of_whStep hs => subst ha; exact whStep_lam_false hs
  | zetaLocal _ => exact Expr.noConfusion ha
  | iotaKClosedCtx w x _ _ _ =>
      have hsp := congrArg appsSpine ha
      unfold recCall at hsp
      rw [appsSpine_foldApps_const] at hsp
      exact Expr.noConfusion (congrArg Prod.fst hsp)
  | appHead _ => exact Expr.noConfusion ha

theorem whRedPiKClosedCtx_sort_eq {E : ResolvedEnv} {Γ : LCtx} {l : Level} {e : Expr Nat}
    (h : WhRedPiKClosedCtx E Γ (.sort l) e) : e = .sort l := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStepPiKClosedCtx_sort_false hs).elim

theorem whRedPiKClosedCtx_pi_eq {E : ResolvedEnv} {Γ : LCtx} {A B e : Expr Nat}
    (h : WhRedPiKClosedCtx E Γ (.pi A B) e) : e = .pi A B := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStepPiKClosedCtx_pi_false hs).elim

private theorem list_eq_nil_or_snoc {α : Type _} :
    ∀ (xs : List α), xs = [] ∨ ∃ pre x, xs = pre ++ [x]
  | [] => Or.inl rfl
  | x :: xs => by
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, y, rfl⟩
      · exact Or.inr ⟨[], x, rfl⟩
      · exact Or.inr ⟨x :: pre, y, rfl⟩

theorem not_whStepPiKClosedCtx_recursor_prefix {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} (w : IotaWitnessS E) (ls : List Level) (xs : List (Expr Nat))
    (hlen : xs.length ≤ w.preMajor.length) {e : Expr Nat}
    (hs : WhStepPiKClosedCtx E Γ (foldApps (.const w.recRef ls) xs) e) : False := by
  have key : ∀ {f e : Expr Nat} (ys : List (Expr Nat)),
      WhStepPiKClosedCtx E Γ f e → f = foldApps (.const w.recRef ls) ys →
      ys.length ≤ w.preMajor.length → False := by
    intro f e ys hstep
    induction hstep generalizing ys with
    | of_whStep hs₀ =>
        intro hf hlen'
        subst hf
        exact not_whStep_recursor_prefix hW w ls ys hlen' hs₀
    | zetaLocal _ =>
        intro hf _
        have hsp := congrArg appsSpine hf
        rw [appsSpine_foldApps_const] at hsp
        exact Expr.noConfusion (congrArg Prod.fst hsp)
    | iotaKClosedCtx w' x _ _ _ =>
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

theorem whStep_and_whStepPiKClosedCtx_det {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} {a b c : Expr Nat}
    (h₁ : WhStep E a b) (h₂ : WhStepPiKClosedCtx E Γ a c) : b = c := by
  induction h₂ generalizing b with
  | of_whStep hs₂ =>
      exact whDet_of_envWfT hW h₁ hs₂
  | zetaLocal _ =>
      exact (whStep_bvar_false h₁).elim
  | iotaKClosedCtx w₂ x₂ hk₂ _ hx₂ =>
      have hx_bot : ∀ args, ¬ ApproxDIK E EnvI.bot x₂ (.spine w₂.ctorRef args) :=
        fun args hsp => hx₂ args (approxDIK_of_bot_to_ctxEnvDIK Γ hsp)
      exact (not_whStep_and_iotaK hW w₂ x₂ hk₂ hx_bot h₁).elim
  | @appHead f f' arg hf₂ ih =>
      generalize ha : Expr.app f arg = a₀ at h₁
      cases h₁ with
      | beta =>
          injection ha with hfEq _
          subst hfEq
          exact (whStepPiKClosedCtx_lam_false hf₂).elim
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
              exact (not_whStepPiKClosedCtx_recursor_prefix hW w₁ w₁.ls w₁.preMajor
                (Nat.le_refl _) hf₂).elim
      | appHead hs₁ =>
          injection ha with hfEq hargEq
          subst hfEq; subst hargEq
          exact congrArg (fun t => Expr.app t arg) (ih hs₁)

/-- **Exact Single-Step Determinism of `WhStepPiKClosedCtx` (`whDetPiKClosedCtx_of_envWfT`):**
    At every `EnvWfT E` and every context `Γ : LCtx`, `WhStepPiKClosedCtx E Γ` is 100%
    single-step deterministic! -/
theorem whDetPiKClosedCtx_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} {a b c : Expr Nat}
    (h₁ : WhStepPiKClosedCtx E Γ a b) (h₂ : WhStepPiKClosedCtx E Γ a c) :
    b = c := by
  induction h₁ generalizing c with
  | of_whStep hs₁ =>
      exact whStep_and_whStepPiKClosedCtx_det hW hs₁ h₂
  | @zetaLocal i v₁ hval₁ =>
      generalize ha : (Expr.bvar i : Expr Nat) = a₀ at h₂
      cases h₂ with
      | of_whStep hs₂ =>
          subst ha
          exact (whStep_bvar_false hs₂).elim
      | @zetaLocal j v₂ hval₂ =>
          injection ha with hij
          subst hij
          exact Option.some.inj (hval₁.symm.trans hval₂)
      | iotaKClosedCtx w₂ x₂ _ _ _ =>
          unfold recCall at ha
          rw [foldApps_snoc] at ha
          exact Expr.noConfusion ha
      | appHead _ =>
          exact Expr.noConfusion ha
  | iotaKClosedCtx w₁ x₁ hk₁ hflds₁ hx₁ =>
      generalize ha : recCall (.const w₁.recRef w₁.ls) w₁.preMajor x₁ = a₀ at h₂
      cases h₂ with
      | of_whStep hs₂ =>
          subst ha
          have hx_bot : ∀ args, ¬ ApproxDIK E EnvI.bot x₁ (.spine w₁.ctorRef args) :=
            fun args hsp => hx₁ args (approxDIK_of_bot_to_ctxEnvDIK Γ hsp)
          exact (not_whStep_and_iotaK hW w₁ x₁ hk₁ hx_bot hs₂).elim
      | zetaLocal _ =>
          unfold recCall at ha
          rw [foldApps_snoc] at ha
          exact Expr.noConfusion ha
      | iotaKClosedCtx w₂ x₂ _ hflds₂ _ =>
          exact iotaKClosed_det w₁ w₂ x₁ x₂ hk₁ hflds₁ hflds₂ ha
      | appHead hf₂ =>
          unfold recCall at ha
          rw [foldApps_snoc] at ha
          injection ha with hfEq _
          subst hfEq
          exact (not_whStepPiKClosedCtx_recursor_prefix hW w₁ w₁.ls w₁.preMajor
            (Nat.le_refl _) hf₂).elim
  | @appHead f f' arg hf₁ ih =>
      generalize ha : Expr.app f arg = a₀ at h₂
      cases h₂ with
      | of_whStep hs₂ =>
          subst ha
          exact (whStep_and_whStepPiKClosedCtx_det hW hs₂ (.appHead hf₁)).symm
      | zetaLocal _ =>
          exact Expr.noConfusion ha
      | iotaKClosedCtx w₂ x₂ _ _ _ =>
          unfold recCall at ha
          rw [foldApps_snoc] at ha
          injection ha with hfEq _
          subst hfEq
          exact (not_whStepPiKClosedCtx_recursor_prefix hW w₂ w₂.ls w₂.preMajor
            (Nat.le_refl _) hf₁).elim
      | appHead hf₂ =>
          injection ha with hfEq hargEq
          subst hfEq; subst hargEq
          exact congrArg (fun t => Expr.app t arg) (ih hf₂)

/-- Normal forms of `WhStepPiKClosedCtx E Γ`. -/
def WhNormalPiKClosedCtx (E : ResolvedEnv) (Γ : LCtx) (a : Expr Nat) : Prop :=
  ∀ b, ¬ WhStepPiKClosedCtx E Γ a b

theorem whNormalPiKClosedCtx_sort (E : ResolvedEnv) (Γ : LCtx) (l : Level) :
    WhNormalPiKClosedCtx E Γ (.sort l) :=
  fun _ h => whStepPiKClosedCtx_sort_false h

theorem whNormalPiKClosedCtx_pi (E : ResolvedEnv) (Γ : LCtx) (A B : Expr Nat) :
    WhNormalPiKClosedCtx E Γ (.pi A B) :=
  fun _ h => whStepPiKClosedCtx_pi_false h

theorem whNormalPiKClosedCtx_lam (E : ResolvedEnv) (Γ : LCtx) (A b : Expr Nat) :
    WhNormalPiKClosedCtx E Γ (.lam A b) :=
  fun _ h => whStepPiKClosedCtx_lam_false h

theorem whRedPiKClosedCtx_of_normal {E : ResolvedEnv} {Γ : LCtx} {X Y : Expr Nat}
    (hX : WhNormalPiKClosedCtx E Γ X) (h : WhRedPiKClosedCtx E Γ X Y) : Y = X := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hX _ hs).elim

theorem whRedPiKClosedCtx_normal_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} {a X Y : Expr Nat}
    (h₁ : WhRedPiKClosedCtx E Γ a X) (hX : WhNormalPiKClosedCtx E Γ X)
    (h₂ : WhRedPiKClosedCtx E Γ a Y) (hY : WhNormalPiKClosedCtx E Γ Y) : X = Y := by
  induction h₁ with
  | refl => exact (whRedPiKClosedCtx_of_normal hX h₂).symm
  | step hs₁ _ ih =>
      cases h₂ with
      | refl => exact (hY _ hs₁).elim
      | step hs₂ hr₂ =>
          have e := whDetPiKClosedCtx_of_envWfT hW hs₁ hs₂
          subst e
          exact ih hX hr₂

theorem whRedPiKClosedCtx_pi_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} {a A₁ B₁ A₂ B₂ : Expr Nat}
    (h₁ : WhRedPiKClosedCtx E Γ a (.pi A₁ B₁))
    (h₂ : WhRedPiKClosedCtx E Γ a (.pi A₂ B₂)) :
    A₁ = A₂ ∧ B₁ = B₂ := by
  have e := whRedPiKClosedCtx_normal_unique_of_envWfT hW
    h₁ (whNormalPiKClosedCtx_pi E Γ A₁ B₁)
    h₂ (whNormalPiKClosedCtx_pi E Γ A₂ B₂)
  injection e with eA eB
  exact ⟨eA, eB⟩

theorem whRedPiKClosedCtx_sort_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {Γ : LCtx} {a : Expr Nat} {l₁ l₂ : Level}
    (h₁ : WhRedPiKClosedCtx E Γ a (.sort l₁))
    (h₂ : WhRedPiKClosedCtx E Γ a (.sort l₂)) :
    l₁ = l₂ := by
  have e := whRedPiKClosedCtx_normal_unique_of_envWfT hW
    h₁ (whNormalPiKClosedCtx_sort E Γ l₁)
    h₂ (whNormalPiKClosedCtx_sort E Γ l₂)
  injection e

/-- **1. `W-ZETALOCAL` Resolved in `WhRedPiKClosedCtx` (`whRedPiKClosedCtx_zetaLocalSortCtx_sort`):**
    In `zetaLocalSortCtx = [.letBinding (.sort (.succ .zero)) (.sort .zero)]`, `.bvar 0` steps in
    one `zetaLocal` step to `.sort .zero`. -/
theorem whRedPiKClosedCtx_zetaLocalSortCtx_sort (E : ResolvedEnv) :
    WhRedPiKClosedCtx E zetaLocalSortCtx (.bvar 0) (.sort .zero) :=
  .step (.zetaLocal rfl) (.refl _)

/-- **2. `W-K` 0-Field Resolved in `WhRedPiKClosedCtx` (`whRedPiKClosedCtx_trueEnvU_kRecVar_sort`):** -/
theorem whRedPiKClosedCtx_trueEnvU_kRecVar_sort :
    WhRedPiKClosedCtx trueEnvU trueEnvU_kVarCtx trueEnvU_kRecVar (.sort .zero) :=
  (whRedPiKClosedCtx_letFree_iff letFreeCtx_trueEnvU_kVarCtx).mpr
    whRedPiKClosed_trueEnvU_kRecVar_sort

/-- **3. `W-K` Fieldful Resolved in `WhRedPiKClosedCtx` (`whRedPiKClosedCtx_andEnvU_mixAndRedex_mixPi`):** -/
theorem whRedPiKClosedCtx_andEnvU_mixAndRedex_mixPi :
    WhRedPiKClosedCtx andEnvU mixAndCtx mixAndRedex mixPi :=
  (whRedPiKClosedCtx_letFree_iff letFreeCtx_mixAndCtx).mpr
    whRedPiKClosed_andEnvU_mixAndRedex_mixPi

/-! ### §6.2. Exact `EnvI` Equalities for `ctxEnvDIK` Under `insertAt` and `substRemove`
(`ctxEnvDIK_insertAt_eq`, `ctxEnvDIK_substLet_eq`, `ctxEnvDIK_substAssump_eq`) and
Unconditional `let`-Substitution Commutation for `WhRedPiKClosedCtx` -/

/-- Exact `EnvI` equality for `denDIK` under `lift k 1` into `EnvI.insert ρ k S`. -/
theorem denDIK_insert_lift_eq (E : ResolvedEnv) (ρ : EnvI) (k : Nat) (S : CptI → Prop)
    (e : Expr Nat) :
    denDIK E (EnvI.insert ρ k S) (lift k 1 e) = denDIK E ρ e := by
  funext c
  exact propext ⟨fun h => approxDIK_lift_elim e h, fun h => approxDIK_lift_intro h k S⟩

/-- Exact `EnvI` equality for `denDIK` under `lift 0 1` into `EnvI.cons S ρ`. -/
theorem denDIK_cons_lift0_eq (E : ResolvedEnv) (ρ : EnvI) (S : CptI → Prop) (e : Expr Nat) :
    denDIK E (EnvI.cons S ρ) (lift 0 1 e) = denDIK E ρ e := by
  rw [← EnvI.insert_zero]
  exact denDIK_insert_lift_eq E ρ 0 S e

/-- **Unconditional Head Weakening Invariance of `ApproxDIK E (ctxEnvDIK E Γ)`
    (`approxDIK_ctxEnvDIK_cons_lift0_iff`):**
    For **every** `d : LocalDecl` (both `.assumption A` and `.letBinding A v`, with **zero**
    restriction on `v`!), `ApproxDIK E (ctxEnvDIK E (d :: Γ)) (lift 0 1 e) c ↔ ApproxDIK E (ctxEnvDIK E Γ) e c`! -/
theorem approxDIK_ctxEnvDIK_cons_lift0_iff (E : ResolvedEnv) (d : LocalDecl) (Γ : LCtx)
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E (ctxEnvDIK E (d :: Γ)) (lift 0 1 e) c ↔
      ApproxDIK E (ctxEnvDIK E Γ) e c := by
  cases d with
  | assumption A =>
      exact approxDIK_lift0_one_iff (ctxEnvDIK E Γ) (fun u => u = .bot) e c
  | letBinding A v =>
      exact approxDIK_lift0_one_iff (ctxEnvDIK E Γ) (denDIK E (ctxEnvDIK E Γ) v) e c

/-- **Exact `EnvI` Insertion Characterization of `ctxEnvDIK E (insertAt d k Γ)`
    (`ctxEnvDIK_insertAt_eq`):**
    For every `k ≤ Γ.length` and every `d : LocalDecl`, there exists `S : CptI → Prop` such that
    `ctxEnvDIK E (insertAt d k Γ) = EnvI.insert (ctxEnvDIK E Γ) k S`! -/
theorem ctxEnvDIK_insertAt_eq (E : ResolvedEnv) (d : LocalDecl) :
    ∀ (k : Nat) (Γ : LCtx), k ≤ Γ.length →
      ∃ S : CptI → Prop, ctxEnvDIK E (insertAt d k Γ) = EnvI.insert (ctxEnvDIK E Γ) k S
  | 0, Γ, _ => by
      cases d with
      | assumption A =>
          refine ⟨fun u => u = .bot, ?_⟩
          simp only [insertAt_zero, ctxEnvDIK, EnvI.insert_zero]
      | letBinding A v =>
          refine ⟨denDIK E (ctxEnvDIK E Γ) v, ?_⟩
          simp only [insertAt_zero, ctxEnvDIK, EnvI.insert_zero]
  | k + 1, [], hk => (Nat.not_succ_le_zero k hk).elim
  | k + 1, x :: Γ, hk => by
      have hk' : k ≤ Γ.length := Nat.le_of_succ_le_succ hk
      obtain ⟨S, ih⟩ := ctxEnvDIK_insertAt_eq E d k Γ hk'
      refine ⟨S, ?_⟩
      cases x with
      | assumption A =>
          simp only [insertAt_succ_cons, liftDecl, ctxEnvDIK, ih, EnvI.cons_insert]
      | letBinding A u =>
          simp only [insertAt_succ_cons, liftDecl, ctxEnvDIK, ih,
            denDIK_insert_lift_eq, EnvI.cons_insert]

/-- **All-Cutoff Weakening Invariance of `ApproxDIK E (ctxEnvDIK E Γ)`
    (`approxDIK_ctxEnvDIK_insertAt_lift_iff`):** -/
theorem approxDIK_ctxEnvDIK_insertAt_lift_iff (E : ResolvedEnv) (d : LocalDecl)
    {k : Nat} {Γ : LCtx} (hk : k ≤ Γ.length) (e : Expr Nat) (c : CptI) :
    ApproxDIK E (ctxEnvDIK E (insertAt d k Γ)) (lift k 1 e) c ↔
      ApproxDIK E (ctxEnvDIK E Γ) e c := by
  obtain ⟨S, heq⟩ := ctxEnvDIK_insertAt_eq E d k Γ hk
  rw [heq]
  exact ⟨fun h => approxDIK_lift_elim e h, fun h => approxDIK_lift_intro h k S⟩

/-- Exact `EnvI` equality for `denDIK` under `instantiate j (lift 0 j s)`. -/
theorem denDIK_subst_eq (E : ResolvedEnv) (ρ : EnvI) (j : Nat) (s e : Expr Nat) :
    denDIK E ρ (instantiate j (lift 0 j s) e) =
      denDIK E (EnvI.insert ρ j (denDIK E ρ (lift 0 j s))) e := by
  have hdrop : denDIK E (EnvI.drop ρ j) s = denDIK E ρ (lift 0 j s) :=
    funext fun _ => propext ⟨approxDIK_liftN_intro ρ j, approxDIK_liftN_elim ρ j⟩
  rw [← hdrop]
  funext c
  exact propext (approxDIK_subst_iff E ρ j s e c)

/-- **Exact `EnvI` Equality for `ctxEnvDIK` Under `let`-Substitution (`ctxEnvDIK_substLet_eq`):**
    For **every** `j : Nat`, **every** `t, w0 : Expr Nat` (with **zero** restriction on `w0`!), and
    **every** `Γ : LCtx` with `Γ[j]? = some (.letBinding t w0)`, inserting
    `denDIK E (ctxEnvDIK E (substRemove w0 j Γ)) (lift 0 j w0)` at slot `j` of
    `ctxEnvDIK E (substRemove w0 j Γ)` equals `ctxEnvDIK E Γ` **exactly (`=`)**! -/
theorem ctxEnvDIK_substLet_eq (E : ResolvedEnv) (t w0 : Expr Nat) :
    ∀ (j : Nat) (Γ : LCtx),
      Γ[j]? = some (.letBinding t w0) →
      EnvI.insert (ctxEnvDIK E (substRemove w0 j Γ)) j
        (denDIK E (ctxEnvDIK E (substRemove w0 j Γ)) (lift 0 j w0)) =
      ctxEnvDIK E Γ
  | 0, [], hget => Option.noConfusion hget
  | 0, x :: Γ, hget => by
      simp only [List.getElem?_cons_zero] at hget
      injection hget with hx
      subst hx
      simp only [substRemove_zero_cons, lift_zero, ctxEnvDIK, EnvI.insert_zero]
  | j + 1, [], hget => Option.noConfusion hget
  | j + 1, x :: Γ, hget => by
      rw [List.getElem?_cons_succ] at hget
      have ih := ctxEnvDIK_substLet_eq E t w0 j Γ hget
      have hlift : lift 0 (j + 1) w0 = lift 0 1 (lift 0 j w0) :=
        (lift_lift_merge 1 j 0 0 (by omega) (by omega) w0).symm
      cases x with
      | assumption A =>
          simp only [substRemove_succ_cons, instDecl, ctxEnvDIK, hlift,
            denDIK_cons_lift0_eq, ← EnvI.cons_insert, ih]
      | letBinding A u =>
          simp only [substRemove_succ_cons, instDecl, ctxEnvDIK, hlift,
            denDIK_cons_lift0_eq, ← EnvI.cons_insert, denDIK_subst_eq, ih]

/-- **Unconditional `let`-Substitution Invariance of `ApproxDIK E (ctxEnvDIK E Γ)` Across ALL
    Let-Values `w0 : Expr Nat` (`approxDIK_ctxEnvDIK_substLet_iff`):**
    Holds for **every** `w0 : Expr Nat` (even `w0 = .sort .zero`, `.pi A B`, `.lam A b`, or a
    constructor spine) with **zero** `⊥`-approximation side condition! -/
theorem approxDIK_ctxEnvDIK_substLet_iff {E : ResolvedEnv} {t w0 : Expr Nat}
    {j : Nat} {Γ : LCtx} (hget : Γ[j]? = some (.letBinding t w0))
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E (ctxEnvDIK E (substRemove w0 j Γ)) (instantiate j (lift 0 j w0) e) c ↔
      ApproxDIK E (ctxEnvDIK E Γ) e c := by
  change denDIK E (ctxEnvDIK E (substRemove w0 j Γ)) (instantiate j (lift 0 j w0) e) c ↔
    denDIK E (ctxEnvDIK E Γ) e c
  rw [denDIK_subst_eq, ctxEnvDIK_substLet_eq E t w0 j Γ hget]

/-- Head (`j = 0`) specialization of `approxDIK_ctxEnvDIK_substLet_iff`: for **every** `t, w0 : Expr Nat`,
    `ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 w0 e) c ↔ ApproxDIK E (ctxEnvDIK E (.letBinding t w0 :: Γ)) e c`! -/
theorem approxDIK_ctxEnvDIK_substLet0_iff (E : ResolvedEnv) (t w0 : Expr Nat) (Γ : LCtx)
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 w0 e) c ↔
      ApproxDIK E (ctxEnvDIK E (.letBinding t w0 :: Γ)) e c := by
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have h0 := approxDIK_ctxEnvDIK_substLet_iff (E := E) hget0 e c
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- **Exact `EnvI` Equality for `ctxEnvDIK` Under Assumption-Substitution (`ctxEnvDIK_substAssump_eq`):** -/
theorem ctxEnvDIK_substAssump_eq (E : ResolvedEnv) (t v : Expr Nat) :
    ∀ (j : Nat) (Γ : LCtx),
      Γ[j]? = some (.assumption t) →
      (∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v j Γ)) (lift 0 j v) u → u = .bot) →
      EnvI.insert (ctxEnvDIK E (substRemove v j Γ)) j
        (denDIK E (ctxEnvDIK E (substRemove v j Γ)) (lift 0 j v)) =
      ctxEnvDIK E Γ
  | 0, [], hget, _ => Option.noConfusion hget
  | 0, x :: Γ, hget, hv => by
      simp only [List.getElem?_cons_zero] at hget
      injection hget with hx
      subst hx
      have hden : denDIK E (ctxEnvDIK E Γ) v = (fun u => u = .bot) := by
        funext u
        exact propext ⟨fun h => hv u (by simpa only [substRemove_zero_cons, lift_zero] using h),
          fun h => h ▸ .bot _ _⟩
      simp only [substRemove_zero_cons, lift_zero, ctxEnvDIK, EnvI.insert_zero, hden]
  | j + 1, [], hget, _ => Option.noConfusion hget
  | j + 1, x :: Γ, hget, hv => by
      rw [List.getElem?_cons_succ] at hget
      have hlift : lift 0 (j + 1) v = lift 0 1 (lift 0 j v) :=
        (lift_lift_merge 1 j 0 0 (by omega) (by omega) v).symm
      have hv₀ : ∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v j Γ)) (lift 0 j v) u → u = .bot := by
        intro u hu
        apply hv u
        rw [substRemove_succ_cons, hlift]
        exact (approxDIK_ctxEnvDIK_cons_lift0_iff E (instDecl j v x)
          (substRemove v j Γ) (lift 0 j v) u).mpr hu
      have ih := ctxEnvDIK_substAssump_eq E t v j Γ hget hv₀
      cases x with
      | assumption A =>
          simp only [substRemove_succ_cons, instDecl, ctxEnvDIK, hlift,
            denDIK_cons_lift0_eq, ← EnvI.cons_insert, ih]
      | letBinding A u =>
          simp only [substRemove_succ_cons, instDecl, ctxEnvDIK, hlift,
            denDIK_cons_lift0_eq, ← EnvI.cons_insert, denDIK_subst_eq, ih]

/-- Assumption-substitution invariance of `ApproxDIK E (ctxEnvDIK E Γ)` for `⊥`-approximated `v`. -/
theorem approxDIK_ctxEnvDIK_substAssump_iff {E : ResolvedEnv} {t v : Expr Nat}
    {j : Nat} {Γ : LCtx} (hget : Γ[j]? = some (.assumption t))
    (hv : ∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v j Γ)) (lift 0 j v) u → u = .bot)
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E (ctxEnvDIK E (substRemove v j Γ)) (instantiate j (lift 0 j v) e) c ↔
      ApproxDIK E (ctxEnvDIK E Γ) e c := by
  change denDIK E (ctxEnvDIK E (substRemove v j Γ)) (instantiate j (lift 0 j v) e) c ↔
    denDIK E (ctxEnvDIK E Γ) e c
  rw [denDIK_subst_eq, ctxEnvDIK_substAssump_eq E t v j Γ hget hv]

/-- **All-Cutoff Weakening Commutation for `WhStepPiKClosedCtx` (`whStepPiKClosedCtx_lift_insertAt`):**
    For every `d : LocalDecl` (both `.assumption` and `.letBinding`) and every `k ≤ Γ.length`,
    `WhStepPiKClosedCtx E Γ a b → WhStepPiKClosedCtx E (insertAt d k Γ) (lift k 1 a) (lift k 1 b)`! -/
theorem whStepPiKClosedCtx_lift_insertAt {E : ResolvedEnv} (hcl : EnvClosed E)
    (d : LocalDecl) {k : Nat} {Γ : LCtx} (hk : k ≤ Γ.length)
    {a b : Expr Nat} (h : WhStepPiKClosedCtx E Γ a b) :
    WhStepPiKClosedCtx E (insertAt d k Γ) (lift k 1 a) (lift k 1 b) := by
  induction h with
  | of_whStep hs =>
      exact .of_whStep (whStep_lift_of_envClosed hcl hs k)
  | @zetaLocal i v hval =>
      by_cases hik : i < k
      · have hsub := lookupValue_insertAt_lt d hik hval
        simp only [lift, if_neg (by omega : ¬ k ≤ i)]
        exact .zetaLocal hsub
      · have hsub := lookupValue_insertAt_ge d (by omega : k ≤ i) hval
        simp only [lift, if_pos (by omega : k ≤ i)]
        exact .zetaLocal hsub
  | iotaKClosedCtx w x hk_prop hflds hx =>
      rw [recCall_const_lift k w x, ← iotaRhsOfS_lift k w]
      refine .iotaKClosedCtx (liftWitnessS k w) (lift k 1 x) hk_prop ?_ ?_
      · simp only [liftWitnessS, List.length_map]
        calc
          w.fields.map (lift k 1)
            = (List.replicate w.fields.length botClosedExpr).map (lift k 1) :=
                congrArg (List.map (lift k 1)) hflds
          _ = List.replicate w.fields.length botClosedExpr :=
                replicate_botClosedExpr_map_lift w.fields.length k 1
      · intro args hsp
        exact hx args
          ((approxDIK_ctxEnvDIK_insertAt_lift_iff E d hk x (.spine w.ctorRef args)).mp hsp)
  | @appHead _ _ _ _ ih =>
      exact .appHead ih

theorem whRedPiKClosedCtx_lift_insertAt {E : ResolvedEnv} (hcl : EnvClosed E)
    (d : LocalDecl) {k : Nat} {Γ : LCtx} (hk : k ≤ Γ.length)
    {a b : Expr Nat} (h : WhRedPiKClosedCtx E Γ a b) :
    WhRedPiKClosedCtx E (insertAt d k Γ) (lift k 1 a) (lift k 1 b) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (whStepPiKClosedCtx_lift_insertAt hcl d hk hs) ih

theorem whStepPiKClosedCtx_lift0_cons {E : ResolvedEnv} (hcl : EnvClosed E)
    (d : LocalDecl) {Γ : LCtx} {a b : Expr Nat}
    (h : WhStepPiKClosedCtx E Γ a b) :
    WhStepPiKClosedCtx E (d :: Γ) (lift 0 1 a) (lift 0 1 b) :=
  whStepPiKClosedCtx_lift_insertAt hcl d (Nat.zero_le _) h

theorem whRedPiKClosedCtx_lift0_cons {E : ResolvedEnv} (hcl : EnvClosed E)
    (d : LocalDecl) {Γ : LCtx} {a b : Expr Nat}
    (h : WhRedPiKClosedCtx E Γ a b) :
    WhRedPiKClosedCtx E (d :: Γ) (lift 0 1 a) (lift 0 1 b) :=
  whRedPiKClosedCtx_lift_insertAt hcl d (Nat.zero_le _) h

/-- **Unconditional `let`-Substitution Commutation for `WhStepPiKClosedCtx` Across ALL Let-Values
    `w0 : Expr Nat` (`whStepPiKClosedCtx_substLet_of_envClosed`):**
    For **every** `j : Nat` and **every** `t, w0 : Expr Nat` (with **zero** restriction on `w0`!)
    such that `Γ[j]? = some (.letBinding t w0)`, every step `WhStepPiKClosedCtx E Γ a b` becomes a
    `WhRedPiKClosedCtx E (substRemove w0 j Γ)` reduction (0 steps when `zetaLocal` unfolds `.bvar j`
    itself, 1 step in all other cases)! -/
theorem whStepPiKClosedCtx_substLet_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {t w0 : Expr Nat} {j : Nat} {Γ : LCtx} (hget : Γ[j]? = some (.letBinding t w0))
    {a b : Expr Nat} (h : WhStepPiKClosedCtx E Γ a b) :
    WhRedPiKClosedCtx E (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) a) (instantiate j (lift 0 j w0) b) := by
  induction h with
  | of_whStep hs =>
      exact .step (.of_whStep (whStep_instantiate_of_envClosed hcl hs j (lift 0 j w0))) (.refl _)
  | @zetaLocal i v0 hvl =>
      by_cases hij : i = j
      · subst hij
        rw [lookupValue_get_letBinding hget] at hvl
        injection hvl with hvl
        subst hvl
        simp only [instantiate, if_true]
        rw [instantiate_lift_cancel (i + 1) 0 i (lift 0 i w0) (by omega) (by omega),
            Nat.add_sub_cancel]
        exact .refl _
      · by_cases hlt : i < j
        · have hsub := lookupValue_substRemove_lt (v := w0) hlt hvl
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .step (.zetaLocal hsub) (.refl _)
        · have hsub := lookupValue_substRemove_gt (v := w0) (by omega : j < i) hvl
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i)]
          exact .step (.zetaLocal hsub) (.refl _)
  | iotaKClosedCtx w x hk_prop hflds hx =>
      rw [recCall_const_instantiate j (lift 0 j w0) w x,
        ← iotaRhsOfS_instantiate j (lift 0 j w0) w]
      refine .step (.iotaKClosedCtx (instWitnessS j (lift 0 j w0) w)
        (instantiate j (lift 0 j w0) x) hk_prop ?_ ?_) (.refl _)
      · simp only [instWitnessS, List.length_map]
        calc
          w.fields.map (instantiate j (lift 0 j w0))
            = (List.replicate w.fields.length botClosedExpr).map (instantiate j (lift 0 j w0)) :=
                congrArg (List.map (instantiate j (lift 0 j w0))) hflds
          _ = List.replicate w.fields.length botClosedExpr :=
                replicate_botClosedExpr_map_instantiate w.fields.length j (lift 0 j w0)
      · intro args hsp
        exact hx args
          ((approxDIK_ctxEnvDIK_substLet_iff hget x (.spine w.ctorRef args)).mp hsp)
  | @appHead _ _ arg _ ih =>
      exact whRedPiKClosedCtx_appHead ih

/-- **Unconditional Multi-Step `let`-Substitution Commutation for `WhRedPiKClosedCtx` Across ALL
    Let-Values `w0 : Expr Nat` (`whRedPiKClosedCtx_substLet_of_envClosed`):** -/
theorem whRedPiKClosedCtx_substLet_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {t w0 : Expr Nat} {j : Nat} {Γ : LCtx} (hget : Γ[j]? = some (.letBinding t w0))
    {a b : Expr Nat} (h : WhRedPiKClosedCtx E Γ a b) :
    WhRedPiKClosedCtx E (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) a) (instantiate j (lift 0 j w0) b) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih =>
      exact whRedPiKClosedCtx_trans
        (whStepPiKClosedCtx_substLet_of_envClosed hcl hget hs) ih

theorem whRedPiKClosedCtx_substLet0_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    (t w0 : Expr Nat) {Γ : LCtx} {a b : Expr Nat}
    (h : WhRedPiKClosedCtx E (.letBinding t w0 :: Γ) a b) :
    WhRedPiKClosedCtx E Γ (instantiate0 w0 a) (instantiate0 w0 b) := by
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have h0 := whRedPiKClosedCtx_substLet_of_envClosed hcl hget0 h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- Assumption-substitution commutation for `WhStepPiKClosedCtx` on `⊥`-approximated `v`. -/
theorem whStepPiKClosedCtx_substAssump_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {t v : Expr Nat} {j : Nat} {Γ : LCtx} (hget : Γ[j]? = some (.assumption t))
    (hv : ∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v j Γ)) (lift 0 j v) u → u = .bot)
    {a b : Expr Nat} (h : WhStepPiKClosedCtx E Γ a b) :
    WhStepPiKClosedCtx E (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b) := by
  induction h with
  | of_whStep hs =>
      exact .of_whStep (whStep_instantiate_of_envClosed hcl hs j (lift 0 j v))
  | @zetaLocal i v0 hvl =>
      by_cases hij : i = j
      · subst hij
        rw [lookupValue_get_assumption hget] at hvl
        exact Option.noConfusion hvl
      · by_cases hlt : i < j
        · have hsub := lookupValue_substRemove_lt (v := v) hlt hvl
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .zetaLocal hsub
        · have hsub := lookupValue_substRemove_gt (v := v) (by omega : j < i) hvl
          simp only [instantiate, if_neg hij, if_pos (by omega : j < i)]
          exact .zetaLocal hsub
  | iotaKClosedCtx w x hk_prop hflds hx =>
      rw [recCall_const_instantiate j (lift 0 j v) w x,
        ← iotaRhsOfS_instantiate j (lift 0 j v) w]
      refine .iotaKClosedCtx (instWitnessS j (lift 0 j v) w)
        (instantiate j (lift 0 j v) x) hk_prop ?_ ?_
      · simp only [instWitnessS, List.length_map]
        calc
          w.fields.map (instantiate j (lift 0 j v))
            = (List.replicate w.fields.length botClosedExpr).map (instantiate j (lift 0 j v)) :=
                congrArg (List.map (instantiate j (lift 0 j v))) hflds
          _ = List.replicate w.fields.length botClosedExpr :=
                replicate_botClosedExpr_map_instantiate w.fields.length j (lift 0 j v)
      · intro args hsp
        exact hx args
          ((approxDIK_ctxEnvDIK_substAssump_iff hget hv x (.spine w.ctorRef args)).mp hsp)
  | @appHead _ _ _ _ ih =>
      exact .appHead ih

theorem whRedPiKClosedCtx_substAssump_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {t v : Expr Nat} {j : Nat} {Γ : LCtx} (hget : Γ[j]? = some (.assumption t))
    (hv : ∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v j Γ)) (lift 0 j v) u → u = .bot)
    {a b : Expr Nat} (h : WhRedPiKClosedCtx E Γ a b) :
    WhRedPiKClosedCtx E (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih =>
      exact .step (whStepPiKClosedCtx_substAssump_of_envClosed hcl hget hv hs) ih

/-! ## §7. Context-Aware Type and Term Logical Relations `LRTypeINPiKClosedCtx` /
`LRTypeINBiDIKClosedCtx` and `LRTermDSubKClosedCtx` / `LRTermDSubKClosedCtxBi`:
Eliminating `LetFreeCtx` and Closing `ConvT.zetaLocal`, `HasTyT.letE`, and `ConvT.zeta`
Unconditionally Across All Contexts -/

/-! ### §7.1. `SameLetProfile`, `LRTypeINPiKClosedCtx`, and `LRTypeINBiDIKClosedCtx` Across All `Γ : LCtx` -/

/-- Two contexts `Γ` and `Γ'` have the same let-binding profile if they agree on `lookupValue` at
    every index `i` and induce the same `ctxEnvDIK E` at every environment `E`. -/
def SameLetProfile (Γ Γ' : LCtx) : Prop :=
  (∀ i, lookupValue Γ i = lookupValue Γ' i) ∧ (∀ E, ctxEnvDIK E Γ = ctxEnvDIK E Γ')

theorem sameLetProfile_refl (Γ : LCtx) : SameLetProfile Γ Γ :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem sameLetProfile_symm {Γ Γ' : LCtx} (h : SameLetProfile Γ Γ') : SameLetProfile Γ' Γ :=
  ⟨fun i => (h.1 i).symm, fun E => (h.2 E).symm⟩

theorem sameLetProfile_trans {Γ₁ Γ₂ Γ₃ : LCtx}
    (h₁ : SameLetProfile Γ₁ Γ₂) (h₂ : SameLetProfile Γ₂ Γ₃) :
    SameLetProfile Γ₁ Γ₃ :=
  ⟨fun i => (h₁.1 i).trans (h₂.1 i), fun E => (h₁.2 E).trans (h₂.2 E)⟩

/-- Replacing an `.assumption A₁` by `.assumption A₂` at the head of a context preserves
    `SameLetProfile` identically! -/
theorem sameLetProfile_assump_head (A₁ A₂ : Expr Nat) (Γ : LCtx) :
    SameLetProfile (.assumption A₁ :: Γ) (.assumption A₂ :: Γ) := by
  refine ⟨fun i => ?_, fun _ => rfl⟩
  cases i with
  | zero => rfl
  | succ i => simp only [lookupValue_cons_succ]

/-- Pushing `.assumption A` preserves `SameLetProfile`. -/
theorem sameLetProfile_cons_assump (A : Expr Nat) {Γ Γ' : LCtx} (h : SameLetProfile Γ Γ') :
    SameLetProfile (.assumption A :: Γ) (.assumption A :: Γ') := by
  refine ⟨fun i => ?_, fun E => by simp only [ctxEnvDIK, h.2 E]⟩
  cases i with
  | zero => rfl
  | succ i => simp only [lookupValue_cons_succ, h.1 i]

theorem whStepPiKClosedCtx_of_sameLetProfile {E : ResolvedEnv} {Γ Γ' : LCtx}
    (hprof : SameLetProfile Γ Γ') {a b : Expr Nat}
    (h : WhStepPiKClosedCtx E Γ a b) : WhStepPiKClosedCtx E Γ' a b := by
  induction h with
  | of_whStep hs => exact .of_whStep hs
  | @zetaLocal i v hval =>
      rw [hprof.1 i] at hval
      exact .zetaLocal hval
  | iotaKClosedCtx w x hk hflds hx =>
      rw [hprof.2 E] at hx
      exact .iotaKClosedCtx w x hk hflds hx
  | @appHead _ _ _ _ ih => exact .appHead ih

theorem whRedPiKClosedCtx_of_sameLetProfile {E : ResolvedEnv} {Γ Γ' : LCtx}
    (hprof : SameLetProfile Γ Γ') {a b : Expr Nat}
    (h : WhRedPiKClosedCtx E Γ a b) : WhRedPiKClosedCtx E Γ' a b := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (whStepPiKClosedCtx_of_sameLetProfile hprof hs) ih

theorem whNormalPiKClosedCtx_of_sameLetProfile {E : ResolvedEnv} {Γ Γ' : LCtx}
    (hprof : SameLetProfile Γ Γ') {a : Expr Nat}
    (h : WhNormalPiKClosedCtx E Γ a) : WhNormalPiKClosedCtx E Γ' a :=
  fun b hs => h b (whStepPiKClosedCtx_of_sameLetProfile (sameLetProfile_symm hprof) hs)

/-- **Context-Aware Type Logical Relation Over `WhRedPiKClosedCtx E Γ` (`LRTypeINPiKClosedCtx`):** -/
inductive LRTypeINPiKClosedCtx (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → CptI → Prop
  | bot (Γ : LCtx) (A A' : Expr Nat) :
      LRTypeINPiKClosedCtx E n Γ A A' .bot
  | sort {Γ : LCtx} {A A' : Expr Nat} {l l' : Level}
      (h : WhRedPiKClosedCtx E Γ A (.sort l)) (h' : WhRedPiKClosedCtx E Γ A' (.sort l')) :
      LRTypeINPiKClosedCtx E n Γ A A' .sort
  | pi {Γ : LCtx} {A A' A₁ B₁ A₂ B₂ : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (h : WhRedPiKClosedCtx E Γ A (.pi A₁ B₁))
      (h' : WhRedPiKClosedCtx E Γ A' (.pi A₂ B₂))
      (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
      (hdom : TyConvT E n Γ A₁ A₂)
      (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
      (ra : LRTypeINPiKClosedCtx E n Γ A₁ A₂ a)
      (rf : ∀ s ∈ f, LRTypeINPiKClosedCtx E n (.assumption A₁ :: Γ) B₁ B₂ s.2) :
      LRTypeINPiKClosedCtx E n Γ A A' (.pi a f)
  | spine {Γ : LCtx} {A A' Y Y' : Expr Nat} {r : Nat} {args : List CptI}
      (h : WhRedPiKClosedCtx E Γ A Y) (h' : WhRedPiKClosedCtx E Γ A' Y')
      (hn : WhNormalPiKClosedCtx E Γ Y) (hn' : WhNormalPiKClosedCtx E Γ Y')
      (hc : TyConvT E n Γ Y Y') :
      LRTypeINPiKClosedCtx E n Γ A A' (.spine r args)

theorem lrTypeINPiKClosedCtx_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {M M' A A' : Expr Nat} {u : CptI}
    (hM : WhRedPiKClosedCtx E Γ M A) (hM' : WhRedPiKClosedCtx E Γ M' A')
    (h : LRTypeINPiKClosedCtx E n Γ A A' u) :
    LRTypeINPiKClosedCtx E n Γ M M' u := by
  cases h with
  | bot => exact .bot _ _ _
  | sort h₁ h₂ =>
      exact .sort (whRedPiKClosedCtx_trans hM h₁) (whRedPiKClosedCtx_trans hM' h₂)
  | pi h₁ h₂ hΓ₁ hdom hcod ra rf =>
      exact .pi (whRedPiKClosedCtx_trans hM h₁) (whRedPiKClosedCtx_trans hM' h₂)
        hΓ₁ hdom hcod ra rf
  | spine h₁ h₂ hn hn' hc =>
      exact .spine (whRedPiKClosedCtx_trans hM h₁) (whRedPiKClosedCtx_trans hM' h₂) hn hn' hc

/-- For any `BotDemand xs` and any context `Γ : LCtx`, `EnvI.cons (demand xs) (ctxEnvDIK E Γ)`
    and `ctxEnvDIK E (.assumption A₁ :: Γ)` have the exact same `ApproxDIK` approximations! -/
theorem approxDIK_cons_botDemand_ctxEnvDIK_iff {E : ResolvedEnv} {xs : List CptI}
    (hxs : BotDemand xs) (A₁ : Expr Nat) (Γ : LCtx) (B : Expr Nat) (c : CptI) :
    ApproxDIK E (EnvI.cons (demand xs) (ctxEnvDIK E Γ)) B c ↔
      ApproxDIK E (ctxEnvDIK E (.assumption A₁ :: Γ)) B c :=
  approxDIK_cons_botDemand_iff (ρ := ctxEnvDIK E Γ) hxs B c

/-- **Reverse Adequacy on `BotPiCpt` Across ALL Contexts `Γ : LCtx`
    (`approxDIK_of_lrTypeINPiKClosedCtx_botPiCpt`):**
    Requires **no** `LetFreeCtx Γ` and **no** `TypeSoundness`! -/
theorem approxDIK_of_lrTypeINPiKClosedCtx_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A A' : Expr Nat} {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeINPiKClosedCtx E n Γ A A' c) :
    ApproxDIK E (ctxEnvDIK E Γ) A c ∧ ApproxDIK E (ctxEnvDIK E Γ) A' c := by
  induction hc generalizing Γ A A' with
  | bot => exact ⟨.bot _ _, .bot _ _⟩
  | sort =>
      cases h with
      | sort hA hA' =>
          exact ⟨approxDIK_ctxEnvDIK_sort_of_whRedPiKClosedCtx hW hA,
            approxDIK_ctxEnvDIK_sort_of_whRedPiKClosedCtx hW hA'⟩
  | @pi a f _ hbd _ iha ihf =>
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ hA hA' _ _ _ ra rf =>
          obtain ⟨hAa, hA'a⟩ := iha ra
          have hBf : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) (ctxEnvDIK E Γ)) B₁ s.2 := by
            intro s hs
            rw [approxDIK_cons_botDemand_ctxEnvDIK_iff (hbd s hs) A₁ Γ B₁ s.2]
            exact (ihf s hs (rf s hs)).1
          have hB'f : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) (ctxEnvDIK E Γ)) B₂ s.2 := by
            intro s hs
            rw [approxDIK_cons_botDemand_ctxEnvDIK_iff (hbd s hs) A₁ Γ B₂ s.2]
            exact (ihf s hs (rf s hs)).2
          exact ⟨approxDIK_ctxEnvDIK_whRedPiKClosedCtx_back hW hA (.pi hAa hBf),
            approxDIK_ctxEnvDIK_whRedPiKClosedCtx_back hW hA' (.pi hA'a hB'f)⟩

theorem lrTypeINPiKClosedCtx_ctx_of_sameLetProfile {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ Γ' : LCtx} (hctx : CtxConvT E n Γ Γ') (hprof : SameLetProfile Γ Γ')
    (hΓ' : CtxWfT E n Γ') {A A' : Expr Nat} {c : CptI}
    (h : LRTypeINPiKClosedCtx E n Γ A A' c) :
    LRTypeINPiKClosedCtx E n Γ' A A' c := by
  have hcl := envClosed_of_envWfT hW
  induction h generalizing Γ' with
  | bot => exact .bot _ _ _
  | sort h h' =>
      exact .sort (whRedPiKClosedCtx_of_sameLetProfile hprof h)
        (whRedPiKClosedCtx_of_sameLetProfile hprof h')
  | @pi Γ A A' A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      cases hΓ₁ with
      | assumption _ _ u _ hA₁ =>
          have hA₁' : HasTyT E n Γ' A₁ (.sort u) := hasTyT_ctx hcl hctx hA₁
          have hΓ₁' : CtxWfT E n (.assumption A₁ :: Γ') := .assumption Γ' A₁ u hΓ' hA₁'
          exact .pi (whRedPiKClosedCtx_of_sameLetProfile hprof h)
            (whRedPiKClosedCtx_of_sameLetProfile hprof h')
            hΓ₁' (tyConvT_ctx hcl hctx hdom)
            (tyConvT_ctx hcl (.same (.assumption A₁) hctx) hcod)
            (iha hctx hprof hΓ')
            (fun s hs =>
              ihf s hs (.same (.assumption A₁) hctx)
                (sameLetProfile_cons_assump A₁ hprof) hΓ₁')
  | spine h h' hn hn' hc =>
      exact .spine (whRedPiKClosedCtx_of_sameLetProfile hprof h)
        (whRedPiKClosedCtx_of_sameLetProfile hprof h')
        (whNormalPiKClosedCtx_of_sameLetProfile hprof hn)
        (whNormalPiKClosedCtx_of_sameLetProfile hprof hn')
        (tyConvT_ctx hcl hctx hc)

theorem lrTypeINPiKClosedCtx_assump_dom {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A₁ A₂ : Expr Nat} → TyConvT E n Γ A₁ A₂ → {u : Level} → HasTyT E n Γ A₁ (.sort u) →
    ∀ {B B' : Expr Nat} {c : CptI},
      LRTypeINPiKClosedCtx E n (.assumption A₂ :: Γ) B B' c →
      LRTypeINPiKClosedCtx E n (.assumption A₁ :: Γ) B B' c
  | _, _, .refl _ _, _, _, _, _, _, h => h
  | _, _, .of _ A₁ A₂ _ hc, _, hA₁, _, _, _, h =>
      let ends := convEnds hW hΓ hc
      lrTypeINPiKClosedCtx_ctx_of_sameLetProfile hW
        (.assumption (ctxConvT_refl Γ) ends.2.1 ends.1 (.symm _ _ _ _ hc))
        (sameLetProfile_assump_head A₂ A₁ Γ)
        (.assumption Γ A₁ _ hΓ hA₁) h
  | _, _, .trans _ A₁ _ A₂ c₁ c₂, _, hA₁, _, _, _, h =>
      let ⟨_, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA₁
      lrTypeINPiKClosedCtx_assump_dom hW hΓ c₁ hA₁
        (lrTypeINPiKClosedCtx_assump_dom hW hΓ c₂ hM h)

/-- **Full Symmetry of `LRTypeINPiKClosedCtx` Across ALL Contexts `Γ : LCtx` and ALL Compacts
    `c : CptI` (`lrTypeINPiKClosedCtx_symm`):** -/
theorem lrTypeINPiKClosedCtx_symm {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A A' : Expr Nat} {c : CptI}
    (h : LRTypeINPiKClosedCtx E n Γ A A' c) :
    LRTypeINPiKClosedCtx E n Γ A' A c := by
  induction h with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort h' h
  | @pi Γ A A' A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      cases hΓ₁ with
      | assumption _ _ _ hΓ hA₁ =>
          obtain ⟨v, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          have hΓ₂ : CtxWfT E n (.assumption A₂ :: Γ) := .assumption Γ A₂ v hΓ hA₂
          exact .pi h' h hΓ₂ hdom.symmT (tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT) iha
            (fun s hs => lrTypeINPiKClosedCtx_assump_dom hW hΓ hdom.symmT hA₂ (ihf s hs))
  | spine h h' hn hn' hc => exact .spine h' h hn' hn hc.symmT

/-- **Unconditional Transitivity of `LRTypeINPiKClosedCtx` Across ALL Contexts `Γ : LCtx` and ALL
    Compacts `c : CptI` at `EnvWfT E` (`lrTypeINPiKClosedCtx_trans_of_envWfT`):** -/
theorem lrTypeINPiKClosedCtx_trans_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A M B : Expr Nat} {c : CptI}
    (h₁ : LRTypeINPiKClosedCtx E n Γ A M c)
    (h₂ : LRTypeINPiKClosedCtx E n Γ M B c) :
    LRTypeINPiKClosedCtx E n Γ A B c := by
  induction h₁ generalizing B with
  | bot => exact .bot _ _ _
  | sort hA _ =>
      cases h₂ with
      | sort _ hB => exact .sort hA hB
  | @pi Γ A M A₁ B₁ M₁ N₁ a f hA hM₁ hΓ₁ hdom₁ hcod₁ _ _ iha ihf =>
      cases h₂ with
      | @pi _ _ B M₂ N₂ A₂ B₂ _ _ hM₂ hB _ hdom₂ hcod₂ ra₂ rf₂ =>
          obtain ⟨eM, eN⟩ := whRedPiKClosedCtx_pi_unique_of_envWfT hW hM₁ hM₂
          subst eM; subst eN
          cases hΓ₁ with
          | assumption _ _ _ hΓ hA₁ =>
              exact .pi hA hB (.assumption Γ A₁ _ hΓ hA₁)
                (.trans _ _ _ _ hdom₁ hdom₂)
                (.trans _ _ _ _ hcod₁ (tyConvT_assump_dom hW hΓ hdom₁ hcod₂))
                (iha ra₂)
                (fun s hs =>
                  ihf s hs (lrTypeINPiKClosedCtx_assump_dom hW hΓ hdom₁ hA₁ (rf₂ s hs)))
  | spine hA hM₁ hnA hnM₁ hc₁ =>
      cases h₂ with
      | spine hM₂ hB hnM₂ hnB hc₂ =>
          have eY := whRedPiKClosedCtx_normal_unique_of_envWfT hW hM₁ hnM₁ hM₂ hnM₂
          subst eY
          exact .spine hA hB hnA hnB (.trans _ _ _ _ hc₁ hc₂)

/-- **All-Cutoff Weakening Stability of `LRTypeINPiKClosedCtx` on `BotPiCpt` Across ALL Contexts
    `Γ : LCtx` (`lrTypeINPiKClosedCtx_weaken_botPiCpt`):** -/
theorem lrTypeINPiKClosedCtx_weaken_botPiCpt {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {c : CptI} (hc : BotPiCpt c) :
    ∀ {Γ : LCtx} {A A' : Expr Nat} (d : LocalDecl) {k : Nat},
      k ≤ Γ.length →
      CtxWfT E n (insertAt d k Γ) →
      LRTypeINPiKClosedCtx E n Γ A A' c →
      LRTypeINPiKClosedCtx E n (insertAt d k Γ) (lift k 1 A) (lift k 1 A') c := by
  induction hc with
  | bot =>
      intro Γ A A' d k _ _ _
      exact .bot _ _ _
  | sort =>
      intro Γ A A' d k hk _ h
      cases h with
      | sort h₁ h₂ =>
          exact .sort (whRedPiKClosedCtx_lift_insertAt hcl d hk h₁)
            (whRedPiKClosedCtx_lift_insertAt hcl d hk h₂)
  | @pi a f _ _ _ iha ihf =>
      intro Γ A A' d k hk hΓ' h
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h₁ h₂ hΓ₁ hdom hcod ra rf =>
          have h₁' : WhRedPiKClosedCtx E (insertAt d k Γ)
              (lift k 1 A) (.pi (lift k 1 A₁) (lift (k + 1) 1 B₁)) :=
            whRedPiKClosedCtx_lift_insertAt hcl d hk h₁
          have h₂' : WhRedPiKClosedCtx E (insertAt d k Γ)
              (lift k 1 A') (.pi (lift k 1 A₂) (lift (k + 1) 1 B₂)) :=
            whRedPiKClosedCtx_lift_insertAt hcl d hk h₂
          have hA₁ : ∃ u, Nonempty (HasTyT E n Γ A₁ (.sort u)) := by
            cases hΓ₁ with
            | assumption _ _ u _ hA₁ => exact ⟨u, ⟨hA₁⟩⟩
          obtain ⟨u, ⟨hA₁⟩⟩ := hA₁
          have hA₁' : HasTyT E n (insertAt d k Γ) (lift k 1 A₁) (.sort u) :=
            hasTyTWeaken d hcl (c := k) hA₁
          have hΓ₁' : CtxWfT E n (.assumption (lift k 1 A₁) :: insertAt d k Γ) :=
            .assumption _ _ u hΓ' hA₁'
          have hdom' : TyConvT E n (insertAt d k Γ) (lift k 1 A₁) (lift k 1 A₂) :=
            tyConvTWeaken d hcl (c := k) hdom
          have hcod' : TyConvT E n (.assumption (lift k 1 A₁) :: insertAt d k Γ)
              (lift (k + 1) 1 B₁) (lift (k + 1) 1 B₂) :=
            tyConvTWeaken d hcl (c := k + 1) (Γ := .assumption A₁ :: Γ) hcod
          exact .pi h₁' h₂' hΓ₁' hdom' hcod'
            (iha d hk hΓ' ra)
            (fun s hs => by
              have hΓ₁_ins : CtxWfT E n (insertAt d (k + 1) (.assumption A₁ :: Γ)) := hΓ₁'
              exact ihf s hs (Γ := .assumption A₁ :: Γ) d (Nat.succ_le_succ hk) hΓ₁_ins (rf s hs))

theorem lrTypeINPiKClosedCtx_weaken0_botPiCpt {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {A A' : Expr Nat} {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeINPiKClosedCtx E n Γ A A' c) :
    LRTypeINPiKClosedCtx E n (d :: Γ) (lift 0 1 A) (lift 0 1 A') c :=
  lrTypeINPiKClosedCtx_weaken_botPiCpt hcl hc d (Nat.zero_le _) hΓ' h

/-- **Unconditional `let`-Substitution Stability of `LRTypeINPiKClosedCtx` on `BotPiCpt` Across
    ALL Let-Values `w0 : Expr Nat` (`lrTypeINPiKClosedCtx_substLet_botPiCpt`):**
    Requires **zero** `⊥`-approximation restriction on `w0`! -/
theorem lrTypeINPiKClosedCtx_substLet_botPiCpt {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (t w0 : Expr Nat)
    {c : CptI} (hc : BotPiCpt c) :
    ∀ {Γ : LCtx} {A A' : Expr Nat} {j : Nat},
      Γ[j]? = some (.letBinding t w0) →
      HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
      CtxWfT E n (substRemove w0 j Γ) →
      LRTypeINPiKClosedCtx E n Γ A A' c →
      LRTypeINPiKClosedCtx E n (substRemove w0 j Γ)
        (instantiate j (lift 0 j w0) A) (instantiate j (lift 0 j w0) A') c := by
  induction hc with
  | bot =>
      intro Γ A A' j _ _ _ _
      exact .bot _ _ _
  | sort =>
      intro Γ A A' j hget _ _ h
      cases h with
      | sort h₁ h₂ =>
          exact .sort (whRedPiKClosedCtx_substLet_of_envClosed hcl hget h₁)
            (whRedPiKClosedCtx_substLet_of_envClosed hcl hget h₂)
  | @pi a f _ _ _ iha ihf =>
      intro Γ A A' j hget hvty hΓ' h
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h₁ h₂ hΓ₁ hdom hcod ra rf =>
          have hlift : lift 0 1 (lift 0 j w0) = lift 0 (j + 1) w0 :=
            lift_lift_merge 1 j 0 0 (by omega) (by omega) w0
          have h₁' : WhRedPiKClosedCtx E (substRemove w0 j Γ) (instantiate j (lift 0 j w0) A)
              (.pi (instantiate j (lift 0 j w0) A₁) (instantiate (j + 1) (lift 0 (j + 1) w0) B₁)) := by
            have h0 := whRedPiKClosedCtx_substLet_of_envClosed hcl hget h₁
            simpa only [instantiate, hlift] using h0
          have h₂' : WhRedPiKClosedCtx E (substRemove w0 j Γ) (instantiate j (lift 0 j w0) A')
              (.pi (instantiate j (lift 0 j w0) A₂) (instantiate (j + 1) (lift 0 (j + 1) w0) B₂)) := by
            have h0 := whRedPiKClosedCtx_substLet_of_envClosed hcl hget h₂
            simpa only [instantiate, hlift] using h0
          have hA₁ : ∃ u, Nonempty (HasTyT E n Γ A₁ (.sort u)) := by
            cases hΓ₁ with
            | assumption _ _ u _ hA₁ => exact ⟨u, ⟨hA₁⟩⟩
          obtain ⟨u, ⟨hA₁⟩⟩ := hA₁
          have hA₁' : HasTyT E n (substRemove w0 j Γ) (instantiate j (lift 0 j w0) A₁) (.sort u) :=
            hasTyT_substLetS hcl hinst t w0 hA₁ hget hvty
          have hΓ₁'' : CtxWfT E n (.assumption (instantiate j (lift 0 j w0) A₁) :: substRemove w0 j Γ) :=
            .assumption _ _ u hΓ' hA₁'
          have hΓ₁' : CtxWfT E n (substRemove w0 (j + 1) (.assumption A₁ :: Γ)) := by
            simpa only [substRemove_succ_cons, instDecl] using hΓ₁''
          have hget' : (LocalDecl.assumption A₁ :: Γ)[j + 1]? = some (.letBinding t w0) := by
            rw [List.getElem?_cons_succ]; exact hget
          have hvty' : HasTyT E n (substRemove w0 (j + 1) (.assumption A₁ :: Γ))
              (lift 0 (j + 1) w0) (lift 0 (j + 1) t) := by
            have h0 := hasTyTWeaken (instDecl j w0 (.assumption A₁)) hcl (c := 0) hvty
            rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
                lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
            exact h0
          have hdom' : TyConvT E n (substRemove w0 j Γ)
              (instantiate j (lift 0 j w0) A₁) (instantiate j (lift 0 j w0) A₂) :=
            tyConvT_substLetS hcl hinst t w0 hdom hget hvty
          have hcod' : TyConvT E n (.assumption (instantiate j (lift 0 j w0) A₁) :: substRemove w0 j Γ)
              (instantiate (j + 1) (lift 0 (j + 1) w0) B₁)
              (instantiate (j + 1) (lift 0 (j + 1) w0) B₂) := by
            simpa only [substRemove_succ_cons, instDecl] using
              tyConvT_substLetS hcl hinst t w0 (j := j + 1) hcod hget' hvty'
          exact .pi h₁' h₂' hΓ₁'' hdom' hcod'
            (iha hget hvty hΓ' ra)
            (fun s hs => by
              simpa only [substRemove_succ_cons, instDecl] using
                ihf s hs hget' hvty' hΓ₁' (rf s hs))

/-- Head (`j = 0`) specialization of `lrTypeINPiKClosedCtx_substLet_botPiCpt` (valid for **all**
    `w0 : Expr Nat` with zero `⊥`-approximation restriction!). -/
theorem lrTypeINPiKClosedCtx_substLet0_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 : Expr Nat}
    (hw0ty : HasTyT E n Γ w0 t)
    {A A' : Expr Nat} {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeINPiKClosedCtx E n (.letBinding t w0 :: Γ) A A' c) :
    LRTypeINPiKClosedCtx E n Γ (instantiate0 w0 A) (instantiate0 w0 A') c := by
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have h0 := lrTypeINPiKClosedCtx_substLet_botPiCpt
    (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) t w0 hc
    (Γ := .letBinding t w0 :: Γ) (j := 0) hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hw0ty)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- **Bidirectional `BotPiCpt`-Restricted Context-Aware Type Logical Relation
    (`LRTypeINBiDIKClosedCtx`):**
    Evaluated over `ApproxDIK E (ctxEnvDIK E Γ)` and `LRTypeINPiKClosedCtx E n Γ` across **all**
    contexts `Γ : LCtx` (without `LetFreeCtx Γ`!). -/
def LRTypeINBiDIKClosedCtx (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B : Expr Nat) : Prop :=
  ∀ c, BotPiCpt c →
    (ApproxDIK E (ctxEnvDIK E Γ) A c ∨ ApproxDIK E (ctxEnvDIK E Γ) B c) →
    LRTypeINPiKClosedCtx E n Γ A B c

theorem lrTypeINBiDIKClosedCtx_symm {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A B : Expr Nat} (h : LRTypeINBiDIKClosedCtx E n Γ A B) :
    LRTypeINBiDIKClosedCtx E n Γ B A :=
  fun c hc hBA => lrTypeINPiKClosedCtx_symm hW (h c hc hBA.symm)

theorem lrTypeINBiDIKClosedCtx_trans_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A M B : Expr Nat}
    (h₁ : LRTypeINBiDIKClosedCtx E n Γ A M) (h₂ : LRTypeINBiDIKClosedCtx E n Γ M B) :
    LRTypeINBiDIKClosedCtx E n Γ A B := by
  intro c hc hAB
  rcases hAB with hAc | hBc
  · have r₁ : LRTypeINPiKClosedCtx E n Γ A M c := h₁ c hc (Or.inl hAc)
    have hMc : ApproxDIK E (ctxEnvDIK E Γ) M c :=
      (approxDIK_of_lrTypeINPiKClosedCtx_botPiCpt hW hc r₁).2
    exact lrTypeINPiKClosedCtx_trans_of_envWfT hW r₁ (h₂ c hc (Or.inl hMc))
  · have r₂ : LRTypeINPiKClosedCtx E n Γ M B c := h₂ c hc (Or.inr hBc)
    have hMc : ApproxDIK E (ctxEnvDIK E Γ) M c :=
      (approxDIK_of_lrTypeINPiKClosedCtx_botPiCpt hW hc r₂).1
    exact lrTypeINPiKClosedCtx_trans_of_envWfT hW (h₁ c hc (Or.inr hMc)) r₂

theorem lrTypeINBiDIKClosedCtx_of_whRedPiKClosedCtx {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {M M' X X' : Expr Nat}
    (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    (h : LRTypeINBiDIKClosedCtx E n Γ X X') :
    LRTypeINBiDIKClosedCtx E n Γ M M' := by
  intro c hc hor
  have hor' : ApproxDIK E (ctxEnvDIK E Γ) X c ∨ ApproxDIK E (ctxEnvDIK E Γ) X' c :=
    hor.elim
      (fun hM => Or.inl ((semEqDIK_ctxEnvDIK_whRedPiKClosedCtx hW hX c).mp hM))
      (fun hM' => Or.inr ((semEqDIK_ctxEnvDIK_whRedPiKClosedCtx hW hX' c).mp hM'))
  exact lrTypeINPiKClosedCtx_expand hX hX' (h c hc hor')

theorem lrTypeINBiDIKClosedCtx_of_whStepPiKClosedCtx {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {M M' : Expr Nat}
    (hs : WhStepPiKClosedCtx E Γ M M')
    (hdiag : LRTypeINBiDIKClosedCtx E n Γ M' M') :
    LRTypeINBiDIKClosedCtx E n Γ M M' :=
  lrTypeINBiDIKClosedCtx_of_whRedPiKClosedCtx hW (.step hs (.refl _)) (.refl _) hdiag

/-- **Unconditional `ConvT.zetaLocal` Soundness in `LRTypeINBiDIKClosedCtx` Across ALL Contexts
    `Γ : LCtx` (`lrTypeINBiDIKClosedCtx_zetaLocal`):** -/
theorem lrTypeINBiDIKClosedCtx_zetaLocal {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {i : Nat} {v : Expr Nat} (hval : lookupValue Γ i = some v)
    (hdiag : LRTypeINBiDIKClosedCtx E n Γ v v) :
    LRTypeINBiDIKClosedCtx E n Γ (.bvar i) v :=
  lrTypeINBiDIKClosedCtx_of_whStepPiKClosedCtx hW (.zetaLocal hval) hdiag

theorem lrTypeINBiDIKClosedCtx_sorts (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l₁ l₂ : Level) :
    LRTypeINBiDIKClosedCtx E n Γ (.sort l₁) (.sort l₂) := by
  intro c _ hor
  rcases hor with h | h <;>
    (rcases approxDIK_sort_inv h with rfl | rfl; exact .bot _ _ _; exact .sort (.refl _) (.refl _))

theorem lrTypeINBiDIKClosedCtx_sort_diag (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level) :
    LRTypeINBiDIKClosedCtx E n Γ (.sort l) (.sort l) :=
  lrTypeINBiDIKClosedCtx_sorts E n Γ l l

/-- **Positive Satisfaction on `zetaLocalSortCtx` (`W-ZETALOCAL`) in `LRTypeINBiDIKClosedCtx`
    (`lrTypeINBiDIKClosedCtx_zetaLocalSortCtx`):**
    Whereas `zetaLocalSortCtx` refuted `LRTypeINBiDI`, `LRTypeINBiDIK`, and `LRTypeINBiDIKCanon`,
    `LRTypeINBiDIKClosedCtx E n zetaLocalSortCtx (.bvar 0) (.sort .zero)` holds **unconditionally**
    for every `E : ResolvedEnv` (`EnvWfT E`) and `n : Nat`! -/
theorem lrTypeINBiDIKClosedCtx_zetaLocalSortCtx {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) :
    LRTypeINBiDIKClosedCtx E n zetaLocalSortCtx (.bvar 0) (.sort .zero) :=
  lrTypeINBiDIKClosedCtx_zetaLocal hW rfl
    (lrTypeINBiDIKClosedCtx_sort_diag E n zetaLocalSortCtx .zero)

theorem lrTypeINBiDIKClosedCtx_weaken0 {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {A A' : Expr Nat} (h : LRTypeINBiDIKClosedCtx E n Γ A A') :
    LRTypeINBiDIKClosedCtx E n (d :: Γ) (lift 0 1 A) (lift 0 1 A') := by
  intro c hc hor
  have hor₀ : ApproxDIK E (ctxEnvDIK E Γ) A c ∨ ApproxDIK E (ctxEnvDIK E Γ) A' c :=
    hor.elim
      (fun hL => Or.inl ((approxDIK_ctxEnvDIK_cons_lift0_iff E d Γ A c).mp hL))
      (fun hR => Or.inr ((approxDIK_ctxEnvDIK_cons_lift0_iff E d Γ A' c).mp hR))
  exact lrTypeINPiKClosedCtx_weaken0_botPiCpt hcl hΓ' hc (h c hc hor₀)

/-- **Unconditional Head `let`-Substitution of `LRTypeINBiDIKClosedCtx` Across ALL Let-Values
    `w0 : Expr Nat` (`lrTypeINBiDIKClosedCtx_substLet0`):**
    Requires **zero** `⊥`-approximation restriction on `w0`! -/
theorem lrTypeINBiDIKClosedCtx_substLet0 {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 : Expr Nat}
    (hw0ty : HasTyT E n Γ w0 t)
    {A A' : Expr Nat}
    (h : LRTypeINBiDIKClosedCtx E n (.letBinding t w0 :: Γ) A A') :
    LRTypeINBiDIKClosedCtx E n Γ (instantiate0 w0 A) (instantiate0 w0 A') := by
  intro c hc hor
  have hor₀ :
      ApproxDIK E (ctxEnvDIK E (.letBinding t w0 :: Γ)) A c ∨
        ApproxDIK E (ctxEnvDIK E (.letBinding t w0 :: Γ)) A' c :=
    hor.elim
      (fun hL => Or.inl ((approxDIK_ctxEnvDIK_substLet0_iff E t w0 Γ A c).mp hL))
      (fun hR => Or.inr ((approxDIK_ctxEnvDIK_substLet0_iff E t w0 Γ A' c).mp hR))
  exact lrTypeINPiKClosedCtx_substLet0_botPiCpt hW hΓ hw0ty hc (h c hc hor₀)

/-- Unrestricted `BotPiCpt` fundamental supply for `LRTypeINPiKClosedCtx` over `ApproxDIK E (ctxEnvDIK E Γ)`
    across **all** well-formed contexts `CtxWfT E n Γ` (no `LetFreeCtx Γ` restriction!). -/
def FundamentalLRINBotDIKClosedCtx (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A B : Expr Nat}, TyConvT E n Γ A B →
      ∀ c, BotPiCpt c → ApproxDIK E (ctxEnvDIK E Γ) A c → LRTypeINPiKClosedCtx E n Γ A B c

/-- Chain closure for `FundamentalLRINBotDIKClosedCtx` across **all** `CtxWfT E n Γ` from diagonal
    and single-link supplies. -/
theorem fundamentalLRINBotDIKClosedCtx_of_links {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hdiag : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ A : Expr Nat, LRTypeINBiDIKClosedCtx E n Γ A A)
    (hlink : ∀ {Γ : LCtx}, CtxWfT E n Γ →
      ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) → LRTypeINBiDIKClosedCtx E n Γ A B) :
    FundamentalLRINBotDIKClosedCtx E n := by
  have hbi : ∀ {Γ : LCtx}, CtxWfT E n Γ →
      ∀ {A B : Expr Nat}, TyConvT E n Γ A B → LRTypeINBiDIKClosedCtx E n Γ A B := by
    intro Γ hΓ A B hc
    induction hc with
    | refl A => exact hdiag hΓ A
    | of A B _ h => exact hlink hΓ h
    | trans A B C _ _ ih₁ ih₂ => exact lrTypeINBiDIKClosedCtx_trans_of_envWfT hW ih₁ ih₂
  intro Γ hΓ A B hc c hbc hA
  exact hbi hΓ hc c hbc (Or.inl hA)

/-- **Direct `PiRowField E n` Extraction from `FundamentalLRINBotDIKClosedCtx` Across ALL Contexts
    `Γ : LCtx` (`piRow_of_fundamentalLRINBotDIKClosedCtx`):**
    Because `LRTypeINPiKClosedCtx` is defined directly on all contexts `Γ : LCtx`, `PiRowField E n`
    projects in 8 lines without needing `LetFreeCtx`! -/
theorem piRow_of_fundamentalLRINBotDIKClosedCtx {E : ResolvedEnv} {n : Nat}
    (hF : FundamentalLRINBotDIKClosedCtx E n) : PiRowField E n := by
  intro Γ hΓ A₁ B₁ A₂ B₂ h
  have hlr : LRTypeINPiKClosedCtx E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.pi .bot []) :=
    hF hΓ h (.pi .bot []) botPiCpt_pi_bot_nil (approxDIK_pi_bot_nil E (ctxEnvDIK E Γ) A₁ B₁)
  cases hlr with
  | pi hA hB _ hdom hcod _ _ =>
      have e₁ := whRedPiKClosedCtx_pi_eq hA
      have e₂ := whRedPiKClosedCtx_pi_eq hB
      injection e₁ with eA₁ eB₁
      injection e₂ with eA₂ eB₂
      subst eA₁; subst eB₁; subst eA₂; subst eB₂
      exact ⟨⟨hdom⟩, ⟨hcod⟩⟩

/-! ### §7.2. `LRTermDSubKClosedCtxCore`, `LRTermDSubKClosedCtx`, and `LRTermDSubKClosedCtxBi`:
Closing `ConvT.zetaLocal`, `HasTyT.letE`, and `ConvT.zeta` Unconditionally Across All Contexts -/

/-- **Context-Aware Term Logical Relation Over `WhRedPiKClosedCtx E Γ` (`LRTermDSubKClosedCtxCore`):** -/
def LRTermDSubKClosedCtxCore (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : CptI → Prop
  | .bot => True
  | .sort => (∃ l, WhRedPiKClosedCtx E Γ A (.sort l)) ∧ LRTypeINPiKClosedCtx E n Γ M M' .sort
  | .pi a f =>
      (∃ l, WhRedPiKClosedCtx E Γ A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ u₁,
        WhRedPiKClosedCtx E Γ M (.pi A₁ B₁) ∧
        WhRedPiKClosedCtx E Γ M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧
        Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        LRTermDSubKClosedCtxCore E n Γ A₁ A₂ (.sort u₁) a ∧
        ∀ s ∈ f, ∃ w₁,
          Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁)) ∧
          ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
            ConvT E n Γ N N' A₁ →
            (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKClosedCtxCore E n Γ N N' A₁ u) →
            IsPropTyI E n Γ (instantiate0 N B₁) ∨
              LRTermDSubKClosedCtxCore E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁) s.2
  | .spine r args =>
      ((∃ l, WhRedPiKClosedCtx E Γ A (.sort l)) ∧ LRTypeINPiKClosedCtx E n Γ M M' (.spine r args)) ∨
      (∃ ls₁ ls₂ : List Level, ∃ args₁ args₂ : List (Expr Nat),
        WhRedPiKClosedCtx E Γ M (foldApps (.const r ls₁) args₁) ∧
        WhRedPiKClosedCtx E Γ M' (foldApps (.const r ls₂) args₂) ∧
        WhNormalPiKClosedCtx E Γ (foldApps (.const r ls₁) args₁) ∧
        WhNormalPiKClosedCtx E Γ (foldApps (.const r ls₂) args₂) ∧
        Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁) (foldApps (.const r ls₂) args₂) A) ∧
        args₁.length = args.length ∧
        args₂.length = args.length)
  | .lam g =>
      ∃ A₁ B₁ : Expr Nat, ∃ w : Level,
        WhRedPiKClosedCtx E Γ A (.pi A₁ B₁) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          ConvT E n Γ N N' A₁ →
          (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKClosedCtxCore E n Γ N N' A₁ u) →
          IsPropTyI E n Γ (instantiate0 N B₁) ∨
            LRTermDSubKClosedCtxCore E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
termination_by c => sizeOf c
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

/-- Top-level `IsPropTyI`-collapsed `LRTermDSubKClosedCtx`. -/
def LRTermDSubKClosedCtx (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (u : CptI) : Prop :=
  IsPropTyI E n Γ A ∨ LRTermDSubKClosedCtxCore E n Γ M M' A u

/-- Bidirectional `ProbeCpt`-restricted context-aware term logical relation over
    `ApproxDIK E (ctxEnvDIK E Γ)` and `LRTermDSubKClosedCtx` across **all** contexts `Γ : LCtx`. -/
def LRTermDSubKClosedCtxBi (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : Prop :=
  ∀ c, ProbeCpt c →
    (ApproxDIK E (ctxEnvDIK E Γ) M c ∨ ApproxDIK E (ctxEnvDIK E Γ) M' c) →
    LRTermDSubKClosedCtx E n Γ M M' A c

theorem lrTermDSubKClosedCtxCore_bot_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermDSubKClosedCtxCore E n Γ M M' A .bot ↔ True := by
  rw [LRTermDSubKClosedCtxCore.eq_def]

theorem lrTermDSubKClosedCtxCore_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermDSubKClosedCtxCore E n Γ M M' A .sort ↔
      (∃ l, WhRedPiKClosedCtx E Γ A (.sort l)) ∧ LRTypeINPiKClosedCtx E n Γ M M' .sort := by
  rw [LRTermDSubKClosedCtxCore.eq_def]

theorem lrTermDSubKClosedCtxCore_pi_iff (Γ : LCtx) (M M' A : Expr Nat)
    (a : CptI) (f : List (List CptI × CptI)) :
    LRTermDSubKClosedCtxCore E n Γ M M' A (.pi a f) ↔
      (∃ l, WhRedPiKClosedCtx E Γ A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ u₁,
        WhRedPiKClosedCtx E Γ M (.pi A₁ B₁) ∧
        WhRedPiKClosedCtx E Γ M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧
        Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        LRTermDSubKClosedCtxCore E n Γ A₁ A₂ (.sort u₁) a ∧
        ∀ s ∈ f, ∃ w₁,
          Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w₁)) ∧
          ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
            ConvT E n Γ N N' A₁ →
            (∀ u ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKClosedCtxCore E n Γ N N' A₁ u) →
            IsPropTyI E n Γ (instantiate0 N B₁) ∨
              LRTermDSubKClosedCtxCore E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort w₁) s.2 := by
  rw [LRTermDSubKClosedCtxCore.eq_def]

/-- **Exact Non-`⊥` `ProbeCpt` Characterization (`lrTermDSubKClosedCtxCore_probe_nonbot_iff`):** -/
theorem lrTermDSubKClosedCtxCore_probe_nonbot_iff {Γ : LCtx} {M M' A : Expr Nat}
    {c : CptI} (hc : ProbeCpt c) (hne : c ≠ .bot) :
    LRTermDSubKClosedCtxCore E n Γ M M' A c ↔
      (∃ l, WhRedPiKClosedCtx E Γ A (.sort l)) ∧ LRTypeINPiKClosedCtx E n Γ M M' c := by
  cases hc with
  | bot => exact (hne rfl).elim
  | sort => exact lrTermDSubKClosedCtxCore_sort_iff Γ M M' A
  | piBotNil =>
      rw [lrTermDSubKClosedCtxCore_pi_iff]
      constructor
      · rintro ⟨hl, A₁, B₁, A₂, B₂, _, h1, h2, ⟨hΓ₁⟩, ⟨hcA⟩, ⟨hcB⟩, _, _⟩
        exact ⟨hl, .pi h1 h2 hΓ₁ hcA hcB (.bot Γ A₁ A₂) (fun _ hs => (List.not_mem_nil _ hs).elim)⟩
      · rintro ⟨hl, hpi⟩
        cases hpi with
        | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h1 h2 hΓ₁ hcA hcB _ _ =>
            exact ⟨hl, A₁, B₁, A₂, B₂, .zero, h1, h2, ⟨hΓ₁⟩, ⟨hcA⟩, ⟨hcB⟩,
              by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial,
              fun _ hs => (List.not_mem_nil _ hs).elim⟩

theorem lrTypeINPiKClosedCtx_of_lrTermDSubKClosedCtxCore_probe {Γ : LCtx} {M M' A : Expr Nat}
    {c : CptI} (hc : ProbeCpt c) (h : LRTermDSubKClosedCtxCore E n Γ M M' A c) :
    LRTypeINPiKClosedCtx E n Γ M M' c := by
  cases hc with
  | bot => exact .bot Γ M M'
  | sort => exact ((lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)).mp h).2
  | piBotNil => exact ((lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)).mp h).2

theorem approxDIK_of_lrTermDSubKClosedCtxCore_probe (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c) (h : LRTermDSubKClosedCtxCore E n Γ M M' A c) :
    ApproxDIK E (ctxEnvDIK E Γ) M c ∧ ApproxDIK E (ctxEnvDIK E Γ) M' c :=
  approxDIK_of_lrTypeINPiKClosedCtx_botPiCpt hW (botPiCpt_of_probeCpt hc)
    (lrTypeINPiKClosedCtx_of_lrTermDSubKClosedCtxCore_probe hc h)

theorem lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_expand_probe {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    {c : CptI} (hc : ProbeCpt c) (h : LRTermDSubKClosedCtxCore E n Γ X X' A c) :
    LRTermDSubKClosedCtxCore E n Γ M M' A c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h ⊢
      exact ⟨h.1, lrTypeINPiKClosedCtx_expand hX hX' h.2⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h ⊢
      exact ⟨h.1, lrTypeINPiKClosedCtx_expand hX hX' h.2⟩

theorem lrTermDSubKClosedCtx_whRedPiKClosedCtx_expand_probe {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    {c : CptI} (hc : ProbeCpt c) (h : LRTermDSubKClosedCtx E n Γ X X' A c) :
    LRTermDSubKClosedCtx E n Γ M M' A c :=
  h.elim Or.inl (fun hC => Or.inr (lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_expand_probe hX hX' hc hC))

theorem lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand (hW : EnvWfT E)
    {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    (h : LRTermDSubKClosedCtxBi E n Γ X X' A) :
    LRTermDSubKClosedCtxBi E n Γ M M' A := by
  intro c hc hor
  have hor' : ApproxDIK E (ctxEnvDIK E Γ) X c ∨ ApproxDIK E (ctxEnvDIK E Γ) X' c :=
    hor.elim
      (fun hM => Or.inl ((semEqDIK_ctxEnvDIK_whRedPiKClosedCtx hW hX c).mp hM))
      (fun hM' => Or.inr ((semEqDIK_ctxEnvDIK_whRedPiKClosedCtx hW hX' c).mp hM'))
  exact lrTermDSubKClosedCtx_whRedPiKClosedCtx_expand_probe hX hX' hc (h c hc hor')

theorem lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat}
    (hs : WhStepPiKClosedCtx E Γ M M') (hdiag : LRTermDSubKClosedCtxBi E n Γ M' M' A) :
    LRTermDSubKClosedCtxBi E n Γ M M' A :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW (.step hs (.refl _)) (.refl _) hdiag

/-- Unconditional symmetry of `LRTermDSubKClosedCtxBi` across **all** contexts `Γ : LCtx`. -/
theorem lrTermDSubKClosedCtxBi_symm (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat}
    (h : LRTermDSubKClosedCtxBi E n Γ M M' A) :
    LRTermDSubKClosedCtxBi E n Γ M' M A := by
  intro c hc hor
  rcases h c hc hor.symm with hP | hC
  · exact Or.inl hP
  · refine Or.inr ?_
    cases hc with
    | bot => rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial
    | sort =>
        rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at hC ⊢
        exact ⟨hC.1, lrTypeINPiKClosedCtx_symm hW hC.2⟩
    | piBotNil =>
        rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at hC ⊢
        exact ⟨hC.1, lrTypeINPiKClosedCtx_symm hW hC.2⟩

/-- Unconditional transitivity of `LRTermDSubKClosedCtxBi` across **all** contexts `Γ : LCtx`. -/
theorem lrTermDSubKClosedCtxBi_trans (hW : EnvWfT E)
    {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat}
    (h₁₂ : LRTermDSubKClosedCtxBi E n Γ M₁ M₂ A)
    (h₂₃ : LRTermDSubKClosedCtxBi E n Γ M₂ M₃ A) :
    LRTermDSubKClosedCtxBi E n Γ M₁ M₃ A := by
  have htransCore : ∀ {c : CptI} (hc : ProbeCpt c),
      LRTermDSubKClosedCtxCore E n Γ M₁ M₂ A c →
      LRTermDSubKClosedCtxCore E n Γ M₂ M₃ A c →
      LRTermDSubKClosedCtxCore E n Γ M₁ M₃ A c := by
    intro c hc h₁ h₂
    cases hc with
    | bot => rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial
    | sort =>
        rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h₁ h₂ ⊢
        exact ⟨h₁.1, lrTypeINPiKClosedCtx_trans_of_envWfT hW h₁.2 h₂.2⟩
    | piBotNil =>
        rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h₁ h₂ ⊢
        exact ⟨h₁.1, lrTypeINPiKClosedCtx_trans_of_envWfT hW h₁.2 h₂.2⟩
  intro c hc hor
  rcases hor with h₁ | h₃
  · rcases h₁₂ c hc (Or.inl h₁) with hP | hC₁₂
    · exact Or.inl hP
    · have h₂ : ApproxDIK E (ctxEnvDIK E Γ) M₂ c :=
        (approxDIK_of_lrTermDSubKClosedCtxCore_probe hW hc hC₁₂).2
      rcases h₂₃ c hc (Or.inl h₂) with hP | hC₂₃
      · exact Or.inl hP
      · exact Or.inr (htransCore hc hC₁₂ hC₂₃)
  · rcases h₂₃ c hc (Or.inr h₃) with hP | hC₂₃
    · exact Or.inl hP
    · have h₂ : ApproxDIK E (ctxEnvDIK E Γ) M₂ c :=
        (approxDIK_of_lrTermDSubKClosedCtxCore_probe hW hc hC₂₃).1
      rcases h₁₂ c hc (Or.inr h₂) with hP | hC₁₂
      · exact Or.inl hP
      · exact Or.inr (htransCore hc hC₁₂ hC₂₃)

/-- **Unconditional `let`-Substitution for `LRTermDSubKClosedCtxCore` on `ProbeCpt` Across ALL
    Let-Values `w0 : Expr Nat` (`lrTermDSubKClosedCtxCore_substLet_probe`):**
    Requires **zero** `⊥`-approximation restriction on `w0`! -/
theorem lrTermDSubKClosedCtxCore_substLet_probe (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (t w0 : Expr Nat)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.letBinding t w0))
    (hvty : HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove w0 j Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCtxCore E n Γ M M' A c) :
    LRTermDSubKClosedCtxCore E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) M) (instantiate j (lift 0 j w0) M')
      (instantiate j (lift 0 j w0) A) c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosedCtx_substLet_of_envClosed hcl hget hl⟩,
        lrTypeINPiKClosedCtx_substLet_botPiCpt hcl hinst t w0 .sort hget hvty hΓ' hlr⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosedCtx_substLet_of_envClosed hcl hget hl⟩,
        lrTypeINPiKClosedCtx_substLet_botPiCpt hcl hinst t w0 botPiCpt_pi_bot_nil hget hvty hΓ' hlr⟩

theorem lrTermDSubKClosedCtx_substLet0_probe (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 : Expr Nat}
    (hw0ty : HasTyT E n Γ w0 t)
    {M M' A : Expr Nat} {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCtx E n (.letBinding t w0 :: Γ) M M' A c) :
    LRTermDSubKClosedCtx E n Γ (instantiate0 w0 M) (instantiate0 w0 M') (instantiate0 w0 A) c := by
  have hcl := envClosed_of_envWfT hW
  have hinst := envMembersSubstStable_of_envWfT hW
  have hget0 : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_substLet0_of_sortRow hW hSort hw0ty hP)
  · have hC' := lrTermDSubKClosedCtxCore_substLet_probe hcl hinst t w0 hget0
      (by simpa only [substRemove_zero_cons, lift_zero] using hw0ty)
      (by simpa only [substRemove_zero_cons] using hΓ) hc hC
    exact Or.inr (by simpa only [substRemove_zero_cons, lift_zero, instantiate0] using hC')

/-- **Unconditional Head `let`-Substitution of `LRTermDSubKClosedCtxBi` Across ALL Let-Values
    `w0 : Expr Nat` (`lrTermDSubKClosedCtxBi_substLet0`):**
    Holds for **every** `w0 : Expr Nat` with **zero** `⊥`-approximation restriction! -/
theorem lrTermDSubKClosedCtxBi_substLet0 (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t w0 : Expr Nat}
    (hw0ty : HasTyT E n Γ w0 t)
    {M M' A : Expr Nat}
    (h : LRTermDSubKClosedCtxBi E n (.letBinding t w0 :: Γ) M M' A) :
    LRTermDSubKClosedCtxBi E n Γ (instantiate0 w0 M) (instantiate0 w0 M') (instantiate0 w0 A) := by
  intro c hc hor
  have hor₀ :
      ApproxDIK E (ctxEnvDIK E (.letBinding t w0 :: Γ)) M c ∨
        ApproxDIK E (ctxEnvDIK E (.letBinding t w0 :: Γ)) M' c :=
    hor.elim
      (fun hL => Or.inl ((approxDIK_ctxEnvDIK_substLet0_iff E t w0 Γ M c).mp hL))
      (fun hR => Or.inr ((approxDIK_ctxEnvDIK_substLet0_iff E t w0 Γ M' c).mp hR))
  exact lrTermDSubKClosedCtx_substLet0_probe hW hSort hΓ hw0ty hc (h c hc hor₀)

/-- **1. Unconditional `ConvT.zetaLocal` Soundness in `LRTermDSubKClosedCtxBi` Across ALL Contexts
    `Γ : LCtx` (`lrTermDSubKClosedCtxBi_zetaLocal`):** -/
theorem lrTermDSubKClosedCtxBi_zetaLocal (hW : EnvWfT E)
    {Γ : LCtx} {i : Nat} {v A : Expr Nat} (hval : lookupValue Γ i = some v)
    (hdiag : LRTermDSubKClosedCtxBi E n Γ v v A) :
    LRTermDSubKClosedCtxBi E n Γ (.bvar i) v A :=
  lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW (.zetaLocal hval) hdiag

/-- **2. Unconditional `ConvT.zeta` Soundness in `LRTermDSubKClosedCtxBi` Across ALL Contexts
    `Γ : LCtx` and ALL Let-Values `v : Expr Nat` (`lrTermDSubKClosedCtxBi_zeta`):**
    Closes `ConvT.zeta` directly from the body induction hypothesis
    `ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A v :: Γ) b b B` alone! -/
theorem lrTermDSubKClosedCtxBi_zeta (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A v b B : Expr Nat}
    (hv_ty : HasTyT E n Γ v A)
    (ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A v :: Γ) b b B) :
    LRTermDSubKClosedCtxBi E n Γ (.letE A v b) (instantiate0 v b) (instantiate0 v B) :=
  lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW (.of_whStep (.zeta A v b))
    (lrTermDSubKClosedCtxBi_substLet0 hW hSort hΓ hv_ty ih_b)

/-- **3. Unconditional `HasTyT.letE` Soundness in `LRTermDSubKClosedCtxBi` Across ALL Contexts
    `Γ : LCtx` and ALL Let-Values `v : Expr Nat` (`lrTermDSubKClosedCtxBi_letE_diag`):**
    Closes `HasTyT.letE` directly from the body induction hypothesis
    `ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A v :: Γ) b b B` alone! -/
theorem lrTermDSubKClosedCtxBi_letE_diag (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A v b B : Expr Nat}
    (hv_ty : HasTyT E n Γ v A)
    (ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A v :: Γ) b b B) :
    LRTermDSubKClosedCtxBi E n Γ (.letE A v b) (.letE A v b) (instantiate0 v B) :=
  have hstep : WhRedPiKClosedCtx E Γ (.letE A v b) (instantiate0 v b) :=
    .step (.of_whStep (.zeta A v b)) (.refl _)
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW hstep hstep
    (lrTermDSubKClosedCtxBi_substLet0 hW hSort hΓ hv_ty ih_b)

theorem lrTermDSubKClosedCtxBi_sorts (Γ : LCtx) (l₁ l₂ : Level) :
    LRTermDSubKClosedCtxBi E n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) := by
  intro c hc hor
  rcases hor with h | h <;>
    (rcases approxDIK_sort_inv h with rfl | rfl
     · exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial)
     · refine Or.inr ?_
       rw [lrTermDSubKClosedCtxCore_sort_iff]
       exact ⟨⟨.succ l₁, .refl _⟩, .sort (.refl _) (.refl _)⟩)

theorem lrTermDSubKClosedCtxBi_sort_diag (Γ : LCtx) (l : Level) :
    LRTermDSubKClosedCtxBi E n Γ (.sort l) (.sort l) (.sort (.succ l)) :=
  lrTermDSubKClosedCtxBi_sorts Γ l l

theorem lrTermDSubKClosedCtxBi_lam (Γ : LCtx) (A A' b b' B : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ (.lam A b) (.lam A' b') (.pi A B) := by
  intro c hc hor
  rcases hor with h | h <;>
    (rw [approxDIK_lam_botPiCpt_eq_bot (botPiCpt_of_probeCpt hc) h]
     exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial))

theorem lrTermDSubKClosedCtxBi_consts_of_body_none {Γ : LCtx} {r : Nat} (ls ls' : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = none) :
    LRTermDSubKClosedCtxBi E n Γ (.const r ls) (.const r ls') A := by
  intro c hc hor
  rcases hor with h | h <;>
    (rw [approxDIK_const_body_none_botPiCpt_eq_bot hm hb (botPiCpt_of_probeCpt hc) h]
     exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial))

theorem lrTermDSubKClosedCtxBi_deltaConsts (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember} {b A : Expr Nat} (hdelta : DeltaConst E r m b)
    (ih : LRTermDSubKClosedCtxBi E n Γ (instantiateLevels ls b) (instantiateLevels ls' b) A) :
    LRTermDSubKClosedCtxBi E n Γ (.const r ls) (.const r ls') A :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW
    (.step (.of_whStep (.delta hdelta.1 hdelta.2.1)) (.refl _))
    (.step (.of_whStep (.delta hdelta.1 hdelta.2.1)) (.refl _)) ih

/-- **`ConvT.pi` in `LRTermDSubKClosedCtxBi` (`lrTermDSubKClosedCtxBi_pi`, ZERO Semantic Induction
    Hypotheses, Across ALL Contexts `Γ : LCtx`):** -/
theorem lrTermDSubKClosedCtxBi_pi {Γ : LCtx} {A₁ A₂ B₁ B₂ : Expr Nat} {u v : Level}
    (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
    (hdom : TyConvT E n Γ A₁ A₂)
    (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :
    LRTermDSubKClosedCtxBi E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort (.imax u v)) := by
  intro c hc hor
  rcases hor with h | h <;>
    (rcases approxDIK_pi_probe_inv hc h with rfl | rfl
     · exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial)
     · refine Or.inr ?_
       rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)]
       exact ⟨⟨.imax u v, .refl _⟩,
         .pi (.refl _) (.refl _) hΓ₁ hdom hcod (.bot _ _ _)
           (fun _ hs => (List.not_mem_nil _ hs).elim)⟩)

theorem lrTermDSubKClosedCtxBi_pi_diag {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} (B : Expr Nat) {u : Level} (v : Level)
    (hA : HasTyT E n Γ A (.sort u)) :
    LRTermDSubKClosedCtxBi E n Γ (.pi A B) (.pi A B) (.sort (.imax u v)) :=
  lrTermDSubKClosedCtxBi_pi (.assumption Γ A u hΓ hA) (.refl Γ A) (.refl (.assumption A :: Γ) B)

theorem not_lrTermDSubKClosedCtxCore_at_pi_of_probe_ne_bot {Γ : LCtx} {M M' A B : Expr Nat}
    {c : CptI} (hc : ProbeCpt c) (hne : c ≠ .bot)
    (h : LRTermDSubKClosedCtxCore E n Γ M M' (.pi A B) c) : False := by
  obtain ⟨⟨l, hl⟩, _⟩ := (lrTermDSubKClosedCtxCore_probe_nonbot_iff hc hne).mp h
  exact Expr.noConfusion (whRedPiKClosedCtx_pi_eq hl)

/-- **`ConvT.eta` in `LRTermDSubKClosedCtxBi` Across ALL Contexts `Γ : LCtx`
    (`lrTermDSubKClosedCtxBi_eta`):** -/
theorem lrTermDSubKClosedCtxBi_eta {Γ : LCtx} {f A B : Expr Nat}
    (hdiag : LRTermDSubKClosedCtxBi E n Γ f f (.pi A B)) :
    LRTermDSubKClosedCtxBi E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) := by
  intro c hc hor
  rcases hor with hlam | hf
  · rw [approxDIK_lam_botPiCpt_eq_bot (botPiCpt_of_probeCpt hc) hlam]
    exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial)
  · rcases hdiag c hc (Or.inl hf) with hP | hC
    · exact Or.inl hP
    · cases hc with
      | bot => exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial)
      | sort => exact (not_lrTermDSubKClosedCtxCore_at_pi_of_probe_ne_bot .sort (by intro h0; cases h0) hC).elim
      | piBotNil => exact (not_lrTermDSubKClosedCtxCore_at_pi_of_probe_ne_bot .piBotNil (by intro h0; cases h0) hC).elim

/-- **`ConvT.irr` in `LRTermDSubKClosedCtxBi` Across ALL Contexts `Γ : LCtx`
    (`lrTermDSubKClosedCtxBi_irr_of_sortRow`):** -/
theorem lrTermDSubKClosedCtxBi_irr_of_sortRow
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero)) :
    LRTermDSubKClosedCtxBi E n Γ p q P :=
  fun _ _ _ => Or.inl (isPropTyI_of_hasTyT_sort_zero hSort hP)

/-- **Self-Contained Type-Conversion Transport in `LRTermDSubKClosedCtxBi` Across ALL Contexts
    `Γ : LCtx` (`lrTermDSubKClosedCtxBi_tyConv_of_bi`):**
    Requires **only** `ih_AB : LRTermDSubKClosedCtxBi E n Γ A B (.sort u)` (with **zero**
    `FundamentalLRINBotDIKClosedCtx` hypothesis!). -/
theorem lrTermDSubKClosedCtxBi_tyConv_of_bi (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hcAB : TyConvT E n Γ A B)
    (ih_M : LRTermDSubKClosedCtxBi E n Γ M M' A)
    (ih_AB : LRTermDSubKClosedCtxBi E n Γ A B (.sort u)) :
    LRTermDSubKClosedCtxBi E n Γ M M' B := by
  intro c hc hor
  rcases ih_M c hc hor with hP | hC
  · exact Or.inl (hProp hΓ hA hcAB hP)
  · refine Or.inr ?_
    cases hc with
    | bot => rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial
    | sort =>
        rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at hC ⊢
        obtain ⟨⟨l, hl⟩, hlr⟩ := hC
        have hAs : ApproxDIK E (ctxEnvDIK E Γ) A .sort :=
          approxDIK_ctxEnvDIK_sort_of_whRedPiKClosedCtx hW hl
        rcases ih_AB .sort .sort (Or.inl hAs) with hPs | hCs
        · exact (not_isPropTyI_sort E n Γ u hPs).elim
        · obtain ⟨_, hABs⟩ :=
            (lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)).mp hCs
          cases hABs with
          | sort _ hBs => exact ⟨⟨_, hBs⟩, hlr⟩
    | piBotNil =>
        rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at hC ⊢
        obtain ⟨⟨l, hl⟩, hlr⟩ := hC
        have hAs : ApproxDIK E (ctxEnvDIK E Γ) A .sort :=
          approxDIK_ctxEnvDIK_sort_of_whRedPiKClosedCtx hW hl
        rcases ih_AB .sort .sort (Or.inl hAs) with hPs | hCs
        · exact (not_isPropTyI_sort E n Γ u hPs).elim
        · obtain ⟨_, hABs⟩ :=
            (lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)).mp hCs
          cases hABs with
          | sort _ hBs => exact ⟨⟨_, hBs⟩, hlr⟩

/-- **1. Positive Satisfaction on `zetaLocalSortCtx` (`W-ZETALOCAL`) in `LRTermDSubKClosedCtxBi`
    (`lrTermDSubKClosedCtxBi_zetaLocalSortCtx`):** -/
theorem lrTermDSubKClosedCtxBi_zetaLocalSortCtx (hW : EnvWfT E) :
    LRTermDSubKClosedCtxBi E n zetaLocalSortCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero)) :=
  lrTermDSubKClosedCtxBi_zetaLocal hW rfl
    (lrTermDSubKClosedCtxBi_sort_diag zetaLocalSortCtx .zero)

/-- **2. Positive Satisfaction on `idPiProp` (`W-DEMAND`) in `LRTermDSubKClosedCtxBi`
    (`lrTermDSubKClosedCtxBi_idPiProp`):** -/
theorem lrTermDSubKClosedCtxBi_idPiProp :
    LRTermDSubKClosedCtxBi E n [] idPiProp idPiProp (.sort (.imax (.succ .zero) .zero)) :=
  lrTermDSubKClosedCtxBi_pi_diag .nil (.bvar 0) .zero (.sort [] .zero)

/-- **3. Positive Satisfaction on `closedIrrPiL` / `closedIrrPiR` (`W-IrrPi`) in
    `LRTermDSubKClosedCtxBi` (`lrTermDSubKClosedCtxBi_closedIrrPi`):** -/
theorem lrTermDSubKClosedCtxBi_closedIrrPi :
    LRTermDSubKClosedCtxBi E n [] closedIrrPiL closedIrrPiR
      (.sort (.imax (.succ .zero)
        (.imax (.imax .zero (.succ .zero)) (.imax .zero (.imax .zero .zero))))) := by
  let Γ₁ : LCtx := [.assumption (.sort .zero)]
  let Γ₂ : LCtx := .assumption (.pi (.bvar 0) (.sort .zero)) :: Γ₁
  let Γ₃ : LCtx := .assumption (.bvar 1) :: Γ₂
  let Γ₄ : LCtx := .assumption (.bvar 2) :: Γ₃
  have hA₁ : HasTyT E n Γ₁ (.pi (.bvar 0) (.sort .zero)) (.sort (.imax .zero (.succ .zero))) :=
    .pi Γ₁ (.bvar 0) .zero (.sort .zero) (.succ .zero)
      (.bvar Γ₁ 0 (.sort .zero) rfl) (.sort _ .zero)
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
  exact lrTermDSubKClosedCtxBi_pi
    (.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero))
    (.refl [] (.sort .zero))
    (.of Γ₁ _ _ _ hcod₁)

/-- **4. Positive Satisfaction on `trueEnvU_kRecVar` (`W-K` 0-Field) in `LRTermDSubKClosedCtxBi`
    (`lrTermDSubKClosedCtxBi_trueEnvU_kRecVar_sort`):** -/
theorem lrTermDSubKClosedCtxBi_trueEnvU_kRecVar_sort :
    LRTermDSubKClosedCtxBi trueEnvU n trueEnvU_kVarCtx
      trueEnvU_kRecVar (.sort .zero) (.sort (.succ .zero)) :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand trueEnvUWfT
    whRedPiKClosedCtx_trueEnvU_kRecVar_sort (.refl _)
    (lrTermDSubKClosedCtxBi_sort_diag trueEnvU_kVarCtx .zero)

/-- **5. Positive Satisfaction on `andEnvU` `mixAndRedex` (`W-K` Fieldful) in
    `LRTermDSubKClosedCtxBi` (`lrTermDSubKClosedCtxBi_andEnvU_mixAndRedex_mixPi`):** -/
theorem lrTermDSubKClosedCtxBi_andEnvU_mixAndRedex_mixPi :
    LRTermDSubKClosedCtxBi andEnvU 0 mixAndCtx
      mixAndRedex mixPi (.sort (.imax (.succ .zero) (.succ .zero))) :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand andEnvUWfT
    whRedPiKClosedCtx_andEnvU_mixAndRedex_mixPi (.refl _)
    (lrTermDSubKClosedCtxBi_pi_diag Rcic.Domain.Model.PiInversion.mixAndCtx_wf
      (.sort .zero) (.succ .zero) (.sort mixAndCtx .zero))

/-- Unrestricted `ProbeCpt` fundamental supply for `LRTermDSubKClosedCtxBi` across **all**
    `CtxWfT E n Γ` (no `LetFreeCtx Γ` restriction!). -/
def FundamentalTermDSubKClosedCtxBiProbe (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {M A : Expr Nat}, HasTyT E n Γ M A → LRTermDSubKClosedCtxBi E n Γ M M A) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {M M' A : Expr Nat},
      HasTyT E n Γ M A → HasTyT E n Γ M' A → ConvT E n Γ M M' A →
      LRTermDSubKClosedCtxBi E n Γ M M' A)

/-- **Direct `PiRowField E n` Extraction from `FundamentalTermDSubKClosedCtxBiProbe` Across ALL
    Contexts `Γ : LCtx` (`piRow_of_fundamentalTermDSubKClosedCtxBiProbe`):**
    Walks `TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)` directly at the single probe compact
    `c = .pi .bot []` (`ProbeCpt.piBotNil`) on any well-formed context `Γ : LCtx` without
    needing `LetFreeCtx Γ`! -/
theorem piRow_of_fundamentalTermDSubKClosedCtxBiProbe (hW : EnvWfT E)
    (hF : FundamentalTermDSubKClosedCtxBiProbe E n) : PiRowField E n := by
  intro Γ hΓ A₁ B₁ A₂ B₂ h
  have hwalk : ∀ {X Y : Expr Nat} {u : Level},
      HasTyT E n Γ X (.sort u) → TyConvT E n Γ X Y →
      ApproxDIK E (ctxEnvDIK E Γ) X (.pi .bot []) →
      LRTypeINPiKClosedCtx E n Γ X Y (.pi .bot []) := by
    intro X Y u hX htc
    revert u
    induction htc with
    | refl X =>
        intro u hX hAc
        rcases hF.1 hΓ hX (.pi .bot []) .piBotNil (Or.inl hAc) with hP | hC
        · exact (not_isPropTyI_sort E n Γ u hP).elim
        · exact lrTypeINPiKClosedCtx_of_lrTermDSubKClosedCtxCore_probe .piBotNil hC
    | of X Y v hc =>
        intro _ _ hAc
        rcases hF.2 hΓ (convEnds hW hΓ hc).1 (convEnds hW hΓ hc).2.1 hc
            (.pi .bot []) .piBotNil (Or.inl hAc) with hP | hC
        · exact (not_isPropTyI_sort E n Γ v hP).elim
        · exact lrTypeINPiKClosedCtx_of_lrTermDSubKClosedCtxCore_probe .piBotNil hC
    | trans X M Y c₁ c₂ ih₁ ih₂ =>
        intro u hX hAc
        obtain ⟨v, hM⟩ := tyConvT_endTyped hW hΓ c₁ hX
        have r₁ := ih₁ hX hAc
        have hcM := (approxDIK_of_lrTypeINPiKClosedCtx_botPiCpt hW botPiCpt_pi_bot_nil r₁).2
        exact lrTypeINPiKClosedCtx_trans_of_envWfT hW r₁ (ih₂ hM hcM)
  rcases tyConvT_firstOf_data h with heq | ⟨_, u, hc₀, _⟩
  · injection heq with eA eB
    subst eA; subst eB
    exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  · have hpi : HasTyT E n Γ (.pi A₁ B₁) (.sort u) := (convEnds hW hΓ hc₀).1
    have hlr := hwalk hpi h (approxDIK_pi_bot_nil E (ctxEnvDIK E Γ) A₁ B₁)
    cases hlr with
    | pi hA hB _ hdom hcod _ _ =>
        have e₁ := whRedPiKClosedCtx_pi_eq hA
        have e₂ := whRedPiKClosedCtx_pi_eq hB
        injection e₁ with eA₁ eB₁
        injection e₂ with eA₂ eB₂
        subst eA₁; subst eB₁; subst eA₂; subst eB₂
        exact ⟨⟨hdom⟩, ⟨hcod⟩⟩


/-! ## §8. All-Cutoff Weakening, `CtxBVarOK`, Let-Refinement `CtxRefines`, Unconditional `ConvT.beta`
Closure Across ALL Arguments, and 27-Constructor Reduction Across ALL Contexts `Γ : LCtx` -/

/-! ### §8.1. All-Cutoff Weakening, Assumption-Substitution, and Same-Value Let-Congruence
for `LRTypeINPiKClosedCtx` and `LRTermDSubKClosedCtxBi` -/

theorem lrTermDSubKClosedCtxCore_weaken_probe (hcl : EnvClosed E)
    {Γ : LCtx} {M M' A : Expr Nat} (d : LocalDecl) {k : Nat} (hk : k ≤ Γ.length)
    (hΓ' : CtxWfT E n (insertAt d k Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCtxCore E n Γ M M' A c) :
    LRTermDSubKClosedCtxCore E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosedCtx_lift_insertAt hcl d hk hl⟩,
        lrTypeINPiKClosedCtx_weaken_botPiCpt hcl .sort d hk hΓ' hlr⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosedCtx_lift_insertAt hcl d hk hl⟩,
        lrTypeINPiKClosedCtx_weaken_botPiCpt hcl botPiCpt_pi_bot_nil d hk hΓ' hlr⟩

theorem lrTermDSubKClosedCtx_weaken_probe (hcl : EnvClosed E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {M M' A : Expr Nat} (d : LocalDecl) {k : Nat} (hk : k ≤ Γ.length)
    (hΓ' : CtxWfT E n (insertAt d k Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCtx E n Γ M M' A c) :
    LRTermDSubKClosedCtx E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) c := by
  rcases h with hP | hC
  · obtain ⟨⟨hA⟩, _⟩ := hP
    exact Or.inl (isPropTyI_of_hasTyT_sort_zero hSort (hasTyTWeaken d hcl (c := k) hA))
  · exact Or.inr (lrTermDSubKClosedCtxCore_weaken_probe hcl d hk hΓ' hc hC)

theorem lrTermDSubKClosedCtx_weaken0_probe (hcl : EnvClosed E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {M M' A : Expr Nat} {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCtx E n Γ M M' A c) :
    LRTermDSubKClosedCtx E n (d :: Γ) (lift 0 1 M) (lift 0 1 M') (lift 0 1 A) c :=
  lrTermDSubKClosedCtx_weaken_probe hcl hSort d (Nat.zero_le _) hΓ' hc h

/-- **All-Cutoff Weakening of `LRTermDSubKClosedCtxBi` Across ALL Contexts `Γ : LCtx`
    (`lrTermDSubKClosedCtxBi_weaken`):** -/
theorem lrTermDSubKClosedCtxBi_weaken (hcl : EnvClosed E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {M M' A : Expr Nat} (d : LocalDecl) {k : Nat} (hk : k ≤ Γ.length)
    (hΓ' : CtxWfT E n (insertAt d k Γ))
    (h : LRTermDSubKClosedCtxBi E n Γ M M' A) :
    LRTermDSubKClosedCtxBi E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) := by
  intro c hc hor
  have hor₀ : ApproxDIK E (ctxEnvDIK E Γ) M c ∨ ApproxDIK E (ctxEnvDIK E Γ) M' c :=
    hor.elim
      (fun hL => Or.inl ((approxDIK_ctxEnvDIK_insertAt_lift_iff E d hk M c).mp hL))
      (fun hR => Or.inr ((approxDIK_ctxEnvDIK_insertAt_lift_iff E d hk M' c).mp hR))
  exact lrTermDSubKClosedCtx_weaken_probe hcl hSort d hk hΓ' hc (h c hc hor₀)

/-- **Head Weakening (`k = 0`) of `LRTermDSubKClosedCtxBi` Across ALL Contexts `Γ : LCtx`
    (`lrTermDSubKClosedCtxBi_weaken0`):** -/
theorem lrTermDSubKClosedCtxBi_weaken0 (hcl : EnvClosed E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {M M' A : Expr Nat}
    (h : LRTermDSubKClosedCtxBi E n Γ M M' A) :
    LRTermDSubKClosedCtxBi E n (d :: Γ) (lift 0 1 M) (lift 0 1 M') (lift 0 1 A) :=
  lrTermDSubKClosedCtxBi_weaken hcl hSort d (Nat.zero_le _) hΓ' h

/-- Weakens a closed `LRTermDSubKClosedCtxBi` relation from the empty context `[]` to any
    well-formed context `CtxWfT E n Γ`. -/
theorem lrTermDSubKClosedCtxBi_closed_weaken_ctx (hcl : EnvClosed E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {M M' A : Expr Nat}
    (hM : lift 0 1 M = M) (hM' : lift 0 1 M' = M') (hA : lift 0 1 A = A)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (h0 : LRTermDSubKClosedCtxBi E n [] M M' A) :
    LRTermDSubKClosedCtxBi E n Γ M M' A := by
  induction hΓ with
  | nil => exact h0
  | @assumption Γ₀ B u hΓ₀ hB ih =>
      have h1 := lrTermDSubKClosedCtxBi_weaken0 hcl hSort (.assumption Γ₀ B u hΓ₀ hB) ih
      rwa [hM, hM', hA] at h1
  | @letBinding Γ₀ B u v hΓ₀ hB hv ih =>
      have h1 := lrTermDSubKClosedCtxBi_weaken0 hcl hSort (.letBinding Γ₀ B u v hΓ₀ hB hv) ih
      rwa [hM, hM', hA] at h1

/-- Assumption-substitution stability of `LRTypeINPiKClosedCtx` on `BotPiCpt` for `⊥`-approximated `v`. -/
theorem lrTypeINPiKClosedCtx_substAssump_botPiCpt {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) (t v : Expr Nat)
    {c : CptI} (hc : BotPiCpt c) :
    ∀ {Γ : LCtx} {A A' : Expr Nat} {j : Nat},
      Γ[j]? = some (.assumption t) →
      (∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v j Γ)) (lift 0 j v) u → u = .bot) →
      HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
      CtxWfT E n (substRemove v j Γ) →
      LRTypeINPiKClosedCtx E n Γ A A' c →
      LRTypeINPiKClosedCtx E n (substRemove v j Γ)
        (instantiate j (lift 0 j v) A) (instantiate j (lift 0 j v) A') c := by
  induction hc with
  | bot =>
      intro Γ A A' j _ _ _ _ _
      exact .bot _ _ _
  | sort =>
      intro Γ A A' j hget hv _ _ h
      cases h with
      | sort h₁ h₂ =>
          exact .sort (whRedPiKClosedCtx_substAssump_of_envClosed hcl hget hv h₁)
            (whRedPiKClosedCtx_substAssump_of_envClosed hcl hget hv h₂)
  | @pi a f _ _ _ iha ihf =>
      intro Γ A A' j hget hv hvty hΓ' h
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h₁ h₂ hΓ₁ hdom hcod ra rf =>
          have hlift : lift 0 1 (lift 0 j v) = lift 0 (j + 1) v :=
            lift_lift_merge 1 j 0 0 (by omega) (by omega) v
          have h₁' : WhRedPiKClosedCtx E (substRemove v j Γ) (instantiate j (lift 0 j v) A)
              (.pi (instantiate j (lift 0 j v) A₁) (instantiate (j + 1) (lift 0 (j + 1) v) B₁)) := by
            have h0 := whRedPiKClosedCtx_substAssump_of_envClosed hcl hget hv h₁
            simpa only [instantiate, hlift] using h0
          have h₂' : WhRedPiKClosedCtx E (substRemove v j Γ) (instantiate j (lift 0 j v) A')
              (.pi (instantiate j (lift 0 j v) A₂) (instantiate (j + 1) (lift 0 (j + 1) v) B₂)) := by
            have h0 := whRedPiKClosedCtx_substAssump_of_envClosed hcl hget hv h₂
            simpa only [instantiate, hlift] using h0
          have hA₁ : ∃ u, Nonempty (HasTyT E n Γ A₁ (.sort u)) := by
            cases hΓ₁ with
            | assumption _ _ u _ hA₁ => exact ⟨u, ⟨hA₁⟩⟩
          obtain ⟨u, ⟨hA₁⟩⟩ := hA₁
          have hA₁' : HasTyT E n (substRemove v j Γ) (instantiate j (lift 0 j v) A₁) (.sort u) :=
            hasTyT_substS hcl hinst v t hA₁ hget hvty
          have hΓ₁'' : CtxWfT E n (.assumption (instantiate j (lift 0 j v) A₁) :: substRemove v j Γ) :=
            .assumption _ _ u hΓ' hA₁'
          have hΓ₁' : CtxWfT E n (substRemove v (j + 1) (.assumption A₁ :: Γ)) := by
            simpa only [substRemove_succ_cons, instDecl] using hΓ₁''
          have hget' : (LocalDecl.assumption A₁ :: Γ)[j + 1]? = some (.assumption t) := by
            rw [List.getElem?_cons_succ]; exact hget
          have hv' : ∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v (j + 1) (.assumption A₁ :: Γ)))
              (lift 0 (j + 1) v) u → u = .bot := by
            intro u hu
            apply hv u
            rw [substRemove_succ_cons, ← hlift] at hu
            exact (approxDIK_ctxEnvDIK_cons_lift0_iff E (instDecl j v (.assumption A₁))
              (substRemove v j Γ) (lift 0 j v) u).mp hu
          have hvty' : HasTyT E n (substRemove v (j + 1) (.assumption A₁ :: Γ))
              (lift 0 (j + 1) v) (lift 0 (j + 1) t) := by
            have h0 := hasTyTWeaken (instDecl j v (.assumption A₁)) hcl (c := 0) hvty
            rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
                lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h0
            exact h0
          have hdom' : TyConvT E n (substRemove v j Γ)
              (instantiate j (lift 0 j v) A₁) (instantiate j (lift 0 j v) A₂) :=
            tyConvT_substS hcl hinst v t hdom hget hvty
          have hcod' : TyConvT E n (.assumption (instantiate j (lift 0 j v) A₁) :: substRemove v j Γ)
              (instantiate (j + 1) (lift 0 (j + 1) v) B₁)
              (instantiate (j + 1) (lift 0 (j + 1) v) B₂) := by
            simpa only [substRemove_succ_cons, instDecl] using
              tyConvT_substS hcl hinst v t (j := j + 1) hcod hget' hvty'
          exact .pi h₁' h₂' hΓ₁'' hdom' hcod'
            (iha hget hv hvty hΓ' ra)
            (fun s hs => by
              simpa only [substRemove_succ_cons, instDecl] using
                ihf s hs hget' hv' hvty' hΓ₁' (rf s hs))

theorem lrTypeINPiKClosedCtx_substAssump0_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t v : Expr Nat}
    (hv : ∀ u, ApproxDIK E (ctxEnvDIK E Γ) v u → u = .bot)
    (hvty : HasTyT E n Γ v t)
    {A A' : Expr Nat} {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeINPiKClosedCtx E n (.assumption t :: Γ) A A' c) :
    LRTypeINPiKClosedCtx E n Γ (instantiate0 v A) (instantiate0 v A') c := by
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  have h0 := lrTypeINPiKClosedCtx_substAssump_botPiCpt
    (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) t v hc
    (Γ := .assumption t :: Γ) (j := 0) hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hv)
    (by simpa only [substRemove_zero_cons, lift_zero] using hvty)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

theorem lrTypeINBiDIKClosedCtx_substAssump0 {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t v : Expr Nat}
    (hv : ∀ u, ApproxDIK E (ctxEnvDIK E Γ) v u → u = .bot)
    (hvty : HasTyT E n Γ v t)
    {A A' : Expr Nat}
    (h : LRTypeINBiDIKClosedCtx E n (.assumption t :: Γ) A A') :
    LRTypeINBiDIKClosedCtx E n Γ (instantiate0 v A) (instantiate0 v A') := by
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  have hv0 : ∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v 0 (.assumption t :: Γ))) (lift 0 0 v) u → u = .bot := by
    simpa only [substRemove_zero_cons, lift_zero] using hv
  intro c hc hor
  have hor₀ :
      ApproxDIK E (ctxEnvDIK E (.assumption t :: Γ)) A c ∨
        ApproxDIK E (ctxEnvDIK E (.assumption t :: Γ)) A' c :=
    hor.elim
      (fun hL => Or.inl ((approxDIK_ctxEnvDIK_substAssump_iff hget0 hv0 A c).mp
        (by simpa only [substRemove_zero_cons, lift_zero, instantiate0] using hL)))
      (fun hR => Or.inr ((approxDIK_ctxEnvDIK_substAssump_iff hget0 hv0 A' c).mp
        (by simpa only [substRemove_zero_cons, lift_zero, instantiate0] using hR)))
  exact lrTypeINPiKClosedCtx_substAssump0_botPiCpt hW hΓ hv hvty hc (h c hc hor₀)

theorem lrTermDSubKClosedCtxCore_substAssump_probe (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (t v : Expr Nat)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.assumption t))
    (hv : ∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v j Γ)) (lift 0 j v) u → u = .bot)
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove v j Γ))
    {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCtxCore E n Γ M M' A c) :
    LRTermDSubKClosedCtxCore E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosedCtx_substAssump_of_envClosed hcl hget hv hl⟩,
        lrTypeINPiKClosedCtx_substAssump_botPiCpt hcl hinst t v .sort hget hv hvty hΓ' hlr⟩
  | piBotNil =>
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil (by intro h0; cases h0)] at h ⊢
      obtain ⟨⟨l, hl⟩, hlr⟩ := h
      exact ⟨⟨l, whRedPiKClosedCtx_substAssump_of_envClosed hcl hget hv hl⟩,
        lrTypeINPiKClosedCtx_substAssump_botPiCpt hcl hinst t v botPiCpt_pi_bot_nil hget hv hvty hΓ' hlr⟩

theorem lrTermDSubKClosedCtx_substAssump0_probe (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t v : Expr Nat}
    (hv : ∀ u, ApproxDIK E (ctxEnvDIK E Γ) v u → u = .bot)
    (hvty : HasTyT E n Γ v t)
    {M M' A : Expr Nat} {c : CptI} (hc : ProbeCpt c)
    (h : LRTermDSubKClosedCtx E n (.assumption t :: Γ) M M' A c) :
    LRTermDSubKClosedCtx E n Γ (instantiate0 v M) (instantiate0 v M') (instantiate0 v A) c := by
  have hcl := envClosed_of_envWfT hW
  have hinst := envMembersSubstStable_of_envWfT hW
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  rcases h with hP | hC
  · obtain ⟨⟨hA⟩, _⟩ := hP
    have hA' := hasTyT_substS hcl hinst v t hA hget0
      (by simpa only [substRemove_zero_cons, lift_zero] using hvty)
    exact Or.inl (isPropTyI_of_hasTyT_sort_zero hSort
      (by simpa only [substRemove_zero_cons, lift_zero, instantiate0] using hA'))
  · have hC' := lrTermDSubKClosedCtxCore_substAssump_probe hcl hinst t v hget0
      (by simpa only [substRemove_zero_cons, lift_zero] using hv)
      (by simpa only [substRemove_zero_cons, lift_zero] using hvty)
      (by simpa only [substRemove_zero_cons] using hΓ) hc hC
    exact Or.inr (by simpa only [substRemove_zero_cons, lift_zero, instantiate0] using hC')

theorem lrTermDSubKClosedCtxBi_substAssump0 (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t v : Expr Nat}
    (hv : ∀ u, ApproxDIK E (ctxEnvDIK E Γ) v u → u = .bot)
    (hvty : HasTyT E n Γ v t)
    {M M' A : Expr Nat}
    (h : LRTermDSubKClosedCtxBi E n (.assumption t :: Γ) M M' A) :
    LRTermDSubKClosedCtxBi E n Γ (instantiate0 v M) (instantiate0 v M') (instantiate0 v A) := by
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  have hv0 : ∀ u, ApproxDIK E (ctxEnvDIK E (substRemove v 0 (.assumption t :: Γ))) (lift 0 0 v) u → u = .bot := by
    simpa only [substRemove_zero_cons, lift_zero] using hv
  intro c hc hor
  have hor₀ :
      ApproxDIK E (ctxEnvDIK E (.assumption t :: Γ)) M c ∨
        ApproxDIK E (ctxEnvDIK E (.assumption t :: Γ)) M' c :=
    hor.elim
      (fun hL => Or.inl ((approxDIK_ctxEnvDIK_substAssump_iff hget0 hv0 M c).mp
        (by simpa only [substRemove_zero_cons, lift_zero, instantiate0] using hL)))
      (fun hR => Or.inr ((approxDIK_ctxEnvDIK_substAssump_iff hget0 hv0 M' c).mp
        (by simpa only [substRemove_zero_cons, lift_zero, instantiate0] using hR)))
  exact lrTermDSubKClosedCtx_substAssump0_probe hW hSort hΓ hv hvty hc (h c hc hor₀)

theorem lrTermDSubKClosedCtxBi_beta_of_botApprox (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A a b B : Expr Nat}
    (ha_bot : ∀ u, ApproxDIK E (ctxEnvDIK E Γ) a u → u = .bot)
    (ha_ty : HasTyT E n Γ a A)
    (ih_b : LRTermDSubKClosedCtxBi E n (.assumption A :: Γ) b b B) :
    LRTermDSubKClosedCtxBi E n Γ (.app (.lam A b) a) (instantiate0 a b) (instantiate0 a B) :=
  lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW (.of_whStep (.beta A b a))
    (lrTermDSubKClosedCtxBi_substAssump0 hW hSort hΓ ha_bot ha_ty ih_b)

/-- **Unconditional Same-Value `ConvT.letE` Congruence in `LRTermDSubKClosedCtxBi` Across ALL
    Contexts `Γ : LCtx` and ALL Let-Values `v : Expr Nat` (`lrTermDSubKClosedCtxBi_letE_sameVal`):** -/
theorem lrTermDSubKClosedCtxBi_letE_sameVal (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' v b b' B : Expr Nat}
    (hv_ty : HasTyT E n Γ v A)
    (ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A v :: Γ) b b' B) :
    LRTermDSubKClosedCtxBi E n Γ (.letE A v b) (.letE A' v b') (instantiate0 v B) :=
  have hL : WhRedPiKClosedCtx E Γ (.letE A v b) (instantiate0 v b) :=
    .step (.of_whStep (.zeta A v b)) (.refl _)
  have hR : WhRedPiKClosedCtx E Γ (.letE A' v b') (instantiate0 v b') :=
    .step (.of_whStep (.zeta A' v b')) (.refl _)
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW hL hR
    (lrTermDSubKClosedCtxBi_substLet0 hW hSort hΓ hv_ty ih_b)

/-! ### §8.2. Context-Aware Variable Lookup and `CtxBVarOK E n Γ` Across All Contexts `Γ : LCtx` -/

theorem approxDIK_ctxEnvDIK_bvar_none_eq_bot {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) {c : CptI}
    (h : ApproxDIK E (ctxEnvDIK E Γ) (.bvar i) c) : c = .bot := by
  cases h with
  | bot => rfl
  | bvar hc => exact ctxEnvDIK_none_bot E Γ i hnone c hc

/-- Unconditional `HasTyT.bvar` soundness in `LRTermDSubKClosedCtxBi` at any assumption-bound
    variable `lookupValue Γ i = none`. -/
theorem lrTermDSubKClosedCtxBi_bvar_of_lookupValue_none {Γ : LCtx} {i : Nat} (A : Expr Nat)
    (hnone : lookupValue Γ i = none) :
    LRTermDSubKClosedCtxBi E n Γ (.bvar i) (.bvar i) A := by
  intro c _ hor
  rcases hor with h | h <;>
    (rw [approxDIK_ctxEnvDIK_bvar_none_eq_bot hnone h]
     exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial))

/-- Unconditional `HasTyT.bvar` soundness in `LRTermDSubKClosedCtxBi` at any let-bound variable
    `lookupValue Γ i = some v` from `LRTermDSubKClosedCtxBi E n Γ v v A`. -/
theorem lrTermDSubKClosedCtxBi_bvar_of_lookupValue_some (hW : EnvWfT E)
    {Γ : LCtx} {i : Nat} {v A : Expr Nat}
    (hval : lookupValue Γ i = some v)
    (hdiag : LRTermDSubKClosedCtxBi E n Γ v v A) :
    LRTermDSubKClosedCtxBi E n Γ (.bvar i) (.bvar i) A :=
  have hstep : WhRedPiKClosedCtx E Γ (.bvar i) v := .step (.zetaLocal hval) (.refl _)
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW hstep hstep hdiag

/-- **Context Bound-Variable Adequacy (`CtxBVarOK E n Γ`):**
    Every bound variable `.bvar i` with `lookupType Γ i = some A` is related to itself in
    `LRTermDSubKClosedCtxBi E n Γ (.bvar i) (.bvar i) A`. -/
def CtxBVarOK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Prop :=
  ∀ i A, lookupType Γ i = some A → LRTermDSubKClosedCtxBi E n Γ (.bvar i) (.bvar i) A

theorem ctxBVarOK_nil : CtxBVarOK E n [] := by
  intro _ _ hty
  exact Option.noConfusion hty

theorem ctxBVarOK_of_letFree {Γ : LCtx} (hlf : LetFreeCtx Γ) : CtxBVarOK E n Γ :=
  fun i A _ => lrTermDSubKClosedCtxBi_bvar_of_lookupValue_none A (hlf i)

theorem ctxBVarOK_cons_assumption (hcl : EnvClosed E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {A₀ : Expr Nat}
    (hΓ' : CtxWfT E n (.assumption A₀ :: Γ))
    (hbv : CtxBVarOK E n Γ) :
    CtxBVarOK E n (.assumption A₀ :: Γ) := by
  intro i A hty
  cases i with
  | zero =>
      exact lrTermDSubKClosedCtxBi_bvar_of_lookupValue_none A rfl
  | succ i =>
      rw [lookupType_cons_succ] at hty
      cases hty₀ : lookupType Γ i with
      | none => rw [hty₀] at hty; exact Option.noConfusion hty
      | some A' =>
          rw [hty₀] at hty
          injection hty with hA
          subst hA
          have ih := lrTermDSubKClosedCtxBi_weaken0 hcl hSort hΓ' (hbv i A' hty₀)
          have hlift : lift 0 1 (.bvar i : Expr Nat) = .bvar (i + 1) := by simp [lift]
          rwa [hlift] at ih

theorem ctxBVarOK_cons_letBinding (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {A₀ v₀ : Expr Nat}
    (hΓ' : CtxWfT E n (.letBinding A₀ v₀ :: Γ))
    (hbv : CtxBVarOK E n Γ)
    (hv₀ : LRTermDSubKClosedCtxBi E n Γ v₀ v₀ A₀) :
    CtxBVarOK E n (.letBinding A₀ v₀ :: Γ) := by
  have hcl := envClosed_of_envWfT hW
  intro i A hty
  cases i with
  | zero =>
      have hty0 : lookupType (.letBinding A₀ v₀ :: Γ) 0 = some (lift 0 1 A₀) := rfl
      have hA : A = lift 0 1 A₀ := Option.some.inj (hty.symm.trans hty0)
      subst hA
      have hval₀ : lookupValue (.letBinding A₀ v₀ :: Γ) 0 = some (lift 0 1 v₀) := rfl
      exact lrTermDSubKClosedCtxBi_bvar_of_lookupValue_some hW hval₀
        (lrTermDSubKClosedCtxBi_weaken0 hcl hSort hΓ' hv₀)
  | succ i =>
      rw [lookupType_cons_succ] at hty
      cases hty₀ : lookupType Γ i with
      | none => rw [hty₀] at hty; exact Option.noConfusion hty
      | some A' =>
          rw [hty₀] at hty
          injection hty with hA
          subst hA
          have ih := lrTermDSubKClosedCtxBi_weaken0 hcl hSort hΓ' (hbv i A' hty₀)
          have hlift : lift 0 1 (.bvar i : Expr Nat) = .bvar (i + 1) := by simp [lift]
          rwa [hlift] at ih

/-! ### §8.3. Context Let-Refinement `CtxRefines`, Typing/Conversion Transport, and
Unconditional `ConvT.beta` Closure Across ALL Arguments (`lrTermDSubKClosedCtxBi_beta_via_let`) -/

/-- **Context Let-Refinement (`CtxRefines Γ Γ'`):**
    `Γ'` refines `Γ` by turning zero or more `.assumption A` entries into `.letBinding A v`
    entries (preserving all binder types `A` and all existing `.letBinding A v` values `v`).
    Because `lookupType` on `.assumption A` and `.letBinding A v` are identical, `CtxRefines Γ Γ'`
    preserves `lookupType` (`lookupType Γ' i = lookupType Γ i`) and is monotone on `lookupValue`
    (`lookupValue Γ i = some v → lookupValue Γ' i = some v`). -/
inductive CtxRefines : LCtx → LCtx → Prop
  | nil : CtxRefines [] []
  | assumption {A : Expr Nat} {Γ Γ' : LCtx} :
      CtxRefines Γ Γ' → CtxRefines (.assumption A :: Γ) (.assumption A :: Γ')
  | letBinding {A v : Expr Nat} {Γ Γ' : LCtx} :
      CtxRefines Γ Γ' → CtxRefines (.letBinding A v :: Γ) (.letBinding A v :: Γ')
  | assumpToLet {A v : Expr Nat} {Γ Γ' : LCtx} :
      CtxRefines Γ Γ' → CtxRefines (.assumption A :: Γ) (.letBinding A v :: Γ')

theorem ctxRefines_refl : ∀ Γ : LCtx, CtxRefines Γ Γ
  | [] => .nil
  | .assumption _ :: Γ => .assumption (ctxRefines_refl Γ)
  | .letBinding _ _ :: Γ => .letBinding (ctxRefines_refl Γ)

theorem ctxRefines_cons (d : LocalDecl) {Γ Γ' : LCtx} (h : CtxRefines Γ Γ') :
    CtxRefines (d :: Γ) (d :: Γ') := by
  cases d with
  | assumption _ => exact .assumption h
  | letBinding _ _ => exact .letBinding h

theorem ctxRefines_get_inv {Γ Γ' : LCtx} (h : CtxRefines Γ Γ') :
    ∀ i : Nat,
      (Γ.get? i = none ∧ Γ'.get? i = none) ∨
      (∃ A, Γ.get? i = some (.assumption A) ∧
        (Γ'.get? i = some (.assumption A) ∨ ∃ v, Γ'.get? i = some (.letBinding A v))) ∨
      (∃ A v, Γ.get? i = some (.letBinding A v) ∧ Γ'.get? i = some (.letBinding A v)) := by
  induction h with
  | nil =>
      intro _
      exact Or.inl ⟨rfl, rfl⟩
  | @assumption A _ _ _ ih =>
      intro i
      cases i with
      | zero => exact Or.inr (Or.inl ⟨A, rfl, Or.inl rfl⟩)
      | succ i => exact ih i
  | @letBinding A v _ _ _ ih =>
      intro i
      cases i with
      | zero => exact Or.inr (Or.inr ⟨A, v, rfl, rfl⟩)
      | succ i => exact ih i
  | @assumpToLet A v _ _ _ ih =>
      intro i
      cases i with
      | zero => exact Or.inr (Or.inl ⟨A, rfl, Or.inr ⟨v, rfl⟩⟩)
      | succ i => exact ih i

theorem lookupType_of_ctxRefines {Γ Γ' : LCtx} (h : CtxRefines Γ Γ') (i : Nat) :
    lookupType Γ' i = lookupType Γ i := by
  unfold lookupType
  rcases ctxRefines_get_inv h i with ⟨h1, h2⟩ | ⟨A, h1, h2 | ⟨v, h2⟩⟩ | ⟨A, v, h1, h2⟩ <;>
    rw [h1, h2]

theorem lookupValue_of_ctxRefines {Γ Γ' : LCtx} (h : CtxRefines Γ Γ') {i : Nat} {v : Expr Nat}
    (hval : lookupValue Γ i = some v) :
    lookupValue Γ' i = some v := by
  unfold lookupValue at hval ⊢
  rcases ctxRefines_get_inv h i with ⟨h1, _⟩ | ⟨A, h1, _⟩ | ⟨A, w, h1, h2⟩
  · rw [h1] at hval; exact Option.noConfusion hval
  · rw [h1] at hval; exact Option.noConfusion hval
  · rw [h1] at hval
    rw [h2]
    exact hval

mutual
/-- Transport of `HasTyT` along `CtxRefines Γ Γ'`. -/
def hasTyT_of_ctxRefines {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A →
    {Γ' : LCtx} → CtxRefines Γ Γ' → HasTyT E n Γ' e A
  | _, _, _, .sort _ l, _, _ => .sort _ l
  | _, _, _, .bvar _ i A hty, _, href =>
      .bvar _ i A (by rw [lookupType_of_ctxRefines href i]; exact hty)
  | _, _, _, .const _ r ls m hres hlen hwf, _, _ =>
      .const _ r ls m hres hlen hwf
  | _, _, _, .pi _ A u B v hA hB, _, href =>
      .pi _ A u B v (hasTyT_of_ctxRefines hA href) (hasTyT_of_ctxRefines hB (.assumption href))
  | _, _, _, .lam _ A u body B hA hbody, _, href =>
      .lam _ A u body B (hasTyT_of_ctxRefines hA href)
        (hasTyT_of_ctxRefines hbody (.assumption href))
  | _, _, _, .app _ f a A B hf ha, _, href =>
      .app _ f a A B (hasTyT_of_ctxRefines hf href) (hasTyT_of_ctxRefines ha href)
  | _, _, _, .letE _ A u value B body hA hv hb, _, href =>
      .letE _ A u value B body (hasTyT_of_ctxRefines hA href) (hasTyT_of_ctxRefines hv href)
        (hasTyT_of_ctxRefines hb (.letBinding href))
  | _, _, _, .lit _ t T hexp, _, href =>
      .lit _ t T (hasTyT_of_ctxRefines hexp href)
  | _, _, _, .conv _ e A B u h hc, _, href =>
      .conv _ e A B u (hasTyT_of_ctxRefines h href) (convT_of_ctxRefines hc href)

/-- Transport of `ConvT` along `CtxRefines Γ Γ'`. -/
def convT_of_ctxRefines {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b A : Expr Nat} → ConvT E n Γ a b A →
    {Γ' : LCtx} → CtxRefines Γ Γ' → ConvT E n Γ' a b A
  | _, _, _, _, .refl _ a A h, _, href =>
      .refl _ a A (hasTyT_of_ctxRefines h href)
  | _, _, _, _, .symm _ a b A h, _, href =>
      .symm _ a b A (convT_of_ctxRefines h href)
  | _, _, _, _, .trans _ a b c A h1 h2, _, href =>
      .trans _ a b c A (convT_of_ctxRefines h1 href) (convT_of_ctxRefines h2 href)
  | _, _, _, _, .beta _ A body arg B u hA hbody harg, _, href =>
      .beta _ A body arg B u (hasTyT_of_ctxRefines hA href)
        (hasTyT_of_ctxRefines hbody (.assumption href)) (hasTyT_of_ctxRefines harg href)
  | _, _, _, _, .zeta _ A value body B u hA hv hb, _, href =>
      .zeta _ A value body B u (hasTyT_of_ctxRefines hA href) (hasTyT_of_ctxRefines hv href)
        (hasTyT_of_ctxRefines hb (.letBinding href))
  | _, _, _, _, .zetaLocal _ i A v hval hty hv, _, href =>
      .zetaLocal _ i A v (lookupValue_of_ctxRefines href hval)
        (by rw [lookupType_of_ctxRefines href i]; exact hty) (hasTyT_of_ctxRefines hv href)
  | _, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb, _, href =>
      .delta _ r ls m b hres hbody htr hlen hwf (hasTyT_of_ctxRefines hb href)
  | _, _, _, _, .iota _ lhs rhs T h hlhs hrhs, _, href =>
      .iota _ lhs rhs T h (hasTyT_of_ctxRefines hlhs href) (hasTyT_of_ctxRefines hrhs href)
  | _, _, _, _, .lit _ t exp T hlit hexp, _, href =>
      have hexp' := hasTyT_of_ctxRefines hexp href
      .lit _ t exp T hlit hexp'
  | _, _, _, _, .app _ f g a b A B h1 h2, _, href =>
      .app _ f g a b A B (convT_of_ctxRefines h1 href) (convT_of_ctxRefines h2 href)
  | _, _, _, _, .lam _ A A' b b' B u hA hb, _, href =>
      .lam _ A A' b b' B u (convT_of_ctxRefines hA href)
        (convT_of_ctxRefines hb (.assumption href))
  | _, _, _, _, .pi _ A A' B B' u v hA hB, _, href =>
      .pi _ A A' B B' u v (convT_of_ctxRefines hA href)
        (convT_of_ctxRefines hB (.assumption href))
  | _, _, _, _, .letE _ A A' v v' b b' B u hA hv hb, _, href =>
      .letE _ A A' v v' b b' B u (convT_of_ctxRefines hA href) (convT_of_ctxRefines hv href)
        (convT_of_ctxRefines hb (.letBinding href))
  | _, _, _, _, .sorts _ l₁ l₂ h, _, _ =>
      .sorts _ l₁ l₂ h
  | _, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h, _, _ =>
      .consts _ r ls ls' m hres hlen hwf hwf' h
  | _, _, _, _, .eta _ f A B h, _, href =>
      .eta _ f A B (hasTyT_of_ctxRefines h href)
  | _, _, _, _, .irr _ P p q hP hp hq, _, href =>
      .irr _ P p q (hasTyT_of_ctxRefines hP href) (hasTyT_of_ctxRefines hp href)
        (hasTyT_of_ctxRefines hq href)
  | _, _, _, _, .tyConv _ a b A A' u h hA, _, href =>
      .tyConv _ a b A A' u (convT_of_ctxRefines h href) (convT_of_ctxRefines hA href)
end

/-- Transport of `TyConvT` along `CtxRefines Γ Γ'`. -/
def tyConvT_of_ctxRefines {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B →
    {Γ' : LCtx} → CtxRefines Γ Γ' → TyConvT E n Γ' A B
  | _, _, _, .refl _ A, _, _ => .refl _ A
  | _, _, _, .of _ A B u h, _, href => .of _ A B u (convT_of_ctxRefines h href)
  | _, _, _, .trans _ A B C h1 h2, _, href =>
      .trans _ A B C (tyConvT_of_ctxRefines h1 href) (tyConvT_of_ctxRefines h2 href)

/-- Head specialization of `hasTyT_of_ctxRefines`: any typing in `.assumption A :: Γ` holds in
    `.letBinding A a :: Γ` for every `a : Expr Nat`. -/
def hasTyT_assump_to_let {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A b B : Expr Nat} (a : Expr Nat)
    (h : HasTyT E n (.assumption A :: Γ) b B) :
    HasTyT E n (.letBinding A a :: Γ) b B :=
  hasTyT_of_ctxRefines h (.assumpToLet (ctxRefines_refl Γ))

/-- Head specialization of `convT_of_ctxRefines`: any conversion in `.assumption A :: Γ` holds in
    `.letBinding A a :: Γ` for every `a : Expr Nat`. -/
def convT_assump_to_let {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A b₁ b₂ B : Expr Nat} (a : Expr Nat)
    (h : ConvT E n (.assumption A :: Γ) b₁ b₂ B) :
    ConvT E n (.letBinding A a :: Γ) b₁ b₂ B :=
  convT_of_ctxRefines h (.assumpToLet (ctxRefines_refl Γ))

/-- Head specialization of `tyConvT_of_ctxRefines`: any type conversion in `.assumption A :: Γ`
    holds in `.letBinding A a :: Γ` for every `a : Expr Nat`. -/
def tyConvT_assump_to_let {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B₁ B₂ : Expr Nat} (a : Expr Nat)
    (h : TyConvT E n (.assumption A :: Γ) B₁ B₂) :
    TyConvT E n (.letBinding A a :: Γ) B₁ B₂ :=
  tyConvT_of_ctxRefines h (.assumpToLet (ctxRefines_refl Γ))

/-- **Unconditional `ConvT.beta` Soundness in `LRTermDSubKClosedCtxBi` Across ALL Contexts
    `Γ : LCtx` and ALL Arguments `a : Expr Nat` (`lrTermDSubKClosedCtxBi_beta_via_let`):**
    Because `lrTermDSubKClosedCtxBi_substLet0` holds for **every** `a : Expr Nat` with **zero**
    `⊥`-approximation restriction, evaluating the body `b` in the let-refined context
    `.letBinding A a :: Γ` (`ih_b_let : LRTermDSubKClosedCtxBi E n (.letBinding A a :: Γ) b b B`)
    and stepping `.app (.lam A b) a` by `WhStep.beta` closes `ConvT.beta` **100% unconditionally**
    for all arguments `a`! -/
theorem lrTermDSubKClosedCtxBi_beta_via_let (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A a b B : Expr Nat}
    (ha_ty : HasTyT E n Γ a A)
    (ih_b_let : LRTermDSubKClosedCtxBi E n (.letBinding A a :: Γ) b b B) :
    LRTermDSubKClosedCtxBi E n Γ (.app (.lam A b) a) (instantiate0 a b) (instantiate0 a B) :=
  lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW (.of_whStep (.beta A b a))
    (lrTermDSubKClosedCtxBi_substLet0 hW hSort hΓ ha_ty ih_b_let)

/-- Unconditional diagonal β-redex adequacy `(.app (.lam A b) a ~ .app (.lam A b) a)` in
    `LRTermDSubKClosedCtxBi` across **all** contexts `Γ : LCtx` and **all** arguments `a : Expr Nat`. -/
theorem lrTermDSubKClosedCtxBi_beta_diag_via_let (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A a b B : Expr Nat}
    (ha_ty : HasTyT E n Γ a A)
    (ih_b_let : LRTermDSubKClosedCtxBi E n (.letBinding A a :: Γ) b b B) :
    LRTermDSubKClosedCtxBi E n Γ (.app (.lam A b) a) (.app (.lam A b) a) (instantiate0 a B) :=
  have hstep : WhRedPiKClosedCtx E Γ (.app (.lam A b) a) (instantiate0 a b) :=
    .step (.of_whStep (.beta A b a)) (.refl _)
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW hstep hstep
    (lrTermDSubKClosedCtxBi_substLet0 hW hSort hΓ ha_ty ih_b_let)

/-! ### §8.4. Complete 27-Constructor Reduction of `FundamentalTermDSubKClosedCtxBiProbe` Across
ALL Contexts `Γ : LCtx` (Closing `HasTyT.bvar`, `HasTyT.letE`, `HasTyT.conv`, `ConvT.beta`,
`ConvT.zeta`, `ConvT.zetaLocal`, and `ConvT.tyConv` Unconditionally) -/

theorem groupMembersT_body_arity_zero {S E : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    {E' : ResolvedEnv} (hmem : GroupMembersT S E ms E')
    (ih : ∀ r m b, E.members r = some m → m.body = some b → m.arity = 0) :
    ∀ r m b, E'.members r = some m → m.body = some b → m.arity = 0 := by
  induction hmem with
  | nil => exact ih
  | @cons E₁ r₁ m₁ _ _ _ hnobody _ _ _ _ _ _ _ _ _ _ _ _ ih_rest =>
      apply ih_rest
      intro r m b hm hb
      by_cases hrr : r = r₁
      · subst hrr
        rw [members_extend_eq] at hm
        cases hm
        rw [hnobody] at hb
        exact Option.noConfusion hb
      · rw [members_extend_ne E₁ r₁ m₁ r hrr] at hm
        exact ih r m b hm hb

/-- Under `EnvWfT E`, every member `m` with `m.body = some b` has universe arity `m.arity = 0`. -/
theorem envWfT_body_arity_zero {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ r m b, E.members r = some m → m.body = some b → m.arity = 0 := by
  induction hW with
  | empty => intro _ _ _ hm _; exact Option.noConfusion hm
  | @«axiom» _ E₀ r₀ _ _ _ _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr; rw [members_extend_eq] at hm; cases hm; cases hb
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm; exact ih r m b hm hb
  | @definition E₀ r₀ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr; rw [members_extend_eq] at hm; cases hm; rfl
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm; exact ih r m b hm hb
  | @thm E₀ r₀ _ _ _ _ _ _ _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr; rw [members_extend_eq] at hm; cases hm; rfl
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm; exact ih r m b hm hb
  | @«opaque» E₀ r₀ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr; rw [members_extend_eq] at hm; cases hm; rfl
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm; exact ih r m b hm hb
  | group _ _ _ _ _ _ _ _ _ _ _ hmem ih =>
      exact groupMembersT_body_arity_zero hmem ih

/-- **Minimal Residual Congruence Supply `AppValCongrSupplyDSubKClosedCtxBi E n`:**
    Because `HasTyT.bvar`, `HasTyT.letE`, `HasTyT.conv`, `ConvT.beta`, `ConvT.zeta`,
    `ConvT.zetaLocal`, `ConvT.delta`, `ConvT.iota`, `ConvT.eta`, `ConvT.irr`, and `ConvT.tyConv`
    are **all 100% closed unconditionally** across all contexts `Γ : LCtx` (and `HasTyT.app`
    factors through `ConvT.app` via `ConvT.refl`), the entire 27-constructor induction on
    `HasTyT` + `ConvT` reduces to just:
    1. `ConvT.app` congruence (`f₁ a₁ ~ f₂ a₂`),
    2. `ConvT.letE` value-substitution congruence on a diagonal body (`instantiate0 v₁ b ~ instantiate0 v₂ b`), and
    3. Empty-context `DeltaConst` body diagonal (`b ~ b` in `[]`, weakened to arbitrary `Γ` by
       `lrTermDSubKClosedCtxBi_closed_weaken_ctx` and `envWfT_body_arity_zero`). -/
def AppValCongrSupplyDSubKClosedCtxBi (E : ResolvedEnv) (n : Nat) : Prop :=
  -- 1. ConvT.app congruence (also closes HasTyT.app via ConvT.refl)
  (∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {f₁ f₂ a₁ a₂ A B : Expr Nat},
      ConvT E n Γ f₁ f₂ (.pi A B) → ConvT E n Γ a₁ a₂ A →
      LRTermDSubKClosedCtxBi E n Γ f₁ f₂ (.pi A B) →
      LRTermDSubKClosedCtxBi E n Γ a₁ a₂ A →
      LRTermDSubKClosedCtxBi E n Γ (.app f₁ a₁) (.app f₂ a₂) (instantiate0 a₁ B)) ∧
  -- 2. ConvT.letE value-substitution congruence on a diagonal body
  (∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A v₁ v₂ b B : Expr Nat},
      HasTyT E n Γ v₁ A → HasTyT E n Γ v₂ A → ConvT E n Γ v₁ v₂ A →
      LRTermDSubKClosedCtxBi E n Γ v₁ v₂ A →
      LRTermDSubKClosedCtxBi E n (.letBinding A v₁ :: Γ) b b B →
      LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) (instantiate0 v₁ B)) ∧
  -- 3. Closed DeltaConst body diagonal in the empty context []
  (∀ {r : Nat} {m : CheckedMember} {b : Expr Nat},
    DeltaConst E r m b →
    LRTermDSubKClosedCtxBi E n [] b b m.mtype)

mutual
theorem fundCtxBiProbe_hasTyT (hW : EnvWfT E)
    (hPS : PropTyTransport E n ∧
      (∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂))
    (hSup : AppValCongrSupplyDSubKClosedCtxBi E n) :
    {Γ : LCtx} → {M A : Expr Nat} → HasTyT E n Γ M A →
      {Γ' : LCtx} → CtxRefines Γ Γ' → CtxWfT E n Γ' → CtxBVarOK E n Γ' →
      LRTermDSubKClosedCtxBi E n Γ' M M A
  | _, _, _, .sort _ l, Γ', _, _, _ =>
      lrTermDSubKClosedCtxBi_sort_diag Γ' l
  | _, _, _, .bvar _ i A hty, _, href, _, hbv =>
      hbv i A (by rw [lookupType_of_ctxRefines href i]; exact hty)
  | _, _, _, .const _ r ls m hm hlen _, Γ', _, hΓ', _ => by
      cases hb : m.body with
      | none => exact lrTermDSubKClosedCtxBi_consts_of_body_none ls ls _ hm hb
      | some b =>
          have har : m.arity = 0 := envWfT_body_arity_zero hW r m b hm hb
          have hls : ls = [] := List.eq_nil_of_length_eq_zero (hlen.trans har)
          subst hls
          obtain ⟨hdelta, _⟩ := envWfT_member_body_closed hW r m b hm hb
          obtain ⟨hclT, hclB⟩ := envClosed_of_envWfT hW r m hm
          have hbody0 : LRTermDSubKClosedCtxBi E n Γ' (instantiateLevels [] b) (instantiateLevels [] b)
              (instantiateLevels [] m.mtype) := by
            rw [instantiateLevels_nil, instantiateLevels_nil]
            exact lrTermDSubKClosedCtxBi_closed_weaken_ctx (envClosed_of_envWfT hW) hPS.2
              (hclB b hb 0) (hclB b hb 0) (hclT 0) hΓ' (hSup.2.2 hdelta)
          exact lrTermDSubKClosedCtxBi_deltaConsts hW hdelta hbody0
  | _, _, _, .pi _ A u B v hA _, _, href, hΓ', _ =>
      lrTermDSubKClosedCtxBi_pi_diag hΓ' B v (hasTyT_of_ctxRefines hA href)
  | _, _, _, .lam _ A _ b B _ _, Γ', _, _, _ =>
      lrTermDSubKClosedCtxBi_lam Γ' A A b b B
  | _, _, _, .app _ f a A B hf ha, Γ', href, hΓ', hbv =>
      have hf' : HasTyT E n Γ' f (.pi A B) := hasTyT_of_ctxRefines hf href
      have ha' : HasTyT E n Γ' a A := hasTyT_of_ctxRefines ha href
      hSup.1 hΓ' (.refl Γ' f (.pi A B) hf') (.refl Γ' a A ha')
        (fundCtxBiProbe_hasTyT hW hPS hSup hf href hΓ' hbv)
        (fundCtxBiProbe_hasTyT hW hPS hSup ha href hΓ' hbv)
  | _, _, _, .letE _ A u v B b hA hv hb, Γ', href, hΓ', hbv =>
      have hA' : HasTyT E n Γ' A (.sort u) := hasTyT_of_ctxRefines hA href
      have hv' : HasTyT E n Γ' v A := hasTyT_of_ctxRefines hv href
      have hΓ'_let : CtxWfT E n (.letBinding A v :: Γ') := .letBinding Γ' A u v hΓ' hA' hv'
      have ih_v : LRTermDSubKClosedCtxBi E n Γ' v v A :=
        fundCtxBiProbe_hasTyT hW hPS hSup hv href hΓ' hbv
      have hbv_let : CtxBVarOK E n (.letBinding A v :: Γ') :=
        ctxBVarOK_cons_letBinding hW hPS.2 hΓ'_let hbv ih_v
      have ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A v :: Γ') b b B :=
        fundCtxBiProbe_hasTyT hW hPS hSup hb (.letBinding href) hΓ'_let hbv_let
      lrTermDSubKClosedCtxBi_letE_diag hW hPS.2 hΓ' hv' ih_b
  | _, _, _, .lit _ t _ hexp, Γ', href, hΓ', hbv =>
      have hstep : WhRedPiKClosedCtx E Γ' (.lit t) (natExpand t) :=
        .step (.of_whStep (.lit t)) (.refl _)
      lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW hstep hstep
        (fundCtxBiProbe_hasTyT hW hPS hSup hexp href hΓ' hbv)
  | _, _, _, .conv _ _ A B u he hc, Γ', href, hΓ', hbv =>
      have hc' : ConvT E n Γ' A B (.sort u) := convT_of_ctxRefines hc href
      lrTermDSubKClosedCtxBi_tyConv_of_bi hW hPS.1 hΓ' (convEnds hW hΓ' hc').1 (.of Γ' A B u hc')
        (fundCtxBiProbe_hasTyT hW hPS hSup he href hΓ' hbv)
        (fundCtxBiProbe_convT hW hPS hSup hc href hΓ' hbv)

theorem fundCtxBiProbe_convT (hW : EnvWfT E)
    (hPS : PropTyTransport E n ∧
      (∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂))
    (hSup : AppValCongrSupplyDSubKClosedCtxBi E n) :
    {Γ : LCtx} → {M M' A : Expr Nat} → ConvT E n Γ M M' A →
      {Γ' : LCtx} → CtxRefines Γ Γ' → CtxWfT E n Γ' → CtxBVarOK E n Γ' →
      LRTermDSubKClosedCtxBi E n Γ' M M' A
  | _, _, _, _, .refl _ _ _ he, _, href, hΓ', hbv =>
      fundCtxBiProbe_hasTyT hW hPS hSup he href hΓ' hbv
  | _, _, _, _, .symm _ _ _ _ h, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_symm hW (fundCtxBiProbe_convT hW hPS hSup h href hΓ' hbv)
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_trans hW
        (fundCtxBiProbe_convT hW hPS hSup h₁ href hΓ' hbv)
        (fundCtxBiProbe_convT hW hPS hSup h₂ href hΓ' hbv)
  | _, _, _, _, .beta _ A body arg B u hA hbody harg, Γ', href, hΓ', hbv =>
      have hA' : HasTyT E n Γ' A (.sort u) := hasTyT_of_ctxRefines hA href
      have harg' : HasTyT E n Γ' arg A := hasTyT_of_ctxRefines harg href
      have hΓ'_let : CtxWfT E n (.letBinding A arg :: Γ') := .letBinding Γ' A u arg hΓ' hA' harg'
      have ih_arg : LRTermDSubKClosedCtxBi E n Γ' arg arg A :=
        fundCtxBiProbe_hasTyT hW hPS hSup harg href hΓ' hbv
      have hbv_let : CtxBVarOK E n (.letBinding A arg :: Γ') :=
        ctxBVarOK_cons_letBinding hW hPS.2 hΓ'_let hbv ih_arg
      have ih_body : LRTermDSubKClosedCtxBi E n (.letBinding A arg :: Γ') body body B :=
        fundCtxBiProbe_hasTyT hW hPS hSup hbody (.assumpToLet href) hΓ'_let hbv_let
      lrTermDSubKClosedCtxBi_beta_via_let hW hPS.2 hΓ' harg' ih_body
  | _, _, _, _, .zeta _ A v b B u hA hv hb, Γ', href, hΓ', hbv =>
      have hA' : HasTyT E n Γ' A (.sort u) := hasTyT_of_ctxRefines hA href
      have hv' : HasTyT E n Γ' v A := hasTyT_of_ctxRefines hv href
      have hΓ'_let : CtxWfT E n (.letBinding A v :: Γ') := .letBinding Γ' A u v hΓ' hA' hv'
      have ih_v : LRTermDSubKClosedCtxBi E n Γ' v v A :=
        fundCtxBiProbe_hasTyT hW hPS hSup hv href hΓ' hbv
      have hbv_let : CtxBVarOK E n (.letBinding A v :: Γ') :=
        ctxBVarOK_cons_letBinding hW hPS.2 hΓ'_let hbv ih_v
      have ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A v :: Γ') b b B :=
        fundCtxBiProbe_hasTyT hW hPS hSup hb (.letBinding href) hΓ'_let hbv_let
      lrTermDSubKClosedCtxBi_zeta hW hPS.2 hΓ' hv' ih_b
  | _, _, _, _, .zetaLocal _ _ _ _ hval _ hv, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_zetaLocal hW (lookupValue_of_ctxRefines href hval)
        (fundCtxBiProbe_hasTyT hW hPS hSup hv href hΓ' hbv)
  | _, _, _, _, .delta _ _ _ _ _ hres hbody _ _ _ hb, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW (.of_whStep (.delta hres hbody))
        (fundCtxBiProbe_hasTyT hW hPS hSup hb href hΓ' hbv)
  | _, _, _, _, .iota _ _ _ _ hI _ hrhs, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW (.of_whStep (.iota (derivedIotaU_ofDerivedIota hI)))
        (fundCtxBiProbe_hasTyT hW hPS hSup hrhs href hΓ' hbv)
  | _, _, _, _, .lit _ t _ _ hlit hexp, _, href, hΓ', hbv => by
      have hexp' := fundCtxBiProbe_hasTyT hW hPS hSup hexp href hΓ' hbv
      cases hlit
      exact lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW (.of_whStep (.lit t)) hexp'
  | _, _, _, _, .app _ _ _ _ _ _ _ hf ha, _, href, hΓ', hbv =>
      hSup.1 hΓ' (convT_of_ctxRefines hf href) (convT_of_ctxRefines ha href)
        (fundCtxBiProbe_convT hW hPS hSup hf href hΓ' hbv)
        (fundCtxBiProbe_convT hW hPS hSup ha href hΓ' hbv)
  | _, _, _, _, .lam _ A₁ A₂ b₁ b₂ B _ _ _, Γ', _, _, _ =>
      lrTermDSubKClosedCtxBi_lam Γ' A₁ A₂ b₁ b₂ B
  | _, _, _, _, .pi _ A₁ A₂ B₁ B₂ u v hcA hcB, Γ', href, hΓ', _ =>
      have hcA' : ConvT E n Γ' A₁ A₂ (.sort u) := convT_of_ctxRefines hcA href
      have hA₁ : HasTyT E n Γ' A₁ (.sort u) := (convEnds hW hΓ' hcA').1
      have hΓ'₁ : CtxWfT E n (.assumption A₁ :: Γ') := .assumption Γ' A₁ u hΓ' hA₁
      have hcB' : ConvT E n (.assumption A₁ :: Γ') B₁ B₂ (.sort v) :=
        convT_of_ctxRefines hcB (.assumption href)
      lrTermDSubKClosedCtxBi_pi hΓ'₁ (.of Γ' A₁ A₂ u hcA') (.of _ B₁ B₂ v hcB')
  | _, _, _, _, .letE _ A₁ A₂ v₁ v₂ b₁ b₂ B u hcA hcv hcb, Γ', href, hΓ', hbv =>
      have hcA' : ConvT E n Γ' A₁ A₂ (.sort u) := convT_of_ctxRefines hcA href
      have hcv' : ConvT E n Γ' v₁ v₂ A₁ := convT_of_ctxRefines hcv href
      have hA₁ : HasTyT E n Γ' A₁ (.sort u) := (convEnds hW hΓ' hcA').1
      have hv₁ : HasTyT E n Γ' v₁ A₁ := (convEnds hW hΓ' hcv').1
      have hv₂ : HasTyT E n Γ' v₂ A₁ := (convEnds hW hΓ' hcv').2.1
      have hΓ'_let : CtxWfT E n (.letBinding A₁ v₁ :: Γ') := .letBinding Γ' A₁ u v₁ hΓ' hA₁ hv₁
      have ih_v : LRTermDSubKClosedCtxBi E n Γ' v₁ v₂ A₁ :=
        fundCtxBiProbe_convT hW hPS hSup hcv href hΓ' hbv
      have ih_v₁ : LRTermDSubKClosedCtxBi E n Γ' v₁ v₁ A₁ :=
        lrTermDSubKClosedCtxBi_trans hW ih_v (lrTermDSubKClosedCtxBi_symm hW ih_v)
      have hbv_let : CtxBVarOK E n (.letBinding A₁ v₁ :: Γ') :=
        ctxBVarOK_cons_letBinding hW hPS.2 hΓ'_let hbv ih_v₁
      have ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A₁ v₁ :: Γ') b₁ b₂ B :=
        fundCtxBiProbe_convT hW hPS hSup hcb (.letBinding href) hΓ'_let hbv_let
      have ih_b₂ : LRTermDSubKClosedCtxBi E n (.letBinding A₁ v₁ :: Γ') b₂ b₂ B :=
        lrTermDSubKClosedCtxBi_trans hW (lrTermDSubKClosedCtxBi_symm hW ih_b) ih_b
      have h_inst_b : LRTermDSubKClosedCtxBi E n Γ' (instantiate0 v₁ b₁) (instantiate0 v₁ b₂)
          (instantiate0 v₁ B) :=
        lrTermDSubKClosedCtxBi_substLet0 hW hPS.2 hΓ' hv₁ ih_b
      have h_inst_v : LRTermDSubKClosedCtxBi E n Γ' (instantiate0 v₁ b₂) (instantiate0 v₂ b₂)
          (instantiate0 v₁ B) :=
        hSup.2.1 hΓ' hv₁ hv₂ hcv' ih_v ih_b₂
      have hL : WhRedPiKClosedCtx E Γ' (.letE A₁ v₁ b₁) (instantiate0 v₁ b₁) :=
        .step (.of_whStep (.zeta A₁ v₁ b₁)) (.refl _)
      have hR : WhRedPiKClosedCtx E Γ' (.letE A₂ v₂ b₂) (instantiate0 v₂ b₂) :=
        .step (.of_whStep (.zeta A₂ v₂ b₂)) (.refl _)
      lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW hL hR
        (lrTermDSubKClosedCtxBi_trans hW h_inst_b h_inst_v)
  | _, _, _, _, .sorts _ l₁ l₂ _, Γ', _, _, _ =>
      lrTermDSubKClosedCtxBi_sorts Γ' l₁ l₂
  | _, _, _, _, .consts _ r ls₁ ls₂ m hm hlen _ _ heq, Γ', _, hΓ', _ => by
      cases hb : m.body with
      | none => exact lrTermDSubKClosedCtxBi_consts_of_body_none ls₁ ls₂ _ hm hb
      | some b =>
          have har : m.arity = 0 := envWfT_body_arity_zero hW r m b hm hb
          have hls₁ : ls₁ = [] := List.eq_nil_of_length_eq_zero (hlen.trans har)
          subst hls₁
          have hls₂ : ls₂ = [] := by
            cases ls₂ with
            | nil => rfl
            | cons _ _ => exact False.elim heq
          subst hls₂
          obtain ⟨hdelta, _⟩ := envWfT_member_body_closed hW r m b hm hb
          obtain ⟨hclT, hclB⟩ := envClosed_of_envWfT hW r m hm
          have hbody0 : LRTermDSubKClosedCtxBi E n Γ' (instantiateLevels [] b) (instantiateLevels [] b)
              (instantiateLevels [] m.mtype) := by
            rw [instantiateLevels_nil, instantiateLevels_nil]
            exact lrTermDSubKClosedCtxBi_closed_weaken_ctx (envClosed_of_envWfT hW) hPS.2
              (hclB b hb 0) (hclB b hb 0) (hclT 0) hΓ' (hSup.2.2 hdelta)
          exact lrTermDSubKClosedCtxBi_deltaConsts hW hdelta hbody0
  | _, _, _, _, .eta _ _ _ _ hf, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_eta (fundCtxBiProbe_hasTyT hW hPS hSup hf href hΓ' hbv)
  | _, _, _, _, .irr _ _ _ _ hP _ _, _, href, _, _ =>
      lrTermDSubKClosedCtxBi_irr_of_sortRow hPS.2 (hasTyT_of_ctxRefines hP href)
  | _, _, _, _, .tyConv _ _ _ A A' u h hA, Γ', href, hΓ', hbv =>
      have hA' : ConvT E n Γ' A A' (.sort u) := convT_of_ctxRefines hA href
      lrTermDSubKClosedCtxBi_tyConv_of_bi hW hPS.1 hΓ' (convEnds hW hΓ' hA').1 (.of Γ' A A' u hA')
        (fundCtxBiProbe_convT hW hPS hSup h href hΓ' hbv)
        (fundCtxBiProbe_convT hW hPS hSup hA href hΓ' hbv)
end

/-- **Unconditional Bound-Variable Adequacy Across ALL Well-Formed Contexts `CtxWfT E n Γ`
    (`ctxBVarOK_of_ctxWfT`):**
    By induction on `hΓ : CtxWfT E n Γ` (using `ctxBVarOK_cons_assumption` on `.assumption` and
    `fundCtxBiProbe_hasTyT` + `ctxBVarOK_cons_letBinding` on `.letBinding`), every well-formed
    context `Γ : LCtx` satisfies `CtxBVarOK E n Γ`! -/
theorem ctxBVarOK_of_ctxWfT (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppValCongrSupplyDSubKClosedCtxBi E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    CtxBVarOK E n Γ := by
  induction hΓ with
  | nil => exact ctxBVarOK_nil
  | @assumption Γ₀ A u hΓ₀ hA ih =>
      exact ctxBVarOK_cons_assumption (envClosed_of_envWfT hW) hSort
        (.assumption Γ₀ A u hΓ₀ hA) ih
  | @letBinding Γ₀ A u v hΓ₀ hA hv ih =>
      have hv_ok : LRTermDSubKClosedCtxBi E n Γ₀ v v A :=
        fundCtxBiProbe_hasTyT hW ⟨hProp, hSort⟩ hSup hv (ctxRefines_refl Γ₀) hΓ₀ ih
      exact ctxBVarOK_cons_letBinding hW hSort (.letBinding Γ₀ A u v hΓ₀ hA hv) ih hv_ok

/-- Unrestricted `ProbeCpt` fundamental supply for one-sided `LRTermDSubKClosedCtx` across **all**
    well-formed contexts `CtxWfT E n Γ`. -/
def FundamentalTermDSubKClosedCtxProbe (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
      ∀ c, ProbeCpt c → ApproxDIK E (ctxEnvDIK E Γ) M c → LRTermDSubKClosedCtx E n Γ M M A c) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {M M' A : Expr Nat},
      HasTyT E n Γ M A → HasTyT E n Γ M' A → ConvT E n Γ M M' A →
      ∀ c, ProbeCpt c → ApproxDIK E (ctxEnvDIK E Γ) M c → LRTermDSubKClosedCtx E n Γ M M' A c)

theorem fundamentalTermDSubKClosedCtxProbe_of_biProbe
    (hF : FundamentalTermDSubKClosedCtxBiProbe E n) :
    FundamentalTermDSubKClosedCtxProbe E n :=
  ⟨fun {_} hΓ {_ _} hM c hc hMc => hF.1 hΓ hM c hc (Or.inl hMc),
   fun {_} hΓ {_ _ _} hM hM' hconv c hc hMc => hF.2 hΓ hM hM' hconv c hc (Or.inl hMc)⟩

/-- **Complete 27-Constructor Reduction Across ALL Contexts `Γ : LCtx` Without `LetFreeCtx` and
    Without `FundamentalLRINBot` (`fundamentalTermDSubKClosedCtxBiProbe_of_supply`):**
    Closes 25 of 27 `HasTyT` + `ConvT` constructors unconditionally (`HasTyT.sort`, `bvar`,
    `const`, `pi`, `lam`, `letE`, `lit`, `conv`, plus `app` via `ConvT.app`; `ConvT.refl`,
    `symm`, `trans`, `beta`, `zeta`, `zetaLocal`, `delta`, `iota`, `lit`, `lam`, `pi`, `sorts`,
    `consts`, `eta`, `irr`, `tyConv`) across **all** well-formed contexts `Γ : LCtx`! -/
theorem fundamentalTermDSubKClosedCtxBiProbe_of_supply (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppValCongrSupplyDSubKClosedCtxBi E n) :
    FundamentalTermDSubKClosedCtxBiProbe E n :=
  ⟨fun {Γ} hΓ {_ _} hM =>
     fundCtxBiProbe_hasTyT hW ⟨hProp, hSort⟩ hSup hM (ctxRefines_refl Γ) hΓ
       (ctxBVarOK_of_ctxWfT hW hProp hSort hSup hΓ),
   fun {Γ} hΓ {_ _ _} _ _ hconv =>
     fundCtxBiProbe_convT hW ⟨hProp, hSort⟩ hSup hconv (ctxRefines_refl Γ) hΓ
       (ctxBVarOK_of_ctxWfT hW hProp hSort hSup hΓ)⟩

theorem fundamentalTermDSubKClosedCtxProbe_of_supply (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppValCongrSupplyDSubKClosedCtxBi E n) :
    FundamentalTermDSubKClosedCtxProbe E n :=
  fundamentalTermDSubKClosedCtxProbe_of_biProbe
    (fundamentalTermDSubKClosedCtxBiProbe_of_supply hW hProp hSort hSup)

/-- **Direct Bridge from `AppValCongrSupplyDSubKClosedCtxBi E n` to `PiRowField E n` Across ALL
    Contexts `Γ : LCtx` (`piRow_of_appValCongrSupplyDSubKClosedCtxBi`):**
    Requires **zero** `LetFreeCtx Γ` restriction, **zero** `FundamentalLRINBot` premise, and
    **zero** external supplies for `HasTyT.bvar`, `HasTyT.letE`, `HasTyT.conv`, `ConvT.beta`,
    `ConvT.zeta`, `ConvT.zetaLocal`, or `ConvT.tyConv`! -/
theorem piRow_of_appValCongrSupplyDSubKClosedCtxBi (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppValCongrSupplyDSubKClosedCtxBi E n) :
    PiRowField E n :=
  piRow_of_fundamentalTermDSubKClosedCtxBiProbe hW
    (fundamentalTermDSubKClosedCtxBiProbe_of_supply hW hProp hSort hSup)

/-! ## §9. Unconditional `DeltaConst` Discharge from `EnvWfT E` (`AppLetCongrSupplyDSubKClosedCtxBi`),
Two-Way Weak-Head Reduction Equivalence (`↔`), and `SemEqDIK` / Neutral-Spine Congruence -/

/-! ### §9.1. Unconditional Discharge of `DeltaConst` Body Diagonal from `EnvWfT E` -/

/-- **Two-Clause Congruence Supply Across ALL Contexts `Γ : LCtx` (`AppLetCongrSupplyDSubKClosedCtxBi`):**
    Contains **only** the 2 congruence clauses (`ConvT.app` congruence and `ConvT.letE` diagonal-body
    value congruence), with **zero** `DeltaConst` clause (`deltaConst_lrTermDSubKClosedCtxBi_of_envWfT`
    below discharges the `DeltaConst` clause unconditionally by induction on `hW : EnvWfT E`!). -/
def AppLetCongrSupplyDSubKClosedCtxBi (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {f g a b A B : Expr Nat},
      ConvT E n Γ f g (.pi A B) → ConvT E n Γ a b A →
      LRTermDSubKClosedCtxBi E n Γ f g (.pi A B) →
      LRTermDSubKClosedCtxBi E n Γ a b A →
      LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g b) (instantiate0 a B)) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A v₁ v₂ b B : Expr Nat},
      HasTyT E n Γ v₁ A → HasTyT E n Γ v₂ A → ConvT E n Γ v₁ v₂ A →
      LRTermDSubKClosedCtxBi E n Γ v₁ v₂ A →
      LRTermDSubKClosedCtxBi E n (.letBinding A v₁ :: Γ) b b B →
      LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) (instantiate0 v₁ B))

mutual
/-- Sub-environment mutual structural induction for `HasTyT E₁ n Γ M A` into the fixed target
    semantic relation `LRTermDSubKClosedCtxBi E n Γ' M M A` along `hext : ∀ r m, E₁.members r = some m → E.members r = some m`. -/
theorem fundCtxBiProbe_sub_hasTyT {E₁ : ResolvedEnv} (hW : EnvWfT E)
    (hPS : PropTyTransport E n ∧
      (∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂))
    (hAppLet : AppLetCongrSupplyDSubKClosedCtxBi E n)
    (hext : ∀ r m, E₁.members r = some m → E.members r = some m)
    (hDelta₁ : ∀ {r : Nat} {m : CheckedMember} {b : Expr Nat},
      E₁.members r = some m → m.body = some b → LRTermDSubKClosedCtxBi E n [] b b m.mtype) :
    {Γ : LCtx} → {M A : Expr Nat} → HasTyT E₁ n Γ M A →
      {Γ' : LCtx} → CtxRefines Γ Γ' → CtxWfT E n Γ' → CtxBVarOK E n Γ' →
      LRTermDSubKClosedCtxBi E n Γ' M M A
  | _, _, _, .sort _ l, Γ', _, _, _ =>
      lrTermDSubKClosedCtxBi_sort_diag Γ' l
  | _, _, _, .bvar _ i A hty, _, href, _, hbv =>
      hbv i A (by rw [lookupType_of_ctxRefines href i]; exact hty)
  | _, _, _, .const _ r ls m hm hlen _, Γ', _, hΓ', _ => by
      have hmE : E.members r = some m := hext r m hm
      cases hb : m.body with
      | none => exact lrTermDSubKClosedCtxBi_consts_of_body_none ls ls _ hmE hb
      | some b =>
          have har : m.arity = 0 := envWfT_body_arity_zero hW r m b hmE hb
          have hls : ls = [] := List.eq_nil_of_length_eq_zero (hlen.trans har)
          subst hls
          obtain ⟨hdelta, _⟩ := envWfT_member_body_closed hW r m b hmE hb
          obtain ⟨hclT, hclB⟩ := envClosed_of_envWfT hW r m hmE
          have hbody0 : LRTermDSubKClosedCtxBi E n Γ' (instantiateLevels [] b) (instantiateLevels [] b)
              (instantiateLevels [] m.mtype) := by
            rw [instantiateLevels_nil, instantiateLevels_nil]
            exact lrTermDSubKClosedCtxBi_closed_weaken_ctx (envClosed_of_envWfT hW) hPS.2
              (hclB b hb 0) (hclB b hb 0) (hclT 0) hΓ' (hDelta₁ hm hb)
          exact lrTermDSubKClosedCtxBi_deltaConsts hW hdelta hbody0
  | _, _, _, .pi _ A u B v hA _, _, href, hΓ', _ =>
      lrTermDSubKClosedCtxBi_pi_diag hΓ' B v (hasTyT_of_ctxRefines (hasTyTExt hext hA) href)
  | _, _, _, .lam _ A _ b B _ _, Γ', _, _, _ =>
      lrTermDSubKClosedCtxBi_lam Γ' A A b b B
  | _, _, _, .app _ f a A B hf ha, Γ', href, hΓ', hbv =>
      have hf' : HasTyT E n Γ' f (.pi A B) := hasTyT_of_ctxRefines (hasTyTExt hext hf) href
      have ha' : HasTyT E n Γ' a A := hasTyT_of_ctxRefines (hasTyTExt hext ha) href
      hAppLet.1 hΓ' (.refl Γ' f (.pi A B) hf') (.refl Γ' a A ha')
        (fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hf href hΓ' hbv)
        (fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ ha href hΓ' hbv)
  | _, _, _, .letE _ A u v B b hA hv hb, Γ', href, hΓ', hbv =>
      have hA' : HasTyT E n Γ' A (.sort u) := hasTyT_of_ctxRefines (hasTyTExt hext hA) href
      have hv' : HasTyT E n Γ' v A := hasTyT_of_ctxRefines (hasTyTExt hext hv) href
      have hΓ'_let : CtxWfT E n (.letBinding A v :: Γ') := .letBinding Γ' A u v hΓ' hA' hv'
      have ih_v : LRTermDSubKClosedCtxBi E n Γ' v v A :=
        fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hv href hΓ' hbv
      have hbv_let : CtxBVarOK E n (.letBinding A v :: Γ') :=
        ctxBVarOK_cons_letBinding hW hPS.2 hΓ'_let hbv ih_v
      have ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A v :: Γ') b b B :=
        fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hb (.letBinding href) hΓ'_let hbv_let
      lrTermDSubKClosedCtxBi_letE_diag hW hPS.2 hΓ' hv' ih_b
  | _, _, _, .lit _ t _ hexp, Γ', href, hΓ', hbv =>
      have hstep : WhRedPiKClosedCtx E Γ' (.lit t) (natExpand t) :=
        .step (.of_whStep (.lit t)) (.refl _)
      lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW hstep hstep
        (fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hexp href hΓ' hbv)
  | _, _, _, .conv _ _ A B u he hc, Γ', href, hΓ', hbv =>
      have hc' : ConvT E n Γ' A B (.sort u) := convT_of_ctxRefines (convTExt hext hc) href
      lrTermDSubKClosedCtxBi_tyConv_of_bi hW hPS.1 hΓ' (convEnds hW hΓ' hc').1 (.of Γ' A B u hc')
        (fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ he href hΓ' hbv)
        (fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ hc href hΓ' hbv)

/-- Sub-environment mutual structural induction for `ConvT E₁ n Γ M M' A` into the fixed target
    semantic relation `LRTermDSubKClosedCtxBi E n Γ' M M' A`. -/
theorem fundCtxBiProbe_sub_convT {E₁ : ResolvedEnv} (hW : EnvWfT E)
    (hPS : PropTyTransport E n ∧
      (∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂))
    (hAppLet : AppLetCongrSupplyDSubKClosedCtxBi E n)
    (hext : ∀ r m, E₁.members r = some m → E.members r = some m)
    (hDelta₁ : ∀ {r : Nat} {m : CheckedMember} {b : Expr Nat},
      E₁.members r = some m → m.body = some b → LRTermDSubKClosedCtxBi E n [] b b m.mtype) :
    {Γ : LCtx} → {M M' A : Expr Nat} → ConvT E₁ n Γ M M' A →
      {Γ' : LCtx} → CtxRefines Γ Γ' → CtxWfT E n Γ' → CtxBVarOK E n Γ' →
      LRTermDSubKClosedCtxBi E n Γ' M M' A
  | _, _, _, _, .refl _ _ _ he, _, href, hΓ', hbv =>
      fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ he href hΓ' hbv
  | _, _, _, _, .symm _ _ _ _ h, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_symm hW
        (fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ h href hΓ' hbv)
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_trans hW
        (fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ h₁ href hΓ' hbv)
        (fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ h₂ href hΓ' hbv)
  | _, _, _, _, .beta _ A body arg B u hA hbody harg, Γ', href, hΓ', hbv =>
      have hA' : HasTyT E n Γ' A (.sort u) := hasTyT_of_ctxRefines (hasTyTExt hext hA) href
      have harg' : HasTyT E n Γ' arg A := hasTyT_of_ctxRefines (hasTyTExt hext harg) href
      have hΓ'_let : CtxWfT E n (.letBinding A arg :: Γ') := .letBinding Γ' A u arg hΓ' hA' harg'
      have ih_arg : LRTermDSubKClosedCtxBi E n Γ' arg arg A :=
        fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ harg href hΓ' hbv
      have hbv_let : CtxBVarOK E n (.letBinding A arg :: Γ') :=
        ctxBVarOK_cons_letBinding hW hPS.2 hΓ'_let hbv ih_arg
      have ih_body : LRTermDSubKClosedCtxBi E n (.letBinding A arg :: Γ') body body B :=
        fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hbody (.assumpToLet href) hΓ'_let hbv_let
      lrTermDSubKClosedCtxBi_beta_via_let hW hPS.2 hΓ' harg' ih_body
  | _, _, _, _, .zeta _ A v b B u hA hv hb, Γ', href, hΓ', hbv =>
      have hA' : HasTyT E n Γ' A (.sort u) := hasTyT_of_ctxRefines (hasTyTExt hext hA) href
      have hv' : HasTyT E n Γ' v A := hasTyT_of_ctxRefines (hasTyTExt hext hv) href
      have hΓ'_let : CtxWfT E n (.letBinding A v :: Γ') := .letBinding Γ' A u v hΓ' hA' hv'
      have ih_v : LRTermDSubKClosedCtxBi E n Γ' v v A :=
        fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hv href hΓ' hbv
      have hbv_let : CtxBVarOK E n (.letBinding A v :: Γ') :=
        ctxBVarOK_cons_letBinding hW hPS.2 hΓ'_let hbv ih_v
      have ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A v :: Γ') b b B :=
        fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hb (.letBinding href) hΓ'_let hbv_let
      lrTermDSubKClosedCtxBi_zeta hW hPS.2 hΓ' hv' ih_b
  | _, _, _, _, .zetaLocal _ _ _ _ hval _ hv, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_zetaLocal hW (lookupValue_of_ctxRefines href hval)
        (fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hv href hΓ' hbv)
  | _, _, _, _, .delta _ _ _ _ _ hres hbody _ _ _ hb, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW (.of_whStep (.delta (hext _ _ hres) hbody))
        (fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hb href hΓ' hbv)
  | _, _, _, _, .iota _ _ _ _ hI _ hrhs, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW
        (.of_whStep (.iota (derivedIotaU_ofDerivedIota (derivedIotaExt hext hI))))
        (fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hrhs href hΓ' hbv)
  | _, _, _, _, .lit _ t _ _ hlit hexp, _, href, hΓ', hbv => by
      have hexp' := fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hexp href hΓ' hbv
      cases hlit
      exact lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx hW (.of_whStep (.lit t)) hexp'
  | _, _, _, _, .app _ _ _ _ _ _ _ hf ha, _, href, hΓ', hbv =>
      hAppLet.1 hΓ' (convT_of_ctxRefines (convTExt hext hf) href)
        (convT_of_ctxRefines (convTExt hext ha) href)
        (fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ hf href hΓ' hbv)
        (fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ ha href hΓ' hbv)
  | _, _, _, _, .lam _ A₁ A₂ b₁ b₂ B _ _ _, Γ', _, _, _ =>
      lrTermDSubKClosedCtxBi_lam Γ' A₁ A₂ b₁ b₂ B
  | _, _, _, _, .pi _ A₁ A₂ B₁ B₂ u v hcA hcB, Γ', href, hΓ', _ =>
      have hcA' : ConvT E n Γ' A₁ A₂ (.sort u) := convT_of_ctxRefines (convTExt hext hcA) href
      have hA₁ : HasTyT E n Γ' A₁ (.sort u) := (convEnds hW hΓ' hcA').1
      have hΓ'₁ : CtxWfT E n (.assumption A₁ :: Γ') := .assumption Γ' A₁ u hΓ' hA₁
      have hcB' : ConvT E n (.assumption A₁ :: Γ') B₁ B₂ (.sort v) :=
        convT_of_ctxRefines (convTExt hext hcB) (.assumption href)
      lrTermDSubKClosedCtxBi_pi hΓ'₁ (.of Γ' A₁ A₂ u hcA') (.of _ B₁ B₂ v hcB')
  | _, _, _, _, .letE _ A₁ A₂ v₁ v₂ b₁ b₂ B u hcA hcv hcb, Γ', href, hΓ', hbv =>
      have hcA' : ConvT E n Γ' A₁ A₂ (.sort u) := convT_of_ctxRefines (convTExt hext hcA) href
      have hcv' : ConvT E n Γ' v₁ v₂ A₁ := convT_of_ctxRefines (convTExt hext hcv) href
      have hA₁ : HasTyT E n Γ' A₁ (.sort u) := (convEnds hW hΓ' hcA').1
      have hv₁ : HasTyT E n Γ' v₁ A₁ := (convEnds hW hΓ' hcv').1
      have hv₂ : HasTyT E n Γ' v₂ A₁ := (convEnds hW hΓ' hcv').2.1
      have hΓ'_let : CtxWfT E n (.letBinding A₁ v₁ :: Γ') := .letBinding Γ' A₁ u v₁ hΓ' hA₁ hv₁
      have ih_v : LRTermDSubKClosedCtxBi E n Γ' v₁ v₂ A₁ :=
        fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ hcv href hΓ' hbv
      have ih_v₁ : LRTermDSubKClosedCtxBi E n Γ' v₁ v₁ A₁ :=
        lrTermDSubKClosedCtxBi_trans hW ih_v (lrTermDSubKClosedCtxBi_symm hW ih_v)
      have hbv_let : CtxBVarOK E n (.letBinding A₁ v₁ :: Γ') :=
        ctxBVarOK_cons_letBinding hW hPS.2 hΓ'_let hbv ih_v₁
      have ih_b : LRTermDSubKClosedCtxBi E n (.letBinding A₁ v₁ :: Γ') b₁ b₂ B :=
        fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ hcb (.letBinding href) hΓ'_let hbv_let
      have ih_b₂ : LRTermDSubKClosedCtxBi E n (.letBinding A₁ v₁ :: Γ') b₂ b₂ B :=
        lrTermDSubKClosedCtxBi_trans hW (lrTermDSubKClosedCtxBi_symm hW ih_b) ih_b
      have h_inst_b : LRTermDSubKClosedCtxBi E n Γ' (instantiate0 v₁ b₁) (instantiate0 v₁ b₂)
          (instantiate0 v₁ B) :=
        lrTermDSubKClosedCtxBi_substLet0 hW hPS.2 hΓ' hv₁ ih_b
      have h_inst_v : LRTermDSubKClosedCtxBi E n Γ' (instantiate0 v₁ b₂) (instantiate0 v₂ b₂)
          (instantiate0 v₁ B) :=
        hAppLet.2 hΓ' hv₁ hv₂ hcv' ih_v ih_b₂
      have hL : WhRedPiKClosedCtx E Γ' (.letE A₁ v₁ b₁) (instantiate0 v₁ b₁) :=
        .step (.of_whStep (.zeta A₁ v₁ b₁)) (.refl _)
      have hR : WhRedPiKClosedCtx E Γ' (.letE A₂ v₂ b₂) (instantiate0 v₂ b₂) :=
        .step (.of_whStep (.zeta A₂ v₂ b₂)) (.refl _)
      lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW hL hR
        (lrTermDSubKClosedCtxBi_trans hW h_inst_b h_inst_v)
  | _, _, _, _, .sorts _ l₁ l₂ _, Γ', _, _, _ =>
      lrTermDSubKClosedCtxBi_sorts Γ' l₁ l₂
  | _, _, _, _, .consts _ r ls₁ ls₂ m hm hlen _ _ heq, Γ', _, hΓ', _ => by
      have hmE : E.members r = some m := hext r m hm
      cases hb : m.body with
      | none => exact lrTermDSubKClosedCtxBi_consts_of_body_none ls₁ ls₂ _ hmE hb
      | some b =>
          have har : m.arity = 0 := envWfT_body_arity_zero hW r m b hmE hb
          have hls₁ : ls₁ = [] := List.eq_nil_of_length_eq_zero (hlen.trans har)
          subst hls₁
          have hls₂ : ls₂ = [] := by
            cases ls₂ with
            | nil => rfl
            | cons _ _ => exact False.elim heq
          subst hls₂
          obtain ⟨hdelta, _⟩ := envWfT_member_body_closed hW r m b hmE hb
          obtain ⟨hclT, hclB⟩ := envClosed_of_envWfT hW r m hmE
          have hbody0 : LRTermDSubKClosedCtxBi E n Γ' (instantiateLevels [] b) (instantiateLevels [] b)
              (instantiateLevels [] m.mtype) := by
            rw [instantiateLevels_nil, instantiateLevels_nil]
            exact lrTermDSubKClosedCtxBi_closed_weaken_ctx (envClosed_of_envWfT hW) hPS.2
              (hclB b hb 0) (hclB b hb 0) (hclT 0) hΓ' (hDelta₁ hm hb)
          exact lrTermDSubKClosedCtxBi_deltaConsts hW hdelta hbody0
  | _, _, _, _, .eta _ _ _ _ hf, _, href, hΓ', hbv =>
      lrTermDSubKClosedCtxBi_eta
        (fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext hDelta₁ hf href hΓ' hbv)
  | _, _, _, _, .irr _ _ _ _ hP _ _, _, href, _, _ =>
      lrTermDSubKClosedCtxBi_irr_of_sortRow hPS.2
        (hasTyT_of_ctxRefines (hasTyTExt hext hP) href)
  | _, _, _, _, .tyConv _ _ _ A A' u h hA, Γ', href, hΓ', hbv =>
      have hA' : ConvT E n Γ' A A' (.sort u) := convT_of_ctxRefines (convTExt hext hA) href
      lrTermDSubKClosedCtxBi_tyConv_of_bi hW hPS.1 hΓ' (convEnds hW hΓ' hA').1 (.of Γ' A A' u hA')
        (fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ h href hΓ' hbv)
        (fundCtxBiProbe_sub_convT hW hPS hAppLet hext hDelta₁ hA href hΓ' hbv)
end

/-- `GroupMembersT` preserves all existing member entries of the base environment. -/
theorem groupMembersT_members_preserved {S : ResolvedEnv} :
    {E₁ : ResolvedEnv} → {list : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E₁ list E' →
    ∀ r m, E₁.members r = some m → E'.members r = some m
  | _, _, _, .nil _, _, _, hm => hm
  | _, _, _, .cons _ _ _ _ _ hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest, r, m, hm =>
      groupMembersT_members_preserved hrest r m (members_extend_preserved hfresh r m hm)

/-- Because every member added in `GroupMembersT.cons` has `m.body = none`, any member with
    `m.body = some b` in `E'` must already be present in the pre-group base environment `E₁`. -/
theorem groupMembersT_body_from_base {S : ResolvedEnv} :
    {E₁ : ResolvedEnv} → {list : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E₁ list E' →
    ∀ {r : Nat} {m : CheckedMember} {b : Expr Nat},
      E'.members r = some m → m.body = some b → E₁.members r = some m
  | _, _, _, .nil _, _, _, _, hm, _ => hm
  | _, _, _, .cons E₁ r₁ m₁ _ _ _ hnobody _ _ _ _ _ _ _ _ _ _ _ hrest, r, m, b, hm, hb => by
      have hm₀ := groupMembersT_body_from_base hrest hm hb
      by_cases hrr : r = r₁
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm₀
        cases hm₀
        rw [hnobody] at hb
        cases hb
      · simp only [extendEnv, if_neg hrr] at hm₀
        exact hm₀

/-- **Induction Over `hW₁ : EnvWfT E₁` Discharging `DeltaConst` Body Diagonals (`envWfT_deltaConst_sub`):**
    At each `.definition`, `.thm`, or `.opaque` step extending `E₁` by `(r₀, m₀)` with body `v`,
    `hv : HasTyT E₁ 0 [] v A` is typed in the strictly earlier environment `E₁`, where the induction
    hypothesis already supplies `hDelta₁` for all members of `E₁`! -/
theorem envWfT_deltaConst_sub (hW : EnvWfT E)
    (hPS : PropTyTransport E n ∧
      (∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂))
    (hAppLet : AppLetCongrSupplyDSubKClosedCtxBi E n) :
    {E₁ : ResolvedEnv} → EnvWfT E₁ →
    (∀ r m, E₁.members r = some m → E.members r = some m) →
    ∀ {r : Nat} {m : CheckedMember} {b : Expr Nat},
      E₁.members r = some m → m.body = some b → LRTermDSubKClosedCtxBi E n [] b b m.mtype
  | _, .empty, _, _, _, _, hm, _ => by
      simp only [emptyEnv] at hm; cases hm
  | _, .axiom (arity := arity) E₁ r₀ A _ hE₁ hfresh _ _ _, hext, r, m, b, hm, hb => by
      have hext₀ : ∀ r' m', E₁.members r' = some m' → E.members r' = some m' :=
        fun r' m' hm' => hext r' m'
          (members_extend_preserved (m := ⟨.axiomM, arity, A, none⟩) hfresh r' m' hm')
      by_cases hrr : r = r₀
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm; cases hb
      · simp only [extendEnv, if_neg hrr] at hm
        exact envWfT_deltaConst_sub hW hPS hAppLet hE₁ hext₀ hm hb
  | _, .definition E₁ r₀ A v _ hE₁ hfresh _ hv _ _ _ _, hext, r, m, b, hm, hb => by
      have hext₀ : ∀ r' m', E₁.members r' = some m' → E.members r' = some m' :=
        fun r' m' hm' => hext r' m'
          (members_extend_preserved (m := ⟨.definitionM, 0, A, some v⟩) hfresh r' m' hm')
      have ih : ∀ {r' : Nat} {m' : CheckedMember} {b' : Expr Nat},
          E₁.members r' = some m' → m'.body = some b' → LRTermDSubKClosedCtxBi E n [] b' b' m'.mtype :=
        fun hm' hb' => envWfT_deltaConst_sub hW hPS hAppLet hE₁ hext₀ hm' hb'
      by_cases hrr : r = r₀
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        injection hb with hb'
        subst hb'
        have hv_n : HasTyT E₁ n [] v A := hasTyT_relocate hv
        exact fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext₀ ih hv_n .nil .nil ctxBVarOK_nil
      · simp only [extendEnv, if_neg hrr] at hm
        exact ih hm hb
  | _, .thm E₁ r₀ A p hE₁ hfresh _ hp _ _ _ _, hext, r, m, b, hm, hb => by
      have hext₀ : ∀ r' m', E₁.members r' = some m' → E.members r' = some m' :=
        fun r' m' hm' => hext r' m'
          (members_extend_preserved (m := ⟨.theoremM, 0, A, some p⟩) hfresh r' m' hm')
      have ih : ∀ {r' : Nat} {m' : CheckedMember} {b' : Expr Nat},
          E₁.members r' = some m' → m'.body = some b' → LRTermDSubKClosedCtxBi E n [] b' b' m'.mtype :=
        fun hm' hb' => envWfT_deltaConst_sub hW hPS hAppLet hE₁ hext₀ hm' hb'
      by_cases hrr : r = r₀
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        injection hb with hb'
        subst hb'
        have hp_n : HasTyT E₁ n [] p A := hasTyT_relocate hp
        exact fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext₀ ih hp_n .nil .nil ctxBVarOK_nil
      · simp only [extendEnv, if_neg hrr] at hm
        exact ih hm hb
  | _, .opaque E₁ r₀ A v _ hE₁ hfresh _ hv _ _ _ _, hext, r, m, b, hm, hb => by
      have hext₀ : ∀ r' m', E₁.members r' = some m' → E.members r' = some m' :=
        fun r' m' hm' => hext r' m'
          (members_extend_preserved (m := ⟨.opaqueM, 0, A, some v⟩) hfresh r' m' hm')
      have ih : ∀ {r' : Nat} {m' : CheckedMember} {b' : Expr Nat},
          E₁.members r' = some m' → m'.body = some b' → LRTermDSubKClosedCtxBi E n [] b' b' m'.mtype :=
        fun hm' hb' => envWfT_deltaConst_sub hW hPS hAppLet hE₁ hext₀ hm' hb'
      by_cases hrr : r = r₀
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        injection hb with hb'
        subst hb'
        have hv_n : HasTyT E₁ n [] v A := hasTyT_relocate hv
        exact fundCtxBiProbe_sub_hasTyT hW hPS hAppLet hext₀ ih hv_n .nil .nil ctxBVarOK_nil
      · simp only [extendEnv, if_neg hrr] at hm
        exact ih hm hb
  | _, .group E₁ _ _ _ _ _ _ hE₁ _ _ _ hmem, hext, _, _, _, hm, hb =>
      envWfT_deltaConst_sub hW hPS hAppLet hE₁
        (fun r' m' hm' => hext r' m' (groupMembersT_members_preserved hmem r' m' hm'))
        (groupMembersT_body_from_base hmem hm hb) hb

/-- **Unconditional Discharge of the `DeltaConst` Body Diagonal from `EnvWfT E`
    (`deltaConst_lrTermDSubKClosedCtxBi_of_envWfT`):**
    Every defined/theorem/opaque constant `DeltaConst E r m b` in an admitted `EnvWfT E` environment
    automatically satisfies `LRTermDSubKClosedCtxBi E n [] b b m.mtype` given only `AppLetCongrSupplyDSubKClosedCtxBi E n`! -/
theorem deltaConst_lrTermDSubKClosedCtxBi_of_envWfT (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hAppLet : AppLetCongrSupplyDSubKClosedCtxBi E n)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some b) :
    LRTermDSubKClosedCtxBi E n [] b b m.mtype :=
  envWfT_deltaConst_sub hW ⟨hProp, hSort⟩ hAppLet hW (fun _ _ h => h) hm hb

/-- Upgrade `AppLetCongrSupplyDSubKClosedCtxBi` (2 clauses) to `AppValCongrSupplyDSubKClosedCtxBi`
    (3 clauses) by discharging the `DeltaConst` clause via `deltaConst_lrTermDSubKClosedCtxBi_of_envWfT`. -/
theorem appValCongrSupply_of_appLetCongrSupply (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hAppLet : AppLetCongrSupplyDSubKClosedCtxBi E n) :
    AppValCongrSupplyDSubKClosedCtxBi E n :=
  ⟨hAppLet.1, hAppLet.2, fun hdelta =>
    deltaConst_lrTermDSubKClosedCtxBi_of_envWfT hW hProp hSort hAppLet hdelta.1 hdelta.2.1⟩

theorem ctxBVarOK_of_ctxWfT_appLetCongr (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hAppLet : AppLetCongrSupplyDSubKClosedCtxBi E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    CtxBVarOK E n Γ :=
  ctxBVarOK_of_ctxWfT hW hProp hSort
    (appValCongrSupply_of_appLetCongrSupply hW hProp hSort hAppLet) hΓ

/-- **Complete 27-Constructor Reduction to the 2-Clause `AppLetCongrSupplyDSubKClosedCtxBi E n`
    (`fundamentalTermDSubKClosedCtxBiProbe_of_appLetCongrSupply`):**
    Closes `HasTyT.const` and `ConvT.consts` across **all** constants (both `body = none` and
    `body = some b`) unconditionally from `hW : EnvWfT E`! -/
theorem fundamentalTermDSubKClosedCtxBiProbe_of_appLetCongrSupply (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hAppLet : AppLetCongrSupplyDSubKClosedCtxBi E n) :
    FundamentalTermDSubKClosedCtxBiProbe E n :=
  fundamentalTermDSubKClosedCtxBiProbe_of_supply hW hProp hSort
    (appValCongrSupply_of_appLetCongrSupply hW hProp hSort hAppLet)

theorem fundamentalTermDSubKClosedCtxProbe_of_appLetCongrSupply (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hAppLet : AppLetCongrSupplyDSubKClosedCtxBi E n) :
    FundamentalTermDSubKClosedCtxProbe E n :=
  fundamentalTermDSubKClosedCtxProbe_of_biProbe
    (fundamentalTermDSubKClosedCtxBiProbe_of_appLetCongrSupply hW hProp hSort hAppLet)

/-- **Direct Bridge from the 2-Clause `AppLetCongrSupplyDSubKClosedCtxBi E n` to `PiRowField E n`
    Across ALL Contexts `Γ : LCtx` (`piRow_of_appLetCongrSupplyDSubKClosedCtxBi`).** -/
theorem piRow_of_appLetCongrSupplyDSubKClosedCtxBi (hW : EnvWfT E)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hAppLet : AppLetCongrSupplyDSubKClosedCtxBi E n) :
    PiRowField E n :=
  piRow_of_appValCongrSupplyDSubKClosedCtxBi hW hProp hSort
    (appValCongrSupply_of_appLetCongrSupply hW hProp hSort hAppLet)

/-! ### §9.2. Two-Way Weak-Head Reduction Equivalence (`↔`) of `LRTypeINPiKClosedCtx` and
`LRTermDSubKClosedCtxBi`, and Equivalence of `letE` Value Congruence with $\beta$/$\zeta$ Congruence -/

/-- By single-step determinism `whDetPiKClosedCtx_of_envWfT`, if `M` steps to `X` in
    `WhStepPiKClosedCtx E Γ` and reduces to a normal form `N`, then `X` also reduces to `N`. -/
theorem whRedPiKClosedCtx_of_whStepPiKClosedCtx_normal (hW : EnvWfT E) {Γ : LCtx}
    {M X N : Expr Nat} (hs : WhStepPiKClosedCtx E Γ M X)
    (hred : WhRedPiKClosedCtx E Γ M N) (hnorm : WhNormalPiKClosedCtx E Γ N) :
    WhRedPiKClosedCtx E Γ X N := by
  cases hred with
  | refl => exact (hnorm X hs).elim
  | step hs₀ hred₀ =>
      have heq := whDetPiKClosedCtx_of_envWfT hW hs hs₀
      subst heq
      exact hred₀

/-- Multi-step forward preservation of reduction to a normal form `N` under `WhRedPiKClosedCtx E Γ`. -/
theorem whRedPiKClosedCtx_of_whRedPiKClosedCtx_normal (hW : EnvWfT E) {Γ : LCtx}
    {M X N : Expr Nat} (hMX : WhRedPiKClosedCtx E Γ M X)
    (hMN : WhRedPiKClosedCtx E Γ M N) (hnorm : WhNormalPiKClosedCtx E Γ N) :
    WhRedPiKClosedCtx E Γ X N := by
  induction hMX with
  | refl => exact hMN
  | step hs _ ih =>
      exact ih (whRedPiKClosedCtx_of_whStepPiKClosedCtx_normal hW hs hMN hnorm)

/-- **Two-Way Weak-Head Reduction Equivalence (`↔`) for Normal Targets
    (`whRedPiKClosedCtx_iff_of_whRedPiKClosedCtx_normal`):**
    Whenever `WhRedPiKClosedCtx E Γ M X` and `WhNormalPiKClosedCtx E Γ N`,
    `WhRedPiKClosedCtx E Γ M N ↔ WhRedPiKClosedCtx E Γ X N`! -/
theorem whRedPiKClosedCtx_iff_of_whRedPiKClosedCtx_normal (hW : EnvWfT E) {Γ : LCtx}
    {M X N : Expr Nat} (hMX : WhRedPiKClosedCtx E Γ M X) (hnorm : WhNormalPiKClosedCtx E Γ N) :
    WhRedPiKClosedCtx E Γ M N ↔ WhRedPiKClosedCtx E Γ X N :=
  ⟨fun hMN => whRedPiKClosedCtx_of_whRedPiKClosedCtx_normal hW hMX hMN hnorm,
   fun hXN => whRedPiKClosedCtx_trans hMX hXN⟩

theorem whRedPiKClosedCtx_sort_iff_of_whRed (hW : EnvWfT E) {Γ : LCtx}
    {M X : Expr Nat} (hMX : WhRedPiKClosedCtx E Γ M X) (l : Level) :
    WhRedPiKClosedCtx E Γ M (.sort l) ↔ WhRedPiKClosedCtx E Γ X (.sort l) :=
  whRedPiKClosedCtx_iff_of_whRedPiKClosedCtx_normal hW hMX (whNormalPiKClosedCtx_sort E Γ l)

theorem whRedPiKClosedCtx_pi_iff_of_whRed (hW : EnvWfT E) {Γ : LCtx}
    {M X : Expr Nat} (hMX : WhRedPiKClosedCtx E Γ M X) (A B : Expr Nat) :
    WhRedPiKClosedCtx E Γ M (.pi A B) ↔ WhRedPiKClosedCtx E Γ X (.pi A B) :=
  whRedPiKClosedCtx_iff_of_whRedPiKClosedCtx_normal hW hMX (whNormalPiKClosedCtx_pi E Γ A B)

/-- Forward preservation of `LRTypeINPiKClosedCtx` under `WhRedPiKClosedCtx E Γ`. -/
theorem lrTypeINPiKClosedCtx_whRedPiKClosedCtx_preserve (hW : EnvWfT E) {Γ : LCtx}
    {M M' X X' : Expr Nat} {c : CptI}
    (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    (h : LRTypeINPiKClosedCtx E n Γ M M' c) :
    LRTypeINPiKClosedCtx E n Γ X X' c := by
  cases h with
  | bot => exact .bot Γ X X'
  | sort h1 h2 =>
      exact .sort ((whRedPiKClosedCtx_sort_iff_of_whRed hW hX _).mp h1)
        ((whRedPiKClosedCtx_sort_iff_of_whRed hW hX' _).mp h2)
  | pi h1 h2 hΓ₁ hcA hcB hdom hcod =>
      exact .pi ((whRedPiKClosedCtx_pi_iff_of_whRed hW hX _ _).mp h1)
        ((whRedPiKClosedCtx_pi_iff_of_whRed hW hX' _ _).mp h2) hΓ₁ hcA hcB hdom hcod
  | spine h1 h2 hN1 hN2 hc =>
      exact .spine
        (whRedPiKClosedCtx_of_whRedPiKClosedCtx_normal hW hX h1 hN1)
        (whRedPiKClosedCtx_of_whRedPiKClosedCtx_normal hW hX' h2 hN2)
        hN1 hN2 hc

/-- **Two-Way `WhRedPiKClosedCtx` Equivalence (`↔`) of `LRTypeINPiKClosedCtx`
    (`lrTypeINPiKClosedCtx_whRedPiKClosedCtx_iff`):** -/
theorem lrTypeINPiKClosedCtx_whRedPiKClosedCtx_iff (hW : EnvWfT E) {Γ : LCtx}
    {M M' X X' : Expr Nat} (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    (c : CptI) :
    LRTypeINPiKClosedCtx E n Γ M M' c ↔ LRTypeINPiKClosedCtx E n Γ X X' c :=
  ⟨lrTypeINPiKClosedCtx_whRedPiKClosedCtx_preserve hW hX hX',
   lrTypeINPiKClosedCtx_expand hX hX'⟩

theorem lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_probe_preserve (hW : EnvWfT E) {Γ : LCtx}
    {M M' X X' A : Expr Nat} (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    {c : CptI} (hc : ProbeCpt c) (h : LRTermDSubKClosedCtxCore E n Γ M M' A c) :
    LRTermDSubKClosedCtxCore E n Γ X X' A c := by
  cases hc with
  | bot => rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial
  | sort =>
      have hne : CptI.sort ≠ .bot := by intro h0; cases h0
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .sort hne] at h ⊢
      exact ⟨h.1, lrTypeINPiKClosedCtx_whRedPiKClosedCtx_preserve hW hX hX' h.2⟩
  | piBotNil =>
      have hne : CptI.pi .bot [] ≠ .bot := by intro h0; cases h0
      rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil hne] at h ⊢
      exact ⟨h.1, lrTypeINPiKClosedCtx_whRedPiKClosedCtx_preserve hW hX hX' h.2⟩

theorem lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_probe_iff (hW : EnvWfT E) {Γ : LCtx}
    {M M' X X' A : Expr Nat} (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    {c : CptI} (hc : ProbeCpt c) :
    LRTermDSubKClosedCtxCore E n Γ M M' A c ↔ LRTermDSubKClosedCtxCore E n Γ X X' A c :=
  ⟨lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_probe_preserve hW hX hX' hc,
   lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_expand_probe hX hX' hc⟩

theorem lrTermDSubKClosedCtx_whRedPiKClosedCtx_probe_iff (hW : EnvWfT E) {Γ : LCtx}
    {M M' X X' A : Expr Nat} (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    {c : CptI} (hc : ProbeCpt c) :
    LRTermDSubKClosedCtx E n Γ M M' A c ↔ LRTermDSubKClosedCtx E n Γ X X' A c :=
  or_congr Iff.rfl (lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_probe_iff hW hX hX' hc)

theorem lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_preserve (hW : EnvWfT E) {Γ : LCtx}
    {M M' X X' A : Expr Nat} (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X')
    (h : LRTermDSubKClosedCtxBi E n Γ M M' A) :
    LRTermDSubKClosedCtxBi E n Γ X X' A := by
  intro c hc hXc
  have hMc : ApproxDIK E (ctxEnvDIK E Γ) M c ∨ ApproxDIK E (ctxEnvDIK E Γ) M' c := by
    rcases hXc with h1 | h2
    · exact Or.inl (approxDIK_ctxEnvDIK_whRedPiKClosedCtx_back hW hX h1)
    · exact Or.inr (approxDIK_ctxEnvDIK_whRedPiKClosedCtx_back hW hX' h2)
  exact (lrTermDSubKClosedCtx_whRedPiKClosedCtx_probe_iff hW hX hX' hc).mp (h c hc hMc)

/-- **Two-Way `WhRedPiKClosedCtx` Equivalence (`↔`) of `LRTermDSubKClosedCtxBi`
    (`lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff`):**
    Because `ApproxDIK E (ctxEnvDIK E Γ)` is invariant under `WhRedPiKClosedCtx E Γ` and
    `WhRedPiKClosedCtx E Γ` is deterministic (`whDetPiKClosedCtx_of_envWfT`), weak-head reduction of
    `M` and `M'` is a two-way equivalence `↔` in `LRTermDSubKClosedCtxBi`! -/
theorem lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff (hW : EnvWfT E) {Γ : LCtx}
    {M M' X X' A : Expr Nat} (hX : WhRedPiKClosedCtx E Γ M X) (hX' : WhRedPiKClosedCtx E Γ M' X') :
    LRTermDSubKClosedCtxBi E n Γ M M' A ↔ LRTermDSubKClosedCtxBi E n Γ X X' A :=
  ⟨lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_preserve hW hX hX',
   lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand hW hX hX'⟩

/-- **Exact Equivalence Between $\beta$-Redex Application Congruence and 0-Instantiation Congruence
    (`lrTermDSubKClosedCtxBi_beta_congr_iff_subst0`):** -/
theorem lrTermDSubKClosedCtxBi_beta_congr_iff_subst0 (hW : EnvWfT E) {Γ : LCtx}
    (A₁ A₂ b₁ b₂ v₁ v₂ T : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ (.app (.lam A₁ b₁) v₁) (.app (.lam A₂ b₂) v₂) T ↔
      LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b₁) (instantiate0 v₂ b₂) T :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff hW
    (.step (.of_whStep (.beta A₁ b₁ v₁)) (.refl _))
    (.step (.of_whStep (.beta A₂ b₂ v₂)) (.refl _))

/-- **Exact Equivalence Between $\zeta$-Redex `letE` Congruence and 0-Instantiation Congruence
    (`lrTermDSubKClosedCtxBi_zeta_congr_iff_subst0`):** -/
theorem lrTermDSubKClosedCtxBi_zeta_congr_iff_subst0 (hW : EnvWfT E) {Γ : LCtx}
    (A₁ A₂ v₁ v₂ b₁ b₂ T : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ (.letE A₁ v₁ b₁) (.letE A₂ v₂ b₂) T ↔
      LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b₁) (instantiate0 v₂ b₂) T :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff hW
    (.step (.of_whStep (.zeta A₁ v₁ b₁)) (.refl _))
    (.step (.of_whStep (.zeta A₂ v₂ b₂)) (.refl _))

/-- Whenever `f₁` and `f₂` weak-head reduce in `WhRedPiKClosedCtx E Γ` to `.lam A₁ b₁` and `.lam A₂ b₂`,
    application congruence `.app f₁ a₁ ~ .app f₂ a₂` is 100% equivalent `↔` to 0-instantiation
    congruence `instantiate0 a₁ b₁ ~ instantiate0 a₂ b₂`. -/
theorem lrTermDSubKClosedCtxBi_app_lam_whRed_iff_subst0 (hW : EnvWfT E) {Γ : LCtx}
    {f₁ f₂ A₁ A₂ b₁ b₂ : Expr Nat}
    (hf₁ : WhRedPiKClosedCtx E Γ f₁ (.lam A₁ b₁))
    (hf₂ : WhRedPiKClosedCtx E Γ f₂ (.lam A₂ b₂))
    (a₁ a₂ T : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ (.app f₁ a₁) (.app f₂ a₂) T ↔
      LRTermDSubKClosedCtxBi E n Γ (instantiate0 a₁ b₁) (instantiate0 a₂ b₂) T :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff hW
    (whRedPiKClosedCtx_trans (whRedPiKClosedCtx_appHead hf₁)
      (.step (.of_whStep (.beta A₁ b₁ a₁)) (.refl _)))
    (whRedPiKClosedCtx_trans (whRedPiKClosedCtx_appHead hf₂)
      (.step (.of_whStep (.beta A₂ b₂ a₂)) (.refl _)))

/-- When the body `b = lift 0 1 b₀` does not depend on index 0, `instantiate0 v₁ b = b₀ = instantiate0 v₂ b`,
    so `ConvT.letE` diagonal-body value congruence holds unconditionally from `ih_b₀` alone! -/
theorem lrTermDSubKClosedCtxBi_subst0_lift0_one {Γ : LCtx} (v₁ v₂ b₀ T : Expr Nat)
    (hb₀ : LRTermDSubKClosedCtxBi E n Γ b₀ b₀ T) :
    LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ (lift 0 1 b₀)) (instantiate0 v₂ (lift 0 1 b₀)) T := by
  have h1 : instantiate0 v₁ (lift 0 1 b₀) = b₀ :=
    (instantiate_lift_cancel 1 0 0 v₁ (by omega) (by omega) b₀).trans (lift_zero 0 b₀)
  have h2 : instantiate0 v₂ (lift 0 1 b₀) = b₀ :=
    (instantiate_lift_cancel 1 0 0 v₂ (by omega) (by omega) b₀).trans (lift_zero 0 b₀)
  rw [h1, h2]
  exact hb₀

/-! ### §9.3. `SemEqDIK` Substitution Congruence and Unconditional Application Congruence on
Non-`.lam` Heads & Neutral / Constructor / Inductive Spines -/

/-- Whenever `SemEqDIK E ρ (lift 0 j v₁) (lift 0 j v₂)` holds,
    `denDIK E ρ (instantiate j (lift 0 j v₁) b) = denDIK E ρ (instantiate j (lift 0 j v₂) b)`
    for **every** body `b : Expr Nat` and cutoff `j : Nat`. -/
theorem denDIK_instantiate_eq_of_semEqDIK {E : ResolvedEnv} {ρ : EnvI} {v₁ v₂ : Expr Nat}
    {j : Nat} (hv : SemEqDIK E ρ (lift 0 j v₁) (lift 0 j v₂)) (b : Expr Nat) :
    denDIK E ρ (instantiate j (lift 0 j v₁) b) = denDIK E ρ (instantiate j (lift 0 j v₂) b) := by
  have hden : denDIK E ρ (lift 0 j v₁) = denDIK E ρ (lift 0 j v₂) := funext fun c => propext (hv c)
  rw [denDIK_subst_eq, denDIK_subst_eq, hden]

/-- **Unconditional `SemEqDIK` Substitution Congruence (`semEqDIK_instantiate_of_semEqDIK`):**
    If `SemEqDIK E ρ (lift 0 j v₁) (lift 0 j v₂)`, then
    `SemEqDIK E ρ (instantiate j (lift 0 j v₁) b) (instantiate j (lift 0 j v₂) b)` for **every**
    expression `b : Expr Nat` and index `j : Nat`! -/
theorem semEqDIK_instantiate_of_semEqDIK {E : ResolvedEnv} {ρ : EnvI} {v₁ v₂ : Expr Nat}
    {j : Nat} (hv : SemEqDIK E ρ (lift 0 j v₁) (lift 0 j v₂)) (b : Expr Nat) :
    SemEqDIK E ρ (instantiate j (lift 0 j v₁) b) (instantiate j (lift 0 j v₂) b) := by
  intro c
  change denDIK E ρ (instantiate j (lift 0 j v₁) b) c ↔ denDIK E ρ (instantiate j (lift 0 j v₂) b) c
  rw [denDIK_instantiate_eq_of_semEqDIK hv b]

theorem semEqDIK_instantiate0_of_semEqDIK {E : ResolvedEnv} {ρ : EnvI} {v₁ v₂ : Expr Nat}
    (hv : SemEqDIK E ρ v₁ v₂) (b : Expr Nat) :
    SemEqDIK E ρ (instantiate0 v₁ b) (instantiate0 v₂ b) := by
  have hv₀ : SemEqDIK E ρ (lift 0 0 v₁) (lift 0 0 v₂) := by simpa only [lift_zero] using hv
  have h0 := semEqDIK_instantiate_of_semEqDIK hv₀ b
  simpa only [lift_zero, instantiate0] using h0

theorem approxDIK_ctxEnvDIK_instantiate0_iff_of_semEqDIK {E : ResolvedEnv} {Γ : LCtx}
    {v₁ v₂ : Expr Nat} (hv : SemEqDIK E (ctxEnvDIK E Γ) v₁ v₂) (b : Expr Nat) (c : CptI) :
    ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₁ b) c ↔
      ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₂ b) c :=
  semEqDIK_instantiate0_of_semEqDIK hv b c

/-- Any pair of terms `M, M'` whose only `ProbeCpt` compact in `ApproxDIK E (ctxEnvDIK E Γ)` is `.bot`
    is unconditionally related in `LRTermDSubKClosedCtxBi E n Γ M M' T` at every type `T`. -/
theorem lrTermDSubKClosedCtxBi_of_probeCpt_eq_bot {Γ : LCtx} {M M' : Expr Nat} (T : Expr Nat)
    (hM : ∀ c, ProbeCpt c → ApproxDIK E (ctxEnvDIK E Γ) M c → c = .bot)
    (hM' : ∀ c, ProbeCpt c → ApproxDIK E (ctxEnvDIK E Γ) M' c → c = .bot) :
    LRTermDSubKClosedCtxBi E n Γ M M' T := by
  intro c hc hMc
  have hbot : c = .bot := by
    rcases hMc with h1 | h2
    · exact hM c hc h1
    · exact hM' c hc h2
  subst hbot
  exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial)

/-- When `SemEqDIK E (ctxEnvDIK E Γ) v₁ v₂` holds and `b` has only `.bot` on `ProbeCpt` in
    `ApproxDIK E (ctxEnvDIK E (.letBinding A v₁ :: Γ))`, 0-instantiation congruence
    `LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) T` holds unconditionally! -/
theorem lrTermDSubKClosedCtxBi_subst0_of_semEqDIK_botProbe {Γ : LCtx} {A v₁ v₂ b : Expr Nat}
    (T : Expr Nat) (hv : SemEqDIK E (ctxEnvDIK E Γ) v₁ v₂)
    (hb : ∀ c, ProbeCpt c → ApproxDIK E (ctxEnvDIK E (.letBinding A v₁ :: Γ)) b c → c = .bot) :
    LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) T := by
  have hb₁ : ∀ c, ProbeCpt c → ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₁ b) c → c = .bot :=
    fun c hc h => hb c hc ((approxDIK_ctxEnvDIK_substLet0_iff E A v₁ Γ b c).mp h)
  have hb₂ : ∀ c, ProbeCpt c → ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₂ b) c → c = .bot :=
    fun c hc h => hb₁ c hc ((approxDIK_ctxEnvDIK_instantiate0_iff_of_semEqDIK hv b c).mpr h)
  exact lrTermDSubKClosedCtxBi_of_probeCpt_eq_bot T hb₁ hb₂

/-- If `f` has no `.lam g` compact in `ApproxDIK E ρ`, then `.app f a` also has no `.lam g` compact
    in `ApproxDIK E ρ` for any argument `a : Expr Nat`. -/
theorem approxDIK_app_not_lam_of_not_lam {E : ResolvedEnv} {ρ : EnvI} {f : Expr Nat}
    (hf : ∀ g, ¬ ApproxDIK E ρ f (.lam g)) (a : Expr Nat) (g : List (List CptI × CptI)) :
    ¬ ApproxDIK E ρ (.app f a) (.lam g) := by
  intro h
  rcases approxDIK_app_inv h with hbot | ⟨g₀, _, _, hfg₀, _, _⟩ | ⟨_, _, _, hsp, _, _⟩
  · cases hbot
  · exact hf g₀ hfg₀
  · cases hsp

/-- By induction on `args`, if the head `hd` has no `.lam g` compact in `ApproxDIK E ρ`, then the
    entire spine `foldApps hd args` has no `.lam g` compact in `ApproxDIK E ρ`. -/
theorem approxDIK_foldApps_not_lam_of_not_lam {E : ResolvedEnv} {ρ : EnvI} {hd : Expr Nat}
    (hhd : ∀ g, ¬ ApproxDIK E ρ hd (.lam g)) :
    ∀ (args : List (Expr Nat)) (g : List (List CptI × CptI)),
      ¬ ApproxDIK E ρ (foldApps hd args) (.lam g)
  | [], g => hhd g
  | a :: args, g =>
      approxDIK_foldApps_not_lam_of_not_lam (approxDIK_app_not_lam_of_not_lam hhd a) args g

/-- **Key `ProbeCpt` Application Exclusion (`approxDIK_app_probeCpt_eq_bot_of_no_lam`):**
    Because `ProbeCpt = {.bot, .sort, .pi .bot []}` contains no `.spine` compacts, if `f` has no
    `.lam g` compact in `ApproxDIK E ρ`, then the **only** `ProbeCpt` compact of `.app f a` in
    `ApproxDIK E ρ` is `.bot`! -/
theorem approxDIK_app_probeCpt_eq_bot_of_no_lam {E : ResolvedEnv} {ρ : EnvI}
    {f a : Expr Nat} (hf : ∀ g, ¬ ApproxDIK E ρ f (.lam g))
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E ρ (.app f a) c) :
    c = .bot := by
  rcases approxDIK_app_inv h with rfl | ⟨g, _, _, hfg, _, _⟩ | ⟨_, _, _, rfl, _, _⟩
  · rfl
  · exact (hf g hfg).elim
  · cases hc

/-- For any non-empty argument list `a :: args`, if `hd` has no `.lam g` compact in `ApproxDIK E ρ`,
    then the only `ProbeCpt` compact of `foldApps hd (a :: args)` in `ApproxDIK E ρ` is `.bot`. -/
theorem approxDIK_foldApps_probeCpt_eq_bot_of_no_lam {E : ResolvedEnv} {ρ : EnvI}
    {hd : Expr Nat} (hhd : ∀ g, ¬ ApproxDIK E ρ hd (.lam g)) :
    ∀ (a : Expr Nat) (args : List (Expr Nat)) {c : CptI},
      ProbeCpt c → ApproxDIK E ρ (foldApps hd (a :: args)) c → c = .bot
  | _, [], _, hc, h => approxDIK_app_probeCpt_eq_bot_of_no_lam hhd hc h
  | a, a' :: args, _, hc, h =>
      approxDIK_foldApps_probeCpt_eq_bot_of_no_lam
        (approxDIK_app_not_lam_of_not_lam hhd a) a' args hc h

/-- An assumption bound variable (`lookupValue Γ i = none`) has no `.lam g` compact in `ApproxDIK E (ctxEnvDIK E Γ)`. -/
theorem approxDIK_ctxEnvDIK_bvar_none_not_lam {E : ResolvedEnv} {Γ : LCtx} {i : Nat}
    (hnone : lookupValue Γ i = none) (g : List (List CptI × CptI)) :
    ¬ ApproxDIK E (ctxEnvDIK E Γ) (.bvar i) (.lam g) := by
  intro h
  have hbot := approxDIK_ctxEnvDIK_bvar_none_eq_bot hnone h
  cases hbot

/-- A sort `.sort l` has no `.lam g` compact in `ApproxDIK E ρ`. -/
theorem approxDIK_sort_not_lam {E : ResolvedEnv} {ρ : EnvI} (l : Level)
    (g : List (List CptI × CptI)) :
    ¬ ApproxDIK E ρ (.sort l) (.lam g) := by
  intro h
  rcases approxDIK_sort_inv h with h0 | h0 <;> cases h0

/-- A Pi-type `.pi A B` has no `.lam g` compact in `ApproxDIK E ρ`. -/
theorem approxDIK_pi_not_lam {E : ResolvedEnv} {ρ : EnvI} (A B : Expr Nat)
    (g : List (List CptI × CptI)) :
    ¬ ApproxDIK E ρ (.pi A B) (.lam g) := by
  intro h
  rcases approxDIK_pi_inv h with h0 | ⟨_, _, h0, _, _⟩ <;> cases h0

/-- Every non-recursor constant with `m.body = none` (axioms, inductive type formers, constructors)
    has no `.lam g` compact in `ApproxDIK E ρ`. -/
theorem approxDIK_rigidConst_not_lam {E : ResolvedEnv} {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} (hm : E.members r = some m) (hb : m.body = none)
    (hnrec : m.mclass ≠ .recursorM) (g : List (List CptI × CptI)) :
    ¬ ApproxDIK E ρ (.const r ls) (.lam g) := by
  intro h
  rcases approxDIK_rigid_const_inv (rigidConst_of_body_none hm hb hnrec) h with h0 | h0 <;> cases h0

/-- **Unconditional Application Congruence in `LRTermDSubKClosedCtxBi` for Non-`.lam` Heads
    (`lrTermDSubKClosedCtxBi_app_of_no_lam`):**
    Whenever `f₁` and `f₂` have no `.lam g` compact in `ApproxDIK E (ctxEnvDIK E Γ)` (for instance,
    when `f₁, f₂` are assumption variables, axioms, inductive type formers, constructors, or spines
    headed by them), `LRTermDSubKClosedCtxBi E n Γ (.app f₁ a₁) (.app f₂ a₂) T` holds **100%
    unconditionally** for **all** arguments `a₁, a₂ : Expr Nat` and **all** types `T`! -/
theorem lrTermDSubKClosedCtxBi_app_of_no_lam {Γ : LCtx} {f₁ f₂ : Expr Nat}
    (hf₁ : ∀ g, ¬ ApproxDIK E (ctxEnvDIK E Γ) f₁ (.lam g))
    (hf₂ : ∀ g, ¬ ApproxDIK E (ctxEnvDIK E Γ) f₂ (.lam g))
    (a₁ a₂ T : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ (.app f₁ a₁) (.app f₂ a₂) T :=
  lrTermDSubKClosedCtxBi_of_probeCpt_eq_bot T
    (fun _ hc h => approxDIK_app_probeCpt_eq_bot_of_no_lam hf₁ hc h)
    (fun _ hc h => approxDIK_app_probeCpt_eq_bot_of_no_lam hf₂ hc h)

/-- Multi-argument spine generalization of `lrTermDSubKClosedCtxBi_app_of_no_lam`. -/
theorem lrTermDSubKClosedCtxBi_foldApps_of_no_lam {Γ : LCtx} {hd₁ hd₂ : Expr Nat}
    (hhd₁ : ∀ g, ¬ ApproxDIK E (ctxEnvDIK E Γ) hd₁ (.lam g))
    (hhd₂ : ∀ g, ¬ ApproxDIK E (ctxEnvDIK E Γ) hd₂ (.lam g))
    (a₁ a₂ : Expr Nat) (args₁ args₂ : List (Expr Nat)) (T : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ (foldApps hd₁ (a₁ :: args₁)) (foldApps hd₂ (a₂ :: args₂)) T :=
  lrTermDSubKClosedCtxBi_of_probeCpt_eq_bot T
    (fun _ hc h => approxDIK_foldApps_probeCpt_eq_bot_of_no_lam hhd₁ a₁ args₁ hc h)
    (fun _ hc h => approxDIK_foldApps_probeCpt_eq_bot_of_no_lam hhd₂ a₂ args₂ hc h)

/-! ## §10. Proposition-Codomain $\Pi$-Inversion, Canonical $\Pi$-Pruning of `ApproxDIK` (`prunePiCpt`),
$\eta$-Application Equivalence, and Reductions Between `AppCongrSupply` & `LetValCongrSupply` -/

/-! ### §10.1. Proposition-Codomain Inversion for $\Pi$-Types (`eqN_zero_of_imax_zero`,
`isPropTyI_codomain_of_pi`, `isPropTyI_inst0_of_pi`, `lrTermDSubKClosedCtxBi_app_of_isPropTyI_pi`) -/

/-- **Unconditional `imax`-Zero Inversion (`eqN_zero_of_imax_zero`):**
    For **every** pair of universe levels `u, v : Level`, `eqN (.imax u v) .zero` forces
    `eqN v .zero` without any side condition on `u` or `v`. -/
theorem eqN_zero_of_imax_zero {u v : Level} (h : eqN (.imax u v) .zero) : eqN v .zero := by
  intro ρ
  have hρ : eval ρ (.imax u v) = some 0 := h ρ
  simp only [eval] at hρ ⊢
  cases hv : eval ρ v with
  | none =>
      rw [hv] at hρ
      cases hρ
  | some y =>
      cases y with
      | zero => rfl
      | succ k =>
          rw [hv] at hρ
          change (if k + 1 = 0 then some 0 else (eval ρ u).map fun x => max x (k + 1)) = some 0 at hρ
          rw [if_neg (Nat.succ_ne_zero k)] at hρ
          cases hu : eval ρ u with
          | none =>
              rw [hu] at hρ
              cases hρ
          | some x =>
              rw [hu] at hρ
              change some (max x (k + 1)) = some 0 at hρ
              injection hρ with hmax
              omega

/-- Under universe consistency (`hSort`), every $\Pi$-type in `Prop` (`HasTyT E n Γ (.pi A B) (.sort .zero)`)
    has its codomain `B` typed in `Prop` (`HasTyT E n (.assumption A :: Γ) B (.sort .zero)`). -/
def hasTyT_codomain_sort_zero_of_pi_sort_zero
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {A B : Expr Nat} (hpi : HasTyT E n Γ (.pi A B) (.sort .zero)) :
    HasTyT E n (.assumption A :: Γ) B (.sort .zero) :=
  let ⟨_, v, _, hB, hc⟩ := hasTyT_pi_inv hpi rfl
  .conv (.assumption A :: Γ) B (.sort v) (.sort .zero) (.succ v) hB
    (.sorts (.assumption A :: Γ) v .zero (eqN_zero_of_imax_zero (hSort hc)))

/-- Under `hSort`, if `.pi A B` is a proposition (`IsPropTyI E n Γ (.pi A B)`), then its codomain `B`
    is a proposition in `.assumption A :: Γ` (`IsPropTyI E n (.assumption A :: Γ) B`). -/
theorem isPropTyI_codomain_of_pi
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {A B : Expr Nat} (hpi : IsPropTyI E n Γ (.pi A B)) :
    IsPropTyI E n (.assumption A :: Γ) B := by
  rcases hpi with ⟨⟨hpi₀⟩, _⟩
  exact isPropTyI_of_hasTyT_sort_zero hSort (hasTyT_codomain_sort_zero_of_pi_sort_zero hSort hpi₀)

/-- Under `EnvWfT E` and `hSort`, if `IsPropTyI E n Γ (.pi A B)` and `HasTyT E n Γ a A`, then
    `IsPropTyI E n Γ (instantiate0 a B)`. -/
theorem isPropTyI_inst0_of_pi (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {A B a : Expr Nat} (hpi : IsPropTyI E n Γ (.pi A B)) (ha : HasTyT E n Γ a A) :
    IsPropTyI E n Γ (instantiate0 a B) :=
  isPropTyI_subst0_of_sortRow hW hSort ha (isPropTyI_codomain_of_pi hSort hpi)

/-- Whenever `IsPropTyI E n Γ T` holds, `LRTermDSubKClosedCtxBi E n Γ M M' T` holds unconditionally
    for **all** `M, M' : Expr Nat`. -/
theorem lrTermDSubKClosedCtxBi_of_isPropTyI {Γ : LCtx} {T : Expr Nat}
    (hP : IsPropTyI E n Γ T) (M M' : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ M M' T :=
  fun _ _ _ => Or.inl hP

/-- **Unconditional Application Congruence for Propositional $\Pi$-Types
    (`lrTermDSubKClosedCtxBi_app_of_isPropTyI_pi`):**
    Whenever `.pi A B` is a proposition (`IsPropTyI E n Γ (.pi A B)`) and `HasTyT E n Γ a A`,
    `LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g b) (instantiate0 a B)` holds **100%
    unconditionally** for **all** `f, g, b : Expr Nat`! -/
theorem lrTermDSubKClosedCtxBi_app_of_isPropTyI_pi (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {A B a : Expr Nat} (hpi : IsPropTyI E n Γ (.pi A B)) (ha : HasTyT E n Γ a A)
    (f g b : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g b) (instantiate0 a B) :=
  lrTermDSubKClosedCtxBi_of_isPropTyI (isPropTyI_inst0_of_pi hW hSort hpi ha) (.app f a) (.app g b)

/-! ### §10.2. Canonical $\Pi$-Pruning of `CptI` and `ApproxDIK` (`PrunedPiCpt`, `prunePiCpt`,
`approxDIK_prunePiCpt`, `approxDIK_bot_prunePiCpt`, `approxDIK_ctxEnvDIK_prunePiCpt`) -/

mutual
/-- Canonical $\Pi$-pruning projection on `CptI`: replaces every `.pi a f` sub-compact anywhere
    inside `c` by `.pi .bot []`. -/
def prunePiCpt : CptI → CptI
  | .bot => .bot
  | .sort => .sort
  | .pi _ _ => .pi .bot []
  | .lam g => .lam (prunePiSteps g)
  | .spine r args => .spine r (prunePiList args)
termination_by c => sizeOf c

def prunePiSteps : List (List CptI × CptI) → List (List CptI × CptI)
  | [] => []
  | (us, d) :: g => (prunePiList us, prunePiCpt d) :: prunePiSteps g
termination_by g => sizeOf g

def prunePiList : List CptI → List CptI
  | [] => []
  | u :: us => prunePiCpt u :: prunePiList us
termination_by us => sizeOf us
end

@[simp] theorem prunePiCpt_bot : prunePiCpt .bot = .bot := by rw [prunePiCpt]
@[simp] theorem prunePiCpt_sort : prunePiCpt .sort = .sort := by rw [prunePiCpt]
@[simp] theorem prunePiCpt_pi (a : CptI) (f : List (List CptI × CptI)) :
    prunePiCpt (.pi a f) = .pi .bot [] := by rw [prunePiCpt]
@[simp] theorem prunePiCpt_lam (g : List (List CptI × CptI)) :
    prunePiCpt (.lam g) = .lam (prunePiSteps g) := by rw [prunePiCpt]
@[simp] theorem prunePiCpt_spine (r : Nat) (args : List CptI) :
    prunePiCpt (.spine r args) = .spine r (prunePiList args) := by rw [prunePiCpt]
@[simp] theorem prunePiSteps_nil : prunePiSteps [] = [] := by rw [prunePiSteps]
@[simp] theorem prunePiSteps_cons (us : List CptI) (d : CptI) (g : List (List CptI × CptI)) :
    prunePiSteps ((us, d) :: g) = (prunePiList us, prunePiCpt d) :: prunePiSteps g := by
  rw [prunePiSteps]
@[simp] theorem prunePiList_nil : prunePiList [] = [] := by rw [prunePiList]
@[simp] theorem prunePiList_cons (u : CptI) (us : List CptI) :
    prunePiList (u :: us) = prunePiCpt u :: prunePiList us := by rw [prunePiList]

/-- Compacts `c : CptI` in which **every** `.pi a f` sub-compact anywhere inside `c` (including
    inside `.lam` demand/output steps and `.spine` arguments) is `.pi .bot []`. -/
def PrunedPiCpt (c : CptI) : Prop :=
  prunePiCpt c = c

theorem prunedPiCpt_of_probeCpt {c : CptI} (hc : ProbeCpt c) : PrunedPiCpt c := by
  cases hc <;> simp [PrunedPiCpt]

theorem prunePiList_eq_map : ∀ us : List CptI, prunePiList us = us.map prunePiCpt
  | [] => by simp
  | u :: us => by simp [prunePiList_eq_map us]

theorem prunePiSteps_eq_map :
    ∀ g : List (List CptI × CptI),
      prunePiSteps g = g.map (fun s => (prunePiList s.1, prunePiCpt s.2))
  | [] => by simp
  | (us, d) :: g => by simp [prunePiSteps_eq_map g]

mutual
theorem prunedPiCpt_prunePiCpt : ∀ c : CptI, PrunedPiCpt (prunePiCpt c)
  | .bot => by simp [PrunedPiCpt]
  | .sort => by simp [PrunedPiCpt]
  | .pi _ _ => by simp [PrunedPiCpt]
  | .lam g => by simp [PrunedPiCpt, prunedPiCpt_prunePiSteps g]
  | .spine _ args => by simp [PrunedPiCpt, prunedPiCpt_prunePiList args]
termination_by c => sizeOf c

theorem prunedPiCpt_prunePiSteps :
    ∀ g : List (List CptI × CptI), prunePiSteps (prunePiSteps g) = prunePiSteps g
  | [] => by simp
  | (us, d) :: g => by
      have hd : prunePiCpt (prunePiCpt d) = prunePiCpt d := prunedPiCpt_prunePiCpt d
      simp [prunedPiCpt_prunePiList us, hd, prunedPiCpt_prunePiSteps g]
termination_by g => sizeOf g

theorem prunedPiCpt_prunePiList :
    ∀ us : List CptI, prunePiList (prunePiList us) = prunePiList us
  | [] => by simp
  | u :: us => by
      have hu : prunePiCpt (prunePiCpt u) = prunePiCpt u := prunedPiCpt_prunePiCpt u
      simp [hu, prunedPiCpt_prunePiList us]
termination_by us => sizeOf us
end

theorem prunePiCpt_eq_self_of_prunedPiCpt {c : CptI} (hc : PrunedPiCpt c) :
    prunePiCpt c = c :=
  hc

theorem prunePiCpt_eq_self_of_probeCpt {c : CptI} (hc : ProbeCpt c) :
    prunePiCpt c = c :=
  prunedPiCpt_of_probeCpt hc

theorem prunePiList_append :
    ∀ (us₁ us₂ : List CptI), prunePiList (us₁ ++ us₂) = prunePiList us₁ ++ prunePiList us₂
  | [], _ => by simp
  | u :: us₁, us₂ => by simp [prunePiList_append us₁ us₂]

theorem prunePiList_replicate_bot :
    ∀ k : Nat, prunePiList (List.replicate k .bot) = List.replicate k .bot
  | 0 => by simp
  | k + 1 => by simp [List.replicate_succ, prunePiList_replicate_bot k]

theorem prunePiCpt_curryStep :
    ∀ (uss : List (List CptI)) (c : CptI),
      prunePiCpt (curryStep uss c) = curryStep (uss.map prunePiList) (prunePiCpt c)
  | [], c => rfl
  | us :: uss, c => by
      simp [curryStep, prunePiCpt_curryStep uss c]

theorem prunePiList_fieldDemandVectors :
    ∀ us_fields : List (List CptI),
      (fieldDemandVectors us_fields).map prunePiList =
        fieldDemandVectors (us_fields.map prunePiList)
  | [] => rfl
  | us :: uss => by
      simp only [fieldDemandVectors, List.map_append, List.map_map, List.length_map,
        ← prunePiList_fieldDemandVectors uss]
      congr 1
      · rw [prunePiList_eq_map, List.map_map]
        apply List.map_congr_left
        intro u _
        simp [prunePiList_replicate_bot]
      · apply List.map_congr_left
        intro vec _
        simp

theorem prunePiList_ctorDemand (ctorRef nparams : Nat) (us_fields : List (List CptI)) :
    prunePiList (ctorDemand ctorRef nparams us_fields) =
      ctorDemand ctorRef nparams (us_fields.map prunePiList) := by
  simp only [ctorDemand, prunePiList_cons, prunePiCpt_spine]
  congr 1
  · rw [prunePiList_append, prunePiList_replicate_bot, prunePiList_replicate_bot, List.length_map]
  · rw [prunePiList_eq_map, List.map_map, ← prunePiList_fieldDemandVectors us_fields, List.map_map]
    apply List.map_congr_left
    intro vec _
    simp [prunePiList_append, prunePiList_replicate_bot]

/-- Image of a compact set `S : CptI → Prop` under `prunePiCpt`. -/
def prunePiSet (S : CptI → Prop) : CptI → Prop :=
  fun c' => ∃ c, S c ∧ prunePiCpt c = c'

/-- Pointwise image of an environment `ρ : EnvI` under `prunePiSet`. -/
def prunePiEnv (ρ : EnvI) : EnvI :=
  fun i => prunePiSet (ρ i)

theorem prunePiSet_demand (us : List CptI) :
    prunePiSet (demand us) = demand (prunePiList us) := by
  funext c'
  simp [prunePiSet, demand, prunePiList_eq_map]

theorem prunePiEnv_cons (S : CptI → Prop) (ρ : EnvI) :
    prunePiEnv (EnvI.cons S ρ) = EnvI.cons (prunePiSet S) (prunePiEnv ρ) := by
  funext i
  cases i <;> rfl

theorem prunePiEnv_bot : prunePiEnv EnvI.bot = EnvI.bot := by
  funext i c'
  apply propext
  simp only [prunePiEnv, prunePiSet, EnvI.bot]
  exact ⟨by rintro ⟨_, rfl, rfl⟩; simp, fun h => ⟨.bot, rfl, by simp [h]⟩⟩

theorem prunePiEnv_pushArgs :
    ∀ (uss : List (List CptI)) (ρ : EnvI),
      prunePiEnv (EnvI.pushArgs (uss.map demand) ρ) =
        EnvI.pushArgs ((uss.map prunePiList).map demand) (prunePiEnv ρ)
  | [], _ => rfl
  | us :: uss, ρ => by
      simp only [List.map_cons, EnvI.pushArgs]
      rw [prunePiEnv_pushArgs uss (EnvI.cons (demand us) ρ), prunePiEnv_cons, prunePiSet_demand]

/-- **Canonical $\Pi$-Pruning of `ApproxDIK` (`approxDIK_prunePiCpt`):**
    Because no rule of `ApproxDIK` ever eliminates a `CptI.pi a f` compact, every derivation
    `ApproxDIK E ρ e c` yields `ApproxDIK E (prunePiEnv ρ) e (prunePiCpt c)`. -/
theorem approxDIK_prunePiCpt {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ e c) :
    ApproxDIK E (prunePiEnv ρ) e (prunePiCpt c) := by
  induction h with
  | bot ρ e =>
      rw [prunePiCpt_bot]
      exact .bot (prunePiEnv ρ) e
  | bvar hρ => exact .bvar ⟨_, hρ, rfl⟩
  | sort ρ l =>
      rw [prunePiCpt_sort]
      exact .sort (prunePiEnv ρ) l
  | pi _ _ =>
      rw [prunePiCpt_pi]
      exact .pi (.bot _ _) (fun _ hs => (List.not_mem_nil _ hs).elim)
  | @lam ρ A b f _ ih =>
      rw [prunePiCpt_lam]
      refine .lam (fun s' hs' => ?_)
      rw [prunePiSteps_eq_map, List.mem_map] at hs'
      rcases hs' with ⟨s, hs, rfl⟩
      have ihs := ih s hs
      rw [prunePiEnv_cons, prunePiSet_demand] at ihs
      exact ihs
  | @app ρ f a g s _ hs _ ihf iha =>
      rw [prunePiCpt_lam] at ihf
      have hs' : (prunePiList s.1, prunePiCpt s.2) ∈ prunePiSteps g := by
        rw [prunePiSteps_eq_map, List.mem_map]
        exact ⟨s, hs, rfl⟩
      refine .app ihf hs' (fun u' hu' => ?_)
      rw [prunePiList_eq_map, List.mem_map] at hu'
      rcases hu' with ⟨u, hu, rfl⟩
      exact iha u hu
  | const ρ r ls hrigid =>
      rw [prunePiCpt_spine, prunePiList_nil]
      exact .const (prunePiEnv ρ) r ls hrigid
  | delta hdelta _ ih =>
      rw [prunePiEnv_bot] at ih
      exact .delta hdelta ih
  | @recursor ρ w ls us_pre us_fields c hpre hflds _ ih =>
      rw [prunePiCpt_curryStep, List.map_append, List.map_singleton, prunePiList_ctorDemand]
      have hpre' : (us_pre.map prunePiList).length = w.preMajor.length := by
        rw [List.length_map, hpre]
      have hflds' : (us_fields.map prunePiList).length = w.fields.length := by
        rw [List.length_map, hflds]
      rw [prunePiEnv_pushArgs, prunePiEnv_bot, List.map_append] at ih
      exact .recursor ls hpre' hflds' ih
  | @recursorK ρ w ls us_pre u_maj c hk hpre hmaj _ ih =>
      have hmaj_eq : prunePiList u_maj = u_maj := by
        rw [prunePiList_eq_map]
        calc
          u_maj.map prunePiCpt = u_maj.map id :=
            List.map_congr_left (fun u hu => by rw [hmaj u hu]; exact prunePiCpt_bot)
          _ = u_maj := List.map_id u_maj
      have hrep_eq :
          (List.replicate w.fields.length ([] : List CptI)).map prunePiList =
            List.replicate w.fields.length [] := by
        induction w.fields.length with
        | zero => rfl
        | succ k ihk => simp [List.replicate_succ, ihk]
      rw [prunePiCpt_curryStep, List.map_append, List.map_singleton, hmaj_eq]
      have hpre' : (us_pre.map prunePiList).length = w.preMajor.length := by
        rw [List.length_map, hpre]
      rw [prunePiEnv_pushArgs, prunePiEnv_bot, List.map_append, hrep_eq] at ih
      exact .recursorK ls hk hpre' hmaj ih
  | appSpine _ _ ihf iha =>
      rw [prunePiCpt_spine] at ihf
      rw [prunePiCpt_spine, prunePiList_append, prunePiList_cons, prunePiList_nil]
      exact .appSpine ihf iha
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih

/-- At `EnvI.bot`, `ApproxDIK E EnvI.bot e c` implies `ApproxDIK E EnvI.bot e (prunePiCpt c)`. -/
theorem approxDIK_bot_prunePiCpt {E : ResolvedEnv} {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E EnvI.bot e c) :
    ApproxDIK E EnvI.bot e (prunePiCpt c) := by
  have h0 := approxDIK_prunePiCpt h
  rwa [prunePiEnv_bot] at h0

theorem prunePiEnv_ctxEnvDIK_le (E : ResolvedEnv) :
    ∀ (Γ : LCtx), EnvI.le (prunePiEnv (ctxEnvDIK E Γ)) (ctxEnvDIK E Γ)
  | [] => by
      rw [ctxEnvDIK, prunePiEnv_bot]
      exact fun _ _ hc => hc
  | .assumption A :: Γ => by
      rw [ctxEnvDIK, prunePiEnv_cons]
      intro i c' hc'
      cases i with
      | zero =>
          rcases hc' with ⟨c, rfl, rfl⟩
          exact prunePiCpt_bot
      | succ i =>
          exact prunePiEnv_ctxEnvDIK_le E Γ i c' hc'
  | .letBinding A v :: Γ => by
      rw [ctxEnvDIK, prunePiEnv_cons]
      intro i c' hc'
      cases i with
      | zero =>
          rcases hc' with ⟨c, hc, rfl⟩
          exact approxDIK_mono_env (prunePiEnv_ctxEnvDIK_le E Γ) (approxDIK_prunePiCpt hc)
      | succ i =>
          exact prunePiEnv_ctxEnvDIK_le E Γ i c' hc'

/-- **Context-Valuation $\Pi$-Pruning in `ApproxDIK` (`approxDIK_ctxEnvDIK_prunePiCpt`):**
    For **every** context `Γ : LCtx`, expression `e : Expr Nat`, and compact `c : CptI`,
    `ApproxDIK E (ctxEnvDIK E Γ) e c` implies `ApproxDIK E (ctxEnvDIK E Γ) e (prunePiCpt c)`
    (with `PrunedPiCpt (prunePiCpt c)`). -/
theorem approxDIK_ctxEnvDIK_prunePiCpt {E : ResolvedEnv} {Γ : LCtx} {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E (ctxEnvDIK E Γ) e c) :
    ApproxDIK E (ctxEnvDIK E Γ) e (prunePiCpt c) :=
  approxDIK_mono_env (prunePiEnv_ctxEnvDIK_le E Γ) (approxDIK_prunePiCpt h)

/-! ### §10.3. $\eta$-Application Equivalence, Unconditional Same-Argument $\lambda$-Application
Congruence, and Reductions Between `AppCongrSupply` & `LetValCongrSupply` -/

/-- Exact syntactic identity `instantiate0 a (.app (lift 0 1 f) (.bvar 0)) = .app f a`. -/
theorem instantiate0_app_lift0_bvar0 (f a : Expr Nat) :
    instantiate0 a (.app (lift 0 1 f) (.bvar 0)) = .app f a := by
  unfold instantiate0
  simp only [instantiate, ↓reduceIte]
  rw [instantiate_lift_cancel 1 0 0 a (by omega) (by omega) f, lift_zero]

/-- Applying an $\eta$-expanded function `.lam A (.app (lift 0 1 f) (.bvar 0))` to any argument `a`
    steps in **one** `WhStep.beta` step to `.app f a`. -/
theorem whStep_app_eta (E : ResolvedEnv) (A f a : Expr Nat) :
    WhStep E (.app (.lam A (.app (lift 0 1 f) (.bvar 0))) a) (.app f a) :=
  instantiate0_app_lift0_bvar0 f a ▸ WhStep.beta A (.app (lift 0 1 f) (.bvar 0)) a

theorem whRedPiKClosedCtx_app_eta (E : ResolvedEnv) (Γ : LCtx) (A f a : Expr Nat) :
    WhRedPiKClosedCtx E Γ (.app (.lam A (.app (lift 0 1 f) (.bvar 0))) a) (.app f a) :=
  .step (.of_whStep (whStep_app_eta E A f a)) (.refl _)

/-- **Exact `SemEqDIK` Equivalence of Applied $\eta$-Expansion (`semEqDIK_app_eta`):**
    Although `.lam A (.app (lift 0 1 f) (.bvar 0))` and `f` need not be `SemEqDIK`-equal when `f`
    is a neutral/constructor spine, **once applied to any argument `a`**,
    `SemEqDIK E ρ (.app (.lam A (.app (lift 0 1 f) (.bvar 0))) a) (.app f a)` holds unconditionally
    at **every** valuation `ρ : EnvI`! -/
theorem semEqDIK_app_eta (E : ResolvedEnv) (ρ : EnvI) (A f a : Expr Nat) :
    SemEqDIK E ρ (.app (.lam A (.app (lift 0 1 f) (.bvar 0))) a) (.app f a) :=
  instantiate0_app_lift0_bvar0 f a ▸ approxDIK_beta E ρ A (.app (lift 0 1 f) (.bvar 0)) a

/-- **Two-Way Equivalence (`↔`) of Left-Applied $\eta$-Expansion in `LRTermDSubKClosedCtxBi`
    (`lrTermDSubKClosedCtxBi_app_eta_left_iff`):** -/
theorem lrTermDSubKClosedCtxBi_app_eta_left_iff (hW : EnvWfT E) {Γ : LCtx}
    (A f g a b T : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ (.app (.lam A (.app (lift 0 1 f) (.bvar 0))) a) (.app g b) T ↔
      LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g b) T :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff hW
    (whRedPiKClosedCtx_app_eta E Γ A f a) (.refl _)

theorem lrTermDSubKClosedCtxBi_app_eta_right_iff (hW : EnvWfT E) {Γ : LCtx}
    (A f g a b T : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app (.lam A (.app (lift 0 1 g) (.bvar 0))) b) T ↔
      LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g b) T :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff hW
    (.refl _) (whRedPiKClosedCtx_app_eta E Γ A g b)

theorem lrTermDSubKClosedCtxBi_app_eta_both_iff (hW : EnvWfT E) {Γ : LCtx}
    (A₁ A₂ f g a b T : Expr Nat) :
    LRTermDSubKClosedCtxBi E n Γ
      (.app (.lam A₁ (.app (lift 0 1 f) (.bvar 0))) a)
      (.app (.lam A₂ (.app (lift 0 1 g) (.bvar 0))) b) T ↔
      LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g b) T :=
  lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff hW
    (whRedPiKClosedCtx_app_eta E Γ A₁ f a)
    (whRedPiKClosedCtx_app_eta E Γ A₂ g b)

/-- **Unconditional Same-Argument $\lambda$-Application Congruence
    (`lrTermDSubKClosedCtxBi_app_lam_same_arg`):**
    Whenever `WhRedPiKClosedCtx E Γ f (.lam A₁ b₁)` and `WhRedPiKClosedCtx E Γ g (.lam A₂ b₂)`,
    for **every** argument `a : Expr Nat` with `HasTyT E n Γ a A₁`, if `b₁` and `b₂` are related in
    `.letBinding A₁ a :: Γ` (`LRTermDSubKClosedCtxBi E n (.letBinding A₁ a :: Γ) b₁ b₂ B`), then
    `LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g a) (instantiate0 a B)` holds **100%
    unconditionally**! -/
theorem lrTermDSubKClosedCtxBi_app_lam_same_arg (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g A₁ A₂ b₁ b₂ a B : Expr Nat}
    (hf : WhRedPiKClosedCtx E Γ f (.lam A₁ b₁))
    (hg : WhRedPiKClosedCtx E Γ g (.lam A₂ b₂))
    (ha : HasTyT E n Γ a A₁)
    (hb : LRTermDSubKClosedCtxBi E n (.letBinding A₁ a :: Γ) b₁ b₂ B) :
    LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g a) (instantiate0 a B) :=
  (lrTermDSubKClosedCtxBi_app_lam_whRed_iff_subst0 hW hf hg a a (instantiate0 a B)).mpr
    (lrTermDSubKClosedCtxBi_substLet0 hW hSort hΓ ha hb)

/-- **Reduction of Two-Sided $\lambda$-Application Congruence to `letE` Value Congruence
    (`lrTermDSubKClosedCtxBi_app_lam_of_letValCongr`):**
    Whenever `WhRedPiKClosedCtx E Γ f (.lam A₁ b₁)` and `WhRedPiKClosedCtx E Γ g (.lam A₂ b₂)`,
    two-sided application congruence `.app f a ~ .app g b` follows directly from
    `LRTermDSubKClosedCtxBi E n (.letBinding A₁ a :: Γ) b₁ b₂ B` and diagonal-body 0-instantiation
    congruence `LRTermDSubKClosedCtxBi E n Γ (instantiate0 a b₂) (instantiate0 b b₂) (instantiate0 a B)`. -/
theorem lrTermDSubKClosedCtxBi_app_lam_of_letValCongr (hW : EnvWfT E)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {f g A₁ A₂ b₁ b₂ a b B : Expr Nat}
    (hf : WhRedPiKClosedCtx E Γ f (.lam A₁ b₁))
    (hg : WhRedPiKClosedCtx E Γ g (.lam A₂ b₂))
    (ha : HasTyT E n Γ a A₁)
    (hb : LRTermDSubKClosedCtxBi E n (.letBinding A₁ a :: Γ) b₁ b₂ B)
    (hval : LRTermDSubKClosedCtxBi E n Γ (instantiate0 a b₂) (instantiate0 b b₂) (instantiate0 a B)) :
    LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g b) (instantiate0 a B) :=
  (lrTermDSubKClosedCtxBi_app_lam_whRed_iff_subst0 hW hf hg a b (instantiate0 a B)).mpr
    (lrTermDSubKClosedCtxBi_trans hW
      (lrTermDSubKClosedCtxBi_substLet0 hW hSort hΓ ha hb)
      hval)

/-- Standalone Clause 1 (`ConvT.app` congruence) of `AppLetCongrSupplyDSubKClosedCtxBi E n`. -/
def AppCongrSupplyDSubKClosedCtxBi (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {f g a b A B : Expr Nat},
      ConvT E n Γ f g (.pi A B) → ConvT E n Γ a b A →
      LRTermDSubKClosedCtxBi E n Γ f g (.pi A B) →
      LRTermDSubKClosedCtxBi E n Γ a b A →
      LRTermDSubKClosedCtxBi E n Γ (.app f a) (.app g b) (instantiate0 a B)

/-- Standalone Clause 2 (`ConvT.letE` diagonal-body value congruence) of `AppLetCongrSupplyDSubKClosedCtxBi E n`. -/
def LetValCongrSupplyDSubKClosedCtxBi (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A v₁ v₂ b B : Expr Nat},
      HasTyT E n Γ v₁ A → HasTyT E n Γ v₂ A → ConvT E n Γ v₁ v₂ A →
      LRTermDSubKClosedCtxBi E n Γ v₁ v₂ A →
      LRTermDSubKClosedCtxBi E n (.letBinding A v₁ :: Γ) b b B →
      LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) (instantiate0 v₁ B)

/-- **Reduction of `.assumption`-Typed 0-Instantiation Congruence to `AppCongrSupplyDSubKClosedCtxBi`
    (`lrTermDSubKClosedCtxBi_subst0_of_appCongr`):**
    Under `AppCongrSupplyDSubKClosedCtxBi E n`, for any `hcA : ConvT E n Γ A₁ A₂ (.sort u)`,
    `hcb : ConvT E n (.assumption A₁ :: Γ) b₁ b₂ B`, and `hcv : ConvT E n Γ v₁ v₂ A₁` with
    `ih_v : LRTermDSubKClosedCtxBi E n Γ v₁ v₂ A₁`, two-sided 0-instantiation congruence
    `LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b₁) (instantiate0 v₂ b₂) (instantiate0 v₁ B)`
    follows immediately by forming `.app (.lam A₁ b₁) v₁ ~ .app (.lam A₂ b₂) v₂`! -/
theorem lrTermDSubKClosedCtxBi_subst0_of_appCongr (hW : EnvWfT E)
    (hApp : AppCongrSupplyDSubKClosedCtxBi E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ A₂ v₁ v₂ b₁ b₂ B : Expr Nat} {u : Level}
    (hcA : ConvT E n Γ A₁ A₂ (.sort u))
    (hcb : ConvT E n (.assumption A₁ :: Γ) b₁ b₂ B)
    (hcv : ConvT E n Γ v₁ v₂ A₁)
    (ih_v : LRTermDSubKClosedCtxBi E n Γ v₁ v₂ A₁) :
    LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b₁) (instantiate0 v₂ b₂) (instantiate0 v₁ B) :=
  (lrTermDSubKClosedCtxBi_beta_congr_iff_subst0 hW A₁ A₂ b₁ b₂ v₁ v₂ (instantiate0 v₁ B)).mp
    (hApp hΓ (.lam Γ A₁ A₂ b₁ b₂ B u hcA hcb) hcv
      (lrTermDSubKClosedCtxBi_lam Γ A₁ A₂ b₁ b₂ B) ih_v)

/-- Diagonal-body specialization of `lrTermDSubKClosedCtxBi_subst0_of_appCongr`:
    every body `b` typed in `.assumption A :: Γ` (`hb : HasTyT E n (.assumption A :: Γ) b B`)
    automatically satisfies 0-instantiation value congruence `instantiate0 v₁ b ~ instantiate0 v₂ b`
    from `AppCongrSupplyDSubKClosedCtxBi E n` alone! -/
theorem lrTermDSubKClosedCtxBi_subst0_diag_of_appCongr (hW : EnvWfT E)
    (hApp : AppCongrSupplyDSubKClosedCtxBi E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A v₁ v₂ b B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hb : HasTyT E n (.assumption A :: Γ) b B)
    (hcv : ConvT E n Γ v₁ v₂ A)
    (ih_v : LRTermDSubKClosedCtxBi E n Γ v₁ v₂ A) :
    LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) (instantiate0 v₁ B) :=
  lrTermDSubKClosedCtxBi_subst0_of_appCongr hW hApp hΓ
    (.refl Γ A (.sort u) hA) (.refl (.assumption A :: Γ) b B hb) hcv ih_v

/-! ## §11. `PrunedSemEqDIK`: Exact `prunePiSet (denDIK ...)` Characterization, Unconditional
Identification of All $\Pi$-Types and Sorts, and Full Congruence & Substitution Algebra -/

/-! ### §11.1. `PrunedPiCpt` Inversion, Idempotence of `prunePiSet` / `prunePiEnv`, and `PrunedEnvLe` -/

theorem prunedPiCpt_bot : PrunedPiCpt .bot :=
  prunePiCpt_bot

theorem prunedPiCpt_sort : PrunedPiCpt .sort :=
  prunePiCpt_sort

theorem prunedPiCpt_pi_bot_nil : PrunedPiCpt (.pi .bot []) :=
  prunePiCpt_pi .bot []

theorem prunedPiCpt_pi_inv {a : CptI} {f : List (List CptI × CptI)}
    (h : PrunedPiCpt (.pi a f)) :
    a = .bot ∧ f = [] := by
  have h0 : CptI.pi .bot [] = .pi a f := by simpa [PrunedPiCpt] using h
  injection h0 with ha hf
  exact ⟨ha.symm, hf.symm⟩

theorem prunedPiCpt_spine_iff (r : Nat) (args : List CptI) :
    PrunedPiCpt (.spine r args) ↔ prunePiList args = args := by
  simp [PrunedPiCpt]

theorem prunedPiCpt_lam_iff (g : List (List CptI × CptI)) :
    PrunedPiCpt (.lam g) ↔ prunePiSteps g = g := by
  simp [PrunedPiCpt]

theorem prunePiList_append_eq_self :
    ∀ {us₁ us₂ : List CptI},
      prunePiList (us₁ ++ us₂) = us₁ ++ us₂ →
        prunePiList us₁ = us₁ ∧ prunePiList us₂ = us₂
  | [], _, h => ⟨prunePiList_nil, h⟩
  | u :: us₁, us₂, h => by
      simp only [List.cons_append, prunePiList_cons, List.cons.injEq] at h
      have ⟨h₁, h₂⟩ := prunePiList_append_eq_self h.2
      exact ⟨by rw [prunePiList_cons, h.1, h₁], h₂⟩

theorem prunedPiCpt_spine_append_inv {r : Nat} {args : List CptI} {u : CptI}
    (h : PrunedPiCpt (.spine r (args ++ [u]))) :
    PrunedPiCpt (.spine r args) ∧ PrunedPiCpt u := by
  rw [prunedPiCpt_spine_iff] at h ⊢
  have ⟨hargs, hu⟩ := prunePiList_append_eq_self h
  simp only [prunePiList_cons, prunePiList_nil, List.cons.injEq] at hu
  exact ⟨hargs, hu.1⟩

theorem prunePiSet_idem (S : CptI → Prop) :
    prunePiSet (prunePiSet S) = prunePiSet S := by
  funext c'
  apply propext
  constructor
  · rintro ⟨_, ⟨c₀, hc₀, rfl⟩, rfl⟩
    exact (prunedPiCpt_prunePiCpt c₀ : prunePiCpt (prunePiCpt c₀) = prunePiCpt c₀).symm ▸
      ⟨c₀, hc₀, rfl⟩
  · rintro ⟨c₀, hc₀, rfl⟩
    exact ⟨prunePiCpt c₀, ⟨c₀, hc₀, rfl⟩, prunedPiCpt_prunePiCpt c₀⟩

theorem prunePiEnv_idem (ρ : EnvI) :
    prunePiEnv (prunePiEnv ρ) = prunePiEnv ρ := by
  funext i
  exact prunePiSet_idem (ρ i)

/-- Environments `ρ : EnvI` that are closed under `prunePiCpt` (`EnvI.le (prunePiEnv ρ) ρ`). -/
def PrunedEnvLe (ρ : EnvI) : Prop :=
  EnvI.le (prunePiEnv ρ) ρ

theorem prunedEnvLe_bot : PrunedEnvLe EnvI.bot := by
  rw [PrunedEnvLe, prunePiEnv_bot]
  exact fun _ _ hc => hc

theorem prunedEnvLe_prunePiEnv (ρ : EnvI) : PrunedEnvLe (prunePiEnv ρ) := by
  rw [PrunedEnvLe, prunePiEnv_idem]
  exact fun _ _ hc => hc

theorem prunedEnvLe_ctxEnvDIK (E : ResolvedEnv) (Γ : LCtx) :
    PrunedEnvLe (ctxEnvDIK E Γ) :=
  prunePiEnv_ctxEnvDIK_le E Γ

theorem prunedEnvLe_drop {ρ : EnvI} (hρ : PrunedEnvLe ρ) (j : Nat) :
    PrunedEnvLe (EnvI.drop ρ j) :=
  fun i c hc => hρ (i + j) c hc

theorem prunedEnvLe_cons_demand {ρ : EnvI} (hρ : PrunedEnvLe ρ)
    {us : List CptI} (hus : prunePiList us = us) :
    PrunedEnvLe (EnvI.cons (demand us) ρ) := by
  rw [PrunedEnvLe, prunePiEnv_cons, prunePiSet_demand, hus]
  exact EnvI.le_cons hρ (demand us)

theorem prunePiEnv_insert (ρ : EnvI) (k : Nat) (S : CptI → Prop) :
    prunePiEnv (EnvI.insert ρ k S) = EnvI.insert (prunePiEnv ρ) k (prunePiSet S) := by
  funext i
  by_cases h1 : i < k
  · simp [prunePiEnv, EnvI.insert_lt _ h1]
  · by_cases h2 : i = k
    · subst h2
      simp [prunePiEnv, EnvI.insert_self]
    · have h3 : k < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp h1) (Ne.symm h2)
      simp [prunePiEnv, EnvI.insert_gt _ h3]

theorem approxDIK_prunePiCpt_of_le {E : ResolvedEnv} {ρ : EnvI} (hρ : PrunedEnvLe ρ)
    {e : Expr Nat} {c : CptI} (h : ApproxDIK E ρ e c) :
    ApproxDIK E ρ e (prunePiCpt c) :=
  approxDIK_mono_env hρ (approxDIK_prunePiCpt h)

theorem approxDIK_prunePiEnv_iff_of_le {E : ResolvedEnv} {ρ : EnvI} (hρ : PrunedEnvLe ρ)
    {e : Expr Nat} {c : CptI} (hc : PrunedPiCpt c) :
    ApproxDIK E (prunePiEnv ρ) e c ↔ ApproxDIK E ρ e c :=
  ⟨approxDIK_mono_env hρ, fun h => hc ▸ approxDIK_prunePiCpt h⟩

theorem approxDIK_ctxEnvDIK_prunePiEnv_iff (E : ResolvedEnv) (Γ : LCtx)
    (e : Expr Nat) {c : CptI} (hc : PrunedPiCpt c) :
    ApproxDIK E (prunePiEnv (ctxEnvDIK E Γ)) e c ↔ ApproxDIK E (ctxEnvDIK E Γ) e c :=
  approxDIK_prunePiEnv_iff_of_le (prunedEnvLe_ctxEnvDIK E Γ) hc

theorem prunedEnvLe_insert_denDIK {E : ResolvedEnv} {ρ ρ' : EnvI}
    (hρ : PrunedEnvLe ρ) (hρ' : PrunedEnvLe ρ') (k : Nat) (v : Expr Nat) :
    PrunedEnvLe (EnvI.insert ρ k (denDIK E ρ' v)) := by
  rw [PrunedEnvLe, prunePiEnv_insert]
  intro i c hc
  by_cases h1 : i < k
  · rw [EnvI.insert_lt _ h1] at hc ⊢
    exact hρ i c hc
  · by_cases h2 : i = k
    · subst h2
      rw [EnvI.insert_self] at hc ⊢
      rcases hc with ⟨c₀, hc₀, rfl⟩
      exact approxDIK_prunePiCpt_of_le hρ' hc₀
    · have h3 : k < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp h1) (Ne.symm h2)
      rw [EnvI.insert_gt _ h3] at hc ⊢
      exact hρ (i - 1) c hc

theorem prunePiSet_denDIK_eq_of_le {E : ResolvedEnv} {ρ : EnvI} (hρ : PrunedEnvLe ρ)
    (v : Expr Nat) :
    prunePiSet (denDIK E ρ v) = (fun c => PrunedPiCpt c ∧ ApproxDIK E ρ v c) := by
  funext c'
  apply propext
  constructor
  · rintro ⟨c₀, hc₀, rfl⟩
    exact ⟨prunedPiCpt_prunePiCpt c₀, approxDIK_prunePiCpt_of_le hρ hc₀⟩
  · rintro ⟨hc', hv⟩
    exact ⟨c', hv, hc'⟩

/-! ### §11.2. `PrunedSemEqDIK`: Exact `prunePiSet (denDIK ...)` Characterization, Unconditional
Identification of All $\Pi$-Types and Sorts, and Full Congruence & Substitution Algebra -/

/-- Semantic equality in `ApproxDIK` restricted to `PrunedPiCpt` compacts (`prunePiCpt c = c`),
    which includes all `ProbeCpt = {.bot, .sort, .pi .bot []}`. -/
def PrunedSemEqDIK (E : ResolvedEnv) (ρ : EnvI) (a b : Expr Nat) : Prop :=
  ∀ c, PrunedPiCpt c → (ApproxDIK E ρ a c ↔ ApproxDIK E ρ b c)

theorem prunedSemEqDIK_refl (E : ResolvedEnv) (ρ : EnvI) (a : Expr Nat) :
    PrunedSemEqDIK E ρ a a :=
  fun _ _ => Iff.rfl

theorem prunedSemEqDIK_symm {E : ResolvedEnv} {ρ : EnvI} {a b : Expr Nat}
    (h : PrunedSemEqDIK E ρ a b) :
    PrunedSemEqDIK E ρ b a :=
  fun c hc => (h c hc).symm

theorem prunedSemEqDIK_trans {E : ResolvedEnv} {ρ : EnvI} {a b d : Expr Nat}
    (h₁ : PrunedSemEqDIK E ρ a b) (h₂ : PrunedSemEqDIK E ρ b d) :
    PrunedSemEqDIK E ρ a d :=
  fun c hc => (h₁ c hc).trans (h₂ c hc)

theorem prunedSemEqDIK_of_semEqDIK {E : ResolvedEnv} {ρ : EnvI} {a b : Expr Nat}
    (h : SemEqDIK E ρ a b) :
    PrunedSemEqDIK E ρ a b :=
  fun c _ => h c

/-- **Exact Characterization of `.pi A B` on `PrunedPiCpt` Compacts (`approxDIK_pi_prunedPiCpt_iff`):**
    At **every** `PrunedPiCpt c`, `ApproxDIK E ρ (.pi A B) c` is equivalent to
    `c = .bot ∨ c = .pi .bot []`, **completely independent of `A` and `B`**! -/
theorem approxDIK_pi_prunedPiCpt_iff (E : ResolvedEnv) (ρ : EnvI) (A B : Expr Nat)
    {c : CptI} (hc : PrunedPiCpt c) :
    ApproxDIK E ρ (.pi A B) c ↔ (c = .bot ∨ c = .pi .bot []) := by
  constructor
  · intro h
    rcases approxDIK_pi_inv h with rfl | ⟨a, f, rfl, _, _⟩
    · exact Or.inl rfl
    · obtain ⟨rfl, rfl⟩ := prunedPiCpt_pi_inv hc
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact .bot ρ (.pi A B)
    · exact approxDIK_pi_bot_nil E ρ A B

theorem approxDIK_sort_prunedPiCpt_iff (E : ResolvedEnv) (ρ : EnvI) (l : Level) (c : CptI) :
    ApproxDIK E ρ (.sort l) c ↔ (c = .bot ∨ c = .sort) :=
  ⟨approxDIK_sort_inv, fun h => h.elim (fun h0 => h0 ▸ .bot ρ (.sort l)) (fun h0 => h0 ▸ .sort ρ l)⟩

/-- **Unconditional Identification of ALL $\Pi$-Types in `PrunedSemEqDIK` (`prunedSemEqDIK_pi`):**
    For **every** `E : ResolvedEnv`, **every** `ρ : EnvI`, and **all** `A₁, B₁, A₂, B₂ : Expr Nat`
    (with **zero** hypotheses on `A₁, B₁, A₂, B₂`!), `.pi A₁ B₁` and `.pi A₂ B₂` are
    `PrunedSemEqDIK`-equal! -/
theorem prunedSemEqDIK_pi (E : ResolvedEnv) (ρ : EnvI) (A₁ B₁ A₂ B₂ : Expr Nat) :
    PrunedSemEqDIK E ρ (.pi A₁ B₁) (.pi A₂ B₂) :=
  fun _ hc =>
    (approxDIK_pi_prunedPiCpt_iff E ρ A₁ B₁ hc).trans
      (approxDIK_pi_prunedPiCpt_iff E ρ A₂ B₂ hc).symm

/-- **Unconditional Identification of ALL Sorts in `PrunedSemEqDIK` (`prunedSemEqDIK_sorts`):** -/
theorem prunedSemEqDIK_sorts (E : ResolvedEnv) (ρ : EnvI) (l₁ l₂ : Level) :
    PrunedSemEqDIK E ρ (.sort l₁) (.sort l₂) :=
  fun c _ =>
    (approxDIK_sort_prunedPiCpt_iff E ρ l₁ c).trans
      (approxDIK_sort_prunedPiCpt_iff E ρ l₂ c).symm

/-- Positive repair of §12.2's `closedIrrPi_conv` counterexample in `PrunedSemEqDIK`:
    although `¬ SemEqDI E EnvI.bot closedIrrPiL closedIrrPiR` (`not_semEqDI_closedIrrPi`),
    `PrunedSemEqDIK E ρ closedIrrPiL closedIrrPiR` holds unconditionally at **every** `E, ρ`! -/
theorem prunedSemEqDIK_closedIrrPi (E : ResolvedEnv) (ρ : EnvI) :
    PrunedSemEqDIK E ρ closedIrrPiL closedIrrPiR :=
  prunedSemEqDIK_pi E ρ _ _ _ _

/-- **Exact Equivalence Between `prunePiSet (denDIK E ρ v₁) = prunePiSet (denDIK E ρ v₂)` and
    `PrunedSemEqDIK E ρ v₁ v₂` (`prunePiSet_denDIK_eq_iff_prunedSemEqDIK`):** -/
theorem prunePiSet_denDIK_eq_iff_prunedSemEqDIK {E : ResolvedEnv} {ρ : EnvI}
    (hρ : PrunedEnvLe ρ) (v₁ v₂ : Expr Nat) :
    prunePiSet (denDIK E ρ v₁) = prunePiSet (denDIK E ρ v₂) ↔
      PrunedSemEqDIK E ρ v₁ v₂ := by
  rw [prunePiSet_denDIK_eq_of_le hρ v₁, prunePiSet_denDIK_eq_of_le hρ v₂]
  constructor
  · intro heq c hc
    have hc_eq := congrFun heq c
    simp only [hc, true_and] at hc_eq
    exact iff_of_eq hc_eq
  · intro h
    funext c
    apply propext
    exact ⟨fun ⟨hc, h₁⟩ => ⟨hc, (h c hc).mp h₁⟩, fun ⟨hc, h₂⟩ => ⟨hc, (h c hc).mpr h₂⟩⟩

/-- **Substitution Congruence of `PrunedSemEqDIK` (`prunedSemEqDIK_instantiate_of_prunedSemEqDIK`):**
    Whenever `PrunedEnvLe ρ` and `PrunedSemEqDIK E (EnvI.drop ρ j) v₁ v₂`, for **every** expression
    `e : Expr Nat`, `instantiate j (lift 0 j v₁) e` and `instantiate j (lift 0 j v₂) e` are
    `PrunedSemEqDIK`-equal! -/
theorem prunedSemEqDIK_instantiate_of_prunedSemEqDIK {E : ResolvedEnv} {ρ : EnvI}
    (hρ : PrunedEnvLe ρ) {j : Nat} {v₁ v₂ : Expr Nat}
    (hv : PrunedSemEqDIK E (EnvI.drop ρ j) v₁ v₂) (e : Expr Nat) :
    PrunedSemEqDIK E ρ (instantiate j (lift 0 j v₁) e) (instantiate j (lift 0 j v₂) e) := by
  intro c hc
  have hset : prunePiSet (denDIK E (EnvI.drop ρ j) v₁) = prunePiSet (denDIK E (EnvI.drop ρ j) v₂) :=
    (prunePiSet_denDIK_eq_iff_prunedSemEqDIK (prunedEnvLe_drop hρ j) v₁ v₂).mpr hv
  have henv :
      prunePiEnv (EnvI.insert ρ j (denDIK E (EnvI.drop ρ j) v₁)) =
        prunePiEnv (EnvI.insert ρ j (denDIK E (EnvI.drop ρ j) v₂)) := by
    rw [prunePiEnv_insert, prunePiEnv_insert, hset]
  rw [approxDIK_subst_iff, approxDIK_subst_iff,
    ← approxDIK_prunePiEnv_iff_of_le (prunedEnvLe_insert_denDIK hρ (prunedEnvLe_drop hρ j) j v₁) hc,
    henv,
    approxDIK_prunePiEnv_iff_of_le (prunedEnvLe_insert_denDIK hρ (prunedEnvLe_drop hρ j) j v₂) hc]

/-- **0-Instantiation Congruence of `PrunedSemEqDIK` (`prunedSemEqDIK_instantiate0_of_prunedSemEqDIK`):** -/
theorem prunedSemEqDIK_instantiate0_of_prunedSemEqDIK {E : ResolvedEnv} {ρ : EnvI}
    (hρ : PrunedEnvLe ρ) {v₁ v₂ : Expr Nat}
    (hv : PrunedSemEqDIK E ρ v₁ v₂) (e : Expr Nat) :
    PrunedSemEqDIK E ρ (instantiate0 v₁ e) (instantiate0 v₂ e) := by
  simpa only [instantiate0, lift_zero] using
    prunedSemEqDIK_instantiate_of_prunedSemEqDIK hρ (j := 0) (by simpa [EnvI.drop_zero] using hv) e

/-- **Context-Valuation 0-Instantiation Congruence of `PrunedSemEqDIK`
    (`approxDIK_ctxEnvDIK_instantiate0_iff_of_prunedSemEqDIK`):**
    Whenever `PrunedSemEqDIK E (ctxEnvDIK E Γ) v₁ v₂` (which holds for **all** `SemEqDIK`-equal
    `v₁, v₂` AND for **every** pair of $\Pi$-types `.pi A₁ B₁, .pi A₂ B₂`), for **every** body
    `e : Expr Nat` and **every** `PrunedPiCpt c` (including all `ProbeCpt c`!),
    `ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₁ e) c ↔ ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₂ e) c`! -/
theorem approxDIK_ctxEnvDIK_instantiate0_iff_of_prunedSemEqDIK {E : ResolvedEnv} {Γ : LCtx}
    {v₁ v₂ : Expr Nat} (hv : PrunedSemEqDIK E (ctxEnvDIK E Γ) v₁ v₂)
    (e : Expr Nat) {c : CptI} (hc : PrunedPiCpt c) :
    ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₁ e) c ↔
      ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₂ e) c :=
  prunedSemEqDIK_instantiate0_of_prunedSemEqDIK (prunedEnvLe_ctxEnvDIK E Γ) hv e c hc

/-- **Application Congruence of `PrunedSemEqDIK` (`prunedSemEqDIK_app`):**
    Under `PrunedEnvLe ρ`, `PrunedSemEqDIK E ρ` is a congruence under `.app`! -/
theorem prunedSemEqDIK_app {E : ResolvedEnv} {ρ : EnvI} (hρ : PrunedEnvLe ρ)
    {f₁ f₂ a₁ a₂ : Expr Nat}
    (hf : PrunedSemEqDIK E ρ f₁ f₂) (ha : PrunedSemEqDIK E ρ a₁ a₂) :
    PrunedSemEqDIK E ρ (.app f₁ a₁) (.app f₂ a₂) := by
  have dir : ∀ {f₁ f₂ a₁ a₂ : Expr Nat},
      PrunedSemEqDIK E ρ f₁ f₂ → PrunedSemEqDIK E ρ a₁ a₂ →
      ∀ c, PrunedPiCpt c → ApproxDIK E ρ (.app f₁ a₁) c → ApproxDIK E ρ (.app f₂ a₂) c := by
    intro f₁ f₂ a₁ a₂ hf' ha' c hc h
    rcases approxDIK_app_inv h with rfl | ⟨g, s, rfl, hfg, hs, hargs⟩ | ⟨r, args, u, rfl, hsp, hu⟩
    · exact .bot ρ (.app f₂ a₂)
    · have hfg_p : ApproxDIK E ρ f₁ (.lam (prunePiSteps g)) := by
        simpa only [prunePiCpt_lam] using approxDIK_prunePiCpt_of_le hρ hfg
      have hlam_p : PrunedPiCpt (.lam (prunePiSteps g)) := by
        simpa only [prunePiCpt_lam] using prunedPiCpt_prunePiCpt (.lam g)
      have hfg₂ : ApproxDIK E ρ f₂ (.lam (prunePiSteps g)) :=
        (hf' (.lam (prunePiSteps g)) hlam_p).mp hfg_p
      have hs' : (prunePiList s.1, s.2) ∈ prunePiSteps g := by
        have hs0 : (prunePiList s.1, prunePiCpt s.2) ∈ prunePiSteps g := by
          rw [prunePiSteps_eq_map, List.mem_map]
          exact ⟨s, hs, rfl⟩
        rwa [hc] at hs0
      refine @ApproxDIK.app E ρ f₂ a₂ (prunePiSteps g) (prunePiList s.1, s.2) hfg₂ hs' (fun u' hu' => ?_)
      rw [prunePiList_eq_map, List.mem_map] at hu'
      rcases hu' with ⟨u₀, hu₀, rfl⟩
      exact (ha' (prunePiCpt u₀) (prunedPiCpt_prunePiCpt u₀)).mp
        (approxDIK_prunePiCpt_of_le hρ (hargs u₀ hu₀))
    · obtain ⟨hsp_p, hu_p⟩ := prunedPiCpt_spine_append_inv hc
      exact .appSpine ((hf' (.spine r args) hsp_p).mp hsp) ((ha' u hu_p).mp hu)
  exact fun c hc => ⟨dir hf ha c hc, dir (prunedSemEqDIK_symm hf) (prunedSemEqDIK_symm ha) c hc⟩

theorem prunedSemEqDIK_ctxEnvDIK_app {E : ResolvedEnv} {Γ : LCtx}
    {f₁ f₂ a₁ a₂ : Expr Nat}
    (hf : PrunedSemEqDIK E (ctxEnvDIK E Γ) f₁ f₂)
    (ha : PrunedSemEqDIK E (ctxEnvDIK E Γ) a₁ a₂) :
    PrunedSemEqDIK E (ctxEnvDIK E Γ) (.app f₁ a₁) (.app f₂ a₂) :=
  prunedSemEqDIK_app (prunedEnvLe_ctxEnvDIK E Γ) hf ha

/-- **$\lambda$-Abstraction Congruence of `PrunedSemEqDIK` (`prunedSemEqDIK_lam`):** -/
theorem prunedSemEqDIK_lam {E : ResolvedEnv} {ρ : EnvI}
    (A₁ A₂ : Expr Nat) {b₁ b₂ : Expr Nat}
    (hb : ∀ us : List CptI, prunePiList us = us →
      PrunedSemEqDIK E (EnvI.cons (demand us) ρ) b₁ b₂) :
    PrunedSemEqDIK E ρ (.lam A₁ b₁) (.lam A₂ b₂) := by
  have dir : ∀ (A₁ A₂ : Expr Nat) {b₁ b₂ : Expr Nat},
      (∀ us : List CptI, prunePiList us = us →
        PrunedSemEqDIK E (EnvI.cons (demand us) ρ) b₁ b₂) →
      ∀ c, PrunedPiCpt c → ApproxDIK E ρ (.lam A₁ b₁) c → ApproxDIK E ρ (.lam A₂ b₂) c := by
    intro A₁ A₂ b₁ b₂ hb' c hc h
    rcases approxDIK_lam_inv h with rfl | ⟨g, rfl, hg⟩
    · exact .bot ρ (.lam A₂ b₂)
    · have hg_eq : prunePiSteps g = g := (prunedPiCpt_lam_iff g).mp hc
      refine .lam (fun s hs => ?_)
      have hs_in : s ∈ prunePiSteps g := by rwa [hg_eq]
      rw [prunePiSteps_eq_map, List.mem_map] at hs_in
      rcases hs_in with ⟨s₀, _, hs_eq⟩
      have hus : prunePiList s.1 = s.1 := by
        have h1 : s.1 = prunePiList s₀.1 := ( Prod.ext_iff.mp hs_eq ).1.symm
        rw [h1, prunedPiCpt_prunePiList]
      have hd : PrunedPiCpt s.2 := by
        have h2 : s.2 = prunePiCpt s₀.2 := ( Prod.ext_iff.mp hs_eq ).2.symm
        rw [h2]
        exact prunedPiCpt_prunePiCpt s₀.2
      exact (hb' s.1 hus s.2 hd).mp (hg s hs)
  exact fun c hc => ⟨dir A₁ A₂ hb c hc, dir A₂ A₁ (fun us hus => prunedSemEqDIK_symm (hb us hus)) c hc⟩

/-! ### §11.3. Consequences for `LRTermDSubKClosedCtxBi` 0-Instantiation and $\Pi$-Argument Congruence -/

/-- **0-Instantiation Congruence in `LRTermDSubKClosedCtxBi` for `PrunedSemEqDIK`-Equal Arguments
    (`lrTermDSubKClosedCtxBi_subst0_of_prunedSemEqDIK_botProbe`):**
    Whenever `PrunedSemEqDIK E (ctxEnvDIK E Γ) v₁ v₂` (which holds for all `SemEqDIK`-equal `v₁, v₂`
    AND for **all** $\Pi$-types `.pi A₁ B₁, .pi A₂ B₂` and sorts `.sort l₁, .sort l₂`) and
    `instantiate0 v₁ b` has `⊥`-only `ProbeCpt` approximations,
    `LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) (instantiate0 v₁ B)`
    holds **unconditionally**! -/
theorem lrTermDSubKClosedCtxBi_subst0_of_prunedSemEqDIK_botProbe
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {v₁ v₂ b B : Expr Nat}
    (hv : PrunedSemEqDIK E (ctxEnvDIK E Γ) v₁ v₂)
    (hbot : ∀ c, ProbeCpt c → ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₁ b) c → c = .bot) :
    LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) (instantiate0 v₁ B) := by
  refine lrTermDSubKClosedCtxBi_of_probeCpt_eq_bot (instantiate0 v₁ B) hbot (fun c hc h₂ => ?_)
  exact hbot c hc
    ((approxDIK_ctxEnvDIK_instantiate0_iff_of_prunedSemEqDIK hv b (prunedPiCpt_of_probeCpt hc)).mpr h₂)

/-- **Unconditional 0-Instantiation Congruence for ANY $\Pi$-Type Arguments on `⊥`-Probed Bodies
    (`lrTermDSubKClosedCtxBi_subst0_pi_arg_of_botProbe`):**
    For **every** pair of $\Pi$-types `.pi A₁ B₁` and `.pi A₂ B₂` (including `closedIrrPiL` and
    `closedIrrPiR` where `ConvT.irr` or `ConvT.eta` occurs inside `Aᵢ, Bᵢ`!) and **every** body `b`
    whose 0-instantiation has `⊥`-only `ProbeCpt` approximations,
    `LRTermDSubKClosedCtxBi E n Γ (instantiate0 (.pi A₁ B₁) b) (instantiate0 (.pi A₂ B₂) b) (instantiate0 (.pi A₁ B₁) B)`
    holds **100% unconditionally**! -/
theorem lrTermDSubKClosedCtxBi_subst0_pi_arg_of_botProbe
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (A₁ B₁ A₂ B₂ : Expr Nat) {b B : Expr Nat}
    (hbot : ∀ c, ProbeCpt c → ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 (.pi A₁ B₁) b) c → c = .bot) :
    LRTermDSubKClosedCtxBi E n Γ
      (instantiate0 (.pi A₁ B₁) b) (instantiate0 (.pi A₂ B₂) b) (instantiate0 (.pi A₁ B₁) B) :=
  lrTermDSubKClosedCtxBi_subst0_of_prunedSemEqDIK_botProbe
    (prunedSemEqDIK_pi E (ctxEnvDIK E Γ) A₁ B₁ A₂ B₂) hbot

/-! ## §12. `PrunedSemEqDIK` Closure Under `letE` / `WhRedPiKClosedCtx`, Pure Syntactic 2-Depth
Binder-Swap Codomain Congruence (`convT_inst1_sortCongrLet`), and Two-Endpoint 0-Instantiation
Congruence Across Sort- and $\Pi$-Probed Bodies -/

/-! ### §12.1. `PrunedSemEqDIK` Closure Under `letBinding` Contexts, `.letE`, `WhStepPiKClosedCtx`,
`WhRedPiKClosedCtx`, and Invariance of the `iotaKClosedCtx` Guard -/

/-- **Exact Characterization of `prunePiEnv` Equality on `.letBinding` Context Extensions
    (`prunePiEnv_ctxEnvDIK_letBinding_eq_iff`):**
    Two `letBinding` extensions of `Γ` have identical `prunePiEnv` valuations if and only if
    their bound values `v₁, v₂` are `PrunedSemEqDIK`-equal in `ctxEnvDIK E Γ` (completely
    independent of the type annotations `A₁, A₂`)! -/
theorem prunePiEnv_ctxEnvDIK_letBinding_eq_iff (E : ResolvedEnv) (Γ : LCtx)
    (A₁ A₂ v₁ v₂ : Expr Nat) :
    prunePiEnv (ctxEnvDIK E (.letBinding A₁ v₁ :: Γ)) =
      prunePiEnv (ctxEnvDIK E (.letBinding A₂ v₂ :: Γ)) ↔
      PrunedSemEqDIK E (ctxEnvDIK E Γ) v₁ v₂ := by
  simp only [ctxEnvDIK, prunePiEnv_cons]
  rw [← prunePiSet_denDIK_eq_iff_prunedSemEqDIK (prunedEnvLe_ctxEnvDIK E Γ) v₁ v₂]
  constructor
  · intro h
    exact congrFun h 0
  · intro h
    funext i
    cases i with
    | zero => exact h
    | succ i => rfl

/-- **Context-Valuation Equivalence Under `PrunedSemEqDIK`-Equal `letBinding` Values
    (`approxDIK_ctxEnvDIK_letBinding_iff_of_prunedSemEqDIK`):** -/
theorem approxDIK_ctxEnvDIK_letBinding_iff_of_prunedSemEqDIK {E : ResolvedEnv} {Γ : LCtx}
    (A₁ A₂ : Expr Nat) {v₁ v₂ : Expr Nat}
    (hv : PrunedSemEqDIK E (ctxEnvDIK E Γ) v₁ v₂)
    (e : Expr Nat) {c : CptI} (hc : PrunedPiCpt c) :
    ApproxDIK E (ctxEnvDIK E (.letBinding A₁ v₁ :: Γ)) e c ↔
      ApproxDIK E (ctxEnvDIK E (.letBinding A₂ v₂ :: Γ)) e c := by
  rw [← approxDIK_ctxEnvDIK_prunePiEnv_iff E (.letBinding A₁ v₁ :: Γ) e hc,
    (prunePiEnv_ctxEnvDIK_letBinding_eq_iff E Γ A₁ A₂ v₁ v₂).mpr hv,
    approxDIK_ctxEnvDIK_prunePiEnv_iff E (.letBinding A₂ v₂ :: Γ) e hc]

/-- **`letE` Congruence of `PrunedSemEqDIK` (`prunedSemEqDIK_letE`):**
    Under `PrunedEnvLe ρ`, `PrunedSemEqDIK` is a congruence under `.letE` (requiring body
    equivalence only in the single left environment `EnvI.cons (denDIK E ρ v₁) ρ`)! -/
theorem prunedSemEqDIK_letE {E : ResolvedEnv} {ρ : EnvI} (hρ : PrunedEnvLe ρ)
    (A₁ A₂ : Expr Nat) {v₁ v₂ b₁ b₂ : Expr Nat}
    (hv : PrunedSemEqDIK E ρ v₁ v₂)
    (hb : PrunedSemEqDIK E (EnvI.cons (denDIK E ρ v₁) ρ) b₁ b₂) :
    PrunedSemEqDIK E ρ (.letE A₁ v₁ b₁) (.letE A₂ v₂ b₂) := by
  have hzeta₁ : PrunedSemEqDIK E ρ (.letE A₁ v₁ b₁) (instantiate0 v₁ b₁) :=
    prunedSemEqDIK_of_semEqDIK (approxDIK_zeta E ρ A₁ v₁ b₁)
  have hzeta₂ : PrunedSemEqDIK E ρ (instantiate0 v₂ b₂) (.letE A₂ v₂ b₂) :=
    prunedSemEqDIK_symm (prunedSemEqDIK_of_semEqDIK (approxDIK_zeta E ρ A₂ v₂ b₂))
  have hb_inst : PrunedSemEqDIK E ρ (instantiate0 v₁ b₁) (instantiate0 v₁ b₂) := by
    intro c hc
    have h₁ := approxDIK_subst_iff E ρ 0 v₁ b₁ c
    have h₂ := approxDIK_subst_iff E ρ 0 v₁ b₂ c
    simp only [lift_zero, EnvI.drop_zero, EnvI.insert_zero] at h₁ h₂
    exact h₁.trans ((hb c hc).trans h₂.symm)
  have hv_inst : PrunedSemEqDIK E ρ (instantiate0 v₁ b₂) (instantiate0 v₂ b₂) :=
    prunedSemEqDIK_instantiate0_of_prunedSemEqDIK hρ hv b₂
  exact prunedSemEqDIK_trans hzeta₁ (prunedSemEqDIK_trans hb_inst (prunedSemEqDIK_trans hv_inst hzeta₂))

theorem prunedSemEqDIK_ctxEnvDIK_letE {E : ResolvedEnv} {Γ : LCtx}
    (A₁ A₂ : Expr Nat) {v₁ v₂ b₁ b₂ : Expr Nat}
    (hv : PrunedSemEqDIK E (ctxEnvDIK E Γ) v₁ v₂)
    (hb : PrunedSemEqDIK E (ctxEnvDIK E (.letBinding A₁ v₁ :: Γ)) b₁ b₂) :
    PrunedSemEqDIK E (ctxEnvDIK E Γ) (.letE A₁ v₁ b₁) (.letE A₂ v₂ b₂) :=
  prunedSemEqDIK_letE (prunedEnvLe_ctxEnvDIK E Γ) A₁ A₂ hv hb

theorem prunedSemEqDIK_ctxEnvDIK_whStepPiKClosedCtx (hW : EnvWfT E) {Γ : LCtx}
    {a b : Expr Nat} (hs : WhStepPiKClosedCtx E Γ a b) :
    PrunedSemEqDIK E (ctxEnvDIK E Γ) a b :=
  prunedSemEqDIK_of_semEqDIK (semEqDIK_ctxEnvDIK_whStepPiKClosedCtx hW hs)

theorem prunedSemEqDIK_ctxEnvDIK_whRedPiKClosedCtx (hW : EnvWfT E) {Γ : LCtx}
    {a b : Expr Nat} (hred : WhRedPiKClosedCtx E Γ a b) :
    PrunedSemEqDIK E (ctxEnvDIK E Γ) a b :=
  prunedSemEqDIK_of_semEqDIK (semEqDIK_ctxEnvDIK_whRedPiKClosedCtx hW hred)

/-- **Invariance of the `WhStepPiKClosedCtx.iotaKClosedCtx` Guard Under `PrunedSemEqDIK`
    (`iotaKClosedCtx_guard_iff_of_prunedSemEqDIK`):**
    Because `approxDIK_ctxEnvDIK_prunePiCpt` prunes any `.spine r args` in `ApproxDIK E (ctxEnvDIK E Γ)`
    to the `PrunedPiCpt` compact `.spine r (prunePiList args)`, the non-constructor-headedness guard
    `∀ args, ¬ ApproxDIK E (ctxEnvDIK E Γ) x (.spine r args)` is completely invariant under
    `PrunedSemEqDIK E (ctxEnvDIK E Γ)`! -/
theorem iotaKClosedCtx_guard_iff_of_prunedSemEqDIK {E : ResolvedEnv} {Γ : LCtx}
    {x₁ x₂ : Expr Nat} (hx : PrunedSemEqDIK E (ctxEnvDIK E Γ) x₁ x₂) (r : Nat) :
    (∀ args, ¬ ApproxDIK E (ctxEnvDIK E Γ) x₁ (.spine r args)) ↔
      (∀ args, ¬ ApproxDIK E (ctxEnvDIK E Γ) x₂ (.spine r args)) := by
  have dir : ∀ {y₁ y₂ : Expr Nat},
      PrunedSemEqDIK E (ctxEnvDIK E Γ) y₁ y₂ →
      (∀ args, ¬ ApproxDIK E (ctxEnvDIK E Γ) y₁ (.spine r args)) →
      (∀ args, ¬ ApproxDIK E (ctxEnvDIK E Γ) y₂ (.spine r args)) := by
    intro y₁ y₂ hy hguard args h₂
    have h₂_p : ApproxDIK E (ctxEnvDIK E Γ) y₂ (.spine r (prunePiList args)) := by
      simpa only [prunePiCpt_spine] using approxDIK_ctxEnvDIK_prunePiCpt h₂
    have hc_p : PrunedPiCpt (.spine r (prunePiList args)) := by
      simpa only [prunePiCpt_spine] using prunedPiCpt_prunePiCpt (.spine r args)
    exact hguard (prunePiList args) ((hy (.spine r (prunePiList args)) hc_p).mpr h₂_p)
  exact ⟨dir hx, dir (prunedSemEqDIK_symm hx)⟩

/-! ### §12.2. Pure Syntactic 2-Depth Binder Swap & Codomain Instantiation Congruence
(`convT_let_self_inst0_sort`, `convT_inst1_sortCongrLet`, `convT_inst1_sortCongr`,
`convT_inst0_letCongr`, `convT_inst0_assumpCongr`) -/

/-- Instantiating slot `j` by `.bvar j` inside a `lift (j+1) 1` gap is the identity. -/
theorem instantiate_bvar_lift_gap_at (j : Nat) (e : Expr Nat) :
    instantiate j (.bvar j) (lift (j + 1) 1 e) = e := by
  induction e generalizing j with
  | bvar i =>
      simp only [lift]
      split
      · simp only [instantiate]
        rw [if_neg (by omega : ¬ i + 1 = j), if_pos (by omega : j < i + 1)]
        exact congrArg Expr.bvar (Nat.add_sub_cancel i 1)
      · simp only [instantiate]
        by_cases h2 : i = j
        · subst h2; rw [if_pos rfl]
        · rw [if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ j < i)]
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app f x ihf ihx => simp only [lift, instantiate, ihf, ihx]
  | lam a b iha ihb =>
      simp only [lift, instantiate, iha j]
      congr 1
      rw [if_pos (Nat.zero_le j)]
      exact ihb (j + 1)
  | pi a b iha ihb =>
      simp only [lift, instantiate, iha j]
      congr 1
      rw [if_pos (Nat.zero_le j)]
      exact ihb (j + 1)
  | letE a v b iha ihv ihb =>
      simp only [lift, instantiate, iha j, ihv j]
      congr 1
      rw [if_pos (Nat.zero_le j)]
      exact ihb (j + 1)

theorem instantiate0_bvar0_lift1 (e : Expr Nat) :
    instantiate0 (.bvar 0) (lift 1 1 e) = e :=
  instantiate_bvar_lift_gap_at 0 e

/-- **Exact 2-Depth Binder-Swap Instantiation Identity
    (`instantiate0_lift0_instantiate0_bvar1_lift2`):**
    For **every** `v, e : Expr Nat`, swapping the top two de Bruijn binders via
    `instantiate0 (.bvar 1) (lift 2 1 e)` and then 0-instantiating by `lift 0 1 v`
    is definitionally equal to the depth-1 instantiation `instantiate 1 (lift 0 1 v) e`! -/
theorem instantiate0_lift0_instantiate0_bvar1_lift2 (v e : Expr Nat) :
    instantiate0 (lift 0 1 v) (instantiate0 (.bvar 1) (lift 2 1 e)) =
      instantiate 1 (lift 0 1 v) e := by
  calc instantiate0 (lift 0 1 v) (instantiate0 (.bvar 1) (lift 2 1 e))
    _ = instantiate 0 (instantiate 0 (lift 0 1 v) (.bvar 1))
          (instantiate 1 (lift 0 1 (lift 0 1 v)) (lift 2 1 e)) :=
        instantiate_instantiate 0 0 (.bvar 1) (lift 0 1 v) (Nat.le_refl 0) (lift 2 1 e)
    _ = instantiate0 (.bvar 0) (instantiate 1 (lift 1 1 (lift 0 1 v)) (lift 2 1 e)) := by
        rw [show instantiate 0 (lift 0 1 v) (.bvar 1) = .bvar 0 from rfl,
            lift_lift_permute 1 1 0 0 (Nat.le_refl 0) v]
        rfl
    _ = instantiate0 (.bvar 0) (lift 1 1 (instantiate 1 (lift 0 1 v) e)) := by
        rw [← lift_instantiate_low 1 1 1 (lift 0 1 v) (Nat.le_refl 1) e]
    _ = instantiate 1 (lift 0 1 v) e :=
        instantiate0_bvar0_lift1 (instantiate 1 (lift 0 1 v) e)

/-- **Self-Instantiation Conversion Under a `letBinding` (`convT_let_self_inst0_sort`):**
    In `.letBinding A v :: Γ`, any sort-typed expression `D : .sort w` is convertible via
    `ConvT.zetaLocal` (`bvar 0 ~ lift 0 1 v`) and `convT_inst0_sortCongrLet` on `lift 1 1 D`
    to its own lifted 0-instantiation `lift 0 1 (instantiate0 v D)`! -/
def convT_let_self_inst0_sort {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {A v D : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv : HasTyT E n Γ v A)
    (hD : HasTyT E n (.letBinding A v :: Γ) D (.sort w)) :
    ConvT E n (.letBinding A v :: Γ) D (lift 0 1 (instantiate0 v D)) (.sort w) := by
  let d : LocalDecl := .letBinding A v
  let Γ' : LCtx := d :: Γ
  have hA' : HasTyT E n Γ' (lift 0 1 A) (.sort u) :=
    hasTyTWeaken d hcl (c := 0) hA
  have hv' : HasTyT E n Γ' (lift 0 1 v) (lift 0 1 A) :=
    hasTyTWeaken d hcl (c := 0) hv
  have hb0 : HasTyT E n Γ' (.bvar 0) (lift 0 1 A) :=
    .bvar Γ' 0 (lift 0 1 A) rfl
  have hzl : ConvT E n Γ' (.bvar 0) (lift 0 1 v) (lift 0 1 A) :=
    .zetaLocal Γ' 0 (lift 0 1 A) (lift 0 1 v) rfl rfl hv'
  have hD₁ : HasTyT E n (.letBinding (lift 0 1 A) (lift 0 1 v) :: Γ') (lift 1 1 D) (.sort w) :=
    hasTyTWeaken d hcl (c := 1) hD
  have hD₀ : HasTyT E n (.letBinding (lift 0 1 A) (.bvar 0) :: Γ') (lift 1 1 D) (.sort w) :=
    hasTyTConvLet hcl (.refl Γ' (lift 0 1 A) (.sort u) hA') hzl hb0 hD₁
  have hc : ConvT E n Γ' (instantiate0 (.bvar 0) (lift 1 1 D))
      (instantiate0 (lift 0 1 v) (lift 1 1 D)) (.sort w) :=
    convT_inst0_sortCongrLet hA' hD₀ hD₁ hb0 hv' hzl
  have heqL : instantiate0 (.bvar 0) (lift 1 1 D) = D :=
    instantiate0_bvar0_lift1 D
  have heqR : instantiate0 (lift 0 1 v) (lift 1 1 D) = lift 0 1 (instantiate0 v D) :=
    (lift_instantiate_low 1 0 0 v (Nat.le_refl 0) D).symm
  rw [heqL, heqR] at hc
  exact hc

/-- **Depth-1 Codomain Instantiation Congruence Under a `letBinding` (`convT_inst1_sortCongrLet`):**
    Given `hD₁ : HasTyT E n (.letBinding A v₁ :: Γ) D₁ (.sort u₁)` and
    `hD₂ : HasTyT E n (.assumption D₁ :: .letBinding A v₁ :: Γ) D₂ (.sort u₂)`, for any
    `hcv : ConvT E n Γ v₁ v₂ A`, the depth-1 codomain instantiations
    `instantiate 1 (lift 0 1 v₁) D₂` and `instantiate 1 (lift 0 1 v₂) D₂` are convertible at
    `.sort u₂` in `.assumption (instantiate0 v₁ D₁) :: Γ` — **with ZERO `PiInj` premise**! -/
def convT_inst1_sortCongrLet {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A v₁ v₂ D₁ D₂ : Expr Nat} {u u₁ u₂ : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv₁ : HasTyT E n Γ v₁ A) (hv₂ : HasTyT E n Γ v₂ A)
    (hcv : ConvT E n Γ v₁ v₂ A)
    (hD₁ : HasTyT E n (.letBinding A v₁ :: Γ) D₁ (.sort u₁))
    (hD₂ : HasTyT E n (.assumption D₁ :: .letBinding A v₁ :: Γ) D₂ (.sort u₂)) :
    ConvT E n (.assumption (instantiate0 v₁ D₁) :: Γ)
      (instantiate 1 (lift 0 1 v₁) D₂) (instantiate 1 (lift 0 1 v₂) D₂) (.sort u₂) := by
  let d₁ : LocalDecl := .assumption (instantiate0 v₁ D₁)
  let Γ₁ : LCtx := d₁ :: Γ
  have hA₁ : HasTyT E n Γ₁ (lift 0 1 A) (.sort u) :=
    hasTyTWeaken d₁ hcl (c := 0) hA
  have hv₁' : HasTyT E n Γ₁ (lift 0 1 v₁) (lift 0 1 A) :=
    hasTyTWeaken d₁ hcl (c := 0) hv₁
  have hv₂' : HasTyT E n Γ₁ (lift 0 1 v₂) (lift 0 1 A) :=
    hasTyTWeaken d₁ hcl (c := 0) hv₂
  have hcv' : ConvT E n Γ₁ (lift 0 1 v₁) (lift 0 1 v₂) (lift 0 1 A) :=
    convTWeaken d₁ hcl (c := 0) hcv
  have hD₁' : HasTyT E n (.letBinding (lift 0 1 A) (lift 0 1 v₁) :: Γ₁) (lift 1 1 D₁) (.sort u₁) :=
    hasTyTWeaken d₁ hcl (c := 1) hD₁
  have hcD₁_self : ConvT E n (.letBinding (lift 0 1 A) (lift 0 1 v₁) :: Γ₁)
      (lift 1 1 D₁) (lift 0 2 (instantiate0 v₁ D₁)) (.sort u₁) := by
    have hc₀ := convT_let_self_inst0_sort hcl hA₁ hv₁' hD₁'
    have h1 : instantiate0 (lift 0 1 v₁) (lift 1 1 D₁) = lift 0 1 (instantiate0 v₁ D₁) :=
      (lift_instantiate_low 1 0 0 v₁ (Nat.le_refl 0) D₁).symm
    have heq : lift 0 1 (instantiate0 (lift 0 1 v₁) (lift 1 1 D₁)) =
        lift 0 2 (instantiate0 v₁ D₁) := by
      rw [h1, lift_lift_merge 1 1 0 0 (Nat.le_refl 0) (Nat.zero_le 1) (instantiate0 v₁ D₁)]
    rwa [heq] at hc₀
  let Γ₂ : LCtx := .letBinding (lift 0 1 A) (lift 0 1 v₁) :: Γ₁
  have hb1_raw : HasTyT E n Γ₂ (.bvar 1) (lift 0 2 (instantiate0 v₁ D₁)) :=
    .bvar Γ₂ 1 (lift 0 2 (instantiate0 v₁ D₁)) rfl
  have hb1 : HasTyT E n Γ₂ (.bvar 1) (lift 1 1 D₁) :=
    .conv Γ₂ (.bvar 1) (lift 0 2 (instantiate0 v₁ D₁)) (lift 1 1 D₁) u₁
      hb1_raw (.symm _ _ _ _ hcD₁_self)
  have hD₂_w : HasTyT E n (.assumption (lift 1 1 D₁) :: Γ₂) (lift 2 1 D₂) (.sort u₂) :=
    hasTyTWeaken d₁ hcl (c := 2) hD₂
  have hD₂_sw₁ : HasTyT E n (.letBinding (lift 0 1 A) (lift 0 1 v₁) :: Γ₁)
      (instantiate0 (.bvar 1) (lift 2 1 D₂)) (.sort u₂) :=
    hasTyT_subst0S hcl hinst hD₂_w hb1
  have hD₂_sw₂ : HasTyT E n (.letBinding (lift 0 1 A) (lift 0 1 v₂) :: Γ₁)
      (instantiate0 (.bvar 1) (lift 2 1 D₂)) (.sort u₂) :=
    hasTyTConvLet hcl (.refl Γ₁ (lift 0 1 A) (.sort u) hA₁) (.symm _ _ _ _ hcv') hv₂' hD₂_sw₁
  have hc_sw : ConvT E n Γ₁
      (instantiate0 (lift 0 1 v₁) (instantiate0 (.bvar 1) (lift 2 1 D₂)))
      (instantiate0 (lift 0 1 v₂) (instantiate0 (.bvar 1) (lift 2 1 D₂))) (.sort u₂) :=
    convT_inst0_sortCongrLet hA₁ hD₂_sw₁ hD₂_sw₂ hv₁' hv₂' hcv'
  rwa [instantiate0_lift0_instantiate0_bvar1_lift2 v₁ D₂,
       instantiate0_lift0_instantiate0_bvar1_lift2 v₂ D₂] at hc_sw

/-- **Depth-1 Codomain Instantiation Congruence Under an `assumption` (`convT_inst1_sortCongr`):** -/
def convT_inst1_sortCongr {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A v₁ v₂ D₁ D₂ : Expr Nat} {u u₁ u₂ : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv₁ : HasTyT E n Γ v₁ A) (hv₂ : HasTyT E n Γ v₂ A)
    (hcv : ConvT E n Γ v₁ v₂ A)
    (hD₁ : HasTyT E n (.assumption A :: Γ) D₁ (.sort u₁))
    (hD₂ : HasTyT E n (.assumption D₁ :: .assumption A :: Γ) D₂ (.sort u₂)) :
    ConvT E n (.assumption (instantiate0 v₁ D₁) :: Γ)
      (instantiate 1 (lift 0 1 v₁) D₂) (instantiate 1 (lift 0 1 v₂) D₂) (.sort u₂) :=
  convT_inst1_sortCongrLet hcl hinst hA hv₁ hv₂ hcv
    (hasTyT_assump_to_let v₁ hD₁)
    (hasTyT_of_ctxRefines hD₂ (.assumption (.assumpToLet (ctxRefines_refl Γ))))

/-- **General 0-Instantiation Value Congruence in `ConvT` Under a `letBinding`
    (`convT_inst0_letCongr`):**
    For **every** body `hb : HasTyT E n (.letBinding A v₁ :: Γ) b B` (at **any** type `B`, not
    just `.sort w`!), `instantiate0 v₁ b` and `instantiate0 v₂ b` are convertible in `ConvT` at
    `instantiate0 v₁ B`! -/
def convT_inst0_letCongr (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A v₁ v₂ b B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv₁ : HasTyT E n Γ v₁ A) (hv₂ : HasTyT E n Γ v₂ A)
    (hcv : ConvT E n Γ v₁ v₂ A)
    (hb : HasTyT E n (.letBinding A v₁ :: Γ) b B) :
    ConvT E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) (instantiate0 v₁ B) := by
  have hcl := envClosed_of_envWfT hW
  have hΓ_let : CtxWfT E n (.letBinding A v₁ :: Γ) := .letBinding Γ A u v₁ hΓ hA hv₁
  obtain ⟨w, hB⟩ := tySort hW hΓ_let hb
  have hb₂ : HasTyT E n (.letBinding A v₂ :: Γ) b B :=
    hasTyTConvLet hcl (.refl Γ A (.sort u) hA) (.symm _ _ _ _ hcv) hv₂ hb
  have hB₂ : HasTyT E n (.letBinding A v₂ :: Γ) B (.sort w) :=
    hasTyTConvLet hcl (.refl Γ A (.sort u) hA) (.symm _ _ _ _ hcv) hv₂ hB
  have hcB : ConvT E n Γ (instantiate0 v₁ B) (instantiate0 v₂ B) (.sort w) :=
    convT_inst0_sortCongrLet hA hB hB₂ hv₁ hv₂ hcv
  have l1 : ConvT E n Γ (instantiate0 v₁ b) (.letE A v₁ b) (instantiate0 v₁ B) :=
    .symm _ _ _ _ (.zeta Γ A v₁ b B u hA hv₁ hb)
  have l2 : ConvT E n Γ (.letE A v₁ b) (.letE A v₂ b) (instantiate0 v₁ B) :=
    .letE Γ A A v₁ v₂ b b B u (.refl Γ A (.sort u) hA) hcv (.refl _ b B hb)
  have l3 : ConvT E n Γ (.letE A v₂ b) (instantiate0 v₂ b) (instantiate0 v₁ B) :=
    .tyConv Γ (.letE A v₂ b) (instantiate0 v₂ b) (instantiate0 v₂ B) (instantiate0 v₁ B) w
      (.zeta Γ A v₂ b B u hA hv₂ hb₂) (.symm _ _ _ _ hcB)
  exact .trans _ _ _ _ _ l1 (.trans _ _ _ _ _ l2 l3)

/-- **General 0-Instantiation Value Congruence in `ConvT` Under an `assumption`
    (`convT_inst0_assumpCongr`):** -/
def convT_inst0_assumpCongr (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A v₁ v₂ b B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv₁ : HasTyT E n Γ v₁ A) (hv₂ : HasTyT E n Γ v₂ A)
    (hcv : ConvT E n Γ v₁ v₂ A)
    (hb : HasTyT E n (.assumption A :: Γ) b B) :
    ConvT E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) (instantiate0 v₁ B) :=
  convT_inst0_letCongr hW hΓ hA hv₁ hv₂ hcv (hasTyT_assump_to_let v₁ hb)

/-! ### §12.3. Unconditional `LRTermDSubKClosedCtxBi` 0-Instantiation Congruence on All $\Pi$-Type
Bodies and Two-Endpoint `PrunedSemEqDIK` Criteria Discharging Both `c = .bot` and `c = .sort` -/

/-- **Unconditional 0-Instantiation Value Congruence in `LRTermDSubKClosedCtxBi` for ANY
    $\Pi$-Expression Body (`lrTermDSubKClosedCtxBi_subst0_pi_body`):**
    Whenever `.pi D₁ D₂` is typed in `.letBinding A v₁ :: Γ` (at `.sort (.imax u₁ u₂)`), for
    **every** `hcv : ConvT E n Γ v₁ v₂ A` (with **zero** semantic hypotheses on `v₁, v₂, D₁, D₂`!),
    `LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ (.pi D₁ D₂)) (instantiate0 v₂ (.pi D₁ D₂)) (.sort (.imax u₁ u₂))`
    holds **100% unconditionally**! -/
theorem lrTermDSubKClosedCtxBi_subst0_pi_body (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A v₁ v₂ D₁ D₂ : Expr Nat} {u u₁ u₂ : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hv₁ : HasTyT E n Γ v₁ A) (hv₂ : HasTyT E n Γ v₂ A)
    (hcv : ConvT E n Γ v₁ v₂ A)
    (hD₁ : HasTyT E n (.letBinding A v₁ :: Γ) D₁ (.sort u₁))
    (hD₂ : HasTyT E n (.assumption D₁ :: .letBinding A v₁ :: Γ) D₂ (.sort u₂)) :
    LRTermDSubKClosedCtxBi E n Γ
      (instantiate0 v₁ (.pi D₁ D₂)) (instantiate0 v₂ (.pi D₁ D₂)) (.sort (.imax u₁ u₂)) := by
  have hcl := envClosed_of_envWfT hW
  have hinst := envMembersSubstStable_of_envWfT hW
  have hD₁_v₂ : HasTyT E n (.letBinding A v₂ :: Γ) D₁ (.sort u₁) :=
    hasTyTConvLet hcl (.refl Γ A (.sort u) hA) (.symm _ _ _ _ hcv) hv₂ hD₁
  have hD₁_inst₁ : HasTyT E n Γ (instantiate0 v₁ D₁) (.sort u₁) :=
    hasTyT_substLet0_of_envWfT hW hD₁ hv₁
  have hΓ₁ : CtxWfT E n (.assumption (instantiate0 v₁ D₁) :: Γ) :=
    .assumption Γ (instantiate0 v₁ D₁) u₁ hΓ hD₁_inst₁
  have hcD₁ : ConvT E n Γ (instantiate0 v₁ D₁) (instantiate0 v₂ D₁) (.sort u₁) :=
    convT_inst0_sortCongrLet hA hD₁ hD₁_v₂ hv₁ hv₂ hcv
  have hcD₂ : ConvT E n (.assumption (instantiate0 v₁ D₁) :: Γ)
      (instantiate 1 (lift 0 1 v₁) D₂) (instantiate 1 (lift 0 1 v₂) D₂) (.sort u₂) :=
    convT_inst1_sortCongrLet hcl hinst hA hv₁ hv₂ hcv hD₁ hD₂
  simpa only [instantiate0, instantiate, lift_zero] using
    lrTermDSubKClosedCtxBi_pi (u := u₁) (v := u₂) hΓ₁
      (.of Γ _ _ u₁ hcD₁)
      (.of (.assumption (instantiate0 v₁ D₁) :: Γ) _ _ u₂ hcD₂)

/-- **Two-Endpoint `PrunedSemEqDIK` Criterion for `LRTermDSubKClosedCtxBi`
    (`lrTermDSubKClosedCtxBi_of_prunedSemEqDIK_and_pi_tyConv`):**
    Whenever `PrunedSemEqDIK E (ctxEnvDIK E Γ) M₁ M₂` holds together with the two diagonal
    relations `h₁ : LRTermDSubKClosedCtxBi E n Γ M₁ M₁ T` and
    `h₂ : LRTermDSubKClosedCtxBi E n Γ M₂ M₂ T`:
    - The `c = .bot` probe is discharged automatically (`True`).
    - The `c = .sort` probe is discharged **automatically** (`hsem` transfers `.sort` between
      `M₁` and `M₂`, so `h₁` gives `M₁ ↠wh .sort l₁` and `h₂` gives `M₂ ↠wh .sort l₂`, yielding
      `LRTypeINPiKClosedCtx.sort`!).
    - At `c = .pi .bot []`, `h₁` and `h₂` already provide `M₁ ↠wh .pi A₁ B₁` (with
      `CtxWfT E n (.assumption A₁ :: Γ)`) and `M₂ ↠wh .pi A₂ B₂`, requiring only `TyConvT`
      between `(A₁, B₁)` and `(A₂, B₂)`! -/
theorem lrTermDSubKClosedCtxBi_of_prunedSemEqDIK_and_pi_tyConv
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {M₁ M₂ T : Expr Nat}
    (hsem : PrunedSemEqDIK E (ctxEnvDIK E Γ) M₁ M₂)
    (h₁ : LRTermDSubKClosedCtxBi E n Γ M₁ M₁ T)
    (h₂ : LRTermDSubKClosedCtxBi E n Γ M₂ M₂ T)
    (hpi : ∀ A₁ B₁ A₂ B₂,
      WhRedPiKClosedCtx E Γ M₁ (.pi A₁ B₁) →
      WhRedPiKClosedCtx E Γ M₂ (.pi A₂ B₂) →
      Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)) :
    LRTermDSubKClosedCtxBi E n Γ M₁ M₂ T := by
  intro c hc hor
  have hc_p : PrunedPiCpt c := prunedPiCpt_of_probeCpt hc
  have hM₁ : ApproxDIK E (ctxEnvDIK E Γ) M₁ c :=
    hor.elim id (fun h => (hsem c hc_p).mpr h)
  have hM₂ : ApproxDIK E (ctxEnvDIK E Γ) M₂ c :=
    (hsem c hc_p).mp hM₁
  cases hc with
  | bot =>
      exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial)
  | sort =>
      rcases h₁ .sort .sort (Or.inl hM₁) with hP | hC₁
      · exact Or.inl hP
      · rcases h₂ .sort .sort (Or.inl hM₂) with hP | hC₂
        · exact Or.inl hP
        · rw [lrTermDSubKClosedCtxCore_sort_iff] at hC₁ hC₂
          rcases hC₁ with ⟨hT, hlr₁⟩
          rcases hC₂ with ⟨_, hlr₂⟩
          cases hlr₁ with
          | sort hred₁ _ =>
              cases hlr₂ with
              | sort hred₂ _ =>
                  refine Or.inr ?_
                  rw [lrTermDSubKClosedCtxCore_sort_iff]
                  exact ⟨hT, .sort hred₁ hred₂⟩
  | piBotNil =>
      rcases h₁ (.pi .bot []) .piBotNil (Or.inl hM₁) with hP | hC₁
      · exact Or.inl hP
      · rcases h₂ (.pi .bot []) .piBotNil (Or.inl hM₂) with hP | hC₂
        · exact Or.inl hP
        · have hne : CptI.pi .bot [] ≠ .bot := by intro h0; cases h0
          rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil hne] at hC₁ hC₂
          rcases hC₁ with ⟨hT, hlr₁⟩
          rcases hC₂ with ⟨_, hlr₂⟩
          cases hlr₁ with
          | @pi _ _ _ A₁ B₁ _ _ _ _ hred₁ _ hΓ₁ _ _ _ _ =>
              cases hlr₂ with
              | @pi _ _ _ A₂ B₂ _ _ _ _ hred₂ _ _ _ _ _ _ =>
                  obtain ⟨⟨hcA⟩, ⟨hcB⟩⟩ := hpi A₁ B₁ A₂ B₂ hred₁ hred₂
                  refine Or.inr ?_
                  rw [lrTermDSubKClosedCtxCore_probe_nonbot_iff .piBotNil hne]
                  exact ⟨hT, .pi hred₁ hred₂ hΓ₁ hcA hcB (.bot Γ A₁ A₂)
                    (fun _ hs => (List.not_mem_nil _ hs).elim)⟩

/-- **Two-Endpoint `PrunedSemEqDIK` Criterion Discharging Both `c = .bot` and `c = .sort`
    Automatically (`lrTermDSubKClosedCtxBi_of_prunedSemEqDIK_and_no_pi_probe`):**
    Whenever `PrunedSemEqDIK E (ctxEnvDIK E Γ) M₁ M₂`, `h₁ : LRTermDSubKClosedCtxBi E n Γ M₁ M₁ T`,
    `h₂ : LRTermDSubKClosedCtxBi E n Γ M₂ M₂ T`, and `¬ ApproxDIK E (ctxEnvDIK E Γ) M₁ (.pi .bot [])`
    (allowing `M₁` and `M₂` to have `.bot` AND `.sort` in `ApproxDIK E (ctxEnvDIK E Γ)`!),
    `LRTermDSubKClosedCtxBi E n Γ M₁ M₂ T` holds **unconditionally**! -/
theorem lrTermDSubKClosedCtxBi_of_prunedSemEqDIK_and_no_pi_probe
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {M₁ M₂ T : Expr Nat}
    (hsem : PrunedSemEqDIK E (ctxEnvDIK E Γ) M₁ M₂)
    (h₁ : LRTermDSubKClosedCtxBi E n Γ M₁ M₁ T)
    (h₂ : LRTermDSubKClosedCtxBi E n Γ M₂ M₂ T)
    (hnopi : ¬ ApproxDIK E (ctxEnvDIK E Γ) M₁ (.pi .bot [])) :
    LRTermDSubKClosedCtxBi E n Γ M₁ M₂ T := by
  intro c hc hor
  have hc_p : PrunedPiCpt c := prunedPiCpt_of_probeCpt hc
  have hM₁ : ApproxDIK E (ctxEnvDIK E Γ) M₁ c :=
    hor.elim id (fun h => (hsem c hc_p).mpr h)
  have hM₂ : ApproxDIK E (ctxEnvDIK E Γ) M₂ c :=
    (hsem c hc_p).mp hM₁
  cases hc with
  | bot =>
      exact Or.inr (by rw [lrTermDSubKClosedCtxCore_bot_iff]; trivial)
  | sort =>
      rcases h₁ .sort .sort (Or.inl hM₁) with hP | hC₁
      · exact Or.inl hP
      · rcases h₂ .sort .sort (Or.inl hM₂) with hP | hC₂
        · exact Or.inl hP
        · rw [lrTermDSubKClosedCtxCore_sort_iff] at hC₁ hC₂
          rcases hC₁ with ⟨hT, hlr₁⟩
          rcases hC₂ with ⟨_, hlr₂⟩
          cases hlr₁ with
          | sort hred₁ _ =>
              cases hlr₂ with
              | sort hred₂ _ =>
                  refine Or.inr ?_
                  rw [lrTermDSubKClosedCtxCore_sort_iff]
                  exact ⟨hT, .sort hred₁ hred₂⟩
  | piBotNil =>
      exact (hnopi hM₁).elim

/-- **0-Instantiation Specialization of `lrTermDSubKClosedCtxBi_of_prunedSemEqDIK_and_no_pi_probe`
    (`lrTermDSubKClosedCtxBi_subst0_of_prunedSemEqDIK_no_pi_probe`):**
    Upgrades §11.3's `lrTermDSubKClosedCtxBi_subst0_of_prunedSemEqDIK_botProbe` by allowing
    `instantiate0 v₁ b` to have **both** `.bot` and `.sort` in `ApproxDIK E (ctxEnvDIK E Γ)`! -/
theorem lrTermDSubKClosedCtxBi_subst0_of_prunedSemEqDIK_no_pi_probe
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {v₁ v₂ b B : Expr Nat}
    (hv : PrunedSemEqDIK E (ctxEnvDIK E Γ) v₁ v₂)
    (h₁ : LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₁ b) (instantiate0 v₁ B))
    (h₂ : LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₂ b) (instantiate0 v₂ b) (instantiate0 v₁ B))
    (hnopi : ¬ ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 v₁ b) (.pi .bot [])) :
    LRTermDSubKClosedCtxBi E n Γ (instantiate0 v₁ b) (instantiate0 v₂ b) (instantiate0 v₁ B) :=
  lrTermDSubKClosedCtxBi_of_prunedSemEqDIK_and_no_pi_probe
    (prunedSemEqDIK_instantiate0_of_prunedSemEqDIK (prunedEnvLe_ctxEnvDIK E Γ) hv b)
    h₁ h₂ hnopi

/-- **Unconditional 0-Instantiation Congruence for ANY $\Pi$-Type Arguments on Non-$\Pi$-Probed
    Bodies (Including Sort-Probed Bodies, `lrTermDSubKClosedCtxBi_subst0_pi_arg_of_no_pi_probe`):** -/
theorem lrTermDSubKClosedCtxBi_subst0_pi_arg_of_no_pi_probe
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (A₁ B₁ A₂ B₂ : Expr Nat) {b B : Expr Nat}
    (h₁ : LRTermDSubKClosedCtxBi E n Γ
      (instantiate0 (.pi A₁ B₁) b) (instantiate0 (.pi A₁ B₁) b) (instantiate0 (.pi A₁ B₁) B))
    (h₂ : LRTermDSubKClosedCtxBi E n Γ
      (instantiate0 (.pi A₂ B₂) b) (instantiate0 (.pi A₂ B₂) b) (instantiate0 (.pi A₁ B₁) B))
    (hnopi : ¬ ApproxDIK E (ctxEnvDIK E Γ) (instantiate0 (.pi A₁ B₁) b) (.pi .bot [])) :
    LRTermDSubKClosedCtxBi E n Γ
      (instantiate0 (.pi A₁ B₁) b) (instantiate0 (.pi A₂ B₂) b) (instantiate0 (.pi A₁ B₁) B) :=
  lrTermDSubKClosedCtxBi_subst0_of_prunedSemEqDIK_no_pi_probe
    (prunedSemEqDIK_pi E (ctxEnvDIK E Γ) A₁ B₁ A₂ B₂) h₁ h₂ hnopi

#print axioms lrTermDSubKCore_probe_transport_of_bi
#print axioms lrTermDSubK_probe_transport_of_bi
#print axioms lrTermDSubKBi_tyConv_of_bi
#print axioms fundamentalTermDSubKBiProbe_letFree_of_supply_noBot
#print axioms fundamentalTermDSubKProbe_letFree_of_supply_noBot
#print axioms piRow_of_appLetProbeSupplyDSubKBi_noBot
#print axioms lrTypeINPiKClosed_substLet_botPiCpt
#print axioms lrTypeINPiKClosed_substLet0_botPiCpt
#print axioms lrTypeINBiDIKClosed_substLet0
#print axioms LRTermDSubKClosedCore
#print axioms LRTermDSubKClosed
#print axioms LRTermDSubKClosedBi
#print axioms lrTermDSubKClosedCore_bot_iff
#print axioms lrTermDSubKClosedCore_sort_iff
#print axioms lrTermDSubKClosedCore_pi_iff
#print axioms lrTermDSubKClosedCore_probe_nonbot_iff
#print axioms lrTermDSubKClosed_probe_sort_iff
#print axioms lrTypeINPiKClosed_of_lrTermDSubKClosedCore_probe
#print axioms approxDIK_of_lrTermDSubKClosedCore_probe
#print axioms lrTermDSubKClosedCore_whRedPiKClosed_expand_probe
#print axioms lrTermDSubKClosed_whRedPiKClosed_expand_probe
#print axioms lrTermDSubKClosedBi_whRedPiKClosed_expand
#print axioms lrTermDSubKClosedBi_of_whStepPiKClosed
#print axioms lrTermDSubKClosedCore_probe_symm
#print axioms lrTermDSubKClosed_probe_symm
#print axioms lrTermDSubKClosedBi_symm
#print axioms lrTermDSubKClosedCore_probe_trans
#print axioms lrTermDSubKClosed_probe_trans
#print axioms lrTermDSubKClosedBi_trans
#print axioms lrTermDSubKClosedCore_weaken_probe
#print axioms lrTermDSubKClosed_weaken_probe
#print axioms lrTermDSubKClosed_weaken0_probe
#print axioms lrTermDSubKClosedBi_weaken
#print axioms lrTermDSubKClosedBi_weaken0
#print axioms lrTermDSubKClosedCore_subst_probe
#print axioms lrTermDSubKClosed_subst_probe
#print axioms lrTermDSubKClosed_subst0_probe
#print axioms lrTermDSubKClosedBi_subst0
#print axioms lrTermDSubKClosedCore_substLet_probe
#print axioms lrTermDSubKClosed_substLet_probe
#print axioms lrTermDSubKClosed_substLet0_probe
#print axioms lrTermDSubKClosedBi_substLet0
#print axioms lrTermDSubKClosedBi_beta_of_botApprox
#print axioms lrTermDSubKClosedBi_zeta_of_botApprox
#print axioms lrTermDSubKClosedBi_letE_diag_of_botApprox
#print axioms WhStepPiKClosedCtx
#print axioms WhRedPiKClosedCtx
#print axioms whRedPiKClosedCtx_trans
#print axioms whRedPiKClosedCtx_of_whRed
#print axioms whRedPiKClosedCtx_appHead
#print axioms whStepPiKClosedCtx_letFree_iff
#print axioms whRedPiKClosedCtx_letFree_iff
#print axioms semEqDIK_ctxEnvDIK_whStepPiKClosedCtx
#print axioms semEqDIK_ctxEnvDIK_whRedPiKClosedCtx
#print axioms approxDIK_ctxEnvDIK_whRedPiKClosedCtx_back
#print axioms approxDIK_ctxEnvDIK_sort_of_whRedPiKClosedCtx
#print axioms whStepPiKClosedCtx_sort_false
#print axioms whStepPiKClosedCtx_pi_false
#print axioms whStepPiKClosedCtx_lam_false
#print axioms whRedPiKClosedCtx_sort_eq
#print axioms whRedPiKClosedCtx_pi_eq
#print axioms not_whStepPiKClosedCtx_recursor_prefix
#print axioms whStep_and_whStepPiKClosedCtx_det
#print axioms whDetPiKClosedCtx_of_envWfT
#print axioms WhNormalPiKClosedCtx
#print axioms whNormalPiKClosedCtx_sort
#print axioms whNormalPiKClosedCtx_pi
#print axioms whNormalPiKClosedCtx_lam
#print axioms whRedPiKClosedCtx_of_normal
#print axioms whRedPiKClosedCtx_normal_unique_of_envWfT
#print axioms whRedPiKClosedCtx_pi_unique_of_envWfT
#print axioms whRedPiKClosedCtx_sort_unique_of_envWfT
#print axioms whRedPiKClosedCtx_zetaLocalSortCtx_sort
#print axioms whRedPiKClosedCtx_trueEnvU_kRecVar_sort
#print axioms whRedPiKClosedCtx_andEnvU_mixAndRedex_mixPi
#print axioms denDIK_insert_lift_eq
#print axioms denDIK_cons_lift0_eq
#print axioms approxDIK_ctxEnvDIK_cons_lift0_iff
#print axioms ctxEnvDIK_insertAt_eq
#print axioms approxDIK_ctxEnvDIK_insertAt_lift_iff
#print axioms denDIK_subst_eq
#print axioms ctxEnvDIK_substLet_eq
#print axioms approxDIK_ctxEnvDIK_substLet_iff
#print axioms approxDIK_ctxEnvDIK_substLet0_iff
#print axioms ctxEnvDIK_substAssump_eq
#print axioms approxDIK_ctxEnvDIK_substAssump_iff
#print axioms whStepPiKClosedCtx_lift_insertAt
#print axioms whRedPiKClosedCtx_lift_insertAt
#print axioms whStepPiKClosedCtx_lift0_cons
#print axioms whRedPiKClosedCtx_lift0_cons
#print axioms whStepPiKClosedCtx_substLet_of_envClosed
#print axioms whRedPiKClosedCtx_substLet_of_envClosed
#print axioms whRedPiKClosedCtx_substLet0_of_envClosed
#print axioms whStepPiKClosedCtx_substAssump_of_envClosed
#print axioms whRedPiKClosedCtx_substAssump_of_envClosed
#print axioms SameLetProfile
#print axioms sameLetProfile_refl
#print axioms sameLetProfile_symm
#print axioms sameLetProfile_trans
#print axioms sameLetProfile_assump_head
#print axioms sameLetProfile_cons_assump
#print axioms whStepPiKClosedCtx_of_sameLetProfile
#print axioms whRedPiKClosedCtx_of_sameLetProfile
#print axioms whNormalPiKClosedCtx_of_sameLetProfile
#print axioms LRTypeINPiKClosedCtx
#print axioms lrTypeINPiKClosedCtx_expand
#print axioms approxDIK_cons_botDemand_ctxEnvDIK_iff
#print axioms approxDIK_of_lrTypeINPiKClosedCtx_botPiCpt
#print axioms lrTypeINPiKClosedCtx_ctx_of_sameLetProfile
#print axioms lrTypeINPiKClosedCtx_assump_dom
#print axioms lrTypeINPiKClosedCtx_symm
#print axioms lrTypeINPiKClosedCtx_trans_of_envWfT
#print axioms lrTypeINPiKClosedCtx_weaken_botPiCpt
#print axioms lrTypeINPiKClosedCtx_weaken0_botPiCpt
#print axioms lrTypeINPiKClosedCtx_substLet_botPiCpt
#print axioms lrTypeINPiKClosedCtx_substLet0_botPiCpt
#print axioms LRTypeINBiDIKClosedCtx
#print axioms lrTypeINBiDIKClosedCtx_symm
#print axioms lrTypeINBiDIKClosedCtx_trans_of_envWfT
#print axioms lrTypeINBiDIKClosedCtx_of_whRedPiKClosedCtx
#print axioms lrTypeINBiDIKClosedCtx_of_whStepPiKClosedCtx
#print axioms lrTypeINBiDIKClosedCtx_zetaLocal
#print axioms lrTypeINBiDIKClosedCtx_sorts
#print axioms lrTypeINBiDIKClosedCtx_sort_diag
#print axioms lrTypeINBiDIKClosedCtx_zetaLocalSortCtx
#print axioms lrTypeINBiDIKClosedCtx_weaken0
#print axioms lrTypeINBiDIKClosedCtx_substLet0
#print axioms FundamentalLRINBotDIKClosedCtx
#print axioms fundamentalLRINBotDIKClosedCtx_of_links
#print axioms piRow_of_fundamentalLRINBotDIKClosedCtx
#print axioms LRTermDSubKClosedCtxCore
#print axioms LRTermDSubKClosedCtx
#print axioms LRTermDSubKClosedCtxBi
#print axioms lrTermDSubKClosedCtxCore_bot_iff
#print axioms lrTermDSubKClosedCtxCore_sort_iff
#print axioms lrTermDSubKClosedCtxCore_pi_iff
#print axioms lrTermDSubKClosedCtxCore_probe_nonbot_iff
#print axioms lrTypeINPiKClosedCtx_of_lrTermDSubKClosedCtxCore_probe
#print axioms approxDIK_of_lrTermDSubKClosedCtxCore_probe
#print axioms lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_expand_probe
#print axioms lrTermDSubKClosedCtx_whRedPiKClosedCtx_expand_probe
#print axioms lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_expand
#print axioms lrTermDSubKClosedCtxBi_of_whStepPiKClosedCtx
#print axioms lrTermDSubKClosedCtxBi_symm
#print axioms lrTermDSubKClosedCtxBi_trans
#print axioms lrTermDSubKClosedCtxCore_substLet_probe
#print axioms lrTermDSubKClosedCtx_substLet0_probe
#print axioms lrTermDSubKClosedCtxBi_substLet0
#print axioms lrTermDSubKClosedCtxBi_zetaLocal
#print axioms lrTermDSubKClosedCtxBi_zeta
#print axioms lrTermDSubKClosedCtxBi_letE_diag
#print axioms lrTermDSubKClosedCtxBi_sorts
#print axioms lrTermDSubKClosedCtxBi_sort_diag
#print axioms lrTermDSubKClosedCtxBi_lam
#print axioms lrTermDSubKClosedCtxBi_consts_of_body_none
#print axioms lrTermDSubKClosedCtxBi_deltaConsts
#print axioms lrTermDSubKClosedCtxBi_pi
#print axioms lrTermDSubKClosedCtxBi_pi_diag
#print axioms not_lrTermDSubKClosedCtxCore_at_pi_of_probe_ne_bot
#print axioms lrTermDSubKClosedCtxBi_eta
#print axioms lrTermDSubKClosedCtxBi_irr_of_sortRow
#print axioms lrTermDSubKClosedCtxBi_tyConv_of_bi
#print axioms lrTermDSubKClosedCtxBi_zetaLocalSortCtx
#print axioms lrTermDSubKClosedCtxBi_idPiProp
#print axioms lrTermDSubKClosedCtxBi_closedIrrPi
#print axioms lrTermDSubKClosedCtxBi_trueEnvU_kRecVar_sort
#print axioms lrTermDSubKClosedCtxBi_andEnvU_mixAndRedex_mixPi
#print axioms FundamentalTermDSubKClosedCtxBiProbe
#print axioms piRow_of_fundamentalTermDSubKClosedCtxBiProbe
#print axioms lrTermDSubKClosedCtxCore_weaken_probe
#print axioms lrTermDSubKClosedCtx_weaken_probe
#print axioms lrTermDSubKClosedCtx_weaken0_probe
#print axioms lrTermDSubKClosedCtxBi_weaken
#print axioms lrTermDSubKClosedCtxBi_weaken0
#print axioms lrTermDSubKClosedCtxBi_closed_weaken_ctx
#print axioms lrTypeINPiKClosedCtx_substAssump_botPiCpt
#print axioms lrTypeINPiKClosedCtx_substAssump0_botPiCpt
#print axioms lrTypeINBiDIKClosedCtx_substAssump0
#print axioms lrTermDSubKClosedCtxCore_substAssump_probe
#print axioms lrTermDSubKClosedCtx_substAssump0_probe
#print axioms lrTermDSubKClosedCtxBi_substAssump0
#print axioms lrTermDSubKClosedCtxBi_beta_of_botApprox
#print axioms lrTermDSubKClosedCtxBi_letE_sameVal
#print axioms approxDIK_ctxEnvDIK_bvar_none_eq_bot
#print axioms lrTermDSubKClosedCtxBi_bvar_of_lookupValue_none
#print axioms lrTermDSubKClosedCtxBi_bvar_of_lookupValue_some
#print axioms CtxBVarOK
#print axioms ctxBVarOK_nil
#print axioms ctxBVarOK_of_letFree
#print axioms ctxBVarOK_cons_assumption
#print axioms ctxBVarOK_cons_letBinding
#print axioms CtxRefines
#print axioms ctxRefines_refl
#print axioms ctxRefines_cons
#print axioms ctxRefines_get_inv
#print axioms lookupType_of_ctxRefines
#print axioms lookupValue_of_ctxRefines
#print axioms hasTyT_of_ctxRefines
#print axioms convT_of_ctxRefines
#print axioms tyConvT_of_ctxRefines
#print axioms hasTyT_assump_to_let
#print axioms convT_assump_to_let
#print axioms tyConvT_assump_to_let
#print axioms lrTermDSubKClosedCtxBi_beta_via_let
#print axioms lrTermDSubKClosedCtxBi_beta_diag_via_let
#print axioms groupMembersT_body_arity_zero
#print axioms envWfT_body_arity_zero
#print axioms AppValCongrSupplyDSubKClosedCtxBi
#print axioms fundCtxBiProbe_hasTyT
#print axioms fundCtxBiProbe_convT
#print axioms ctxBVarOK_of_ctxWfT
#print axioms FundamentalTermDSubKClosedCtxProbe
#print axioms fundamentalTermDSubKClosedCtxProbe_of_biProbe
#print axioms fundamentalTermDSubKClosedCtxBiProbe_of_supply
#print axioms fundamentalTermDSubKClosedCtxProbe_of_supply
#print axioms piRow_of_appValCongrSupplyDSubKClosedCtxBi
#print axioms AppLetCongrSupplyDSubKClosedCtxBi
#print axioms fundCtxBiProbe_sub_hasTyT
#print axioms fundCtxBiProbe_sub_convT
#print axioms groupMembersT_members_preserved
#print axioms groupMembersT_body_from_base
#print axioms envWfT_deltaConst_sub
#print axioms deltaConst_lrTermDSubKClosedCtxBi_of_envWfT
#print axioms appValCongrSupply_of_appLetCongrSupply
#print axioms ctxBVarOK_of_ctxWfT_appLetCongr
#print axioms fundamentalTermDSubKClosedCtxBiProbe_of_appLetCongrSupply
#print axioms fundamentalTermDSubKClosedCtxProbe_of_appLetCongrSupply
#print axioms piRow_of_appLetCongrSupplyDSubKClosedCtxBi
#print axioms whRedPiKClosedCtx_of_whStepPiKClosedCtx_normal
#print axioms whRedPiKClosedCtx_of_whRedPiKClosedCtx_normal
#print axioms whRedPiKClosedCtx_iff_of_whRedPiKClosedCtx_normal
#print axioms whRedPiKClosedCtx_sort_iff_of_whRed
#print axioms whRedPiKClosedCtx_pi_iff_of_whRed
#print axioms lrTypeINPiKClosedCtx_whRedPiKClosedCtx_preserve
#print axioms lrTypeINPiKClosedCtx_whRedPiKClosedCtx_iff
#print axioms lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_probe_preserve
#print axioms lrTermDSubKClosedCtxCore_whRedPiKClosedCtx_probe_iff
#print axioms lrTermDSubKClosedCtx_whRedPiKClosedCtx_probe_iff
#print axioms lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_preserve
#print axioms lrTermDSubKClosedCtxBi_whRedPiKClosedCtx_iff
#print axioms lrTermDSubKClosedCtxBi_beta_congr_iff_subst0
#print axioms lrTermDSubKClosedCtxBi_zeta_congr_iff_subst0
#print axioms lrTermDSubKClosedCtxBi_app_lam_whRed_iff_subst0
#print axioms lrTermDSubKClosedCtxBi_subst0_lift0_one
#print axioms denDIK_instantiate_eq_of_semEqDIK
#print axioms semEqDIK_instantiate_of_semEqDIK
#print axioms semEqDIK_instantiate0_of_semEqDIK
#print axioms approxDIK_ctxEnvDIK_instantiate0_iff_of_semEqDIK
#print axioms lrTermDSubKClosedCtxBi_of_probeCpt_eq_bot
#print axioms lrTermDSubKClosedCtxBi_subst0_of_semEqDIK_botProbe
#print axioms approxDIK_app_not_lam_of_not_lam
#print axioms approxDIK_foldApps_not_lam_of_not_lam
#print axioms approxDIK_app_probeCpt_eq_bot_of_no_lam
#print axioms approxDIK_foldApps_probeCpt_eq_bot_of_no_lam
#print axioms approxDIK_ctxEnvDIK_bvar_none_not_lam
#print axioms approxDIK_sort_not_lam
#print axioms approxDIK_pi_not_lam
#print axioms approxDIK_rigidConst_not_lam
#print axioms lrTermDSubKClosedCtxBi_app_of_no_lam
#print axioms lrTermDSubKClosedCtxBi_foldApps_of_no_lam
#print axioms eqN_zero_of_imax_zero
#print axioms hasTyT_codomain_sort_zero_of_pi_sort_zero
#print axioms isPropTyI_codomain_of_pi
#print axioms isPropTyI_inst0_of_pi
#print axioms lrTermDSubKClosedCtxBi_of_isPropTyI
#print axioms lrTermDSubKClosedCtxBi_app_of_isPropTyI_pi
#print axioms prunePiCpt
#print axioms prunePiSteps
#print axioms prunePiList
#print axioms prunePiCpt_bot
#print axioms prunePiCpt_sort
#print axioms prunePiCpt_pi
#print axioms prunePiCpt_lam
#print axioms prunePiCpt_spine
#print axioms prunePiSteps_nil
#print axioms prunePiSteps_cons
#print axioms prunePiList_nil
#print axioms prunePiList_cons
#print axioms PrunedPiCpt
#print axioms prunedPiCpt_of_probeCpt
#print axioms prunePiList_eq_map
#print axioms prunePiSteps_eq_map
#print axioms prunedPiCpt_prunePiCpt
#print axioms prunedPiCpt_prunePiSteps
#print axioms prunedPiCpt_prunePiList
#print axioms prunePiCpt_eq_self_of_prunedPiCpt
#print axioms prunePiCpt_eq_self_of_probeCpt
#print axioms prunePiList_append
#print axioms prunePiList_replicate_bot
#print axioms prunePiCpt_curryStep
#print axioms prunePiList_fieldDemandVectors
#print axioms prunePiList_ctorDemand
#print axioms prunePiSet
#print axioms prunePiEnv
#print axioms prunePiSet_demand
#print axioms prunePiEnv_cons
#print axioms prunePiEnv_bot
#print axioms prunePiEnv_pushArgs
#print axioms approxDIK_prunePiCpt
#print axioms approxDIK_bot_prunePiCpt
#print axioms prunePiEnv_ctxEnvDIK_le
#print axioms approxDIK_ctxEnvDIK_prunePiCpt
#print axioms instantiate0_app_lift0_bvar0
#print axioms whStep_app_eta
#print axioms whRedPiKClosedCtx_app_eta
#print axioms semEqDIK_app_eta
#print axioms lrTermDSubKClosedCtxBi_app_eta_left_iff
#print axioms lrTermDSubKClosedCtxBi_app_eta_right_iff
#print axioms lrTermDSubKClosedCtxBi_app_eta_both_iff
#print axioms lrTermDSubKClosedCtxBi_app_lam_same_arg
#print axioms lrTermDSubKClosedCtxBi_app_lam_of_letValCongr
#print axioms AppCongrSupplyDSubKClosedCtxBi
#print axioms LetValCongrSupplyDSubKClosedCtxBi
#print axioms lrTermDSubKClosedCtxBi_subst0_of_appCongr
#print axioms lrTermDSubKClosedCtxBi_subst0_diag_of_appCongr
#print axioms prunedPiCpt_bot
#print axioms prunedPiCpt_sort
#print axioms prunedPiCpt_pi_bot_nil
#print axioms prunedPiCpt_pi_inv
#print axioms prunedPiCpt_spine_iff
#print axioms prunedPiCpt_lam_iff
#print axioms prunePiList_append_eq_self
#print axioms prunedPiCpt_spine_append_inv
#print axioms prunePiSet_idem
#print axioms prunePiEnv_idem
#print axioms PrunedEnvLe
#print axioms prunedEnvLe_bot
#print axioms prunedEnvLe_prunePiEnv
#print axioms prunedEnvLe_ctxEnvDIK
#print axioms prunedEnvLe_drop
#print axioms prunedEnvLe_cons_demand
#print axioms prunePiEnv_insert
#print axioms approxDIK_prunePiCpt_of_le
#print axioms approxDIK_prunePiEnv_iff_of_le
#print axioms approxDIK_ctxEnvDIK_prunePiEnv_iff
#print axioms prunedEnvLe_insert_denDIK
#print axioms prunePiSet_denDIK_eq_of_le
#print axioms PrunedSemEqDIK
#print axioms prunedSemEqDIK_refl
#print axioms prunedSemEqDIK_symm
#print axioms prunedSemEqDIK_trans
#print axioms prunedSemEqDIK_of_semEqDIK
#print axioms approxDIK_pi_prunedPiCpt_iff
#print axioms approxDIK_sort_prunedPiCpt_iff
#print axioms prunedSemEqDIK_pi
#print axioms prunedSemEqDIK_sorts
#print axioms prunedSemEqDIK_closedIrrPi
#print axioms prunePiSet_denDIK_eq_iff_prunedSemEqDIK
#print axioms prunedSemEqDIK_instantiate_of_prunedSemEqDIK
#print axioms prunedSemEqDIK_instantiate0_of_prunedSemEqDIK
#print axioms approxDIK_ctxEnvDIK_instantiate0_iff_of_prunedSemEqDIK
#print axioms prunedSemEqDIK_app
#print axioms prunedSemEqDIK_ctxEnvDIK_app
#print axioms prunedSemEqDIK_lam
#print axioms lrTermDSubKClosedCtxBi_subst0_of_prunedSemEqDIK_botProbe
#print axioms lrTermDSubKClosedCtxBi_subst0_pi_arg_of_botProbe
#print axioms prunePiEnv_ctxEnvDIK_letBinding_eq_iff
#print axioms approxDIK_ctxEnvDIK_letBinding_iff_of_prunedSemEqDIK
#print axioms prunedSemEqDIK_letE
#print axioms prunedSemEqDIK_ctxEnvDIK_letE
#print axioms prunedSemEqDIK_ctxEnvDIK_whStepPiKClosedCtx
#print axioms prunedSemEqDIK_ctxEnvDIK_whRedPiKClosedCtx
#print axioms iotaKClosedCtx_guard_iff_of_prunedSemEqDIK
#print axioms instantiate_bvar_lift_gap_at
#print axioms instantiate0_bvar0_lift1
#print axioms instantiate0_lift0_instantiate0_bvar1_lift2
#print axioms convT_let_self_inst0_sort
#print axioms convT_inst1_sortCongrLet
#print axioms convT_inst1_sortCongr
#print axioms convT_inst0_letCongr
#print axioms convT_inst0_assumpCongr
#print axioms lrTermDSubKClosedCtxBi_subst0_pi_body
#print axioms lrTermDSubKClosedCtxBi_of_prunedSemEqDIK_and_pi_tyConv
#print axioms lrTermDSubKClosedCtxBi_of_prunedSemEqDIK_and_no_pi_probe
#print axioms lrTermDSubKClosedCtxBi_subst0_of_prunedSemEqDIK_no_pi_probe
#print axioms lrTermDSubKClosedCtxBi_subst0_pi_arg_of_no_pi_probe

end Rcic.Declarative.NativeValleys.PiModelDeltaIotaCtxAudit

