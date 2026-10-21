import rcic.RcicNativePiModelDeltaIota
import rcic.RcicNativePiModelLRTermS
import rcic.RcicNativePiModelLRTermD
import rcic.RcicNativePiModelLRTermSubst

/-!
# RcicNativePiModelDeltaIotaTerm — Term-Level Index Transport, Admitted Obstructions, Related-Substitution Stability, Concrete δ/ι Cases, and Symmetry/Transitivity for `LRTermS` and `LRTermD`

Building on `RcicNativePiModelDeltaIota` (#7649), `RcicNativePiModelFundCases` (#7648),
`RcicNativePiModelLRTermS` / `RcicNativePiModelLRTermD` (#7646), and
`RcicNativePiModelLRTermSubst` (#7660), this module delivers nine layers:

1. **§1 — Discharging `LRTermSTransportLam` (#7646) and `LRTermSpineSplit` (#7648), plus Full Index Transport for `LRTermS` and `LRTermSDI`:**
   - Unconditional discharge of `RcicNativePiModelFundCases.LRTermSpineSplit` (`lrTermSpineSplit`).
   - Full index transport `lrTermS_transport` across **all** compacts `c : CptI` (including `.lam g`)
     using §9.1 `whDet_of_envWfT` and §14.2 `codomain_transport_of_tyConvT`, discharging
     `RcicNativePiModelLRTermS.LRTermSTransportLam` (`lrTermSTransportLam_of_typeSoundness` and
     `lrTermSTransportLam_of_botDI`).
   - The `ApproxDI` counterpart `LRTermSDI` (whose constructor-spine clause reads `A` in
     `ApproxDI E EnvI.bot A (.spine r' args')`), its expansion and universe-readback lemmas, and
     its full index transport `lrTermSDI_transport`.

2. **§2 — Full Index Transport for `LRTermDCore` and `LRTermD` (#7646) Without `WhApproxInv`, `FundamentalLRINT`, or `TypeSoundnessI`:**
   - Unfolding and expansion lemmas for `LRTermDCore` (`lrTermDCore_bot`, `lrTermDCore_sort_iff`,
     `lrTermDCore_pi_iff`, `lrTermDCore_spine_iff`, `lrTermDCore_lam_iff`, `lrTermDCore_expand`,
     `lrTypeIN_of_lrTermDCore_sort`).
   - Unconditional weak-head index invariance `lrTermDCore_whRed_index_iff` under `EnvWfT E` alone
     (with zero logical-relation hypotheses).
   - Full index transport `lrTermDCore_transport` and `lrTermD_transport` across all `c : CptI`
     using only `EnvWfT E`, the repaired non-vacuous `FundamentalLRINBotDI E n` (§12.3), and
     `PropTyTransport E n` — requiring **no** `WhApproxInvCore`, **no** `FundamentalLRINT`, and
     **no** `TypeSoundnessI`.

3. **§3 — Admitted Obstructions on Un-Restricted `LRTermS` and `LRTermD` (#7646, #7652, #7653):**
   - `not_isPropTyI_sort`: `IsPropTyI E n Γ (.sort u)` is syntactically false for every `E, n, Γ, u`.
   - Diagonal refutation at `idPiProp = .pi (.sort .zero) (.bvar 0)` and
     `idPiPropSortStep = .pi .bot [([.sort], .sort)]`: proves `not_lrTermS_idPiProp_sortStep`,
     `not_lrTermSDI_idPiProp_sortStep`, `not_lrTermDCore_idPiProp_sortStep`, and
     `not_lrTermD_idPiProp_sortStep`, unconditionally refuting `FundamentalTermS E n`,
     `FundamentalTermSDI E n`, `FundamentalTermD E n` (#7646), and `FundamentalTermD_DI E n` for
     **every** `E : ResolvedEnv` and `n : Nat`.
   - Conversion refutation at `closedIrrPi_conv` (`ConvT.irr` under `ConvT.app` + `ConvT.pi` in
     `Γ = []`): proves `whStep_app_bvar_false`, `whRed_app_bvar_eq`, and
     `not_lrTypeIN_closedIrrPi`, refuting `LRTermI`, `LRTermS`, `LRTermSDI`, `LRTermDCore`, and
     `LRTermD` on `(closedIrrPiL, closedIrrPiR, closedIrrPiCpt)` for **every** `E` and `n` —
     demonstrating that `LRTermD`'s `IsPropTyI` collapse (`irrCaseD`) does not survive
     `ConvT.app` + `ConvT.pi` into a universe unless `.pi` compacts are restricted to `BotPiCpt`
     (`not_botPiCpt_closedIrrPiCpt`, `lrTypeINBiDI_closedIrrPi`).
   - Syntactic typing inversions `hasTyT_sort_inv` and `hasTyT_pi_inv`, proving that
     `IsPropTyI E n Γ (.pi (.sort .zero) (.sort .zero))` forces universe collapse
     (`Sort 1 ~ Sort v` and `Sort (imax u v) ~ Sort 0`), and unconditional refutations of
     `LRTermS` on `ConvT.irr`/`ConvT.eta` and of `LRTermDCore` on `etaIdPiPropFn`.

4. **§4 — Weakening and Related-Substitution Stability on `BotPiCpt` and `.bvar j` (Discharging `hι` and Extending #7652):**
   - Using §14.1 `whStep_iota_instantiate` / `whRed_instantiate_of_envClosed` (discharging `#7652`'s
     `hι` premise unconditionally) and §14.3 `lrTypeIN_weaken_botPiCpt` / `lrTypeIN_subst_botPiCpt`,
     proves weakening and substitution stability of `LRTermS`, `LRTermSDI`, `LRTermDCore`, and
     `LRTermD` across **all** `BotPiCpt` compacts (`.bot`, `.sort`, and `.pi a f`), plus
     related-substitution stability at `.bvar j` (`lrTermS_subst_sort_and_bvar`,
     `lrTermSDI_subst_sort_and_bvar`, `lrTermD_subst_bvar`).

5. **§5 — Concrete δ/ι Fundamental-Lemma Cases over `ApproxDI` and the Repaired `BotPiCpt` Term Layer (`FundamentalTermBotDI`):**
   - Unconditional `WhStep`/`WhRed`/β/ζ/lit/δ/ι conversion cases for `LRTermSDI` and `LRTermD` over
     `ApproxDI E EnvI.bot` at every `EnvWfT E` (`fundConvSDI_delta`, `fundConvSDI_iota`,
     `fundConvD_DI_delta`, `fundConvD_DI_iota`).
   - The repaired `BotPiCpt`-restricted term-level fundamental lemma `FundamentalTermBotDI E n`,
     positive satisfaction on both `idPiProp` and `closedIrrPi`, and reduction to
     `FundamentalLRINBotDI E n` and `piRow` (`fundamentalLRINBotDI_of_fundamentalTermBotDI`,
     `piRow_of_fundamentalTermBotDI`, `not_tyConvT_pi_sort_of_fundamentalTermBotDI`) without
     `WhDet` or `TypeSoundness`.

6. **§6 — Structural Vacuity of `LRTermDCore`'s Data-Spine Argument Clause, Transparent-Body Characterization, and Additional #7653 Obstructions:**
   - Proves `hasTyT_idPiProp_ctx` and `isPropTyI_idPiProp` in **every** `E, n, Γ`, and shows that
     `LRTermDCore`'s existential `Ts : List (Expr Nat)` in the data-spine branch
     (`RcicNativePiModelLRTermD.lean:88-93`) is unconditionally satisfied by
     `Ts := List.replicate args.length idPiProp` (`lrTermDCore_dataSpine_args_vacuous`,
     `lrTermDCore_spine_iff_simple`).
   - Proves `not_lrTermD_etaIdPiPropFn_diag`, `not_lrTermDCore_etaK_etaIdPiPropFn`, and
     `not_lrTermD_etaK_etaIdPiPropFn` (refuting `#7653`'s `EtaDiagD`, `EtaCaseD`, and `EtaKChainD`),
     plus `polyPi = .lam (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))` at
     `polyPiCpt = .lam [([], .pi .bot [])]` (`tyConvT_pi_sort_of_lrTermDCore_polyPi`,
     `not_lrTermDCore_polyPi_of_not_pi_sort`).

7. **§7 — Symmetry and Transitivity of `LRTermS`, `LRTermSDI`, `LRTermDCore`, and `LRTermD` on Non-`λ`, `BotPiCpt`, and `FirstOrderCpt` Compacts:**
   - Proves unconditional symmetry and `EnvWfT E`-transitivity for `LRTermS`, `LRTermSDI`,
     `LRTermDCore`, and `LRTermD` across all non-`.lam` compacts (`.bot`, `.sort`, `.pi a f`,
     `.spine r args`), and transitivity across all `FirstOrderCpt` compacts (including curried
     `.lam g` compacts whose argument demands are non-`.lam`) without `WhDet`, `TypeSoundness`, or
     index transport, plus `BotPiCpt` symmetry/transitivity/type-conversion cases for
     `FundamentalTermBotDI`.

8. **§8 — Direct Discharge of `FundamentalTermIS` (#7660), Side-Condition-Free `IsPropTyI` Substitution (#7653/#7655), All-Variable (`< / = / >`) Related Substitution, and Data-Spine Substitution Stability:**
   - Discharges `RcicNativePiModelLRTermSubst.FundamentalTermIS` unconditionally via
     `whStep_iota_instantiate` (`approxSubstDI`, `fundamentalTermIS_of_envClosed`,
     `fundamentalTermIS_of_envWfT`, `fundamentalTermIS_DI`).
   - Proves `not_hasTyT_sort_zero_of_sortRow` and `isPropTyI_of_hasTyT_sort_zero` (via
     `hasTyT_sort_inv`), eliminating the syntactic `∀ l, P ≠ .sort l` and `∀ l, r ≠ .sort l` side
     conditions of `#7653` and `#7655` (`isPropTyI_weaken`, `isPropTyI_subst_of_sortRow`,
     `isPropTyI_subst_of_botDI`, `fundamentalTermDIS_of_sortRow`, `fundamentalTermDIS_of_botDI`).
   - Proves all-variable (`i < j`, `i = j`, `i > j`) related-substitution stability at `EnvI.bot`
     (`lrTermS_subst_bvar_all`, `lrTermSDI_subst_bvar_all`, `lrTermDCore_subst_bvar_all`,
     `lrTermD_subst_bvar_all`) and general `.spine r args` substitution stability for `LRTermDCore`
     and `LRTermD` across all non-recursor opaque constants (`whNormal_foldApps_of_rigidNonRec`,
     `lrTermDCore_spine_subst_of_rigidNonRec`, `lrTermD_spine_subst_of_rigidNonRec`).

9. **§9 — No-Transport Transitivity From Left-Reflexivity, Higher-Order Type-Valued Function Symmetry (`TypeValuedLamCpt`), and `LRTermD` Refutation on `polyPi`:**
   - Proves `lrTermI_noLam_symm`, `lrTermI_noLam_trans`, `lrTermI_noLam_refl_left`,
     `lrTermI_firstOrder_trans`, and general transitivity across **all** compacts `c : CptI` from
     `EnvWfT E` and left-reflexivity alone (`lrTermI_trans_of_reflLeft`,
     `lrTermS_trans_of_reflLeft`, `lrTermSDI_trans_of_reflLeft`, `lrTermDCore_trans_of_reflLeft`,
     `lrTermD_trans_of_reflLeft` — requiring zero `LRTermIndexTransport`).
   - Defines `TypeValuedLamCpt` (higher-order `.lam g` compacts with type-code outputs `.bot`,
     `.sort`, or `.pi a f`) and proves unconditional symmetry and transitivity for `LRTermI`,
     `LRTermS`, and `LRTermSDI` across all `TypeValuedLamCpt` compacts.
   - Proves `not_isPropTyI_pi_sort1_sort1` and `not_lrTermD_polyPi_of_not_pi_sort` (ruling out the
     outer `IsPropTyI` disjunct on `polyPi` / `#7652`'s `lamPiBot`), plus
     `lrTermDCore_idPiProp_lam_pi_total` and `lrTermD_idPiProp_lam_pi_total`.

`closure_claim = 0`. Zero `sorry`; axioms `⊆ {propext, Quot.sound}`.
-/

namespace Rcic.Declarative.NativeValleys.PiModelDeltaIotaTermAudit

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ## §1. Discharging `LRTermSpineSplit` (#7648) and `LRTermSTransportLam` (#7646), plus Full Index Transport for `LRTermS` and `LRTermSDI` -/

/-- Unconditional discharge of `RcicNativePiModelFundCases.LRTermSpineSplit` for every `E` and `n`. -/
theorem lrTermSpineSplit (E : ResolvedEnv) (n : Nat) : LRTermSpineSplit E n :=
  fun h => Or.inl (lrTermI_spine_forces_sort h)

/-- `.pi .bot []` approximates any `A` that weak-head reduces to `.pi A₁ B₁`, under weak-head
    invariance of `ApproxI`. -/
theorem approxI_pi_bot_of_whRed
    (hinv : ∀ {a b : Expr Nat}, WhStep E a b → ∀ ρ c, ApproxI ρ a c ↔ ApproxI ρ b c)
    {A A₁ B₁ : Expr Nat} (h : WhRed E A (.pi A₁ B₁)) :
    ApproxI EnvI.bot A (.pi .bot []) :=
  approxI_whRed_back hinv h (approxI_pi_bot_nil EnvI.bot A₁ B₁)

/-- `.pi .bot []` approximates any `A` that weak-head reduces to `.pi A₁ B₁` in `ApproxDI` at
    every `EnvWfT E` (without any `WhApproxInv` hypothesis). -/
theorem approxDI_pi_bot_of_whRed (hW : EnvWfT E)
    {A A₁ B₁ : Expr Nat} (h : WhRed E A (.pi A₁ B₁)) :
    ApproxDI E EnvI.bot A (.pi .bot []) :=
  approxDI_whRed_back hW h (approxDI_pi_bot_nil E EnvI.bot A₁ B₁)

/-- Full index transport for `LRTermS` across **all** compacts `c : CptI` (including `.lam g`),
    under `EnvWfT E` and the `BotPiCpt` fundamental lemma `FundamentalLRINBotDI E n` plus spine
    membership transport `hSp`. -/
theorem lrTermS_transport_of_botDI (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDI E n)
    (hSp : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat}, TyConvT E n Γ A A' →
      ∀ r' args', ApproxI EnvI.bot A (.spine r' args') →
        ∃ r'' args'', ApproxI EnvI.bot A' (.spine r'' args''))
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hAA' : TyConvT E n Γ A A') {M M' : Expr Nat} :
    (c : CptI) → LRTermS E n Γ M M' A c → LRTermS E n Γ M M' A' c
  | .bot, _ => lrTermS_bot _ _ _ _
  | .sort, h => by
      rw [lrTermS_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hBot hΓ hA hAA' .sort .sort (approxDI_sort_of_whRed hW hl EnvI.bot)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .pi a f, h => by
      rw [lrTermS_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hBot hΓ hA hAA' .sort .sort (approxDI_sort_of_whRed hW hl EnvI.bot)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .spine r args, h => by
      rw [lrTermS_spine_iff] at h ⊢
      rcases h with ⟨⟨l, hl⟩, h2⟩ | ⟨⟨r', args', hsp⟩, Y, Y', hY, hY', hn, hn', ⟨hc⟩⟩
      · have hs := hBot hΓ hA hAA' .sort .sort (approxDI_sort_of_whRed hW hl EnvI.bot)
        cases hs with
        | sort _ hl' => exact Or.inl ⟨⟨_, hl'⟩, h2⟩
      · exact Or.inr ⟨hSp hΓ hAA' r' args' hsp, Y, Y', hY, hY', hn, hn',
          ⟨convT_of_tyConv hc hAA'⟩⟩
  | .lam g, h => by
      rw [lrTermS_lam_iff] at h ⊢
      obtain ⟨A₁, B₁, w, hAred, ⟨cΓ₁⟩, ⟨cB₁⟩, happ⟩ := h
      have hpi : LRTypeIN E n Γ A A' (.pi .bot []) :=
        hBot hΓ hA hAA' (.pi .bot []) botPiCpt_pi_bot_nil (approxDI_pi_bot_of_whRed hW hAred)
      cases hpi with
      | @pi _ _ _ A₁' B₁' A₂ B₂ _ _ h1 h2 _ hdom hcod _ _ =>
          have heq := whRed_normal_unique_of_envWfT hW hAred (whNormal_pi _ _) h1 (whNormal_pi _ _)
          injection heq with eA eB
          subst eA; subst eB
          have hA₁ : ∃ u₁, Nonempty (HasTyT E n Γ A₁ (.sort u₁)) := by
            cases cΓ₁ with
            | assumption _ _ u₁ _ hA₁ => exact ⟨u₁, ⟨hA₁⟩⟩
          obtain ⟨u₁, ⟨hA₁⟩⟩ := hA₁
          obtain ⟨u₂, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          obtain ⟨hΓ₂, _, _, w₂, hB₂⟩ := codomain_transport_of_tyConvT hW hΓ hA₂ hdom cB₁ hcod
          have hdom_symm : TyConvT E n Γ A₂ A₁ := hdom.symmT
          refine ⟨A₂, B₂, w₂, h2, hΓ₂, hB₂, fun s hs N N' hN₂ hN'₂ hrel₂ => ?_⟩
          have hN₁ : HasTyT E n Γ N A₁ := hasTyT_of_tyConv hN₂ hdom_symm
          have hN'₁ : HasTyT E n Γ N' A₁ := hasTyT_of_tyConv hN'₂ hdom_symm
          have hrel₁ : ∀ u₀ ∈ s.1, LRTermS E n Γ N N' A₁ u₀ := fun u₀ hu₀ =>
            lrTermS_transport_of_botDI hW hBot hSp hΓ hA₂ hdom_symm u₀ (hrel₂ u₀ hu₀)
          have hout₁ : LRTermS E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2 :=
            happ s hs N N' hN₁ hN'₁ hrel₁
          have hB₁N : HasTyT E n Γ (instantiate0 N B₁) (.sort w) :=
            hasTyT_subst0_of_envWfT hW cB₁ hN₁
          have hB₁B₂N : TyConvT E n Γ (instantiate0 N B₁) (instantiate0 N B₂) :=
            tyConvT_subst0_of_envWfT hW hN₁ hcod
          exact lrTermS_transport_of_botDI hW hBot hSp hΓ hB₁N hB₁B₂N s.2 hout₁
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u₀ ∈ s.1 from ‹_›)
    have h₃ := sizeOfS_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOfS_snd_lt s
    omega

/-- Discharge of `LRTermSTransportLam` from `EnvWfT E`, `FundamentalLRINBotDI E n`, and spine
    membership transport `hSp`. -/
theorem lrTermSTransportLam_of_botDI (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDI E n)
    (hSp : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat}, TyConvT E n Γ A A' →
      ∀ r' args', ApproxI EnvI.bot A (.spine r' args') →
        ∃ r'' args'', ApproxI EnvI.bot A' (.spine r'' args'')) :
    LRTermSTransportLam E n :=
  fun {_} hΓ {_ _ _} hA hAA' {_ _} g h =>
    lrTermS_transport_of_botDI hW hBot hSp hΓ hA hAA' (.lam g) h

/-- Full index transport for `LRTermS` across **all** compacts `c : CptI` under the exact
    hypotheses of `lrTermS_transport_typeCode` (`RcicNativePiModelLRTermS.lean:156`) plus `EnvWfT E`. -/
theorem lrTermS_transport (hW : EnvWfT E)
    (hinv : ∀ {a b : Expr Nat}, WhStep E a b → ∀ ρ c, ApproxI ρ a c ↔ ApproxI ρ b c)
    (hT : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
      HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' → ∀ c, ApproxI EnvI.bot A c →
      LRTypeIN E n Γ A A' c)
    (hS : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat}, TyConvT E n Γ A A' →
      ∀ c, ApproxI EnvI.bot A c → ApproxI EnvI.bot A' c)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hAA' : TyConvT E n Γ A A') {M M' : Expr Nat} :
    (c : CptI) → LRTermS E n Γ M M' A c → LRTermS E n Γ M M' A' c
  | .bot, _ => lrTermS_bot _ _ _ _
  | .sort, h => lrTermS_transport_typeCode hinv hT hS hΓ hA hAA' .sort (fun _ h => nomatch h) h
  | .pi a f, h => lrTermS_transport_typeCode hinv hT hS hΓ hA hAA' (.pi a f) (fun _ h => nomatch h) h
  | .spine r args, h =>
      lrTermS_transport_typeCode hinv hT hS hΓ hA hAA' (.spine r args) (fun _ h => nomatch h) h
  | .lam g, h => by
      rw [lrTermS_lam_iff] at h ⊢
      obtain ⟨A₁, B₁, w, hAred, ⟨cΓ₁⟩, ⟨cB₁⟩, happ⟩ := h
      have hpi : LRTypeIN E n Γ A A' (.pi .bot []) :=
        hT hΓ hA hAA' (.pi .bot []) (approxI_pi_bot_of_whRed hinv hAred)
      cases hpi with
      | @pi _ _ _ A₁' B₁' A₂ B₂ _ _ h1 h2 _ hdom hcod _ _ =>
          have heq := whRed_normal_unique_of_envWfT hW hAred (whNormal_pi _ _) h1 (whNormal_pi _ _)
          injection heq with eA eB
          subst eA; subst eB
          have hA₁ : ∃ u₁, Nonempty (HasTyT E n Γ A₁ (.sort u₁)) := by
            cases cΓ₁ with
            | assumption _ _ u₁ _ hA₁ => exact ⟨u₁, ⟨hA₁⟩⟩
          obtain ⟨u₁, ⟨hA₁⟩⟩ := hA₁
          obtain ⟨u₂, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          obtain ⟨hΓ₂, _, _, w₂, hB₂⟩ := codomain_transport_of_tyConvT hW hΓ hA₂ hdom cB₁ hcod
          have hdom_symm : TyConvT E n Γ A₂ A₁ := hdom.symmT
          refine ⟨A₂, B₂, w₂, h2, hΓ₂, hB₂, fun s hs N N' hN₂ hN'₂ hrel₂ => ?_⟩
          have hN₁ : HasTyT E n Γ N A₁ := hasTyT_of_tyConv hN₂ hdom_symm
          have hN'₁ : HasTyT E n Γ N' A₁ := hasTyT_of_tyConv hN'₂ hdom_symm
          have hrel₁ : ∀ u₀ ∈ s.1, LRTermS E n Γ N N' A₁ u₀ := fun u₀ hu₀ =>
            lrTermS_transport hW hinv hT hS hΓ hA₂ hdom_symm u₀ (hrel₂ u₀ hu₀)
          have hout₁ : LRTermS E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2 :=
            happ s hs N N' hN₁ hN'₁ hrel₁
          have hB₁N : HasTyT E n Γ (instantiate0 N B₁) (.sort w) :=
            hasTyT_subst0_of_envWfT hW cB₁ hN₁
          have hB₁B₂N : TyConvT E n Γ (instantiate0 N B₁) (instantiate0 N B₂) :=
            tyConvT_subst0_of_envWfT hW hN₁ hcod
          exact lrTermS_transport hW hinv hT hS hΓ hB₁N hB₁B₂N s.2 hout₁
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u₀ ∈ s.1 from ‹_›)
    have h₃ := sizeOfS_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOfS_snd_lt s
    omega

/-- Discharge of `RcicNativePiModelLRTermS.LRTermSTransportLam` under the hypotheses of
    `lrTermS_transport_typeCode` plus `EnvWfT E`. -/
theorem lrTermSTransportLam_of_typeSoundness (hW : EnvWfT E)
    (hinv : ∀ {a b : Expr Nat}, WhStep E a b → ∀ ρ c, ApproxI ρ a c ↔ ApproxI ρ b c)
    (hT : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
      HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' → ∀ c, ApproxI EnvI.bot A c →
      LRTypeIN E n Γ A A' c)
    (hS : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat}, TyConvT E n Γ A A' →
      ∀ c, ApproxI EnvI.bot A c → ApproxI EnvI.bot A' c) :
    LRTermSTransportLam E n :=
  fun {_} hΓ {_ _ _} hA hAA' {_ _} g h =>
    lrTermS_transport hW hinv hT hS hΓ hA hAA' (.lam g) h

/-- The `ApproxDI` counterpart of `LRTermS`: identical to `LRTermS` except the constructor-spine
    reading checks `ApproxDI E EnvI.bot A (.spine r' args')` so transparent definitions and
    recursors in `A` are interpreted by `ApproxDI`. -/
def LRTermSDI (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : CptI → Prop
  | .bot => True
  | .sort => (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' .sort
  | .pi a f => (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.pi a f)
  | .spine r args =>
      ((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
      ((∃ r' args', ApproxDI E EnvI.bot A (.spine r' args')) ∧
        ∃ Y Y', WhRed E M Y ∧ WhRed E M' Y' ∧ WhNormal E Y ∧ WhNormal E Y' ∧
          Nonempty (ConvT E n Γ Y Y' A))
  | .lam g =>
      ∃ A₁ B₁ w, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          (∀ u ∈ s.1, LRTermSDI E n Γ N N' A₁ u) →
          LRTermSDI E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
    have h₃ := sizeOfS_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOfS_snd_lt s
    omega

theorem lrTermSDI_bot (Γ : LCtx) (M M' A : Expr Nat) : LRTermSDI E n Γ M M' A .bot := by
  rw [LRTermSDI]; trivial

theorem lrTermSDI_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermSDI E n Γ M M' A .sort ↔ (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' .sort := by
  rw [LRTermSDI]

theorem lrTermSDI_pi_iff (Γ : LCtx) (M M' A : Expr Nat) (a : CptI) (f : List (List CptI × CptI)) :
    LRTermSDI E n Γ M M' A (.pi a f) ↔
      (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.pi a f) := by
  rw [LRTermSDI]

theorem lrTermSDI_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptI) :
    LRTermSDI E n Γ M M' A (.spine r args) ↔
      ((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
      ((∃ r' args', ApproxDI E EnvI.bot A (.spine r' args')) ∧
        ∃ Y Y', WhRed E M Y ∧ WhRed E M' Y' ∧ WhNormal E Y ∧ WhNormal E Y' ∧
          Nonempty (ConvT E n Γ Y Y' A)) := by
  rw [LRTermSDI]

theorem lrTermSDI_lam_iff (Γ : LCtx) (M M' A : Expr Nat) (g : List (List CptI × CptI)) :
    LRTermSDI E n Γ M M' A (.lam g) ↔
      ∃ A₁ B₁ w, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          (∀ u ∈ s.1, LRTermSDI E n Γ N N' A₁ u) →
          LRTermSDI E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2 := by
  rw [LRTermSDI]

/-- Closure of `LRTermSDI` under weak-head expansion on both sides. -/
theorem lrTermSDI_expand {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRed E M X) (hX' : WhRed E M' X') :
    (u : CptI) → LRTermSDI E n Γ X X' A u → LRTermSDI E n Γ M M' A u
  | .bot, _ => lrTermSDI_bot _ _ _ _
  | .sort, h => by
      rw [lrTermSDI_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .pi a f, h => by
      rw [lrTermSDI_pi_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .spine r args, h => by
      rw [lrTermSDI_spine_iff] at h ⊢
      rcases h with ⟨h1, h2⟩ | ⟨h1, Y, Y', hY, hY', hn, hn', hc⟩
      · exact Or.inl ⟨h1, lrTypeIN_expand hX hX' h2⟩
      · exact Or.inr ⟨h1, Y, Y', whRed_trans hX hY, whRed_trans hX' hY', hn, hn', hc⟩
  | .lam g, h => by
      rw [lrTermSDI_lam_iff] at h ⊢
      obtain ⟨A₁, B₁, w, hA, hΓ₁, hB₁, happ⟩ := h
      refine ⟨A₁, B₁, w, hA, hΓ₁, hB₁, fun s hs N N' hN hN' hrel => ?_⟩
      exact lrTermSDI_expand (whRedS_appHead hX) (whRedS_appHead hX') s.2
        (happ s hs N N' hN hN' hrel)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOfS_snd_lt s
  omega

/-- A universe is never accepted as a step function in `LRTermSDI`. -/
theorem lrTermSDI_lam_at_sort_false {Γ : LCtx} {M M' : Expr Nat} {u : Level}
    {g : List (List CptI × CptI)} (h : LRTermSDI E n Γ M M' (.sort u) (.lam g)) : False := by
  rw [lrTermSDI_lam_iff] at h
  obtain ⟨A₁, B₁, _, hA, _, _, _⟩ := h
  exact nomatch whRed_sort_eq hA

/-- At a universe, `LRTermSDI` at a spine compact forces the type-code reading. -/
theorem lrTermSDI_spine_at_sort {Γ : LCtx} {M M' : Expr Nat} {u : Level} {r : Nat} {args : List CptI}
    (h : LRTermSDI E n Γ M M' (.sort u) (.spine r args)) : LRTypeIN E n Γ M M' (.spine r args) := by
  rw [lrTermSDI_spine_iff] at h
  rcases h with ⟨_, h2⟩ | ⟨⟨r', args', hsp⟩, _⟩
  · exact h2
  · rcases approxDI_sort_inv hsp with h0 | h0 <;> cases h0

/-- Extracting `LRTypeIN` from `LRTermSDI` at a universe `.sort u`. -/
theorem lrTypeIN_of_lrTermSDI_sort {Γ : LCtx} {M M' : Expr Nat} {u : Level} :
    (c : CptI) → LRTermSDI E n Γ M M' (.sort u) c → LRTypeIN E n Γ M M' c
  | .bot, _ => .bot _ _ _
  | .sort, h => ((lrTermSDI_sort_iff _ _ _ _).mp h).2
  | .pi _ _, h => ((lrTermSDI_pi_iff _ _ _ _ _ _).mp h).2
  | .spine _ _, h => lrTermSDI_spine_at_sort h
  | .lam _, h => (lrTermSDI_lam_at_sort_false h).elim

/-- Full index transport for `LRTermSDI` across all `c : CptI` under `EnvWfT E`,
    `FundamentalLRINBotDI E n`, and `ApproxDI` spine-membership transport `hSp`. -/
theorem lrTermSDI_transport (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDI E n)
    (hSp : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat}, TyConvT E n Γ A A' →
      ∀ r' args', ApproxDI E EnvI.bot A (.spine r' args') →
        ∃ r'' args'', ApproxDI E EnvI.bot A' (.spine r'' args''))
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hAA' : TyConvT E n Γ A A') {M M' : Expr Nat} :
    (c : CptI) → LRTermSDI E n Γ M M' A c → LRTermSDI E n Γ M M' A' c
  | .bot, _ => lrTermSDI_bot _ _ _ _
  | .sort, h => by
      rw [lrTermSDI_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hBot hΓ hA hAA' .sort .sort (approxDI_sort_of_whRed hW hl EnvI.bot)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .pi a f, h => by
      rw [lrTermSDI_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hBot hΓ hA hAA' .sort .sort (approxDI_sort_of_whRed hW hl EnvI.bot)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .spine r args, h => by
      rw [lrTermSDI_spine_iff] at h ⊢
      rcases h with ⟨⟨l, hl⟩, h2⟩ | ⟨⟨r', args', hsp⟩, Y, Y', hY, hY', hn, hn', ⟨hc⟩⟩
      · have hs := hBot hΓ hA hAA' .sort .sort (approxDI_sort_of_whRed hW hl EnvI.bot)
        cases hs with
        | sort _ hl' => exact Or.inl ⟨⟨_, hl'⟩, h2⟩
      · exact Or.inr ⟨hSp hΓ hAA' r' args' hsp, Y, Y', hY, hY', hn, hn',
          ⟨convT_of_tyConv hc hAA'⟩⟩
  | .lam g, h => by
      rw [lrTermSDI_lam_iff] at h ⊢
      obtain ⟨A₁, B₁, w, hAred, ⟨cΓ₁⟩, ⟨cB₁⟩, happ⟩ := h
      have hpi : LRTypeIN E n Γ A A' (.pi .bot []) :=
        hBot hΓ hA hAA' (.pi .bot []) botPiCpt_pi_bot_nil (approxDI_pi_bot_of_whRed hW hAred)
      cases hpi with
      | @pi _ _ _ A₁' B₁' A₂ B₂ _ _ h1 h2 _ hdom hcod _ _ =>
          have heq := whRed_normal_unique_of_envWfT hW hAred (whNormal_pi _ _) h1 (whNormal_pi _ _)
          injection heq with eA eB
          subst eA; subst eB
          have hA₁ : ∃ u₁, Nonempty (HasTyT E n Γ A₁ (.sort u₁)) := by
            cases cΓ₁ with
            | assumption _ _ u₁ _ hA₁ => exact ⟨u₁, ⟨hA₁⟩⟩
          obtain ⟨u₁, ⟨hA₁⟩⟩ := hA₁
          obtain ⟨u₂, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          obtain ⟨hΓ₂, _, _, w₂, hB₂⟩ := codomain_transport_of_tyConvT hW hΓ hA₂ hdom cB₁ hcod
          have hdom_symm : TyConvT E n Γ A₂ A₁ := hdom.symmT
          refine ⟨A₂, B₂, w₂, h2, hΓ₂, hB₂, fun s hs N N' hN₂ hN'₂ hrel₂ => ?_⟩
          have hN₁ : HasTyT E n Γ N A₁ := hasTyT_of_tyConv hN₂ hdom_symm
          have hN'₁ : HasTyT E n Γ N' A₁ := hasTyT_of_tyConv hN'₂ hdom_symm
          have hrel₁ : ∀ u₀ ∈ s.1, LRTermSDI E n Γ N N' A₁ u₀ := fun u₀ hu₀ =>
            lrTermSDI_transport hW hBot hSp hΓ hA₂ hdom_symm u₀ (hrel₂ u₀ hu₀)
          have hout₁ : LRTermSDI E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2 :=
            happ s hs N N' hN₁ hN'₁ hrel₁
          have hB₁N : HasTyT E n Γ (instantiate0 N B₁) (.sort w) :=
            hasTyT_subst0_of_envWfT hW cB₁ hN₁
          have hB₁B₂N : TyConvT E n Γ (instantiate0 N B₁) (instantiate0 N B₂) :=
            tyConvT_subst0_of_envWfT hW hN₁ hcod
          exact lrTermSDI_transport hW hBot hSp hΓ hB₁N hB₁B₂N s.2 hout₁
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u₀ ∈ s.1 from ‹_›)
    have h₃ := sizeOfS_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOfS_snd_lt s
    omega

/-! ## §2. Full Index Transport for `LRTermDCore` and `LRTermD` (#7646) Without `WhApproxInv`, `FundamentalLRINT`, or `TypeSoundnessI` -/

theorem lrTermDCore_bot (Γ : LCtx) (M M' A : Expr Nat) : LRTermDCore E n Γ M M' A .bot := by
  rw [LRTermDCore.eq_def]; trivial

theorem lrTermDCore_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRTermDCore E n Γ M M' A .sort ↔ (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' .sort := by
  rw [LRTermDCore.eq_def]

theorem lrTermDCore_pi_iff (Γ : LCtx) (M M' A : Expr Nat) (a : CptI) (f : List (List CptI × CptI)) :
    LRTermDCore E n Γ M M' A (.pi a f) ↔
      (∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.pi a f) := by
  rw [LRTermDCore.eq_def]

theorem lrTermDCore_spine_iff (Γ : LCtx) (M M' A : Expr Nat) (r : Nat) (args : List CptI) :
    LRTermDCore E n Γ M M' A (.spine r args) ↔
      ((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
      (∃ ls₁ ls₂ args₁ args₂,
        WhRed E M (foldApps (.const r ls₁) args₁) ∧
        WhRed E M' (foldApps (.const r ls₂) args₂) ∧
        WhNormal E (foldApps (.const r ls₁) args₁) ∧
        WhNormal E (foldApps (.const r ls₂) args₂) ∧
        Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
          (foldApps (.const r ls₂) args₂) A) ∧
        ∃ (Ts : List (Expr Nat)) (hb1 : args.length ≤ args₁.length)
          (hb2 : args.length ≤ args₂.length) (hl : args.length = Ts.length),
          ∀ i : Fin args.length,
            IsPropTyI E n Γ (Ts.get (i.cast hl)) ∨
            LRTermDCore E n Γ (args₁.get (i.castLE hb1)) (args₂.get (i.castLE hb2))
              (Ts.get (i.cast hl)) (args.get i)) := by
  rw [LRTermDCore.eq_def]

theorem lrTermDCore_lam_iff (Γ : LCtx) (M M' A : Expr Nat) (g : List (List CptI × CptI)) :
    LRTermDCore E n Γ M M' A (.lam g) ↔
      ∃ A₁ B₁ w, WhRed E A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          (∀ u ∈ s.1, LRTermDCore E n Γ N N' A₁ u) →
          (IsPropTyI E n Γ (instantiate0 N B₁) ∨
            LRTermDCore E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2) := by
  rw [LRTermDCore.eq_def]

/-- Closure of `LRTermDCore` under weak-head expansion on both sides. -/
theorem lrTermDCore_expand {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRed E M X) (hX' : WhRed E M' X') :
    (u : CptI) → LRTermDCore E n Γ X X' A u → LRTermDCore E n Γ M M' A u
  | .bot, _ => lrTermDCore_bot _ _ _ _
  | .sort, h => by
      rw [lrTermDCore_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .pi a f, h => by
      rw [lrTermDCore_pi_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_expand hX hX' h.2⟩
  | .spine r args, h => by
      rw [lrTermDCore_spine_iff] at h ⊢
      rcases h with ⟨h1, h2⟩ | ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, hc, Ts, hb1, hb2, hl, harg⟩
      · exact Or.inl ⟨h1, lrTypeIN_expand hX hX' h2⟩
      · exact Or.inr ⟨ls₁, ls₂, args₁, args₂, whRed_trans hX h1, whRed_trans hX' h2,
          n1, n2, hc, Ts, hb1, hb2, hl, harg⟩
  | .lam g, h => by
      rw [lrTermDCore_lam_iff] at h ⊢
      obtain ⟨A₁, B₁, w, hA, hΓ₁, hB₁, happ⟩ := h
      refine ⟨A₁, B₁, w, hA, hΓ₁, hB₁, fun s hs N N' hN hN' hrel => ?_⟩
      rcases happ s hs N N' hN hN' hrel with hP | hcore
      · exact Or.inl hP
      · exact Or.inr (lrTermDCore_expand (whRedD_appHead hX) (whRedD_appHead hX') s.2 hcore)
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOfD_snd_lt s
  omega

/-- Extracting `LRTypeIN` from `LRTermDCore` at a universe `.sort u`. -/
theorem lrTypeIN_of_lrTermDCore_sort {Γ : LCtx} {M M' : Expr Nat} {u : Level}
    (c : CptI) (h : LRTermDCore E n Γ M M' (.sort u) c) : LRTypeIN E n Γ M M' c :=
  lrTypeIN_of_lrTermD_sort c (Or.inr h)

/-- Under `EnvWfT E` alone (with **zero** logical-relation hypotheses), weak-head reduction
    `WhRed E A A'` along a `TyConvT E n Γ A A'` chain preserves `LRTermDCore` in both directions
    at every compact `c : CptI`. -/
theorem lrTermDCore_whRed_index_iff (hW : EnvWfT E)
    {Γ : LCtx} {A A' M M' : Expr Nat} (hred : WhRed E A A') (hconv : TyConvT E n Γ A A')
    (c : CptI) :
    LRTermDCore E n Γ M M' A c ↔ LRTermDCore E n Γ M M' A' c := by
  have hdet : WhDet E := whDet_of_envWfT hW
  have hsort : (∃ l, WhRed E A (.sort l)) ↔ (∃ l, WhRed E A' (.sort l)) := by
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨l, ?_⟩
      clear hconv
      induction hred with
      | refl => exact hl
      | step hs _ ih =>
          cases hl with
          | refl => exact (whStep_sort_false hs).elim
          | step hs' hrest =>
              have := hdet hs hs'
              subst this
              exact ih hrest
    · rintro ⟨l, hl'⟩
      exact ⟨l, whRed_trans hred hl'⟩
  have hpi : ∀ A₁ B₁, WhRed E A (.pi A₁ B₁) ↔ WhRed E A' (.pi A₁ B₁) := by
    intro A₁ B₁
    constructor
    · intro hl
      clear hconv hsort
      induction hred with
      | refl => exact hl
      | step hs _ ih =>
          cases hl with
          | refl => exact (whStep_pi_false hs).elim
          | step hs' hrest =>
              have := hdet hs hs'
              subst this
              exact ih hrest
    · intro hl'
      exact whRed_trans hred hl'
  cases c with
  | bot =>
      simp only [lrTermDCore_bot]
  | sort =>
      rw [lrTermDCore_sort_iff, lrTermDCore_sort_iff, hsort]
  | pi a f =>
      rw [lrTermDCore_pi_iff, lrTermDCore_pi_iff, hsort]
  | spine r args =>
      rw [lrTermDCore_spine_iff, lrTermDCore_spine_iff, hsort]
      refine or_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, ⟨hc⟩, Ts, hb1, hb2, hl, harg⟩
        exact ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, ⟨convT_of_tyConv hc hconv⟩,
          Ts, hb1, hb2, hl, harg⟩
      · rintro ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, ⟨hc⟩, Ts, hb1, hb2, hl, harg⟩
        exact ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, ⟨convT_of_tyConv hc hconv.symmT⟩,
          Ts, hb1, hb2, hl, harg⟩
  | lam g =>
      rw [lrTermDCore_lam_iff, lrTermDCore_lam_iff]
      constructor
      · rintro ⟨A₁, B₁, w, hA, hΓ₁, hB₁, happ⟩
        exact ⟨A₁, B₁, w, (hpi A₁ B₁).mp hA, hΓ₁, hB₁, happ⟩
      · rintro ⟨A₁, B₁, w, hA', hΓ₁, hB₁, happ⟩
        exact ⟨A₁, B₁, w, (hpi A₁ B₁).mpr hA', hΓ₁, hB₁, happ⟩

/-- Transport of `IsPropTyI` along a `TyConvT` chain (needed when transporting the proposition
    disjunct `IsPropTyI E n Γ (instantiate0 N B₁)` inside `LRTermDCore`'s `.lam` clause and at the
    top level of `LRTermD`). -/
def PropTyTransport (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' → IsPropTyI E n Γ A → IsPropTyI E n Γ A'

/-- Full index transport for `LRTermDCore` across **all** compacts `c : CptI` using **only**
    `EnvWfT E`, `FundamentalLRINBotDI E n` (§12.3), and `PropTyTransport E n` — requiring **no**
    `WhApproxInvCore`, **no** `FundamentalLRINT`, and **no** `TypeSoundnessI`. -/
theorem lrTermDCore_transport (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDI E n)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hAA' : TyConvT E n Γ A A') {M M' : Expr Nat} :
    (c : CptI) → LRTermDCore E n Γ M M' A c → LRTermDCore E n Γ M M' A' c
  | .bot, _ => lrTermDCore_bot _ _ _ _
  | .sort, h => by
      rw [lrTermDCore_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hBot hΓ hA hAA' .sort .sort (approxDI_sort_of_whRed hW hl EnvI.bot)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .pi a f, h => by
      rw [lrTermDCore_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hBot hΓ hA hAA' .sort .sort (approxDI_sort_of_whRed hW hl EnvI.bot)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .spine r args, h => by
      rw [lrTermDCore_spine_iff] at h ⊢
      rcases h with ⟨⟨l, hl⟩, h2⟩ | ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, ⟨hc⟩, Ts, hb1, hb2, hl, harg⟩
      · have hs := hBot hΓ hA hAA' .sort .sort (approxDI_sort_of_whRed hW hl EnvI.bot)
        cases hs with
        | sort _ hl' => exact Or.inl ⟨⟨_, hl'⟩, h2⟩
      · exact Or.inr ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2,
          ⟨convT_of_tyConv hc hAA'⟩, Ts, hb1, hb2, hl, harg⟩
  | .lam g, h => by
      rw [lrTermDCore_lam_iff] at h ⊢
      obtain ⟨A₁, B₁, w, hAred, ⟨cΓ₁⟩, ⟨cB₁⟩, happ⟩ := h
      have hpi : LRTypeIN E n Γ A A' (.pi .bot []) :=
        hBot hΓ hA hAA' (.pi .bot []) botPiCpt_pi_bot_nil (approxDI_pi_bot_of_whRed hW hAred)
      cases hpi with
      | @pi _ _ _ A₁' B₁' A₂ B₂ _ _ h1 h2 _ hdom hcod _ _ =>
          have heq := whRed_normal_unique_of_envWfT hW hAred (whNormal_pi _ _) h1 (whNormal_pi _ _)
          injection heq with eA eB
          subst eA; subst eB
          have hA₁ : ∃ u₁, Nonempty (HasTyT E n Γ A₁ (.sort u₁)) := by
            cases cΓ₁ with
            | assumption _ _ u₁ _ hA₁ => exact ⟨u₁, ⟨hA₁⟩⟩
          obtain ⟨u₁, ⟨hA₁⟩⟩ := hA₁
          obtain ⟨u₂, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          obtain ⟨hΓ₂, _, _, w₂, hB₂⟩ := codomain_transport_of_tyConvT hW hΓ hA₂ hdom cB₁ hcod
          have hdom_symm : TyConvT E n Γ A₂ A₁ := hdom.symmT
          refine ⟨A₂, B₂, w₂, h2, hΓ₂, hB₂, fun s hs N N' hN₂ hN'₂ hrel₂ => ?_⟩
          have hN₁ : HasTyT E n Γ N A₁ := hasTyT_of_tyConv hN₂ hdom_symm
          have hN'₁ : HasTyT E n Γ N' A₁ := hasTyT_of_tyConv hN'₂ hdom_symm
          have hrel₁ : ∀ u₀ ∈ s.1, LRTermDCore E n Γ N N' A₁ u₀ := fun u₀ hu₀ =>
            lrTermDCore_transport hW hBot hProp hΓ hA₂ hdom_symm u₀ (hrel₂ u₀ hu₀)
          have hB₁N : HasTyT E n Γ (instantiate0 N B₁) (.sort w) :=
            hasTyT_subst0_of_envWfT hW cB₁ hN₁
          have hB₁B₂N : TyConvT E n Γ (instantiate0 N B₁) (instantiate0 N B₂) :=
            tyConvT_subst0_of_envWfT hW hN₁ hcod
          rcases happ s hs N N' hN₁ hN'₁ hrel₁ with hP | hout₁
          · exact Or.inl (hProp hΓ hB₁N hB₁B₂N hP)
          · exact Or.inr (lrTermDCore_transport hW hBot hProp hΓ hB₁N hB₁B₂N s.2 hout₁)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₂ := List.sizeOf_lt_of_mem (show u₀ ∈ s.1 from ‹_›)
    have h₃ := sizeOfD_fst_lt s
    omega
  · have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
    have h₃ := sizeOfD_snd_lt s
    omega

/-- Full index transport for `LRTermD` across **all** compacts `c : CptI` using only `EnvWfT E`,
    `FundamentalLRINBotDI E n`, and `PropTyTransport E n`. -/
theorem lrTermD_transport (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDI E n)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hAA' : TyConvT E n Γ A A') {M M' : Expr Nat}
    (c : CptI) (h : LRTermD E n Γ M M' A c) :
    LRTermD E n Γ M M' A' c := by
  rcases h with hP | hcore
  · exact Or.inl (hProp hΓ hA hAA' hP)
  · exact Or.inr (lrTermDCore_transport hW hBot hProp hΓ hA hAA' c hcore)

/-- The `LRTermD` counterpart of `LRTermSTransportLam`. -/
def LRTermDTransportLam (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
    TyConvT E n Γ A A' → ∀ {M M' : Expr Nat} (g : List (List CptI × CptI)),
      LRTermD E n Γ M M' A (.lam g) → LRTermD E n Γ M M' A' (.lam g)

/-- Discharge of `LRTermDTransportLam` from `EnvWfT E`, `FundamentalLRINBotDI E n`, and
    `PropTyTransport E n`. -/
theorem lrTermDTransportLam_of_botDI (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDI E n)
    (hProp : PropTyTransport E n) :
    LRTermDTransportLam E n :=
  fun {_} hΓ {_ _ _} hA hAA' {_ _} g h =>
    lrTermD_transport hW hBot hProp hΓ hA hAA' (.lam g) h

/-! ## §3. Admitted Obstructions on Un-Restricted `LRTermS` and `LRTermD` (#7646, #7652, #7653) -/

/-- A literal universe `.sort u` never satisfies `IsPropTyI` in any environment or context. -/
theorem not_isPropTyI_sort (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (u : Level) :
    ¬ IsPropTyI E n Γ (.sort u) :=
  fun ⟨_, hns⟩ => hns u rfl

/-- Unconditional refutation of `LRTermS` at `idPiProp = .pi (.sort .zero) (.bvar 0)` and
    `idPiPropSortStep = .pi .bot [([.sort], .sort)]` for every `E : ResolvedEnv`, `n : Nat`,
    and `u : Level`. -/
theorem not_lrTermS_idPiProp_sortStep (E : ResolvedEnv) (n : Nat) {u : Level} :
    ¬ LRTermS E n [] idPiProp idPiProp (.sort u) idPiPropSortStep :=
  fun h => not_lrTypeIN_idPiProp_sortStep E n (lrTypeIN_of_lrTermS_sort idPiPropSortStep h)

/-- Unconditional refutation of `LRTermSDI` at `idPiProp` and `idPiPropSortStep` for every `E, n, u`. -/
theorem not_lrTermSDI_idPiProp_sortStep (E : ResolvedEnv) (n : Nat) {u : Level} :
    ¬ LRTermSDI E n [] idPiProp idPiProp (.sort u) idPiPropSortStep :=
  fun h => not_lrTypeIN_idPiProp_sortStep E n (lrTypeIN_of_lrTermSDI_sort idPiPropSortStep h)

/-- Unconditional refutation of `LRTermDCore` at `idPiProp` and `idPiPropSortStep` for every `E, n, u`. -/
theorem not_lrTermDCore_idPiProp_sortStep (E : ResolvedEnv) (n : Nat) {u : Level} :
    ¬ LRTermDCore E n [] idPiProp idPiProp (.sort u) idPiPropSortStep :=
  fun h => not_lrTypeIN_idPiProp_sortStep E n (lrTypeIN_of_lrTermDCore_sort idPiPropSortStep h)

/-- Unconditional refutation of `LRTermD` (`RcicNativePiModelLRTermD`, #7646) at `idPiProp` and
    `idPiPropSortStep` for every `E : ResolvedEnv`, `n : Nat`, and `u : Level` (because `A = .sort u`
    is a literal sort, so `IsPropTyI E n [] (.sort u)` is syntactically false). -/
theorem not_lrTermD_idPiProp_sortStep (E : ResolvedEnv) (n : Nat) {u : Level} :
    ¬ LRTermD E n [] idPiProp idPiProp (.sort u) idPiPropSortStep :=
  fun h => not_lrTypeIN_idPiProp_sortStep E n (lrTypeIN_of_lrTermD_sort idPiPropSortStep h)

/-- The environment-`⊥` fundamental lemma for `LRTermS` over `ApproxI`. -/
def FundamentalTermS (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ u, ApproxI EnvI.bot M u → LRTermS E n Γ M M A u) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ u, ApproxI EnvI.bot M u → LRTermS E n Γ M M' A u)

/-- The environment-`⊥` fundamental lemma for `LRTermSDI` over `ApproxDI`. -/
def FundamentalTermSDI (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ u, ApproxDI E EnvI.bot M u → LRTermSDI E n Γ M M A u) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ u, ApproxDI E EnvI.bot M u → LRTermSDI E n Γ M M' A u)

/-- The environment-`⊥` fundamental lemma for `LRTermD` over `ApproxDI`. -/
def FundamentalTermD_DI (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ u, ApproxDI E EnvI.bot M u → LRTermD E n Γ M M A u) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ u, ApproxDI E EnvI.bot M u → LRTermD E n Γ M M' A u)

/-- **Admitted Obstruction (`not_fundamentalTermS`)**: `FundamentalTermS E n` is unconditionally
    false for **every** `E : ResolvedEnv` and `n : Nat`. -/
theorem not_fundamentalTermS (E : ResolvedEnv) (n : Nat) : ¬ FundamentalTermS E n :=
  fun F => not_lrTermS_idPiProp_sortStep E n
    (F.1 .nil (hasTyT_idPiProp E n) idPiPropSortStep approxI_idPiProp_sortStep)

/-- **Admitted Obstruction (`not_fundamentalTermSDI`)**: `FundamentalTermSDI E n` is unconditionally
    false for **every** `E : ResolvedEnv` and `n : Nat`. -/
theorem not_fundamentalTermSDI (E : ResolvedEnv) (n : Nat) : ¬ FundamentalTermSDI E n :=
  fun F => not_lrTermSDI_idPiProp_sortStep E n
    (F.1 .nil (hasTyT_idPiProp E n) idPiPropSortStep (approxDI_idPiProp_sortStep E))

/-- **Admitted Obstruction (`not_fundamentalTermD`)**: `RcicNativePiModelLRTermD.FundamentalTermD E n`
    (#7646) is unconditionally false for **every** `E : ResolvedEnv` and `n : Nat` (both on its
    `HasTyT` diagonal conjunct `.1` and on its `ConvT` conjunct `.2`). Consequently,
    `fundamentalLRINT_of_fundamentalTermD` and `piRow_of_fundamentalTermD` in
    `RcicNativePiModelLRTermD` have an uninhabited premise on every `(E, n)`. -/
theorem not_fundamentalTermD (E : ResolvedEnv) (n : Nat) : ¬ FundamentalTermD E n :=
  fun F => not_lrTermD_idPiProp_sortStep E n
    (F.1 .nil (hasTyT_idPiProp E n) idPiPropSortStep approxI_idPiProp_sortStep)

/-- **Admitted Obstruction (`not_fundamentalTermD_DI`)**: `FundamentalTermD_DI E n` is
    unconditionally false for **every** `E : ResolvedEnv` and `n : Nat`. -/
theorem not_fundamentalTermD_DI (E : ResolvedEnv) (n : Nat) : ¬ FundamentalTermD_DI E n :=
  fun F => not_lrTermD_idPiProp_sortStep E n
    (F.1 .nil (hasTyT_idPiProp E n) idPiPropSortStep (approxDI_idPiProp_sortStep E))

/-- An application `.app (.bvar i) a` with a bound-variable head never takes a weak-head step
    in any `E : ResolvedEnv`. -/
theorem whStep_app_bvar_false {E : ResolvedEnv} {i : Nat} {a e : Expr Nat}
    (h : WhStep E (.app (.bvar i) a) e) : False := by
  cases h with
  | iota hI =>
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      have hsp := congrArg (Prod.fst ∘ appsSpine) hl
      simp only [appsSpine, recCall, appsSpine_foldApps, appsSpine_const,
        Function.comp_apply] at hsp
      cases hsp
  | appHead hf => exact whStep_bvar_false hf

/-- Weak-head reduction from `.app (.bvar i) a` is always reflexive. -/
theorem whRed_app_bvar_eq {E : ResolvedEnv} {i : Nat} {a e : Expr Nat}
    (h : WhRed E (.app (.bvar i) a) e) : e = .app (.bvar i) a := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStep_app_bvar_false hs).elim

/-- `closedIrrPiCpt` is excluded by `BotPiCpt` (its second step uses demand `[.lam [([.sort], .sort)]]`). -/
theorem not_botPiCpt_closedIrrPiCpt : ¬ BotPiCpt closedIrrPiCpt := by
  intro h
  cases h with
  | pi _ _ hf₁ =>
      have h₁ := hf₁ _ (List.Mem.head _)
      cases h₁ with
      | pi _ hbd₂ _ =>
          have h₂ := hbd₂ _ (List.Mem.head _) (.lam [([.sort], .sort)]) (List.Mem.head _)
          cases h₂

/-- The sort level of `closedIrrPi_conv`:
    `.imax (.succ .zero) (.imax (.imax .zero (.succ .zero)) (.imax .zero (.imax .zero .zero)))`. -/
abbrev closedIrrPiSortLevel : Level :=
  .imax (.succ .zero) (.imax (.imax .zero (.succ .zero)) (.imax .zero (.imax .zero .zero)))

/-- **Admitted Obstruction (`not_lrTypeIN_closedIrrPi`)**: in `Γ = []`, `closedIrrPiL` and
    `closedIrrPiR` are convertible at `.sort closedIrrPiSortLevel` via `closedIrrPi_conv`
    (`ConvT.irr` under `ConvT.app` + four `ConvT.pi` steps), and `closedIrrPiCpt` approximates
    `closedIrrPiL` in `ApproxI EnvI.bot` and `ApproxDI E EnvI.bot`, yet
    `LRTypeIN E n [] closedIrrPiL closedIrrPiR closedIrrPiCpt` is **false** for every `E, n`. -/
theorem not_lrTypeIN_closedIrrPi (E : ResolvedEnv) (n : Nat) :
    ¬ LRTypeIN E n [] closedIrrPiL closedIrrPiR closedIrrPiCpt := by
  intro h₁
  cases h₁ with
  | pi hL₁ hR₁ _ _ _ _ rf₁ =>
      have eL₁ := whRed_pi_eq hL₁; injection eL₁ with _ eB₁; subst eB₁
      have eR₁ := whRed_pi_eq hR₁; injection eR₁ with _ eB₁'; subst eB₁'
      have h₂ := rf₁ _ (List.Mem.head _)
      cases h₂ with
      | pi hL₂ hR₂ _ _ _ _ rf₂ =>
          have eL₂ := whRed_pi_eq hL₂; injection eL₂ with _ eB₂; subst eB₂
          have eR₂ := whRed_pi_eq hR₂; injection eR₂ with _ eB₂'; subst eB₂'
          have h₃ := rf₂ _ (List.Mem.head _)
          cases h₃ with
          | pi hL₃ hR₃ _ _ _ _ rf₃ =>
              have eL₃ := whRed_pi_eq hL₃; injection eL₃ with _ eB₃; subst eB₃
              have eR₃ := whRed_pi_eq hR₃; injection eR₃ with _ eB₃'; subst eB₃'
              have h₄ := rf₃ _ (List.Mem.head _)
              cases h₄ with
              | pi hL₄ hR₄ _ _ _ _ rf₄ =>
                  have eL₄ := whRed_pi_eq hL₄; injection eL₄ with _ eB₄; subst eB₄
                  have eR₄ := whRed_pi_eq hR₄; injection eR₄ with _ eB₄'; subst eB₄'
                  have h₅ := rf₄ _ (List.Mem.head _)
                  cases h₅ with
                  | sort hS _ =>
                      exact nomatch whRed_app_bvar_eq hS

/-- `LRTermI` is false on `closedIrrPi_conv` at `closedIrrPiCpt` for every `E, n`. -/
theorem not_lrTermI_closedIrrPi (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermI E n [] closedIrrPiL closedIrrPiR (.sort closedIrrPiSortLevel) closedIrrPiCpt :=
  fun h => not_lrTypeIN_closedIrrPi E n (lrTypeIN_of_lrTermI_sort closedIrrPiCpt h)

/-- `LRTermS` is false on `closedIrrPi_conv` at `closedIrrPiCpt` for every `E, n`. -/
theorem not_lrTermS_closedIrrPi (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermS E n [] closedIrrPiL closedIrrPiR (.sort closedIrrPiSortLevel) closedIrrPiCpt :=
  fun h => not_lrTypeIN_closedIrrPi E n (lrTypeIN_of_lrTermS_sort closedIrrPiCpt h)

/-- `LRTermSDI` is false on `closedIrrPi_conv` at `closedIrrPiCpt` for every `E, n`. -/
theorem not_lrTermSDI_closedIrrPi (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermSDI E n [] closedIrrPiL closedIrrPiR (.sort closedIrrPiSortLevel) closedIrrPiCpt :=
  fun h => not_lrTypeIN_closedIrrPi E n (lrTypeIN_of_lrTermSDI_sort closedIrrPiCpt h)

/-- `LRTermDCore` is false on `closedIrrPi_conv` at `closedIrrPiCpt` for every `E, n`. -/
theorem not_lrTermDCore_closedIrrPi (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermDCore E n [] closedIrrPiL closedIrrPiR (.sort closedIrrPiSortLevel) closedIrrPiCpt :=
  fun h => not_lrTypeIN_closedIrrPi E n (lrTypeIN_of_lrTermDCore_sort closedIrrPiCpt h)

/-- **Admitted Obstruction (`not_lrTermD_closedIrrPi`)**: even though `LRTermD` (#7646/#7653)
    collapses propositions via `IsPropTyI` (`irrCaseD`), `closedIrrPi_conv` lifts `ConvT.irr` via
    `ConvT.app` + `ConvT.pi` to a conversion in `Γ = []` at `.sort closedIrrPiSortLevel` (where
    `IsPropTyI` is syntactically false), refuting `LRTermD` at `closedIrrPiCpt` for **every**
    `E : ResolvedEnv` and `n : Nat`. -/
theorem not_lrTermD_closedIrrPi (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermD E n [] closedIrrPiL closedIrrPiR (.sort closedIrrPiSortLevel) closedIrrPiCpt :=
  fun h => not_lrTypeIN_closedIrrPi E n (lrTypeIN_of_lrTermD_sort closedIrrPiCpt h)

/-- `LRTermS` is unconditionally false on the `ConvT.eta` redex of `etaIdPiPropFn` at
    `etaIdPiPropCpt` in `Γ = []` for every `E, n`. -/
theorem not_lrTermS_eta_etaIdPiPropFn (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermS E n [] (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)))
        etaIdPiPropFn (.pi (.sort .zero) (.sort .zero)) etaIdPiPropCpt := by
  intro h
  rw [etaIdPiPropCpt, lrTermS_lam_iff] at h
  obtain ⟨A₁, B₁, _, hP, _, _, happ⟩ := h
  have e := whRed_pi_eq hP
  injection e with eA eB; subst eA; subst eB
  have hid₀ : HasTyT E n [] idPiProp (.sort .zero) :=
    .conv [] idPiProp (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
      (.succ (.imax (.succ .zero) .zero))
      (hasTyT_idPiProp E n) (.sorts [] (.imax (.succ .zero) .zero) .zero (fun _ => rfl))
  have h₂ := happ ([], idPiPropSortStep) (List.Mem.head _)
    idPiProp idPiProp hid₀ hid₀ (fun _ hu => nomatch hu)
  change LRTermS E n []
    (.app (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0))) idPiProp)
    (.app etaIdPiPropFn idPiProp) (.sort .zero) idPiPropSortStep at h₂
  rw [idPiPropSortStep, lrTermS_pi_iff] at h₂
  cases h₂.2 with
  | pi _ hR _ _ _ _ rf =>
      have hR₁ : WhRed E idPiProp (.pi _ _) :=
        whRed_step_inv_of_unique hR (fun _ => whStep_app_lam_eq) (fun h => by cases h)
      have eR := whRed_pi_eq hR₁
      injection eR with _ eB₂; subst eB₂
      have h₃ := rf ([.sort], .sort) (List.Mem.head _)
      cases h₃ with
      | sort _ hsort => exact nomatch whRed_bvar_eq hsort

/-- `LRTermDCore` is unconditionally false on the diagonal of `etaIdPiPropFn` at `etaIdPiPropCpt`
    in `Γ = []` for every `E, n` (the `.lam` output index is `instantiate0 idPiProp (.sort .zero) =
    .sort .zero`, where `IsPropTyI` is syntactically false). -/
theorem not_lrTermDCore_etaIdPiPropFn_diag (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermDCore E n [] etaIdPiPropFn etaIdPiPropFn
        (.pi (.sort .zero) (.sort .zero)) etaIdPiPropCpt := by
  intro h
  rw [etaIdPiPropCpt, lrTermDCore_lam_iff] at h
  obtain ⟨A₁, B₁, _, hP, _, _, happ⟩ := h
  have e := whRed_pi_eq hP
  injection e with eA eB; subst eA; subst eB
  have hid₀ : HasTyT E n [] idPiProp (.sort .zero) :=
    .conv [] idPiProp (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
      (.succ (.imax (.succ .zero) .zero))
      (hasTyT_idPiProp E n) (.sorts [] (.imax (.succ .zero) .zero) .zero (fun _ => rfl))
  have h₂ := happ ([], idPiPropSortStep) (List.Mem.head _)
    idPiProp idPiProp hid₀ hid₀ (fun _ hu => nomatch hu)
  change IsPropTyI E n [] (.sort .zero) ∨
    LRTermDCore E n [] (.app etaIdPiPropFn idPiProp) (.app etaIdPiPropFn idPiProp)
      (.sort .zero) idPiPropSortStep at h₂
  rcases h₂ with hP₀ | hcore
  · exact not_isPropTyI_sort E n [] .zero hP₀
  · rw [idPiPropSortStep, lrTermDCore_pi_iff] at hcore
    cases hcore.2 with
    | pi _ hR _ _ _ _ rf =>
        have hR₁ : WhRed E idPiProp (.pi _ _) :=
          whRed_step_inv_of_unique hR (fun _ => whStep_app_lam_eq) (fun h => by cases h)
        have eR := whRed_pi_eq hR₁
        injection eR with _ eB₂; subst eB₂
        have h₃ := rf ([.sort], .sort) (List.Mem.head _)
        cases h₃ with
        | sort _ hsort => exact nomatch whRed_bvar_eq hsort

/-- `LRTermDCore` is unconditionally false on the `ConvT.eta` redex of `etaIdPiPropFn` at
    `etaIdPiPropCpt` in `Γ = []` for every `E, n`. -/
theorem not_lrTermDCore_eta_etaIdPiPropFn (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermDCore E n [] (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)))
        etaIdPiPropFn (.pi (.sort .zero) (.sort .zero)) etaIdPiPropCpt := by
  intro h
  rw [etaIdPiPropCpt, lrTermDCore_lam_iff] at h
  obtain ⟨A₁, B₁, _, hP, _, _, happ⟩ := h
  have e := whRed_pi_eq hP
  injection e with eA eB; subst eA; subst eB
  have hid₀ : HasTyT E n [] idPiProp (.sort .zero) :=
    .conv [] idPiProp (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
      (.succ (.imax (.succ .zero) .zero))
      (hasTyT_idPiProp E n) (.sorts [] (.imax (.succ .zero) .zero) .zero (fun _ => rfl))
  have h₂ := happ ([], idPiPropSortStep) (List.Mem.head _)
    idPiProp idPiProp hid₀ hid₀ (fun _ hu => nomatch hu)
  change IsPropTyI E n [] (.sort .zero) ∨
    LRTermDCore E n []
      (.app (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0))) idPiProp)
      (.app etaIdPiPropFn idPiProp) (.sort .zero) idPiPropSortStep at h₂
  rcases h₂ with hP₀ | hcore
  · exact not_isPropTyI_sort E n [] .zero hP₀
  · rw [idPiPropSortStep, lrTermDCore_pi_iff] at hcore
    cases hcore.2 with
    | pi _ hR _ _ _ _ rf =>
        have hR₁ : WhRed E idPiProp (.pi _ _) :=
          whRed_step_inv_of_unique hR (fun _ => whStep_app_lam_eq) (fun h => by cases h)
        have eR := whRed_pi_eq hR₁
        injection eR with _ eB₂; subst eB₂
        have h₃ := rf ([.sort], .sort) (List.Mem.head _)
        cases h₃ with
        | sort _ hsort => exact nomatch whRed_bvar_eq hsort

/-- Exact syntactic inversion of `HasTyT` on `.sort l`: every typing derivation of `.sort l` at
    `T` converts `.sort (.succ l)` to `T` via `TyConvT`. -/
def hasTyT_sort_inv {l : Level} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTyT E n Γ e T → e = .sort l →
    TyConvT E n Γ (.sort (.succ l)) T
  | _, _, _, .sort _ l', heq => by
      injection heq with hl
      subst hl
      exact .refl _ _
  | _, _, _, .conv _ _ _ _ u h hc, heq =>
      .trans _ _ _ _ (hasTyT_sort_inv h heq) (.of _ _ _ u hc)
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- Exact syntactic inversion of `HasTyT` on `.pi A B`: every typing derivation of `.pi A B` at
    `T` factors through `HasTyT E n Γ A (.sort u)`, `HasTyT E n (.assumption A :: Γ) B (.sort v)`,
    and `TyConvT E n Γ (.sort (.imax u v)) T`. -/
def hasTyT_pi_inv {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTyT E n Γ e T → e = .pi A B →
    Σ' (u v : Level),
      HasTyT E n Γ A (.sort u) ×'
      HasTyT E n (.assumption A :: Γ) B (.sort v) ×'
      TyConvT E n Γ (.sort (.imax u v)) T
  | _, _, _, .pi _ A' u B' v hA hB, heq => by
      injection heq with eA eB
      subst eA; subst eB
      exact ⟨u, v, hA, hB, .refl _ _⟩
  | _, _, _, .conv _ _ _ _ w h hc, heq =>
      let ⟨u, v, hA, hB, hcv⟩ := hasTyT_pi_inv h heq
      ⟨u, v, hA, hB, .trans _ _ _ _ hcv (.of _ _ _ w hc)⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- In any universe-consistent environment where `TyConvT` between sorts preserves `eqN`
    (`SortRow`), `.pi (.sort .zero) (.sort .zero)` (`Prop → Prop`) cannot be a proposition
    (`¬ IsPropTyI E n Γ (.pi (.sort .zero) (.sort .zero))`), and hence `LRTermD` on `etaIdPiPropFn`
    at `etaIdPiPropCpt` is false (`¬ EtaDiagD E n` and `¬ EtaCaseD E n` from #7653). -/
theorem not_isPropTyI_pi_sort0_sort0
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (Γ : LCtx) :
    ¬ IsPropTyI E n Γ (.pi (.sort .zero) (.sort .zero)) := by
  rintro ⟨⟨hpi⟩, _⟩
  let ⟨u, v, hA, hB, hc⟩ := hasTyT_pi_inv hpi rfl
  have hcA := hasTyT_sort_inv hA rfl
  have hcB := hasTyT_sort_inv hB rfl
  have hu : eval (fun _ => some 0) u = some 1 :=
    (hSort hcA (fun _ => some 0)).symm
  have hv : eval (fun _ => some 0) v = some 1 :=
    (hSort hcB (fun _ => some 0)).symm
  have himax : eval (fun _ => some 0) (.imax u v) = some 0 :=
    hSort hc (fun _ => some 0)
  simp only [eval, hu, hv, Option.bind_some, Option.map_some] at himax
  cases himax

/-- Under universe consistency `hSort`, `LRTermD` is false on the `ConvT.eta` redex of
    `etaIdPiPropFn` at `etaIdPiPropCpt` in `Γ = []`. -/
theorem not_lrTermD_eta_etaIdPiPropFn
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂) :
    ¬ LRTermD E n [] (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)))
        etaIdPiPropFn (.pi (.sort .zero) (.sort .zero)) etaIdPiPropCpt := by
  rintro (hP | hcore)
  · exact not_isPropTyI_pi_sort0_sort0 hSort [] hP
  · exact not_lrTermDCore_eta_etaIdPiPropFn E n hcore

/-! ## §4. Weakening and Related-Substitution Stability of `LRTermS`, `LRTermSDI`, `LRTermDCore`, and `LRTermD` on `BotPiCpt` and `.bvar j` (Discharging `hι` and Extending #7652) -/

/-- `LRTermS` on any `BotPiCpt` compact `c` (`.bot`, `.sort`, or `.pi a f`) is stable under
    one-declaration weakening `insertAt d k Γ` / `lift k 1` at every `EnvClosed E`. -/
theorem lrTermS_weaken_botPiCpt (hcl : EnvClosed E) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} (d : LocalDecl) (k : Nat)
    (hΓ' : CtxWfT E n (insertAt d k Γ))
    (h : LRTermS E n Γ M M' A c) :
    LRTermS E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) c := by
  cases hc with
  | bot => exact lrTermS_bot _ _ _ _
  | sort =>
      rw [lrTermS_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_lift_of_envClosed hcl hl k⟩,
        lrTypeIN_weaken_botPiCpt hcl .sort d k hΓ' hLR⟩
  | pi ha hbd hf =>
      rw [lrTermS_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_lift_of_envClosed hcl hl k⟩,
        lrTypeIN_weaken_botPiCpt hcl (.pi ha hbd hf) d k hΓ' hLR⟩

/-- `LRTermSDI` on any `BotPiCpt` compact `c` is stable under one-declaration weakening at every
    `EnvClosed E`. -/
theorem lrTermSDI_weaken_botPiCpt (hcl : EnvClosed E) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} (d : LocalDecl) (k : Nat)
    (hΓ' : CtxWfT E n (insertAt d k Γ))
    (h : LRTermSDI E n Γ M M' A c) :
    LRTermSDI E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) c := by
  cases hc with
  | bot => exact lrTermSDI_bot _ _ _ _
  | sort =>
      rw [lrTermSDI_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_lift_of_envClosed hcl hl k⟩,
        lrTypeIN_weaken_botPiCpt hcl .sort d k hΓ' hLR⟩
  | pi ha hbd hf =>
      rw [lrTermSDI_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_lift_of_envClosed hcl hl k⟩,
        lrTypeIN_weaken_botPiCpt hcl (.pi ha hbd hf) d k hΓ' hLR⟩

/-- `LRTermDCore` on any `BotPiCpt` compact `c` is stable under one-declaration weakening at every
    `EnvClosed E`. -/
theorem lrTermDCore_weaken_botPiCpt (hcl : EnvClosed E) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} (d : LocalDecl) (k : Nat)
    (hΓ' : CtxWfT E n (insertAt d k Γ))
    (h : LRTermDCore E n Γ M M' A c) :
    LRTermDCore E n (insertAt d k Γ) (lift k 1 M) (lift k 1 M') (lift k 1 A) c := by
  cases hc with
  | bot => exact lrTermDCore_bot _ _ _ _
  | sort =>
      rw [lrTermDCore_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_lift_of_envClosed hcl hl k⟩,
        lrTypeIN_weaken_botPiCpt hcl .sort d k hΓ' hLR⟩
  | pi ha hbd hf =>
      rw [lrTermDCore_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_lift_of_envClosed hcl hl k⟩,
        lrTypeIN_weaken_botPiCpt hcl (.pi ha hbd hf) d k hΓ' hLR⟩

/-- `LRTermS` on any `BotPiCpt` compact `c` (`.bot`, `.sort`, or `.pi a f`) is stable under
    `substRemove v j Γ` / `instantiate j (lift 0 j v)` at an `.assumption t` hole (using
    §14.1 `whRed_instantiate_of_envClosed`, which discharges `#7652`'s `hι` premise unconditionally,
    and §14.3 `lrTypeIN_subst_botPiCpt`). -/
theorem lrTermS_subst_botPiCpt (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (v t : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove v j Γ))
    (h : LRTermS E n Γ M M' A c) :
    LRTermS E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) c := by
  cases hc with
  | bot => exact lrTermS_bot _ _ _ _
  | sort =>
      rw [lrTermS_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j v)⟩,
        lrTypeIN_subst_botPiCpt hcl hinst v t .sort hget hvty hΓ' hLR⟩
  | pi ha hbd hf =>
      rw [lrTermS_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j v)⟩,
        lrTypeIN_subst_botPiCpt hcl hinst v t (.pi ha hbd hf) hget hvty hΓ' hLR⟩

/-- Head (`j = 0`) specialization: `LRTermS` on any `BotPiCpt` compact is stable under
    `instantiate0 v` for any `HasTyT E n Γ v t` at `EnvWfT E`. -/
theorem lrTermS_subst0_botPiCpt (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t M M' A : Expr Nat}
    (hv : HasTyT E n Γ v t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermS E n (.assumption t :: Γ) M M' A c) :
    LRTermS E n Γ (instantiate0 v M) (instantiate0 v M') (instantiate0 v A) c := by
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  have h0 := lrTermS_subst_botPiCpt (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) v t hc hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hv)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- `LRTermSDI` on any `BotPiCpt` compact `c` is stable under `substRemove v j Γ` /
    `instantiate j (lift 0 j v)`. -/
theorem lrTermSDI_subst_botPiCpt (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (v t : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove v j Γ))
    (h : LRTermSDI E n Γ M M' A c) :
    LRTermSDI E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) c := by
  cases hc with
  | bot => exact lrTermSDI_bot _ _ _ _
  | sort =>
      rw [lrTermSDI_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j v)⟩,
        lrTypeIN_subst_botPiCpt hcl hinst v t .sort hget hvty hΓ' hLR⟩
  | pi ha hbd hf =>
      rw [lrTermSDI_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j v)⟩,
        lrTypeIN_subst_botPiCpt hcl hinst v t (.pi ha hbd hf) hget hvty hΓ' hLR⟩

/-- Head (`j = 0`) specialization: `LRTermSDI` on any `BotPiCpt` compact is stable under
    `instantiate0 v`. -/
theorem lrTermSDI_subst0_botPiCpt (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t M M' A : Expr Nat}
    (hv : HasTyT E n Γ v t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermSDI E n (.assumption t :: Γ) M M' A c) :
    LRTermSDI E n Γ (instantiate0 v M) (instantiate0 v M') (instantiate0 v A) c := by
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  have h0 := lrTermSDI_subst_botPiCpt (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) v t hc hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hv)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- `LRTermDCore` on any `BotPiCpt` compact `c` is stable under `substRemove v j Γ` /
    `instantiate j (lift 0 j v)`. -/
theorem lrTermDCore_subst_botPiCpt (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (v t : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} {j : Nat}
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ' : CtxWfT E n (substRemove v j Γ))
    (h : LRTermDCore E n Γ M M' A c) :
    LRTermDCore E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) c := by
  cases hc with
  | bot => exact lrTermDCore_bot _ _ _ _
  | sort =>
      rw [lrTermDCore_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j v)⟩,
        lrTypeIN_subst_botPiCpt hcl hinst v t .sort hget hvty hΓ' hLR⟩
  | pi ha hbd hf =>
      rw [lrTermDCore_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, hLR⟩ := h
      exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j v)⟩,
        lrTypeIN_subst_botPiCpt hcl hinst v t (.pi ha hbd hf) hget hvty hΓ' hLR⟩

/-- Head (`j = 0`) specialization: `LRTermDCore` on any `BotPiCpt` compact is stable under
    `instantiate0 v`. -/
theorem lrTermDCore_subst0_botPiCpt (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t M M' A : Expr Nat}
    (hv : HasTyT E n Γ v t) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermDCore E n (.assumption t :: Γ) M M' A c) :
    LRTermDCore E n Γ (instantiate0 v M) (instantiate0 v M') (instantiate0 v A) c := by
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  have h0 := lrTermDCore_subst_botPiCpt (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) v t hc hget0
    (by simpa only [substRemove_zero_cons, lift_zero] using hv)
    (by simpa only [substRemove_zero_cons] using hΓ) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- Related-substitution stability at `.bvar j` and `.sort` for `LRTermS` over `ApproxI`
    WITHOUT `#7652`'s `hι` hypothesis (discharged via §14.1 `whRed_instantiate_sort_of_envClosed`). -/
theorem lrTermS_subst_sort_and_bvar (hcl : EnvClosed E)
    {ρ : EnvI} {j : Nat} {r r' T : Expr Nat} {Γ : LCtx}
    (hrel : ∀ c, ApproxI (EnvI.drop ρ j) r c →
      LRTermS E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermS E n Γ M M' A .sort →
        LRTermS E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxI ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermS E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) := by
  constructor
  · intro M M' A h
    rw [lrTermS_sort_iff] at h ⊢
    rcases h with ⟨⟨l, hA⟩, hLR⟩
    cases hLR with
    | sort hM hM' =>
        exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hA j (lift 0 j r)⟩,
          .sort (whRed_instantiate_sort_of_envClosed hcl hM j (lift 0 j r))
            (whRed_instantiate_sort_of_envClosed hcl hM' j (lift 0 j r'))⟩
  · intro c hmem
    have hlook : ApproxI (EnvI.insert ρ j (denI (EnvI.drop ρ j) r)) (.bvar j) c :=
      approxI_subst_elim (.bvar j) hmem
    have hL : instantiate j (lift 0 j r) (.bvar j) = lift 0 j r := by
      rw [instantiate, if_pos rfl]
    have hR : instantiate j (lift 0 j r') (.bvar j) = lift 0 j r' := by
      rw [instantiate, if_pos rfl]
    rw [hL, hR]
    rcases approxI_bvar_inv hlook with rfl | hmem'
    · exact lrTermS_bot _ _ _ _
    · rw [EnvI.insert_self] at hmem'
      exact hrel c hmem'

/-- Related-substitution stability at `.bvar j` and `.sort` for `LRTermSDI` over `ApproxDI`. -/
theorem lrTermSDI_subst_sort_and_bvar (hcl : EnvClosed E)
    {ρ : EnvI} {j : Nat} {r r' T : Expr Nat} {Γ : LCtx}
    (hrel : ∀ c, ApproxDI E (EnvI.drop ρ j) r c →
      LRTermSDI E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermSDI E n Γ M M' A .sort →
        LRTermSDI E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxDI E ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermSDI E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) := by
  constructor
  · intro M M' A h
    rw [lrTermSDI_sort_iff] at h ⊢
    rcases h with ⟨⟨l, hA⟩, hLR⟩
    cases hLR with
    | sort hM hM' =>
        exact ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hA j (lift 0 j r)⟩,
          .sort (whRed_instantiate_sort_of_envClosed hcl hM j (lift 0 j r))
            (whRed_instantiate_sort_of_envClosed hcl hM' j (lift 0 j r'))⟩
  · intro c hmem
    have hlook : ApproxDI E (EnvI.insert ρ j (denDI E (EnvI.drop ρ j) r)) (.bvar j) c :=
      approxDI_subst_elim (.bvar j) hmem
    have hL : instantiate j (lift 0 j r) (.bvar j) = lift 0 j r := by
      rw [instantiate, if_pos rfl]
    have hR : instantiate j (lift 0 j r') (.bvar j) = lift 0 j r' := by
      rw [instantiate, if_pos rfl]
    rw [hL, hR]
    rcases approxDI_bvar_inv hlook with rfl | hmem'
    · exact lrTermSDI_bot _ _ _ _
    · rw [EnvI.insert_self] at hmem'
      exact hrel c hmem'

/-- Related-substitution stability at `.bvar j` for `LRTermD` over `ApproxDI`. -/
theorem lrTermD_subst_bvar
    {ρ : EnvI} {j : Nat} {r r' T : Expr Nat} {Γ : LCtx}
    (hrel : ∀ c, ApproxDI E (EnvI.drop ρ j) r c →
      LRTermD E n Γ (lift 0 j r) (lift 0 j r') T c)
    (c : CptI) (hmem : ApproxDI E ρ (instantiate j (lift 0 j r) (.bvar j)) c) :
    LRTermD E n Γ (instantiate j (lift 0 j r) (.bvar j))
      (instantiate j (lift 0 j r') (.bvar j)) T c := by
  have hlook : ApproxDI E (EnvI.insert ρ j (denDI E (EnvI.drop ρ j) r)) (.bvar j) c :=
    approxDI_subst_elim (.bvar j) hmem
  have hL : instantiate j (lift 0 j r) (.bvar j) = lift 0 j r := by
    rw [instantiate, if_pos rfl]
  have hR : instantiate j (lift 0 j r') (.bvar j) = lift 0 j r' := by
    rw [instantiate, if_pos rfl]
  rw [hL, hR]
  rcases approxDI_bvar_inv hlook with rfl | hmem'
  · exact lrTermD_bot _ _ _ _
  · rw [EnvI.insert_self] at hmem'
    exact hrel c hmem'

/-! ## §5. Concrete δ/ι Fundamental-Lemma Cases for `LRTermSDI` and `LRTermD` over `ApproxDI` and the Repaired `BotPiCpt` Term Layer (`FundamentalTermBotDI`) -/

/-- The `sort` typing rule on the diagonal for `LRTermSDI` over `ApproxDI`. -/
theorem fundTermSDI_sorts {Γ : LCtx} (l : Level) :
    ∀ u, ApproxDI E EnvI.bot (.sort l) u →
      LRTermSDI E n Γ (.sort l) (.sort l) (.sort (.succ l)) u := by
  intro u hu
  rcases approxDI_sort_inv hu with rfl | rfl
  · exact lrTermSDI_bot _ _ _ _
  · rw [lrTermSDI_sort_iff]
    exact ⟨⟨_, .refl _⟩, lrTypeIN_sort_congr Γ l l⟩

/-- The `sort` typing rule on the diagonal for `LRTermD` over `ApproxDI`. -/
theorem fundTermD_DI_sorts {Γ : LCtx} (l : Level) :
    ∀ u, ApproxDI E EnvI.bot (.sort l) u →
      LRTermD E n Γ (.sort l) (.sort l) (.sort (.succ l)) u := by
  intro u hu
  rcases approxDI_sort_inv hu with rfl | rfl
  · exact lrTermD_bot _ _ _ _
  · refine Or.inr ?_
    rw [lrTermDCore_sort_iff]
    exact ⟨⟨_, .refl _⟩, lrTypeIN_sort_congr Γ l l⟩

/-- One weak-head step for `LRTermSDI` over `ApproxDI` (unconditional at every `EnvWfT E`,
    without `WhApproxInv`). -/
theorem fundConvSDI_of_whStep (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (h : WhStep E M M')
    (hdiag : ∀ u, ApproxDI E EnvI.bot M' u → LRTermSDI E n Γ M' M' A u) :
    ∀ u, ApproxDI E EnvI.bot M u → LRTermSDI E n Γ M M' A u := by
  intro u hu
  have hu' : ApproxDI E EnvI.bot M' u := (semEqDI_whStep hW h EnvI.bot u).mp hu
  exact lrTermSDI_expand (.step h (.refl _)) (.refl _) u (hdiag u hu')

/-- Multi-step weak-head reduction for `LRTermSDI` over `ApproxDI`. -/
theorem fundConvSDI_of_whRed (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (h : WhRed E M M')
    (hdiag : ∀ u, ApproxDI E EnvI.bot M' u → LRTermSDI E n Γ M' M' A u) :
    ∀ u, ApproxDI E EnvI.bot M u → LRTermSDI E n Γ M M' A u := by
  intro u hu
  have hu' : ApproxDI E EnvI.bot M' u := (semEqDI_whRed hW h EnvI.bot u).mp hu
  exact lrTermSDI_expand h (.refl _) u (hdiag u hu')

/-- Concrete `ConvT.delta` case for `LRTermSDI` over `ApproxDI` (even without `EnvWfT E`). -/
theorem fundConvSDI_delta {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b A : Expr Nat} (hd : DeltaConst E r m b)
    (hdiag : ∀ u, ApproxDI E EnvI.bot (instantiateLevels ls b) u →
      LRTermSDI E n Γ (instantiateLevels ls b) (instantiateLevels ls b) A u) :
    ∀ u, ApproxDI E EnvI.bot (.const r ls) u →
      LRTermSDI E n Γ (.const r ls) (instantiateLevels ls b) A u := by
  intro u hu
  have hu' : ApproxDI E EnvI.bot (instantiateLevels ls b) u :=
    (semEqDI_delta_bot (ls := ls) hd u).mp hu
  exact lrTermSDI_expand (.step (.delta hd.1 hd.2.1) (.refl _)) (.refl _) u (hdiag u hu')

/-- Concrete `ConvT.iota` case for `LRTermSDI` over `ApproxDI` at every `EnvWfT E`. -/
theorem fundConvSDI_iota (hW : EnvWfT E) {Γ : LCtx} {lhs rhs A : Expr Nat}
    (h : DerivedIota E lhs rhs)
    (hdiag : ∀ u, ApproxDI E EnvI.bot rhs u → LRTermSDI E n Γ rhs rhs A u) :
    ∀ u, ApproxDI E EnvI.bot lhs u → LRTermSDI E n Γ lhs rhs A u :=
  fundConvSDI_of_whStep hW (.iota (derivedIotaU_ofDerivedIota h)) hdiag

/-- One weak-head step for `LRTermD` over `ApproxDI` (unconditional at every `EnvWfT E`,
    without `WhApproxInv`). -/
theorem fundConvD_DI_of_whStep (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (h : WhStep E M M')
    (hdiag : ∀ u, ApproxDI E EnvI.bot M' u → LRTermD E n Γ M' M' A u) :
    ∀ u, ApproxDI E EnvI.bot M u → LRTermD E n Γ M M' A u := by
  intro u hu
  have hu' : ApproxDI E EnvI.bot M' u := (semEqDI_whStep hW h EnvI.bot u).mp hu
  exact lrTermD_expand (.step h (.refl _)) (.refl _) u (hdiag u hu')

/-- Multi-step weak-head reduction for `LRTermD` over `ApproxDI`. -/
theorem fundConvD_DI_of_whRed (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (h : WhRed E M M')
    (hdiag : ∀ u, ApproxDI E EnvI.bot M' u → LRTermD E n Γ M' M' A u) :
    ∀ u, ApproxDI E EnvI.bot M u → LRTermD E n Γ M M' A u := by
  intro u hu
  have hu' : ApproxDI E EnvI.bot M' u := (semEqDI_whRed hW h EnvI.bot u).mp hu
  exact lrTermD_expand h (.refl _) u (hdiag u hu')

/-- Concrete `ConvT.delta` case for `LRTermD` over `ApproxDI` (even without `EnvWfT E`). -/
theorem fundConvD_DI_delta {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b A : Expr Nat} (hd : DeltaConst E r m b)
    (hdiag : ∀ u, ApproxDI E EnvI.bot (instantiateLevels ls b) u →
      LRTermD E n Γ (instantiateLevels ls b) (instantiateLevels ls b) A u) :
    ∀ u, ApproxDI E EnvI.bot (.const r ls) u →
      LRTermD E n Γ (.const r ls) (instantiateLevels ls b) A u := by
  intro u hu
  have hu' : ApproxDI E EnvI.bot (instantiateLevels ls b) u :=
    (semEqDI_delta_bot (ls := ls) hd u).mp hu
  exact lrTermD_expand (.step (.delta hd.1 hd.2.1) (.refl _)) (.refl _) u (hdiag u hu')

/-- Concrete `ConvT.iota` case for `LRTermD` over `ApproxDI` at every `EnvWfT E`. -/
theorem fundConvD_DI_iota (hW : EnvWfT E) {Γ : LCtx} {lhs rhs A : Expr Nat}
    (h : DerivedIota E lhs rhs)
    (hdiag : ∀ u, ApproxDI E EnvI.bot rhs u → LRTermD E n Γ rhs rhs A u) :
    ∀ u, ApproxDI E EnvI.bot lhs u → LRTermD E n Γ lhs rhs A u :=
  fundConvD_DI_of_whStep hW (.iota (derivedIotaU_ofDerivedIota h)) hdiag

/-- Positive repair of both §3 obstructions (`idPiProp` and `closedIrrPi`) for `LRTermD` when
    restricted to `BotPiCpt` compacts: `LRTermD E n [] idPiProp idPiProp (.sort .zero) c` holds
    for every `BotPiCpt c` approximating `idPiProp`. -/
theorem lrTermD_botPiCpt_idPiProp (E : ResolvedEnv) (n : Nat) :
    ∀ c, BotPiCpt c → ApproxDI E EnvI.bot idPiProp c →
      LRTermD E n [] idPiProp idPiProp (.sort .zero) c := by
  intro c hc happrox
  have hLR : LRTypeIN E n [] idPiProp idPiProp c :=
    lrTypeINBiDI_idPiProp E n c hc (Or.inl happrox)
  cases hc with
  | bot => exact lrTermD_bot _ _ _ _
  | sort =>
      refine Or.inr ?_
      rw [lrTermDCore_sort_iff]
      exact ⟨⟨.zero, .refl _⟩, hLR⟩
  | pi _ _ _ =>
      refine Or.inr ?_
      rw [lrTermDCore_pi_iff]
      exact ⟨⟨.zero, .refl _⟩, hLR⟩

/-- Positive repair of the `closedIrrPi` obstruction for `LRTermD` when restricted to `BotPiCpt`
    compacts: `LRTermD E n [] closedIrrPiL closedIrrPiR (.sort closedIrrPiSortLevel) c` holds
    for every `BotPiCpt c` approximating `closedIrrPiL` or `closedIrrPiR`. -/
theorem lrTermD_botPiCpt_closedIrrPi (E : ResolvedEnv) (n : Nat) :
    ∀ c, BotPiCpt c →
      (ApproxDI E EnvI.bot closedIrrPiL c ∨ ApproxDI E EnvI.bot closedIrrPiR c) →
      LRTermD E n [] closedIrrPiL closedIrrPiR (.sort closedIrrPiSortLevel) c := by
  intro c hc happrox
  have hLR : LRTypeIN E n [] closedIrrPiL closedIrrPiR c :=
    lrTypeINBiDI_closedIrrPi E n c hc happrox
  cases hc with
  | bot => exact lrTermD_bot _ _ _ _
  | sort =>
      refine Or.inr ?_
      rw [lrTermDCore_sort_iff]
      exact ⟨⟨closedIrrPiSortLevel, .refl _⟩, hLR⟩
  | pi _ _ _ =>
      refine Or.inr ?_
      rw [lrTermDCore_pi_iff]
      exact ⟨⟨closedIrrPiSortLevel, .refl _⟩, hLR⟩

/-- The repaired `BotPiCpt`-restricted term-level fundamental lemma over `ApproxDI E EnvI.bot`:
    avoids the §3 counterexamples (`idPiPropSortStep` and `closedIrrPiCpt`) by restricting `u` to
    `BotPiCpt u`. -/
def FundamentalTermBotDI (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ u, BotPiCpt u → ApproxDI E EnvI.bot M u → LRTermD E n Γ M M A u) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ u, BotPiCpt u →
      (ApproxDI E EnvI.bot M u ∨ ApproxDI E EnvI.bot M' u) →
      LRTermD E n Γ M M' A u)

/-- `FundamentalTermBotDI` implies `FundamentalLRINBotDI` at every `EnvWfT E` **without** `WhDet`
    or `TypeSoundness` (via `lrTypeIN_of_lrTermD_sort` and `fundamentalLRINBotDI_of_links`). -/
theorem fundamentalLRINBotDI_of_fundamentalTermBotDI (hW : EnvWfT E)
    (F : FundamentalTermBotDI E n) : FundamentalLRINBotDI E n :=
  fundamentalLRINBotDI_of_links (envClosed_of_envWfT hW) hW
    (fun {_} hΓ {_ _} hA c hc happrox => lrTypeIN_of_lrTermD_sort c (F.1 hΓ hA c hc happrox))
    (fun {_} hΓ {_ _ _} hconv c hc happrox =>
      lrTypeIN_of_lrTermD_sort c (F.2 hΓ hconv c hc (Or.inl happrox)))

/-- Π-injectivity (`piRow` shape) from `FundamentalTermBotDI` at every `EnvWfT E` (without `WhDet`
    or `TypeSoundness`). -/
theorem piRow_of_fundamentalTermBotDI (hW : EnvWfT E)
    (F : FundamentalTermBotDI E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  piRow_of_fundamentalLRINBotDI hW (fundamentalLRINBotDI_of_fundamentalTermBotDI hW F)

/-- Sort-Π disjointness (`TyConvT (.pi A B) (.sort u) → False`) from `FundamentalTermBotDI` at every
    `EnvWfT E`. -/
theorem not_tyConvT_pi_sort_of_fundamentalTermBotDI (hW : EnvWfT E)
    (F : FundamentalTermBotDI E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} {u : Level}
    (hc : TyConvT E n Γ (.pi A B) (.sort u)) : False :=
  not_tyConvT_pi_sort_of_fundamentalLRINBotDI hW
    (fundamentalLRINBotDI_of_fundamentalTermBotDI hW F) hΓ A B u hc

/-! ## §6. Structural Vacuity of `LRTermDCore`'s Data-Spine Argument Clause, Transparent-Body Characterization, and Additional #7653 Obstructions -/

/-- Because `RcicNativePiModelLR.WhStep.delta` and `RcicNativePiModelLRTermD.whNormal_const_of_opaque`
    step on any member with `m.body = some b`, `DeltaConst` matches `WhStep.delta` unconditionally;
    in any environment where stored bodies only appear on transparent definitions
    (`∀ r m b, E.members r = some m → m.body = some b → transparent m.mclass = true`),
    `DeltaConst E r m b` is equivalent to `E.members r = some m ∧ m.body = some b ∧ transparent m.mclass = true`. -/
theorem deltaConst_iff_transparent_of_bodyTransparent
    (htrEnv : ∀ r m b, E.members r = some m → m.body = some b → transparent m.mclass = true)
    (r : Nat) (m : CheckedMember) (b : Expr Nat) :
    DeltaConst E r m b ↔
      (E.members r = some m ∧ m.body = some b ∧ transparent m.mclass = true) :=
  ⟨fun hd => ⟨hd.1, hd.2.1, htrEnv r m b hd.1 hd.2.1⟩,
   fun ⟨hres, hbody, htr⟩ => deltaConst_of_transparent hres hbody htr⟩

/-- In **every** `E : ResolvedEnv`, `n : Nat`, and `Γ : LCtx`, `idPiProp = .pi (.sort .zero) (.bvar 0)`
    (`∀ (X : Prop), X`) has type `.sort .zero`. -/
def hasTyT_idPiProp_ctx (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ idPiProp (.sort .zero) :=
  .conv Γ idPiProp (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
    (.succ (.imax (.succ .zero) .zero))
    (.pi Γ (.sort .zero) (.succ .zero) (.bvar 0) .zero
      (.sort Γ .zero) (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl))
    (.sorts Γ (.imax (.succ .zero) .zero) .zero (fun _ => rfl))

/-- `IsPropTyI E n Γ idPiProp` holds unconditionally for **every** `E : ResolvedEnv`, `n : Nat`,
    and `Γ : LCtx` (`idPiProp` has type `.sort .zero` and is syntactically a `.pi`, not a `.sort`). -/
theorem isPropTyI_idPiProp (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    IsPropTyI E n Γ idPiProp :=
  ⟨⟨hasTyT_idPiProp_ctx E n Γ⟩, fun _ h => nomatch h⟩

/-- **Structural Vacuity (`lrTermDCore_dataSpine_args_vacuous`)**: in `LRTermDCore`'s data-spine
    branch (`RcicNativePiModelLRTermD.lean:88-93`), the existential list of argument types
    `Ts : List (Expr Nat)` is unconstrained (it does not require `HasTyT E n Γ (args₁.get i) (Ts.get i)`).
    Consequently, choosing `Ts := List.replicate args.length idPiProp` satisfies the left disjunct
    `IsPropTyI E n Γ (Ts.get (i.cast hl))` for **every** `i : Fin args.length` in **every**
    `E, n, Γ`, making the per-argument `LRTermDCore` check vacuous whenever `args.length ≤ args₁.length`
    and `args.length ≤ args₂.length`. -/
theorem lrTermDCore_dataSpine_args_vacuous (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (args : List CptI) {args₁ args₂ : List (Expr Nat)}
    (hb1 : args.length ≤ args₁.length) (hb2 : args.length ≤ args₂.length) :
    ∃ (Ts : List (Expr Nat)) (hb1' : args.length ≤ args₁.length)
      (hb2' : args.length ≤ args₂.length) (hl : args.length = Ts.length),
      ∀ i : Fin args.length,
        IsPropTyI E n Γ (Ts.get (i.cast hl)) ∨
        LRTermDCore E n Γ (args₁.get (i.castLE hb1')) (args₂.get (i.castLE hb2'))
          (Ts.get (i.cast hl)) (args.get i) := by
  refine ⟨List.replicate args.length idPiProp, hb1, hb2,
    (List.length_replicate args.length idPiProp).symm, fun i => Or.inl ?_⟩
  have hget : (List.replicate args.length idPiProp).get
      (i.cast (List.length_replicate args.length idPiProp).symm) = idPiProp := by
    simp
  rw [hget]
  exact isPropTyI_idPiProp E n Γ

/-- Equivalence simplifying `LRTermDCore` at `.spine r args` by discharging the unconstrained
    argument-type existential via `lrTermDCore_dataSpine_args_vacuous`. -/
theorem lrTermDCore_spine_iff_simple (Γ : LCtx) (M M' A : Expr Nat) (r : Nat)
    (args : List CptI) :
    LRTermDCore E n Γ M M' A (.spine r args) ↔
      ((∃ l, WhRed E A (.sort l)) ∧ LRTypeIN E n Γ M M' (.spine r args)) ∨
      (∃ ls₁ ls₂ args₁ args₂,
        WhRed E M (foldApps (.const r ls₁) args₁) ∧
        WhRed E M' (foldApps (.const r ls₂) args₂) ∧
        WhNormal E (foldApps (.const r ls₁) args₁) ∧
        WhNormal E (foldApps (.const r ls₂) args₂) ∧
        Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
          (foldApps (.const r ls₂) args₂) A) ∧
        args.length ≤ args₁.length ∧ args.length ≤ args₂.length) := by
  rw [lrTermDCore_spine_iff]
  constructor
  · rintro (h1 | ⟨ls₁, ls₂, args₁, args₂, hM, hM', n1, n2, hc, _, hb1, hb2, _, _⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨ls₁, ls₂, args₁, args₂, hM, hM', n1, n2, hc, hb1, hb2⟩
  · rintro (h1 | ⟨ls₁, ls₂, args₁, args₂, hM, hM', n1, n2, hc, hb1, hb2⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨ls₁, ls₂, args₁, args₂, hM, hM', n1, n2, hc,
        lrTermDCore_dataSpine_args_vacuous E n Γ args hb1 hb2⟩

/-- Under universe consistency `hSort`, `LRTermD` is false on the diagonal of `etaIdPiPropFn`
    at `etaIdPiPropCpt` in `Γ = []` (refuting `#7653`'s `EtaDiagD E n`). -/
theorem not_lrTermD_etaIdPiPropFn_diag
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂) :
    ¬ LRTermD E n [] etaIdPiPropFn etaIdPiPropFn
        (.pi (.sort .zero) (.sort .zero)) etaIdPiPropCpt := by
  rintro (hP | hcore)
  · exact not_isPropTyI_pi_sort0_sort0 hSort [] hP
  · exact not_lrTermDCore_etaIdPiPropFn_diag E n hcore

/-- `LRTermDCore` is unconditionally false on the η-K pair
    `(.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)), etaIdPiPropFn)` at
    `etaIdPiPropCpt` in `Γ = []` for **every** `E : ResolvedEnv` and `n : Nat` (where
    `etaIdPiPropFn = .lam (.sort .zero) idPiProp`). -/
theorem not_lrTermDCore_etaK_etaIdPiPropFn (E : ResolvedEnv) (n : Nat) :
    ¬ LRTermDCore E n [] (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)))
        (.lam (.sort .zero) idPiProp) (.pi (.sort .zero) (.sort .zero)) etaIdPiPropCpt :=
  not_lrTermDCore_eta_etaIdPiPropFn E n

/-- Under universe consistency `hSort`, `LRTermD` is false on the η-K pair
    `(.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)), .lam (.sort .zero) idPiProp)`
    at `etaIdPiPropCpt` in `Γ = []` (refuting `#7653`'s `EtaKChainD E n`). -/
theorem not_lrTermD_etaK_etaIdPiPropFn
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂) :
    ¬ LRTermD E n [] (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)))
        (.lam (.sort .zero) idPiProp) (.pi (.sort .zero) (.sort .zero)) etaIdPiPropCpt :=
  not_lrTermD_eta_etaIdPiPropFn hSort

/-- Closed type-polymorphic function `fun (X : Sort 1) => Π (_ : X), X` of type
    `Π (_ : Sort 1), Sort 1` in `Γ = []`. -/
def polyPi : Expr Nat :=
  .lam (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))

/-- Step-function compact `λ ([] ↦ .pi .bot [])` approximating `polyPi` (whose inner `.pi` compact
    is `.pi .bot []`, which satisfies `BotPiCpt`). -/
def polyPiCpt : CptI :=
  .lam [([], .pi .bot [])]

/-- `polyPi` has type `.pi (.sort (.succ .zero)) (.sort (.succ .zero))` (`Sort 1 → Sort 1`) in
    `Γ = []` for every `E : ResolvedEnv` and `n : Nat`. -/
def hasTyT_polyPi (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] polyPi (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .lam [] (.sort (.succ .zero)) (.succ (.succ .zero))
    (.pi (.bvar 0) (.bvar 1)) (.sort (.succ .zero))
    (.sort [] (.succ .zero))
    (.conv [.assumption (.sort (.succ .zero))] (.pi (.bvar 0) (.bvar 1))
      (.sort (.imax (.succ .zero) (.succ .zero))) (.sort (.succ .zero))
      (.succ (.imax (.succ .zero) (.succ .zero)))
      (.pi [.assumption (.sort (.succ .zero))] (.bvar 0) (.succ .zero) (.bvar 1) (.succ .zero)
        (.bvar _ 0 (.sort (.succ .zero)) rfl)
        (.bvar _ 1 (.sort (.succ .zero)) rfl))
      (.sorts [.assumption (.sort (.succ .zero))]
        (.imax (.succ .zero) (.succ .zero)) (.succ .zero)
        (fun ρ => by simp [eval])))

/-- `polyPiCpt = .lam [([], .pi .bot [])]` approximates `polyPi` in `ApproxI EnvI.bot`. -/
theorem approxI_polyPi :
    ApproxI EnvI.bot polyPi polyPiCpt := by
  refine .lam (fun s hs => ?_)
  simp only [List.mem_singleton] at hs; subst hs
  exact .pi (.bot _ _) (fun _ h => nomatch h)

/-- `polyPiCpt = .lam [([], .pi .bot [])]` approximates `polyPi` in `ApproxDI E EnvI.bot`. -/
theorem approxDI_polyPi (E : ResolvedEnv) :
    ApproxDI E EnvI.bot polyPi polyPiCpt := by
  refine .lam (fun s hs => ?_)
  simp only [List.mem_singleton] at hs; subst hs
  exact .pi (.bot _ _) (fun _ h => nomatch h)

/-- **Admitted Obstruction (`tyConvT_pi_sort_of_lrTermDCore_polyPi`)**: because the `.lam g` clause
    of `LRTermI`, `LRTermS`, `LRTermSDI`, and `LRTermDCore` only requires
    `∀ u ∈ s.1, LRTerm* E n Γ N N' A₁ u` without requiring `ConvT E n Γ N N' A₁`, at
    `s = ([], .pi .bot [])` (where `s.1 = []` and `s.2 = .pi .bot []` IS `BotPiCpt`!) any two
    unrelated closed types `N = .pi (.sort .zero) (.sort .zero)` and `N' = .sort .zero` of type
    `.sort (.succ .zero)` satisfy the `s.1 = []` premise vacuously, forcing
    `TyConvT E n [] (.pi (.sort .zero) (.sort .zero)) (.sort .zero)`! -/
theorem tyConvT_pi_sort_of_lrTermDCore_polyPi
    (h : LRTermDCore E n [] polyPi polyPi
      (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) polyPiCpt) :
    Nonempty (TyConvT E n [] (.pi (.sort .zero) (.sort .zero)) (.sort .zero)) := by
  rw [polyPiCpt, lrTermDCore_lam_iff] at h
  obtain ⟨A₁, B₁, _, hP, _, _, happ⟩ := h
  have e := whRed_pi_eq hP
  injection e with eA eB; subst eA; subst eB
  have hN : HasTyT E n [] (.pi (.sort .zero) (.sort .zero)) (.sort (.succ .zero)) :=
    .conv [] (.pi (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) (.sort (.succ .zero))
      (.succ (.imax (.succ .zero) (.succ .zero)))
      (.pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
        (.sort [] .zero) (.sort [.assumption (.sort .zero)] .zero))
      (.sorts [] (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun ρ => by simp [eval]))
  have hN' : HasTyT E n [] (.sort .zero) (.sort (.succ .zero)) := .sort [] .zero
  have h₂ := happ ([], .pi .bot []) (List.Mem.head _)
    (.pi (.sort .zero) (.sort .zero)) (.sort .zero) hN hN' (fun _ hu => nomatch hu)
  change IsPropTyI E n [] (.sort (.succ .zero)) ∨
    LRTermDCore E n [] (.app polyPi (.pi (.sort .zero) (.sort .zero)))
      (.app polyPi (.sort .zero)) (.sort (.succ .zero)) (.pi .bot []) at h₂
  rcases h₂ with hP₁ | hcore
  · exact (not_isPropTyI_sort E n [] (.succ .zero) hP₁).elim
  · rw [lrTermDCore_pi_iff] at hcore
    cases hcore.2 with
    | pi hL hR _ hdom _ _ _ =>
        have hL₁ : WhRed E (.pi (.pi (.sort .zero) (.sort .zero))
            (.pi (.sort .zero) (.sort .zero))) (.pi _ _) :=
          whRed_step_inv_of_unique hL (fun _ => whStep_app_lam_eq) (fun h => by cases h)
        have hR₁ : WhRed E (.pi (.sort .zero) (.sort .zero)) (.pi _ _) :=
          whRed_step_inv_of_unique hR (fun _ => whStep_app_lam_eq) (fun h => by cases h)
        have eL := whRed_pi_eq hL₁
        have eR := whRed_pi_eq hR₁
        injection eL with eA₁ _; subst eA₁
        injection eR with eA₂ _; subst eA₂
        exact ⟨hdom⟩

/-- In any environment where `.pi (.sort .zero) (.sort .zero)` is not `TyConvT`-convertible to
    `.sort .zero` (in particular under `FundamentalLRINBotDI E n` or `FundamentalTermBotDI E n`),
    `LRTermDCore` is false on the diagonal of `polyPi` at `polyPiCpt = .lam [([], .pi .bot [])]`. -/
theorem not_lrTermDCore_polyPi_of_not_pi_sort
    (hdisj : ¬ Nonempty (TyConvT E n [] (.pi (.sort .zero) (.sort .zero)) (.sort .zero))) :
    ¬ LRTermDCore E n [] polyPi polyPi
        (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) polyPiCpt :=
  fun h => hdisj (tyConvT_pi_sort_of_lrTermDCore_polyPi h)

/-! ## §7. Symmetry and Transitivity of `LRTermS`, `LRTermSDI`, `LRTermDCore`, and `LRTermD` on Non-`λ`, `BotPiCpt`, and `FirstOrderCpt` Compacts -/

/-- Any weak-head reduction from a `WhNormal` term is reflexive. -/
theorem whRed_of_whNormal {a b : Expr Nat} (hn : WhNormal E a) (h : WhRed E a b) : a = b := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hn _ hs).elim

/-- Every `BotPiCpt` compact is non-`.lam` (`∀ g, c ≠ .lam g`) and non-`.spine`
    (`∀ r args, c ≠ .spine r args`). -/
theorem noLam_of_botPiCpt {c : CptI} (hc : BotPiCpt c) :
    (∀ g, c ≠ .lam g) ∧ (∀ r args, c ≠ .spine r args) := by
  cases hc <;> exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩

/-- Symmetry of `LRTermS` across all non-`.lam` compacts (`.bot`, `.sort`, `.pi a f`,
    `.spine r args`) at every `EnvWfT E`. -/
theorem lrTermS_noLam_symm (hW : EnvWfT E) {c : CptI} (hno : ∀ g, c ≠ .lam g)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermS E n Γ M M' A c) :
    LRTermS E n Γ M' M A c := by
  cases c with
  | bot => exact lrTermS_bot _ _ _ _
  | sort =>
      rw [lrTermS_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW h.2⟩
  | pi a f =>
      rw [lrTermS_pi_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW h.2⟩
  | spine r args =>
      rw [lrTermS_spine_iff] at h ⊢
      rcases h with ⟨hl, hLR⟩ | ⟨hsp, X, X', hX, hX', nX, nX', ⟨hc⟩⟩
      · exact Or.inl ⟨hl, lrTypeIN_symm (envClosed_of_envWfT hW) hW hLR⟩
      · exact Or.inr ⟨hsp, X', X, hX', hX, nX', nX, ⟨.symm _ _ _ _ hc⟩⟩
  | lam g => exact (hno g rfl).elim

/-- Symmetry of `LRTermSDI` across all non-`.lam` compacts (`.bot`, `.sort`, `.pi a f`,
    `.spine r args`) at every `EnvWfT E`. -/
theorem lrTermSDI_noLam_symm (hW : EnvWfT E) {c : CptI} (hno : ∀ g, c ≠ .lam g)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermSDI E n Γ M M' A c) :
    LRTermSDI E n Γ M' M A c := by
  cases c with
  | bot => exact lrTermSDI_bot _ _ _ _
  | sort =>
      rw [lrTermSDI_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW h.2⟩
  | pi a f =>
      rw [lrTermSDI_pi_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW h.2⟩
  | spine r args =>
      rw [lrTermSDI_spine_iff] at h ⊢
      rcases h with ⟨hl, hLR⟩ | ⟨hsp, X, X', hX, hX', nX, nX', ⟨hc⟩⟩
      · exact Or.inl ⟨hl, lrTypeIN_symm (envClosed_of_envWfT hW) hW hLR⟩
      · exact Or.inr ⟨hsp, X', X, hX', hX, nX', nX, ⟨.symm _ _ _ _ hc⟩⟩
  | lam g => exact (hno g rfl).elim

/-- Symmetry of `LRTermDCore` across all non-`.lam` compacts (`.bot`, `.sort`, `.pi a f`,
    `.spine r args`, using `lrTermDCore_spine_iff_simple`) at every `EnvWfT E`. -/
theorem lrTermDCore_noLam_symm (hW : EnvWfT E) {c : CptI} (hno : ∀ g, c ≠ .lam g)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermDCore E n Γ M M' A c) :
    LRTermDCore E n Γ M' M A c := by
  cases c with
  | bot => exact lrTermDCore_bot _ _ _ _
  | sort =>
      rw [lrTermDCore_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW h.2⟩
  | pi a f =>
      rw [lrTermDCore_pi_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW h.2⟩
  | spine r args =>
      rw [lrTermDCore_spine_iff_simple] at h ⊢
      rcases h with ⟨hl, hLR⟩ | ⟨ls₁, ls₂, args₁, args₂, hM, hM', n1, n2, ⟨hc⟩, hb1, hb2⟩
      · exact Or.inl ⟨hl, lrTypeIN_symm (envClosed_of_envWfT hW) hW hLR⟩
      · exact Or.inr ⟨ls₂, ls₁, args₂, args₁, hM', hM, n2, n1, ⟨.symm _ _ _ _ hc⟩, hb2, hb1⟩
  | lam g => exact (hno g rfl).elim

/-- Symmetry of `LRTermD` across all non-`.lam` compacts at every `EnvWfT E`. -/
theorem lrTermD_noLam_symm (hW : EnvWfT E) {c : CptI} (hno : ∀ g, c ≠ .lam g)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermD E n Γ M M' A c) :
    LRTermD E n Γ M' M A c := by
  rcases h with hP | hcore
  · exact Or.inl hP
  · exact Or.inr (lrTermDCore_noLam_symm hW hno hcore)

/-- Transitivity of `LRTermS` across all non-`.lam`, non-`.spine` compacts (`.bot`, `.sort`,
    `.pi a f`) at every `EnvWfT E` (using `lrTypeIN_trans_of_envWfT`, without `WhDet` or
    `TypeSoundness`). -/
theorem lrTermS_noLam_trans (hW : EnvWfT E) {c : CptI}
    (hno : (∀ g, c ≠ .lam g) ∧ (∀ r args, c ≠ .spine r args))
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermS E n Γ M N A c) (h₂ : LRTermS E n Γ N P A c) :
    LRTermS E n Γ M P A c := by
  cases c with
  | bot => exact lrTermS_bot _ _ _ _
  | sort =>
      rw [lrTermS_sort_iff] at h₁ h₂ ⊢
      exact ⟨h₁.1, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW h₁.2 h₂.2⟩
  | pi a f =>
      rw [lrTermS_pi_iff] at h₁ h₂ ⊢
      exact ⟨h₁.1, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW h₁.2 h₂.2⟩
  | spine r args => exact (hno.2 r args rfl).elim
  | lam g => exact (hno.1 g rfl).elim

/-- Transitivity of `LRTermSDI` across **all** non-`.lam` compacts (including `.spine r args`!) at
    every `EnvWfT E`: in `ApproxDI`, the type-code branch (`WhRed E A (.sort l)`) and the
    constructor-spine branch (`ApproxDI E EnvI.bot A (.spine r' args')`) are mutually exclusive via
    `semEqDI_whRed` + `approxDI_sort_inv`. -/
theorem lrTermSDI_noLam_trans (hW : EnvWfT E) {c : CptI} (hno : ∀ g, c ≠ .lam g)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermSDI E n Γ M N A c) (h₂ : LRTermSDI E n Γ N P A c) :
    LRTermSDI E n Γ M P A c := by
  cases c with
  | bot => exact lrTermSDI_bot _ _ _ _
  | sort =>
      rw [lrTermSDI_sort_iff] at h₁ h₂ ⊢
      exact ⟨h₁.1, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW h₁.2 h₂.2⟩
  | pi a f =>
      rw [lrTermSDI_pi_iff] at h₁ h₂ ⊢
      exact ⟨h₁.1, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW h₁.2 h₂.2⟩
  | spine r args =>
      rw [lrTermSDI_spine_iff] at h₁ h₂ ⊢
      rcases h₁ with ⟨⟨l, hl⟩, hLR₁⟩ | ⟨⟨r', args', hsp⟩, X₁, X₂, hM, hN₁, n1, n2, ⟨hc₁⟩⟩
      · rcases h₂ with ⟨_, hLR₂⟩ | ⟨⟨r', args', hsp⟩, _, _, _, _, _, _, _⟩
        · exact Or.inl ⟨⟨l, hl⟩, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW hLR₁ hLR₂⟩
        · have hsp' : ApproxDI E EnvI.bot (.sort l) (.spine r' args') :=
            (semEqDI_whRed hW hl EnvI.bot (.spine r' args')).mp hsp
          rcases approxDI_sort_inv hsp' with h0 | h0 <;> cases h0
      · rcases h₂ with ⟨⟨l, hl⟩, _⟩ | ⟨_, X₂', X₃, hN₂, hP, n2', n3, ⟨hc₂⟩⟩
        · have hsp' : ApproxDI E EnvI.bot (.sort l) (.spine r' args') :=
            (semEqDI_whRed hW hl EnvI.bot (.spine r' args')).mp hsp
          rcases approxDI_sort_inv hsp' with h0 | h0 <;> cases h0
        · have heq : X₂ = X₂' := whRed_normal_unique_of_envWfT hW hN₁ n2 hN₂ n2'
          subst heq
          exact Or.inr ⟨⟨r', args', hsp⟩, X₁, X₃, hM, hP, n1, n3,
            ⟨.trans _ _ _ _ _ hc₁ hc₂⟩⟩
  | lam g => exact (hno g rfl).elim

/-- Transitivity of `LRTermDCore` across all non-`.lam`, non-`.spine` compacts (`.bot`, `.sort`,
    `.pi a f`) at every `EnvWfT E`. -/
theorem lrTermDCore_noLam_trans (hW : EnvWfT E) {c : CptI}
    (hno : (∀ g, c ≠ .lam g) ∧ (∀ r args, c ≠ .spine r args))
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermDCore E n Γ M N A c) (h₂ : LRTermDCore E n Γ N P A c) :
    LRTermDCore E n Γ M P A c := by
  cases c with
  | bot => exact lrTermDCore_bot _ _ _ _
  | sort =>
      rw [lrTermDCore_sort_iff] at h₁ h₂ ⊢
      exact ⟨h₁.1, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW h₁.2 h₂.2⟩
  | pi a f =>
      rw [lrTermDCore_pi_iff] at h₁ h₂ ⊢
      exact ⟨h₁.1, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW h₁.2 h₂.2⟩
  | spine r args => exact (hno.2 r args rfl).elim
  | lam g => exact (hno.1 g rfl).elim

/-- Transitivity of `LRTermD` across all non-`.lam`, non-`.spine` compacts (`.bot`, `.sort`,
    `.pi a f`) at every `EnvWfT E`. -/
theorem lrTermD_noLam_trans (hW : EnvWfT E) {c : CptI}
    (hno : (∀ g, c ≠ .lam g) ∧ (∀ r args, c ≠ .spine r args))
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermD E n Γ M N A c) (h₂ : LRTermD E n Γ N P A c) :
    LRTermD E n Γ M P A c := by
  rcases h₁ with hP | hcore₁
  · exact Or.inl hP
  · rcases h₂ with hP | hcore₂
    · exact Or.inl hP
    · exact Or.inr (lrTermDCore_noLam_trans hW hno hcore₁ hcore₂)

/-- Left-reflexivity of `LRTermS` on non-`.lam`, non-`.spine` compacts (`M ~ N → M ~ M`) at every
    `EnvWfT E`. -/
theorem lrTermS_noLam_refl_left (hW : EnvWfT E) {c : CptI}
    (hno : (∀ g, c ≠ .lam g) ∧ (∀ r args, c ≠ .spine r args))
    {Γ : LCtx} {M N A : Expr Nat} (h : LRTermS E n Γ M N A c) :
    LRTermS E n Γ M M A c :=
  lrTermS_noLam_trans hW hno h (lrTermS_noLam_symm hW hno.1 h)

/-- Left-reflexivity of `LRTermSDI` on all non-`.lam` compacts (including `.spine r args`) at every
    `EnvWfT E`. -/
theorem lrTermSDI_noLam_refl_left (hW : EnvWfT E) {c : CptI} (hno : ∀ g, c ≠ .lam g)
    {Γ : LCtx} {M N A : Expr Nat} (h : LRTermSDI E n Γ M N A c) :
    LRTermSDI E n Γ M M A c :=
  lrTermSDI_noLam_trans hW hno h (lrTermSDI_noLam_symm hW hno h)

/-- Left-reflexivity of `LRTermDCore` on non-`.lam`, non-`.spine` compacts at every `EnvWfT E`. -/
theorem lrTermDCore_noLam_refl_left (hW : EnvWfT E) {c : CptI}
    (hno : (∀ g, c ≠ .lam g) ∧ (∀ r args, c ≠ .spine r args))
    {Γ : LCtx} {M N A : Expr Nat} (h : LRTermDCore E n Γ M N A c) :
    LRTermDCore E n Γ M M A c :=
  lrTermDCore_noLam_trans hW hno h (lrTermDCore_noLam_symm hW hno.1 h)

/-- First-order compact elements (`FirstOrderCpt`): includes `.bot`, `.sort`, `.pi a f`, and all
    curried `.lam g` compacts of arbitrary arity whose input demands `u ∈ s.1` are `.bot`, `.sort`,
    or `.pi` compacts. -/
inductive FirstOrderCpt : CptI → Prop
  | bot : FirstOrderCpt .bot
  | sort : FirstOrderCpt .sort
  | pi (a : CptI) (f : List (List CptI × CptI)) : FirstOrderCpt (.pi a f)
  | lam {g : List (List CptI × CptI)}
      (hdom : ∀ s ∈ g, ∀ u ∈ s.1, (∀ g', u ≠ .lam g') ∧ (∀ r args, u ≠ .spine r args))
      (hcod : ∀ s ∈ g, FirstOrderCpt s.2) :
      FirstOrderCpt (.lam g)

/-- Every `BotPiCpt` compact is a `FirstOrderCpt`. -/
theorem firstOrderCpt_of_botPiCpt {c : CptI} (hc : BotPiCpt c) : FirstOrderCpt c := by
  cases hc with
  | bot => exact .bot
  | sort => exact .sort
  | pi _ _ _ => exact .pi _ _

/-- Transitivity of `LRTermS` across all `FirstOrderCpt` compacts (including curried `.lam g`
    compacts) at every `EnvWfT E` — requiring **no** `WhDet`, **no** `TypeSoundness`, and **no**
    index transport (because in `happ₁₂` at `(N, N)` and `happ₂₃` at `(N, N')`, the left argument
    is `N` in both calls, so both calls share the exact same codomain index `instantiate0 N B₁`). -/
theorem lrTermS_firstOrder_trans (hW : EnvWfT E) {c : CptI} (hc : FirstOrderCpt c)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermS E n Γ M N A c) (h₂ : LRTermS E n Γ N P A c) :
    LRTermS E n Γ M P A c := by
  induction hc generalizing Γ M N P A with
  | bot => exact lrTermS_bot _ _ _ _
  | sort =>
      exact lrTermS_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂
  | pi a f =>
      exact lrTermS_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂
  | @lam g hdom _ ih =>
      rw [lrTermS_lam_iff] at h₁ h₂ ⊢
      obtain ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, happ₁₂⟩ := h₁
      obtain ⟨A₂, B₂, _, hA₂, _, _, happ₂₃⟩ := h₂
      have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
        whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
          hA₂ (fun _ h => whStep_pi_false h)
      injection heq with eA eB; subst eA; subst eB
      refine ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, fun s hs N N' hN hN' hrel => ?_⟩
      have hrelNN : ∀ u ∈ s.1, LRTermS E n Γ N N A₁ u :=
        fun u hu => lrTermS_noLam_refl_left hW (hdom s hs u hu) (hrel u hu)
      exact ih s hs (happ₁₂ s hs N N hN hN hrelNN) (happ₂₃ s hs N N' hN hN' hrel)

/-- Transitivity of `LRTermSDI` across all `FirstOrderCpt` compacts at every `EnvWfT E`. -/
theorem lrTermSDI_firstOrder_trans (hW : EnvWfT E) {c : CptI} (hc : FirstOrderCpt c)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermSDI E n Γ M N A c) (h₂ : LRTermSDI E n Γ N P A c) :
    LRTermSDI E n Γ M P A c := by
  induction hc generalizing Γ M N P A with
  | bot => exact lrTermSDI_bot _ _ _ _
  | sort =>
      exact lrTermSDI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | pi a f =>
      exact lrTermSDI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | @lam g hdom _ ih =>
      rw [lrTermSDI_lam_iff] at h₁ h₂ ⊢
      obtain ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, happ₁₂⟩ := h₁
      obtain ⟨A₂, B₂, _, hA₂, _, _, happ₂₃⟩ := h₂
      have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
        whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
          hA₂ (fun _ h => whStep_pi_false h)
      injection heq with eA eB; subst eA; subst eB
      refine ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, fun s hs N N' hN hN' hrel => ?_⟩
      have hrelNN : ∀ u ∈ s.1, LRTermSDI E n Γ N N A₁ u :=
        fun u hu => lrTermSDI_noLam_refl_left hW (hdom s hs u hu).1 (hrel u hu)
      exact ih s hs (happ₁₂ s hs N N hN hN hrelNN) (happ₂₃ s hs N N' hN hN' hrel)

/-- Transitivity of `LRTermDCore` across all `FirstOrderCpt` compacts (including curried `.lam g`
    compacts) at every `EnvWfT E` — discharging `#7653`'s `lrTermD_trans` obligation across all
    `FirstOrderCpt` compacts without `WhDet`, `TypeSoundness`, or index transport. -/
theorem lrTermDCore_firstOrder_trans (hW : EnvWfT E) {c : CptI} (hc : FirstOrderCpt c)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermDCore E n Γ M N A c) (h₂ : LRTermDCore E n Γ N P A c) :
    LRTermDCore E n Γ M P A c := by
  induction hc generalizing Γ M N P A with
  | bot => exact lrTermDCore_bot _ _ _ _
  | sort =>
      exact lrTermDCore_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂
  | pi a f =>
      exact lrTermDCore_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂
  | @lam g hdom _ ih =>
      rw [lrTermDCore_lam_iff] at h₁ h₂ ⊢
      obtain ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, happ₁₂⟩ := h₁
      obtain ⟨A₂, B₂, _, hA₂, _, _, happ₂₃⟩ := h₂
      have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
        whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
          hA₂ (fun _ h => whStep_pi_false h)
      injection heq with eA eB; subst eA; subst eB
      refine ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, fun s hs N N' hN hN' hrel => ?_⟩
      have hrelNN : ∀ u ∈ s.1, LRTermDCore E n Γ N N A₁ u :=
        fun u hu => lrTermDCore_noLam_refl_left hW (hdom s hs u hu) (hrel u hu)
      rcases happ₁₂ s hs N N hN hN hrelNN with hP | hcore₁₂
      · exact Or.inl hP
      · rcases happ₂₃ s hs N N' hN hN' hrel with hP | hcore₂₃
        · exact Or.inl hP
        · exact Or.inr (ih s hs hcore₁₂ hcore₂₃)

/-- Transitivity of `LRTermD` across all `FirstOrderCpt` compacts at every `EnvWfT E`. -/
theorem lrTermD_firstOrder_trans (hW : EnvWfT E) {c : CptI} (hc : FirstOrderCpt c)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermD E n Γ M N A c) (h₂ : LRTermD E n Γ N P A c) :
    LRTermD E n Γ M P A c := by
  rcases h₁ with hP | hcore₁
  · exact Or.inl hP
  · rcases h₂ with hP | hcore₂
    · exact Or.inl hP
    · exact Or.inr (lrTermDCore_firstOrder_trans hW hc hcore₁ hcore₂)

/-- Symmetry of `LRTermD` on `BotPiCpt` compacts at every `EnvWfT E`. -/
theorem lrTermD_botPiCpt_symm (hW : EnvWfT E) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermD E n Γ M M' A c) :
    LRTermD E n Γ M' M A c :=
  lrTermD_noLam_symm hW (noLam_of_botPiCpt hc).1 h

/-- Transitivity of `LRTermD` on `BotPiCpt` compacts at every `EnvWfT E`. -/
theorem lrTermD_botPiCpt_trans (hW : EnvWfT E) {c : CptI} (hc : BotPiCpt c)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermD E n Γ M N A c) (h₂ : LRTermD E n Γ N P A c) :
    LRTermD E n Γ M P A c :=
  lrTermD_noLam_trans hW (noLam_of_botPiCpt hc) h₁ h₂

/-- The `ConvT.symm` case of `FundamentalTermBotDI`: symmetry of the bilateral `BotPiCpt` clause
    `∀ u, BotPiCpt u → (ApproxDI E EnvI.bot M u ∨ ApproxDI E EnvI.bot M' u) → LRTermD E n Γ M M' A u`. -/
theorem fundConvBotDI_symm (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (ih : ∀ u, BotPiCpt u →
      (ApproxDI E EnvI.bot M u ∨ ApproxDI E EnvI.bot M' u) →
      LRTermD E n Γ M M' A u) :
    ∀ u, BotPiCpt u →
      (ApproxDI E EnvI.bot M' u ∨ ApproxDI E EnvI.bot M u) →
      LRTermD E n Γ M' M A u :=
  fun u hu happrox => lrTermD_botPiCpt_symm hW hu (ih u hu happrox.symm)

/-- The `ConvT.tyConv` case of `FundamentalTermBotDI` (using `lrTermD_transport` from §2). -/
theorem fundConvBotDI_tyConv (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDI E n)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M M' A A' : Expr Nat} {v : Level}
    (hA : HasTyT E n Γ A (.sort v)) (hAA' : TyConvT E n Γ A A')
    (ih : ∀ u, BotPiCpt u →
      (ApproxDI E EnvI.bot M u ∨ ApproxDI E EnvI.bot M' u) →
      LRTermD E n Γ M M' A u) :
    ∀ u, BotPiCpt u →
      (ApproxDI E EnvI.bot M u ∨ ApproxDI E EnvI.bot M' u) →
      LRTermD E n Γ M M' A' u :=
  fun u hu happrox => lrTermD_transport hW hBot hProp hΓ hA hAA' u (ih u hu happrox)

/-! ## §8. Direct Discharge of `FundamentalTermIS` (#7660), Side-Condition-Free `IsPropTyI` Substitution (#7653/#7655), All-Variable (`< / = / >`) Related Substitution, and Data-Spine Substitution Stability -/

/-- The `ApproxDI` counterpart of `RcicNativePiModelLRTermSubst.approxSubst` (#7660):
    instantiating index `j` with `lift 0 j r` is equivalent to inserting the full `ApproxDI`
    denotation `denDI E (EnvI.drop ρ j) r` at index `j`. -/
theorem approxSubstDI (E : ResolvedEnv) (ρ : EnvI) (j : Nat) (r e : Expr Nat) (c : CptI) :
    ApproxDI E ρ (instantiate j (lift 0 j r) e) c ↔
      ApproxDI E (EnvI.insert ρ j (denDI E (EnvI.drop ρ j) r)) e c :=
  ⟨fun h => approxDI_subst_elim e h, fun h => approxDI_subst_intro h ρ j r rfl⟩

/-- Unconditional discharge of `RcicNativePiModelLRTermSubst.FundamentalTermIS` (#7660) under
    `EnvClosed E`: the `hι` hypothesis on `DerivedIotaU` instantiation is discharged unconditionally
    by §14.1 `whStep_iota_instantiate`. -/
theorem fundamentalTermIS_of_envClosed (hcl : EnvClosed E) {ρ : EnvI} {j : Nat}
    {r r' T : Expr Nat} {Γ : LCtx}
    (hrel : ∀ c, ApproxI (EnvI.drop ρ j) r c →
      LRTermS E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermS E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M M' A : Expr Nat},
        LRTermS E n Γ M M' A .sort →
        LRTermS E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxI ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermS E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) :=
  FundamentalTermIS (fun h j s => whStep_iota_instantiate h j s) hcl hrel

/-- `EnvWfT`-fronted specialization of `fundamentalTermIS_of_envClosed`. -/
theorem fundamentalTermIS_of_envWfT (hW : EnvWfT E) {ρ : EnvI} {j : Nat}
    {r r' T : Expr Nat} {Γ : LCtx}
    (hrel : ∀ c, ApproxI (EnvI.drop ρ j) r c →
      LRTermS E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermS E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M M' A : Expr Nat},
        LRTermS E n Γ M M' A .sort →
        LRTermS E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxI ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermS E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) :=
  fundamentalTermIS_of_envClosed (envClosed_of_envWfT hW) hrel

/-- Full `ApproxDI` / `LRTermSDI` version of `FundamentalTermIS` (#7660) under `EnvClosed E`. -/
theorem fundamentalTermIS_DI (hcl : EnvClosed E) {ρ : EnvI} {j : Nat}
    {r r' T : Expr Nat} {Γ : LCtx}
    (hrel : ∀ c, ApproxDI E (EnvI.drop ρ j) r c →
      LRTermSDI E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermSDI E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M M' A : Expr Nat},
        LRTermSDI E n Γ M M' A .sort →
        LRTermSDI E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxDI E ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermSDI E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) :=
  ⟨fun {_ _ _} => lrTermSDI_bot _ _ _ _,
   (lrTermSDI_subst_sort_and_bvar hcl hrel).1,
   (lrTermSDI_subst_sort_and_bvar hcl hrel).2⟩

/-- Under universe consistency `hSort`, no literal sort `.sort l` can have type `.sort .zero`:
    `hasTyT_sort_inv` produces `TyConvT E n Γ (.sort (.succ l)) (.sort .zero)`, which `hSort`
    refutes at the level valuation `fun _ => some 0`. -/
theorem not_hasTyT_sort_zero_of_sortRow {Γ : LCtx}
    (hSort : ∀ {l₁ l₂ : Level}, TyConvT E n Γ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (l : Level) (h : HasTyT E n Γ (.sort l) (.sort .zero)) : False := by
  have hcv := hasTyT_sort_inv h rfl
  have hev := hSort hcv (fun _ => some 0)
  cases hl : eval (fun _ => some 0) l with
  | none =>
      simp only [eval, hl, Option.map_none] at hev
      cases hev
  | some k =>
      simp only [eval, hl, Option.map_some] at hev
      cases hev

/-- Under universe consistency `hSort`, **every** expression `P` typed at `.sort .zero`
    automatically satisfies `∀ l, P ≠ .sort l` and hence `IsPropTyI E n Γ P` — eliminating the
    extra syntactic `∀ l, P ≠ .sort l` hypothesis from `#7653` (`IrrCaseD`, `KCaseD`, `EtaKCaseD`)
    and the `∀ l, r ≠ .sort l` hypothesis from `#7655` (`isPropTyI_subst`) without needing
    `SortUnique`. -/
theorem isPropTyI_of_hasTyT_sort_zero {Γ : LCtx}
    (hSort : ∀ {l₁ l₂ : Level}, TyConvT E n Γ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {P : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero)) :
    IsPropTyI E n Γ P :=
  ⟨⟨hP⟩, fun l hl => not_hasTyT_sort_zero_of_sortRow hSort l (hl ▸ hP)⟩

/-- Under universe consistency `hSort`, `IsPropTyI E n Γ P` is equivalent to
    `Nonempty (HasTyT E n Γ P (.sort .zero))`. -/
theorem isPropTyI_iff_hasTyT_sort_zero {Γ : LCtx}
    (hSort : ∀ {l₁ l₂ : Level}, TyConvT E n Γ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (P : Expr Nat) :
    IsPropTyI E n Γ P ↔ Nonempty (HasTyT E n Γ P (.sort .zero)) :=
  ⟨fun h => h.1, fun ⟨hP⟩ => isPropTyI_of_hasTyT_sort_zero hSort hP⟩

/-- From `TypedRowsWf E n` (`hRows.sortRow`), every `P` with `HasTyT E n Γ P (.sort .zero)` in a
    well-formed context `Γ` satisfies `IsPropTyI E n Γ P`. -/
theorem isPropTyI_of_hasTyT_sort_zero_botDI (hRows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {P : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) :
    IsPropTyI E n Γ P :=
  isPropTyI_of_hasTyT_sort_zero (hRows.sortRow hΓ) hP

/-- Lifting preserves non-sorts: if `lift k d e = .sort l`, then `e = .sort l`. -/
theorem lift_sort_inv_term {k d : Nat} {e : Expr Nat} {l : Level}
    (h : lift k d e = .sort l) : e = .sort l := by
  cases e <;> simp only [lift] at h
  case bvar i => split at h <;> exact nomatch h
  case sort l' => exact h
  all_goals exact nomatch h

/-- Unconditional weakening stability of `IsPropTyI` under `EnvClosed E` alone (requiring no
    `hSort` or `SortUnique` hypothesis). -/
theorem isPropTyI_weaken (hcl : EnvClosed E) (d : LocalDecl)
    {Γ : LCtx} {c : Nat} {P : Expr Nat} (h : IsPropTyI E n Γ P) :
    IsPropTyI E n (insertAt d c Γ) (lift c 1 P) := by
  obtain ⟨⟨hP⟩, hns⟩ := h
  refine ⟨⟨hasTyTWeaken d hcl (c := c) hP⟩, fun l hl => hns l (lift_sort_inv_term hl)⟩

/-- Head (`c = 0`) specialization: `IsPropTyI` is stable under `lift 0 1` when extending `Γ`
    by any declaration `d`. -/
theorem isPropTyI_weaken0 (hcl : EnvClosed E) (d : LocalDecl)
    {Γ : LCtx} {P : Expr Nat} (h : IsPropTyI E n Γ P) :
    IsPropTyI E n (d :: Γ) (lift 0 1 P) :=
  isPropTyI_weaken hcl d (c := 0) h

/-- Side-condition-free substitution stability of `IsPropTyI` under `EnvWfT E` and `hSort` —
    requiring **no** `∀ l, r ≠ .sort l` hypothesis (`#7655`) and **no** `SortUnique`. -/
theorem isPropTyI_subst_of_sortRow (hW : EnvWfT E) {Γ' : LCtx} {j : Nat} {r T₀ A : Expr Nat}
    (hSort : ∀ {l₁ l₂ : Level},
      TyConvT E n (substRemove r j Γ') (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hj : Γ'[j]? = some (.assumption T₀))
    (hr : HasTyT E n (substRemove r j Γ') (lift 0 j r) (lift 0 j T₀))
    (h : IsPropTyI E n Γ' A) :
    IsPropTyI E n (substRemove r j Γ') (instantiate j (lift 0 j r) A) := by
  obtain ⟨⟨hA⟩, _⟩ := h
  exact isPropTyI_of_hasTyT_sort_zero hSort
    (hasTyT_substS (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) r T₀ hA hj hr)

/-- Head (`j = 0`) specialization of `isPropTyI_subst_of_sortRow` (without `∀ l, r ≠ .sort l`). -/
theorem isPropTyI_subst0_of_sortRow (hW : EnvWfT E) {Γ : LCtx} {r T₀ A : Expr Nat}
    (hSort : ∀ {l₁ l₂ : Level}, TyConvT E n Γ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hr : HasTyT E n Γ r T₀)
    (h : IsPropTyI E n (.assumption T₀ :: Γ) A) :
    IsPropTyI E n Γ (instantiate0 r A) := by
  have hj : (LocalDecl.assumption T₀ :: Γ)[0]? = some (.assumption T₀) := by simp
  have hSort' : ∀ {l₁ l₂ : Level},
      TyConvT E n (substRemove r 0 (.assumption T₀ :: Γ)) (.sort l₁) (.sort l₂) → eqN l₁ l₂ :=
    fun hcv => hSort (by simpa only [substRemove_zero_cons] using hcv)
  have h0 := isPropTyI_subst_of_sortRow hW (Γ' := .assumption T₀ :: Γ) (j := 0) (r := r)
    hSort' hj (by simpa only [substRemove_zero_cons, lift_zero] using hr) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- Side-condition-free substitution stability of `IsPropTyI` from `TypedRowsWf E n`. -/
theorem isPropTyI_subst_of_botDI (hW : EnvWfT E) (hRows : TypedRowsWf E n)
    {Γ' : LCtx} {j : Nat} {r T₀ A : Expr Nat}
    (hΓ : CtxWfT E n (substRemove r j Γ'))
    (hj : Γ'[j]? = some (.assumption T₀))
    (hr : HasTyT E n (substRemove r j Γ') (lift 0 j r) (lift 0 j T₀))
    (h : IsPropTyI E n Γ' A) :
    IsPropTyI E n (substRemove r j Γ') (instantiate j (lift 0 j r) A) :=
  isPropTyI_subst_of_sortRow hW (hRows.sortRow hΓ) hj hr h

/-- Head (`j = 0`) specialization of `isPropTyI_subst_of_botDI`. -/
theorem isPropTyI_subst0_of_botDI (hW : EnvWfT E) (hRows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r T₀ A : Expr Nat}
    (hr : HasTyT E n Γ r T₀)
    (h : IsPropTyI E n (.assumption T₀ :: Γ) A) :
    IsPropTyI E n Γ (instantiate0 r A) :=
  isPropTyI_subst0_of_sortRow hW (hRows.sortRow hΓ) hr h

/-- Let-binding substitution stability of `IsPropTyI` under `EnvWfT E` and `hSort`. -/
theorem isPropTyI_substLet_of_sortRow (hW : EnvWfT E) {Γ' : LCtx} {j : Nat} {t w0 A : Expr Nat}
    (hSort : ∀ {l₁ l₂ : Level},
      TyConvT E n (substRemove w0 j Γ') (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hj : Γ'[j]? = some (.letBinding t w0))
    (hw0 : HasTyT E n (substRemove w0 j Γ') (lift 0 j w0) (lift 0 j t))
    (h : IsPropTyI E n Γ' A) :
    IsPropTyI E n (substRemove w0 j Γ') (instantiate j (lift 0 j w0) A) := by
  obtain ⟨⟨hA⟩, _⟩ := h
  exact isPropTyI_of_hasTyT_sort_zero hSort
    (hasTyT_substLetS (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) t w0 hA hj hw0)

/-- Head (`j = 0`) specialization of `isPropTyI_substLet_of_sortRow`. -/
theorem isPropTyI_substLet0_of_sortRow (hW : EnvWfT E) {Γ : LCtx} {t w0 A : Expr Nat}
    (hSort : ∀ {l₁ l₂ : Level}, TyConvT E n Γ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hw0 : HasTyT E n Γ w0 t)
    (h : IsPropTyI E n (.letBinding t w0 :: Γ) A) :
    IsPropTyI E n Γ (instantiate0 w0 A) := by
  have hj : (LocalDecl.letBinding t w0 :: Γ)[0]? = some (.letBinding t w0) := by simp
  have hSort' : ∀ {l₁ l₂ : Level},
      TyConvT E n (substRemove w0 0 (.letBinding t w0 :: Γ)) (.sort l₁) (.sort l₂) → eqN l₁ l₂ :=
    fun hcv => hSort (by simpa only [substRemove_zero_cons] using hcv)
  have h0 := isPropTyI_substLet_of_sortRow hW (Γ' := .letBinding t w0 :: Γ) (j := 0) (t := t) (w0 := w0)
    hSort' hj (by simpa only [substRemove_zero_cons, lift_zero] using hw0) h
  simpa only [substRemove_zero_cons, lift_zero, instantiate0] using h0

/-- Full typed related-substitution triple for `LRTermD` over `ApproxDI` under `EnvWfT E` and
    `hSort` — requiring **no** `hι` hypothesis and **no** `∀ l, r ≠ .sort l` side condition
    (improving `#7655`'s `fundamentalTermDIS_typed`). -/
theorem fundamentalTermDIS_of_sortRow (hW : EnvWfT E)
    {ρ : EnvI} {j : Nat} {r r' T T₀ : Expr Nat} {Γ' : LCtx}
    (hSort : ∀ {l₁ l₂ : Level},
      TyConvT E n (substRemove r j Γ') (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hj : Γ'[j]? = some (.assumption T₀))
    (hr : HasTyT E n (substRemove r j Γ') (lift 0 j r) (lift 0 j T₀))
    (hΓ' : CtxWfT E n (substRemove r j Γ'))
    (hrel : ∀ c, ApproxDI E (EnvI.drop ρ j) r c →
      LRTermD E n (substRemove r j Γ') (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermD E n (substRemove r j Γ') (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M : Expr Nat} {A : Expr Nat},
        LRTermD E n Γ' M M A .sort →
        LRTermD E n (substRemove r j Γ') (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxDI E ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermD E n (substRemove r j Γ') (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) := by
  refine ⟨fun {_ _ _} => lrTermD_bot _ _ _ _, ?_, lrTermD_subst_bvar hrel⟩
  intro M A h
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_subst_of_sortRow hW hSort hj hr hP)
  · exact Or.inr (lrTermDCore_subst_botPiCpt (envClosed_of_envWfT hW)
      (envMembersSubstStable_of_envWfT hW) r T₀ .sort hj hr hΓ' hC)

/-- `TypedRowsWf`-fronted specialization of `fundamentalTermDIS_of_sortRow`. -/
theorem fundamentalTermDIS_of_botDI (hW : EnvWfT E) (hRows : TypedRowsWf E n)
    {ρ : EnvI} {j : Nat} {r r' T T₀ : Expr Nat} {Γ' : LCtx}
    (hj : Γ'[j]? = some (.assumption T₀))
    (hr : HasTyT E n (substRemove r j Γ') (lift 0 j r) (lift 0 j T₀))
    (hΓ' : CtxWfT E n (substRemove r j Γ'))
    (hrel : ∀ c, ApproxDI E (EnvI.drop ρ j) r c →
      LRTermD E n (substRemove r j Γ') (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermD E n (substRemove r j Γ') (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M : Expr Nat} {A : Expr Nat},
        LRTermD E n Γ' M M A .sort →
        LRTermD E n (substRemove r j Γ') (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxDI E ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermD E n (substRemove r j Γ') (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) :=
  fundamentalTermDIS_of_sortRow hW (hRows.sortRow hΓ') hj hr hΓ' hrel

/-- At `EnvI.bot`, the only compact approximating `.bvar i` in `ApproxDI` is `.bot`. -/
theorem approxDI_bot_bvar_inv {i : Nat} {c : CptI}
    (h : ApproxDI E EnvI.bot (.bvar i) c) : c = .bot := by
  rcases approxDI_bvar_inv h with rfl | hmem
  · rfl
  · exact hmem

/-- In `EnvI.insert EnvI.bot j S`, any compact `c` approximating `.bvar i` is `.bot` when `i ≠ j`,
    and is `.bot` or in `S` when `i = j`. -/
theorem approxDI_insert_bot_bvar_inv {j i : Nat} {S : CptI → Prop} {c : CptI}
    (h : ApproxDI E (EnvI.insert EnvI.bot j S) (.bvar i) c) :
    c = .bot ∨ (i = j ∧ S c) := by
  rcases approxDI_bvar_inv h with rfl | hmem
  · exact Or.inl rfl
  · by_cases hij : i = j
    · subst hij
      rw [EnvI.insert_self] at hmem
      exact Or.inr ⟨rfl, hmem⟩
    · by_cases hlt : i < j
      · rw [EnvI.insert_lt S hlt] at hmem
        exact Or.inl hmem
      · have hgt : j < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (Ne.symm hij)
        rw [EnvI.insert_gt S hgt] at hmem
        exact Or.inl hmem

/-- Related-substitution stability of `LRTermS` across **all** variable indices `i : Nat`
    (`i < j`, `i = j`, and `i > j`) at `EnvI.bot`. -/
theorem lrTermS_subst_bvar_all {j : Nat} {r r' : Expr Nat} {Γ : LCtx} (i : Nat) (A : Expr Nat)
    (hrel : ∀ c, ApproxI EnvI.bot r c →
      LRTermS E n Γ (lift 0 j r) (lift 0 j r') (instantiate j (lift 0 j r) A) c) :
    ∀ c, ApproxI EnvI.bot (instantiate j (lift 0 j r) (.bvar i)) c →
      LRTermS E n Γ (instantiate j (lift 0 j r) (.bvar i))
        (instantiate j (lift 0 j r') (.bvar i)) (instantiate j (lift 0 j r) A) c := by
  intro c hmem
  have hlook : ApproxI (EnvI.insert EnvI.bot j (denI EnvI.bot r)) (.bvar i) c :=
    approxI_subst_elim (.bvar i) hmem
  rcases approxI_bvar_inv hlook with rfl | hmem'
  · exact lrTermS_bot _ _ _ _
  · by_cases hij : i = j
    · subst hij
      rw [EnvI.insert_self] at hmem'
      have hL : instantiate i (lift 0 i r) (.bvar i) = lift 0 i r := by
        rw [instantiate, if_pos rfl]
      have hR : instantiate i (lift 0 i r') (.bvar i) = lift 0 i r' := by
        rw [instantiate, if_pos rfl]
      rw [hL, hR]
      exact hrel c hmem'
    · by_cases hlt : i < j
      · rw [EnvI.insert_lt _ hlt] at hmem'
        cases hmem'
        exact lrTermS_bot _ _ _ _
      · have hgt : j < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (Ne.symm hij)
        rw [EnvI.insert_gt _ hgt] at hmem'
        cases hmem'
        exact lrTermS_bot _ _ _ _

/-- Related-substitution stability of `LRTermSDI` across **all** variable indices `i : Nat`
    (`i < j`, `i = j`, and `i > j`) over `ApproxDI` at `EnvI.bot`. -/
theorem lrTermSDI_subst_bvar_all {j : Nat} {r r' : Expr Nat} {Γ : LCtx} (i : Nat) (A : Expr Nat)
    (hrel : ∀ c, ApproxDI E EnvI.bot r c →
      LRTermSDI E n Γ (lift 0 j r) (lift 0 j r') (instantiate j (lift 0 j r) A) c) :
    ∀ c, ApproxDI E EnvI.bot (instantiate j (lift 0 j r) (.bvar i)) c →
      LRTermSDI E n Γ (instantiate j (lift 0 j r) (.bvar i))
        (instantiate j (lift 0 j r') (.bvar i)) (instantiate j (lift 0 j r) A) c := by
  intro c hmem
  have hlook : ApproxDI E (EnvI.insert EnvI.bot j (denDI E EnvI.bot r)) (.bvar i) c :=
    approxDI_subst_elim (.bvar i) hmem
  rcases approxDI_insert_bot_bvar_inv hlook with rfl | ⟨rfl, hr⟩
  · exact lrTermSDI_bot _ _ _ _
  · have hL : instantiate i (lift 0 i r) (.bvar i) = lift 0 i r := by
      rw [instantiate, if_pos rfl]
    have hR : instantiate i (lift 0 i r') (.bvar i) = lift 0 i r' := by
      rw [instantiate, if_pos rfl]
    rw [hL, hR]
    exact hrel c hr

/-- Related-substitution stability of `LRTermDCore` across **all** variable indices `i : Nat`
    (`i < j`, `i = j`, and `i > j`) over `ApproxDI` at `EnvI.bot`. -/
theorem lrTermDCore_subst_bvar_all {j : Nat} {r r' : Expr Nat} {Γ : LCtx} (i : Nat) (A : Expr Nat)
    (hrel : ∀ c, ApproxDI E EnvI.bot r c →
      LRTermDCore E n Γ (lift 0 j r) (lift 0 j r') (instantiate j (lift 0 j r) A) c) :
    ∀ c, ApproxDI E EnvI.bot (instantiate j (lift 0 j r) (.bvar i)) c →
      LRTermDCore E n Γ (instantiate j (lift 0 j r) (.bvar i))
        (instantiate j (lift 0 j r') (.bvar i)) (instantiate j (lift 0 j r) A) c := by
  intro c hmem
  have hlook : ApproxDI E (EnvI.insert EnvI.bot j (denDI E EnvI.bot r)) (.bvar i) c :=
    approxDI_subst_elim (.bvar i) hmem
  rcases approxDI_insert_bot_bvar_inv hlook with rfl | ⟨rfl, hr⟩
  · exact lrTermDCore_bot _ _ _ _
  · have hL : instantiate i (lift 0 i r) (.bvar i) = lift 0 i r := by
      rw [instantiate, if_pos rfl]
    have hR : instantiate i (lift 0 i r') (.bvar i) = lift 0 i r' := by
      rw [instantiate, if_pos rfl]
    rw [hL, hR]
    exact hrel c hr

/-- Related-substitution stability of `LRTermD` across **all** variable indices `i : Nat`
    (`i < j`, `i = j`, and `i > j`) over `ApproxDI` at `EnvI.bot`. -/
theorem lrTermD_subst_bvar_all {j : Nat} {r r' : Expr Nat} {Γ : LCtx} (i : Nat) (A : Expr Nat)
    (hrel : ∀ c, ApproxDI E EnvI.bot r c →
      LRTermD E n Γ (lift 0 j r) (lift 0 j r') (instantiate j (lift 0 j r) A) c) :
    ∀ c, ApproxDI E EnvI.bot (instantiate j (lift 0 j r) (.bvar i)) c →
      LRTermD E n Γ (instantiate j (lift 0 j r) (.bvar i))
        (instantiate j (lift 0 j r') (.bvar i)) (instantiate j (lift 0 j r) A) c := by
  intro c hmem
  have hlook : ApproxDI E (EnvI.insert EnvI.bot j (denDI E EnvI.bot r)) (.bvar i) c :=
    approxDI_subst_elim (.bvar i) hmem
  rcases approxDI_insert_bot_bvar_inv hlook with rfl | ⟨rfl, hr⟩
  · exact lrTermD_bot _ _ _ _
  · have hL : instantiate i (lift 0 i r) (.bvar i) = lift 0 i r := by
      rw [instantiate, if_pos rfl]
    have hR : instantiate i (lift 0 i r') (.bvar i) = lift 0 i r' := by
      rw [instantiate, if_pos rfl]
    rw [hL, hR]
    exact hrel c hr

/-- `instantiate` distributes over `foldApps`. -/
theorem instantiate_foldApps_term (j : Nat) (s f : Expr Nat) :
    (xs : List (Expr Nat)) →
    instantiate j s (foldApps f xs) = foldApps (instantiate j s f) (xs.map (instantiate j s))
  | [] => rfl
  | x :: xs => by
      simp only [foldApps, List.map, instantiate]
      exact instantiate_foldApps_term j s (.app f x) xs

/-- Every application spine `foldApps (.const r ls) args` headed by a non-recursor opaque
    constant (`m.body = none ∧ m.mclass ≠ .recursorM`, covering all `.inductiveM`, `.constructorM`,
    `.axiomM`, and `.quotM` declarations) is weak-head normal (`WhNormal`) for every `ls` and `args`. -/
theorem whNormal_foldApps_of_rigidNonRec {r : Nat} {m : CheckedMember}
    (hmem : E.members r = some m) (hbody : m.body = none) (hnrec : m.mclass ≠ .recursorM)
    (ls : List Level) (args : List (Expr Nat)) :
    WhNormal E (foldApps (.const r ls) args) := by
  intro t hs
  have key : ∀ {f e : Expr Nat}, WhStep E f e → (appsSpine f).1 = .const r ls → False := by
    intro f e hstep
    induction hstep with
    | beta _ _ _ => intro hsp; simp [appsSpine] at hsp
    | zeta _ _ _ => intro hsp; simp [appsSpine] at hsp
    | delta hres hbody' =>
        intro hsp
        simp only [appsSpine, Expr.const.injEq] at hsp
        rcases hsp with ⟨rfl, _⟩
        rw [hmem] at hres
        injection hres with hm
        subst hm
        rw [hbody] at hbody'
        exact Option.noConfusion hbody'
    | iota hI =>
        intro hsp
        cases hI with
        | ofU w =>
            unfold iotaLhsOf recCall at hsp
            have s₂ := appsSpine_foldApps (.const w.recRef w.ls)
              (w.preMajor ++ [ctorMajor w])
            simp only [appsSpine_const, List.nil_append] at s₂
            rw [s₂] at hsp
            injection hsp with hrec _
            subst hrec
            have hm : w.recMember = m := Option.some.inj (w.hrec.symm.trans hmem)
            subst hm
            exact hnrec w.hrecK
        | ofUS w =>
            unfold iotaLhsOfS recCall at hsp
            have s₂ := appsSpine_foldApps (.const w.recRef w.ls)
              (w.preMajor ++ [foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)])
            simp only [appsSpine_const, List.nil_append] at s₂
            rw [s₂] at hsp
            injection hsp with hrec _
            subst hrec
            have hm : w.recMember = m := Option.some.inj (w.hrec.symm.trans hmem)
            subst hm
            exact hnrec w.hrecK
    | lit _ => intro hsp; simp [appsSpine] at hsp
    | appHead _ ih =>
        intro hsp
        simp only [appsSpine] at hsp
        exact ih hsp
  have hsp₀ := appsSpine_foldApps (.const r ls) args
  simp only [appsSpine_const, List.nil_append] at hsp₀
  exact key hs (congrArg Prod.fst hsp₀)

/-- General `.spine r args` substitution stability for `LRTermDCore` across all non-recursor
    opaque constants `r` (`m.body = none ∧ m.mclass ≠ .recursorM`, covering all inductive type
    constructors and data constructors) and **arbitrary** `args : List CptI`, whenever either `A`
    does not weak-head reduce to a sort (`∀ l, ¬ WhRed E A (.sort l)`, covering every inductive
    data type) or `M, M'` weak-head reduce to `r`-headed spines (generalizing `#7655`'s 0-argument
    diagonal `lrTermD_const_diag_subst`). -/
theorem lrTermDCore_spine_subst_of_rigidNonRec (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember}
    (hmem : E.members r = some m) (hbody : m.body = none) (hnrec : m.mclass ≠ .recursorM)
    (v T₀ : Expr Nat) (args : List CptI)
    {Γ' : LCtx} {j : Nat} {M M' A : Expr Nat}
    (hA_or_M : (∀ l, ¬ WhRed E A (.sort l)) ∨
      (∃ ls₁ ls₂ args₁ args₂,
        WhRed E M (foldApps (.const r ls₁) args₁) ∧
        WhRed E M' (foldApps (.const r ls₂) args₂)))
    (hj : Γ'[j]? = some (.assumption T₀))
    (hv : HasTyT E n (substRemove v j Γ') (lift 0 j v) (lift 0 j T₀))
    (h : LRTermDCore E n Γ' M M' A (.spine r args)) :
    LRTermDCore E n (substRemove v j Γ')
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) (.spine r args) := by
  have hcl := envClosed_of_envWfT hW
  have hinst := envMembersSubstStable_of_envWfT hW
  rw [lrTermDCore_spine_iff_simple] at h ⊢
  rcases h with ⟨⟨l, hl⟩, hLR⟩ | ⟨ls₁, ls₂, args₁, args₂, hM, hM', _, _, ⟨hc⟩, hb1, hb2⟩
  · rcases hA_or_M with hnoSort | ⟨ls₁, ls₂, args₁, args₂, hM₀, hM'₀⟩
    · exact (hnoSort l hl).elim
    · refine Or.inl ⟨⟨l, whRed_instantiate_sort_of_envClosed hcl hl j (lift 0 j v)⟩, ?_⟩
      cases hLR with
      | spine h1 h2 n1 n2 hconv =>
          have hn₀ := whNormal_foldApps_of_rigidNonRec hmem hbody hnrec ls₁ args₁
          have hn'₀ := whNormal_foldApps_of_rigidNonRec hmem hbody hnrec ls₂ args₂
          have e1 := whRed_normal_unique_of_envWfT hW h1 n1 hM₀ hn₀
          have e2 := whRed_normal_unique_of_envWfT hW h2 n2 hM'₀ hn'₀
          subst e1; subst e2
          have h1' := whRed_instantiate_of_envClosed hcl h1 j (lift 0 j v)
          have h2' := whRed_instantiate_of_envClosed hcl h2 j (lift 0 j v)
          rw [instantiate_foldApps_term] at h1' h2'
          simp only [instantiate] at h1' h2'
          have hc' := tyConvT_substS hcl hinst v T₀ hconv hj hv
          rw [instantiate_foldApps_term, instantiate_foldApps_term] at hc'
          simp only [instantiate] at hc'
          exact .spine h1' h2'
            (whNormal_foldApps_of_rigidNonRec hmem hbody hnrec _ _)
            (whNormal_foldApps_of_rigidNonRec hmem hbody hnrec _ _) hc'
  · refine Or.inr ⟨ls₁, ls₂, args₁.map (instantiate j (lift 0 j v)),
      args₂.map (instantiate j (lift 0 j v)), ?_, ?_,
      whNormal_foldApps_of_rigidNonRec hmem hbody hnrec ls₁ _,
      whNormal_foldApps_of_rigidNonRec hmem hbody hnrec ls₂ _,
      ⟨?_⟩, by simpa using hb1, by simpa using hb2⟩
    · have h1 := whRed_instantiate_of_envClosed hcl hM j (lift 0 j v)
      simpa only [instantiate_foldApps_term, instantiate] using h1
    · have h2 := whRed_instantiate_of_envClosed hcl hM' j (lift 0 j v)
      simpa only [instantiate_foldApps_term, instantiate] using h2
    · have hc' := convT_substS hcl hinst v T₀ hc hj hv
      simpa only [instantiate_foldApps_term, instantiate] using hc'

/-- General `.spine r args` substitution stability for `LRTermD` across all non-recursor opaque
    constants `r` (`m.body = none ∧ m.mclass ≠ .recursorM`) under `EnvWfT E` and `hSort` —
    requiring **no** `∀ l, v ≠ .sort l` side condition. -/
theorem lrTermD_spine_subst_of_rigidNonRec (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember}
    (hmem : E.members r = some m) (hbody : m.body = none) (hnrec : m.mclass ≠ .recursorM)
    (v T₀ : Expr Nat) (args : List CptI)
    {Γ' : LCtx} {j : Nat} {M M' A : Expr Nat}
    (hSort : ∀ {l₁ l₂ : Level},
      TyConvT E n (substRemove v j Γ') (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hA_or_M : (∀ l, ¬ WhRed E A (.sort l)) ∨
      (∃ ls₁ ls₂ args₁ args₂,
        WhRed E M (foldApps (.const r ls₁) args₁) ∧
        WhRed E M' (foldApps (.const r ls₂) args₂)))
    (hj : Γ'[j]? = some (.assumption T₀))
    (hv : HasTyT E n (substRemove v j Γ') (lift 0 j v) (lift 0 j T₀))
    (h : LRTermD E n Γ' M M' A (.spine r args)) :
    LRTermD E n (substRemove v j Γ')
      (instantiate j (lift 0 j v) M) (instantiate j (lift 0 j v) M')
      (instantiate j (lift 0 j v) A) (.spine r args) := by
  rcases h with hP | hC
  · exact Or.inl (isPropTyI_subst_of_sortRow hW hSort hj hv hP)
  · exact Or.inr (lrTermDCore_spine_subst_of_rigidNonRec hW hmem hbody hnrec v T₀ args hA_or_M hj hv hC)

/-! ## §9. No-Transport Transitivity From Left-Reflexivity, Higher-Order Type-Valued Function Symmetry (`TypeValuedLamCpt`), and `LRTermD` Refutation on `polyPi` -/

/-- Symmetry of `LRTermI` on non-`λ` compacts (`∀ g, c ≠ .lam g`) at every `EnvWfT E`. -/
theorem lrTermI_noLam_symm (hW : EnvWfT E) {c : CptI} (hno : ∀ g, c ≠ .lam g)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermI E n Γ M M' A c) :
    LRTermI E n Γ M' M A c := by
  cases c with
  | bot => exact lrTermI_bot _ _ _ _
  | sort =>
      rw [lrTermI_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW h.2⟩
  | pi a f =>
      rw [lrTermI_pi_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW h.2⟩
  | spine r args =>
      rw [lrTermI_spine_iff] at h ⊢
      exact ⟨h.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW h.2⟩
  | lam g => exact (hno g rfl).elim

/-- Transitivity of `LRTermI` on non-`λ` compacts (`∀ g, c ≠ .lam g`) at every `EnvWfT E`. -/
theorem lrTermI_noLam_trans (hW : EnvWfT E) {c : CptI} (hno : ∀ g, c ≠ .lam g)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermI E n Γ M N A c) (h₂ : LRTermI E n Γ N P A c) :
    LRTermI E n Γ M P A c := by
  cases c with
  | bot => exact lrTermI_bot _ _ _ _
  | sort =>
      rw [lrTermI_sort_iff] at h₁ h₂ ⊢
      exact ⟨h₁.1, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW h₁.2 h₂.2⟩
  | pi a f =>
      rw [lrTermI_pi_iff] at h₁ h₂ ⊢
      exact ⟨h₁.1, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW h₁.2 h₂.2⟩
  | spine r args =>
      rw [lrTermI_spine_iff] at h₁ h₂ ⊢
      exact ⟨h₁.1, lrTypeIN_trans_of_envWfT (envClosed_of_envWfT hW) hW h₁.2 h₂.2⟩
  | lam g => exact (hno g rfl).elim

/-- Left-reflexivity of `LRTermI` on non-`λ` compacts (`∀ g, c ≠ .lam g`) at every `EnvWfT E`. -/
theorem lrTermI_noLam_refl_left (hW : EnvWfT E) {c : CptI} (hno : ∀ g, c ≠ .lam g)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermI E n Γ M M' A c) :
    LRTermI E n Γ M M A c :=
  lrTermI_noLam_trans hW hno h (lrTermI_noLam_symm hW hno h)

/-- Transitivity of `LRTermI` across all `FirstOrderCpt` compacts at every `EnvWfT E`. -/
theorem lrTermI_firstOrder_trans (hW : EnvWfT E) {c : CptI} (hc : FirstOrderCpt c)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermI E n Γ M N A c) (h₂ : LRTermI E n Γ N P A c) :
    LRTermI E n Γ M P A c := by
  induction hc generalizing Γ M N P A with
  | bot => exact lrTermI_bot _ _ _ _
  | sort => exact lrTermI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | pi a f => exact lrTermI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | @lam g hdom _ ih =>
      rw [lrTermI_lam_iff] at h₁ h₂ ⊢
      obtain ⟨A₁, B₁, hA₁, hΓ₁, happ₁₂⟩ := h₁
      obtain ⟨A₂, B₂, hA₂, _, happ₂₃⟩ := h₂
      have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
        whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
          hA₂ (fun _ h => whStep_pi_false h)
      injection heq with eA eB; subst eA; subst eB
      refine ⟨A₁, B₁, hA₁, hΓ₁, fun s hs N N' hrel => ?_⟩
      have hrelNN : ∀ u ∈ s.1, LRTermI E n Γ N N A₁ u :=
        fun u hu => lrTermI_noLam_refl_left hW (hdom s hs u hu).1 (hrel u hu)
      exact ih s hs (happ₁₂ s hs N N hrelNN) (happ₂₃ s hs N N' hrel)

/-- Left-reflexivity of a term-level logical relation `R` (`R Γ M M' A u → R Γ M M A u`). -/
def LRTermReflLeft (R : LCtx → Expr Nat → Expr Nat → Expr Nat → CptI → Prop) : Prop :=
  ∀ {Γ : LCtx} {M M' A : Expr Nat} {u : CptI}, R Γ M M' A u → R Γ M M A u

/-- **No-Transport Transitivity (`lrTermI_trans_of_reflLeft`)**: `RcicNativePiModelFundCases.LRTermTrans E n`
    holds across **all** compacts `c : CptI` from `EnvWfT E` and left-reflexivity of `LRTermI`
    alone — requiring **zero `LRTermIndexTransport`** (feeding `(N, N)` to `happ₁₂` and `(N, N')`
    to `happ₂₃` keeps the left argument `N` and codomain `instantiate0 N B₁` identical on both sides). -/
theorem lrTermI_trans_of_reflLeft (hW : EnvWfT E)
    (hrefl : LRTermReflLeft (LRTermI E n))
    {Γ : LCtx} {M N P A : Expr Nat} :
    {c : CptI} → LRTermI E n Γ M N A c → LRTermI E n Γ N P A c → LRTermI E n Γ M P A c
  | .bot, _, _ => lrTermI_bot _ _ _ _
  | .sort, h₁, h₂ => lrTermI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | .pi _ _, h₁, h₂ => lrTermI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | .spine _ _, h₁, h₂ => lrTermI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | .lam g, h₁, h₂ => by
      rw [lrTermI_lam_iff] at h₁ h₂ ⊢
      obtain ⟨A₁, B₁, hA₁, hΓ₁, happ₁₂⟩ := h₁
      obtain ⟨A₂, B₂, hA₂, _, happ₂₃⟩ := h₂
      have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
        whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
          hA₂ (fun _ h => whStep_pi_false h)
      injection heq with eA eB; subst eA; subst eB
      refine ⟨A₁, B₁, hA₁, hΓ₁, fun s hs N₀ N₀' hrel => ?_⟩
      have hrelNN : ∀ u ∈ s.1, LRTermI E n Γ N₀ N₀ A₁ u :=
        fun u hu => hrefl (hrel u hu)
      exact lrTermI_trans_of_reflLeft hW hrefl (happ₁₂ s hs N₀ N₀ hrelNN) (happ₂₃ s hs N₀ N₀' hrel)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOf_snd_lt s
  omega

/-- Full transitivity of `LRTermS` across **all** compacts `c : CptI` from `EnvWfT E`,
    left-reflexivity, and `.spine` transitivity — requiring **zero** index transport. -/
theorem lrTermS_trans_of_reflLeft (hW : EnvWfT E)
    (hrefl : LRTermReflLeft (LRTermS E n))
    (hsp : ∀ {Γ : LCtx} {M N P A : Expr Nat} {r : Nat} {args : List CptI},
      LRTermS E n Γ M N A (.spine r args) → LRTermS E n Γ N P A (.spine r args) →
      LRTermS E n Γ M P A (.spine r args))
    {Γ : LCtx} {M N P A : Expr Nat} :
    {c : CptI} → LRTermS E n Γ M N A c → LRTermS E n Γ N P A c → LRTermS E n Γ M P A c
  | .bot, _, _ => lrTermS_bot _ _ _ _
  | .sort, h₁, h₂ =>
      lrTermS_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂
  | .pi _ _, h₁, h₂ =>
      lrTermS_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂
  | .spine _ _, h₁, h₂ => hsp h₁ h₂
  | .lam g, h₁, h₂ => by
      rw [lrTermS_lam_iff] at h₁ h₂ ⊢
      obtain ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, happ₁₂⟩ := h₁
      obtain ⟨A₂, B₂, _, hA₂, _, _, happ₂₃⟩ := h₂
      have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
        whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
          hA₂ (fun _ h => whStep_pi_false h)
      injection heq with eA eB; subst eA; subst eB
      refine ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, fun s hs N₀ N₀' hN₀ hN₀' hrel => ?_⟩
      have hrelNN : ∀ u ∈ s.1, LRTermS E n Γ N₀ N₀ A₁ u :=
        fun u hu => hrefl (hrel u hu)
      exact lrTermS_trans_of_reflLeft hW hrefl hsp
        (happ₁₂ s hs N₀ N₀ hN₀ hN₀ hrelNN) (happ₂₃ s hs N₀ N₀' hN₀ hN₀' hrel)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOf_snd_lt s
  omega

/-- Full transitivity of `LRTermSDI` across **all** compacts `c : CptI` (including `.spine r args`
    and `.lam g`!) from `EnvWfT E` and left-reflexivity alone — requiring **zero** index transport. -/
theorem lrTermSDI_trans_of_reflLeft (hW : EnvWfT E)
    (hrefl : LRTermReflLeft (LRTermSDI E n))
    {Γ : LCtx} {M N P A : Expr Nat} :
    {c : CptI} → LRTermSDI E n Γ M N A c → LRTermSDI E n Γ N P A c → LRTermSDI E n Γ M P A c
  | .bot, _, _ => lrTermSDI_bot _ _ _ _
  | .sort, h₁, h₂ => lrTermSDI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | .pi _ _, h₁, h₂ => lrTermSDI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | .spine _ _, h₁, h₂ => lrTermSDI_noLam_trans hW (fun _ h => by cases h) h₁ h₂
  | .lam g, h₁, h₂ => by
      rw [lrTermSDI_lam_iff] at h₁ h₂ ⊢
      obtain ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, happ₁₂⟩ := h₁
      obtain ⟨A₂, B₂, _, hA₂, _, _, happ₂₃⟩ := h₂
      have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
        whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
          hA₂ (fun _ h => whStep_pi_false h)
      injection heq with eA eB; subst eA; subst eB
      refine ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, fun s hs N₀ N₀' hN₀ hN₀' hrel => ?_⟩
      have hrelNN : ∀ u ∈ s.1, LRTermSDI E n Γ N₀ N₀ A₁ u :=
        fun u hu => hrefl (hrel u hu)
      exact lrTermSDI_trans_of_reflLeft hW hrefl
        (happ₁₂ s hs N₀ N₀ hN₀ hN₀ hrelNN) (happ₂₃ s hs N₀ N₀' hN₀ hN₀' hrel)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOf_snd_lt s
  omega

/-- Full transitivity of `LRTermDCore` across **all** compacts `c : CptI` from `EnvWfT E`,
    left-reflexivity, and `.spine` transitivity — requiring **zero** index transport. -/
theorem lrTermDCore_trans_of_reflLeft (hW : EnvWfT E)
    (hrefl : LRTermReflLeft (LRTermDCore E n))
    (hsp : ∀ {Γ : LCtx} {M N P A : Expr Nat} {r : Nat} {args : List CptI},
      LRTermDCore E n Γ M N A (.spine r args) → LRTermDCore E n Γ N P A (.spine r args) →
      LRTermDCore E n Γ M P A (.spine r args))
    {Γ : LCtx} {M N P A : Expr Nat} :
    {c : CptI} → LRTermDCore E n Γ M N A c → LRTermDCore E n Γ N P A c → LRTermDCore E n Γ M P A c
  | .bot, _, _ => lrTermDCore_bot _ _ _ _
  | .sort, h₁, h₂ =>
      lrTermDCore_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂
  | .pi _ _, h₁, h₂ =>
      lrTermDCore_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂
  | .spine _ _, h₁, h₂ => hsp h₁ h₂
  | .lam g, h₁, h₂ => by
      rw [lrTermDCore_lam_iff] at h₁ h₂ ⊢
      obtain ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, happ₁₂⟩ := h₁
      obtain ⟨A₂, B₂, _, hA₂, _, _, happ₂₃⟩ := h₂
      have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
        whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
          hA₂ (fun _ h => whStep_pi_false h)
      injection heq with eA eB; subst eA; subst eB
      refine ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, fun s hs N₀ N₀' hN₀ hN₀' hrel => ?_⟩
      have hrelNN : ∀ u ∈ s.1, LRTermDCore E n Γ N₀ N₀ A₁ u :=
        fun u hu => hrefl (hrel u hu)
      rcases happ₁₂ s hs N₀ N₀ hN₀ hN₀ hrelNN with hP | hcore₁₂
      · exact Or.inl hP
      · rcases happ₂₃ s hs N₀ N₀' hN₀ hN₀' hrel with hP | hcore₂₃
        · exact Or.inl hP
        · exact Or.inr (lrTermDCore_trans_of_reflLeft hW hrefl hsp hcore₁₂ hcore₂₃)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOf_snd_lt s
  omega

/-- Full transitivity of `LRTermD` across **all** compacts `c : CptI` from `EnvWfT E`,
    left-reflexivity of `LRTermDCore`, and `.spine` transitivity — requiring **zero** index transport. -/
theorem lrTermD_trans_of_reflLeft (hW : EnvWfT E)
    (hrefl : LRTermReflLeft (LRTermDCore E n))
    (hsp : ∀ {Γ : LCtx} {M N P A : Expr Nat} {r : Nat} {args : List CptI},
      LRTermDCore E n Γ M N A (.spine r args) → LRTermDCore E n Γ N P A (.spine r args) →
      LRTermDCore E n Γ M P A (.spine r args))
    {c : CptI} {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermD E n Γ M N A c) (h₂ : LRTermD E n Γ N P A c) :
    LRTermD E n Γ M P A c := by
  rcases h₁ with hP | hcore₁
  · exact Or.inl hP
  · rcases h₂ with hP | hcore₂
    · exact Or.inl hP
    · exact Or.inr (lrTermDCore_trans_of_reflLeft hW hrefl hsp hcore₁ hcore₂)

/-- Higher-order type-valued function compacts: extends non-`λ` compacts (`.bot`, `.sort`, `.pi a f`)
    by allowing `.lam g` whenever every step `s ∈ g` has `TypeValuedLamCpt` argument demands
    `u ∈ s.1` (allowing arbitrary higher-order nesting in `s.1`) and a type-code output `s.2`
    (`.bot`, `.sort`, or `.pi a f`, whose `LRTypeIN` payload does not depend on the codomain index
    `instantiate0 N B₁`). -/
inductive TypeValuedLamCpt : CptI → Prop
  | bot : TypeValuedLamCpt .bot
  | sort : TypeValuedLamCpt .sort
  | pi (a : CptI) (f : List (List CptI × CptI)) : TypeValuedLamCpt (.pi a f)
  | lam (g : List (List CptI × CptI))
      (hdom : ∀ s ∈ g, ∀ u ∈ s.1, TypeValuedLamCpt u)
      (hcod : ∀ s ∈ g, s.2 = .bot ∨ s.2 = .sort ∨ ∃ a f, s.2 = .pi a f) :
      TypeValuedLamCpt (.lam g)

/-- Every non-`λ`, non-`.spine` compact satisfies `TypeValuedLamCpt`. -/
theorem typeValuedLamCpt_of_noLam {c : CptI}
    (hno : (∀ g, c ≠ .lam g) ∧ (∀ r args, c ≠ .spine r args)) : TypeValuedLamCpt c := by
  cases c with
  | bot => exact .bot
  | sort => exact .sort
  | pi a f => exact .pi a f
  | spine r args => exact (hno.2 r args rfl).elim
  | lam g => exact (hno.1 g rfl).elim

/-- Every `BotPiCpt` compact satisfies `TypeValuedLamCpt`. -/
theorem typeValuedLamCpt_of_botPiCpt {c : CptI} (hc : BotPiCpt c) : TypeValuedLamCpt c :=
  typeValuedLamCpt_of_noLam (noLam_of_botPiCpt hc)

/-- Simultaneous symmetry and transitivity of `LRTermI` across all `TypeValuedLamCpt` compacts
    (including higher-order `.lam g` compacts) at every `EnvWfT E` — requiring **no**
    `TypeSoundness` and **no** index transport (`happ (N, N')` supplies the sort witness
    `∃ l, WhRed E (instantiate0 N B₁) (.sort l)` for `N`, while `happ (N', N)` supplies the
    symmetric `LRTypeIN` payload on `(.app M' N)` and `(.app M N')`). -/
theorem lrTermI_typeValued_symm_and_trans (hW : EnvWfT E) {c : CptI}
    (hc : TypeValuedLamCpt c) :
    (∀ {Γ : LCtx} {M M' A : Expr Nat},
      LRTermI E n Γ M M' A c → LRTermI E n Γ M' M A c) ∧
    (∀ {Γ : LCtx} {M N P A : Expr Nat},
      LRTermI E n Γ M N A c → LRTermI E n Γ N P A c → LRTermI E n Γ M P A c) := by
  induction hc with
  | bot =>
      exact ⟨fun h => lrTermI_noLam_symm hW (fun _ h => by cases h) h,
        fun h₁ h₂ => lrTermI_noLam_trans hW (fun _ h => by cases h) h₁ h₂⟩
  | sort =>
      exact ⟨fun h => lrTermI_noLam_symm hW (fun _ h => by cases h) h,
        fun h₁ h₂ => lrTermI_noLam_trans hW (fun _ h => by cases h) h₁ h₂⟩
  | pi a f =>
      exact ⟨fun h => lrTermI_noLam_symm hW (fun _ h => by cases h) h,
        fun h₁ h₂ => lrTermI_noLam_trans hW (fun _ h => by cases h) h₁ h₂⟩
  | @lam g _ hcod ih =>
      refine ⟨?_, ?_⟩
      · intro Γ M M' A h
        rw [lrTermI_lam_iff] at h ⊢
        obtain ⟨A₁, B₁, hA₁, hΓ₁, happ⟩ := h
        refine ⟨A₁, B₁, hA₁, hΓ₁, fun s hs N N' hrel => ?_⟩
        have hNN' := happ s hs N N' hrel
        have hN'N := happ s hs N' N (fun u hu => (ih s hs u hu).1 (hrel u hu))
        rcases hcod s hs with hbot | hsort | ⟨a, f, hpi⟩
        · rw [hbot]; exact lrTermI_bot _ _ _ _
        · rw [hsort] at hNN' hN'N ⊢
          rw [lrTermI_sort_iff] at hNN' hN'N ⊢
          exact ⟨hNN'.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW hN'N.2⟩
        · rw [hpi] at hNN' hN'N ⊢
          rw [lrTermI_pi_iff] at hNN' hN'N ⊢
          exact ⟨hNN'.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW hN'N.2⟩
      · intro Γ M N P A h₁ h₂
        rw [lrTermI_lam_iff] at h₁ h₂ ⊢
        obtain ⟨A₁, B₁, hA₁, hΓ₁, happ₁₂⟩ := h₁
        obtain ⟨A₂, B₂, hA₂, _, happ₂₃⟩ := h₂
        have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
          whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
            hA₂ (fun _ h => whStep_pi_false h)
        injection heq with eA eB; subst eA; subst eB
        refine ⟨A₁, B₁, hA₁, hΓ₁, fun s hs N₀ N₀' hrel => ?_⟩
        have hrelNN : ∀ u ∈ s.1, LRTermI E n Γ N₀ N₀ A₁ u :=
          fun u hu => (ih s hs u hu).2 (hrel u hu) ((ih s hs u hu).1 (hrel u hu))
        have h₁₂ := happ₁₂ s hs N₀ N₀ hrelNN
        have h₂₃ := happ₂₃ s hs N₀ N₀' hrel
        have hno : ∀ g', s.2 ≠ .lam g' := by
          rcases hcod s hs with hbot | hsort | ⟨a, f, hpi⟩
          · rw [hbot]; intro _ h; cases h
          · rw [hsort]; intro _ h; cases h
          · rw [hpi]; intro _ h; cases h
        exact lrTermI_noLam_trans hW hno h₁₂ h₂₃

/-- Symmetry of `LRTermI` across all `TypeValuedLamCpt` compacts at every `EnvWfT E`. -/
theorem lrTermI_typeValued_symm (hW : EnvWfT E) {c : CptI} (hc : TypeValuedLamCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermI E n Γ M M' A c) :
    LRTermI E n Γ M' M A c :=
  (lrTermI_typeValued_symm_and_trans hW hc).1 h

/-- Transitivity of `LRTermI` across all `TypeValuedLamCpt` compacts at every `EnvWfT E`. -/
theorem lrTermI_typeValued_trans (hW : EnvWfT E) {c : CptI} (hc : TypeValuedLamCpt c)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermI E n Γ M N A c) (h₂ : LRTermI E n Γ N P A c) :
    LRTermI E n Γ M P A c :=
  (lrTermI_typeValued_symm_and_trans hW hc).2 h₁ h₂

/-- Simultaneous symmetry and transitivity of `LRTermS` across all `TypeValuedLamCpt` compacts
    at every `EnvWfT E`. -/
theorem lrTermS_typeValued_symm_and_trans (hW : EnvWfT E) {c : CptI}
    (hc : TypeValuedLamCpt c) :
    (∀ {Γ : LCtx} {M M' A : Expr Nat},
      LRTermS E n Γ M M' A c → LRTermS E n Γ M' M A c) ∧
    (∀ {Γ : LCtx} {M N P A : Expr Nat},
      LRTermS E n Γ M N A c → LRTermS E n Γ N P A c → LRTermS E n Γ M P A c) := by
  induction hc with
  | bot =>
      exact ⟨fun h => lrTermS_noLam_symm hW (fun _ h => by cases h) h,
        fun h₁ h₂ =>
          lrTermS_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂⟩
  | sort =>
      exact ⟨fun h => lrTermS_noLam_symm hW (fun _ h => by cases h) h,
        fun h₁ h₂ =>
          lrTermS_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂⟩
  | pi a f =>
      exact ⟨fun h => lrTermS_noLam_symm hW (fun _ h => by cases h) h,
        fun h₁ h₂ =>
          lrTermS_noLam_trans hW ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩ h₁ h₂⟩
  | @lam g _ hcod ih =>
      refine ⟨?_, ?_⟩
      · intro Γ M M' A h
        rw [lrTermS_lam_iff] at h ⊢
        obtain ⟨A₁, B₁, w, hA₁, hΓ₁, hB₁, happ⟩ := h
        refine ⟨A₁, B₁, w, hA₁, hΓ₁, hB₁, fun s hs N N' hN hN' hrel => ?_⟩
        have hNN' := happ s hs N N' hN hN' hrel
        have hN'N := happ s hs N' N hN' hN
          (fun u hu => (ih s hs u hu).1 (hrel u hu))
        rcases hcod s hs with hbot | hsort | ⟨a, f, hpi⟩
        · rw [hbot]; exact lrTermS_bot _ _ _ _
        · rw [hsort] at hNN' hN'N ⊢
          rw [lrTermS_sort_iff] at hNN' hN'N ⊢
          exact ⟨hNN'.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW hN'N.2⟩
        · rw [hpi] at hNN' hN'N ⊢
          rw [lrTermS_pi_iff] at hNN' hN'N ⊢
          exact ⟨hNN'.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW hN'N.2⟩
      · intro Γ M N P A h₁ h₂
        rw [lrTermS_lam_iff] at h₁ h₂ ⊢
        obtain ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, happ₁₂⟩ := h₁
        obtain ⟨A₂, B₂, _, hA₂, _, _, happ₂₃⟩ := h₂
        have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
          whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
            hA₂ (fun _ h => whStep_pi_false h)
        injection heq with eA eB; subst eA; subst eB
        refine ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, fun s hs N₀ N₀' hN₀ hN₀' hrel => ?_⟩
        have hrelNN : ∀ u ∈ s.1, LRTermS E n Γ N₀ N₀ A₁ u := fun u hu => by
          have ihu := ih s hs u hu
          exact ihu.2 (hrel u hu) (ihu.1 (hrel u hu))
        have h₁₂ := happ₁₂ s hs N₀ N₀ hN₀ hN₀ hrelNN
        have h₂₃ := happ₂₃ s hs N₀ N₀' hN₀ hN₀' hrel
        have hno : (∀ g', s.2 ≠ .lam g') ∧ (∀ r args, s.2 ≠ .spine r args) := by
          rcases hcod s hs with hbot | hsort | ⟨a, f, hpi⟩
          · rw [hbot]; exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
          · rw [hsort]; exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
          · rw [hpi]; exact ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩
        exact lrTermS_noLam_trans hW hno h₁₂ h₂₃

/-- Symmetry of `LRTermS` across all `TypeValuedLamCpt` compacts at every `EnvWfT E`. -/
theorem lrTermS_typeValued_symm (hW : EnvWfT E) {c : CptI}
    (hc : TypeValuedLamCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermS E n Γ M M' A c) :
    LRTermS E n Γ M' M A c :=
  (lrTermS_typeValued_symm_and_trans hW hc).1 h

/-- Transitivity of `LRTermS` across all `TypeValuedLamCpt` compacts at every `EnvWfT E`. -/
theorem lrTermS_typeValued_trans (hW : EnvWfT E) {c : CptI}
    (hc : TypeValuedLamCpt c)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermS E n Γ M N A c) (h₂ : LRTermS E n Γ N P A c) :
    LRTermS E n Γ M P A c :=
  (lrTermS_typeValued_symm_and_trans hW hc).2 h₁ h₂

/-- Simultaneous symmetry and transitivity of `LRTermSDI` across **all** `TypeValuedLamCpt` compacts
    (including higher-order `.lam g` compacts) at every `EnvWfT E`. -/
theorem lrTermSDI_typeValued_symm_and_trans (hW : EnvWfT E) {c : CptI}
    (hc : TypeValuedLamCpt c) :
    (∀ {Γ : LCtx} {M M' A : Expr Nat},
      LRTermSDI E n Γ M M' A c → LRTermSDI E n Γ M' M A c) ∧
    (∀ {Γ : LCtx} {M N P A : Expr Nat},
      LRTermSDI E n Γ M N A c → LRTermSDI E n Γ N P A c → LRTermSDI E n Γ M P A c) := by
  induction hc with
  | bot =>
      exact ⟨fun h => lrTermSDI_noLam_symm hW (fun _ h => by cases h) h,
        fun h₁ h₂ => lrTermSDI_noLam_trans hW (fun _ h => by cases h) h₁ h₂⟩
  | sort =>
      exact ⟨fun h => lrTermSDI_noLam_symm hW (fun _ h => by cases h) h,
        fun h₁ h₂ => lrTermSDI_noLam_trans hW (fun _ h => by cases h) h₁ h₂⟩
  | pi a f =>
      exact ⟨fun h => lrTermSDI_noLam_symm hW (fun _ h => by cases h) h,
        fun h₁ h₂ => lrTermSDI_noLam_trans hW (fun _ h => by cases h) h₁ h₂⟩
  | @lam g _ hcod ih =>
      refine ⟨?_, ?_⟩
      · intro Γ M M' A h
        rw [lrTermSDI_lam_iff] at h ⊢
        obtain ⟨A₁, B₁, w, hA₁, hΓ₁, hB₁, happ⟩ := h
        refine ⟨A₁, B₁, w, hA₁, hΓ₁, hB₁, fun s hs N N' hN hN' hrel => ?_⟩
        have hNN' := happ s hs N N' hN hN' hrel
        have hN'N := happ s hs N' N hN' hN (fun u hu => (ih s hs u hu).1 (hrel u hu))
        rcases hcod s hs with hbot | hsort | ⟨a, f, hpi⟩
        · rw [hbot]; exact lrTermSDI_bot _ _ _ _
        · rw [hsort] at hNN' hN'N ⊢
          rw [lrTermSDI_sort_iff] at hNN' hN'N ⊢
          exact ⟨hNN'.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW hN'N.2⟩
        · rw [hpi] at hNN' hN'N ⊢
          rw [lrTermSDI_pi_iff] at hNN' hN'N ⊢
          exact ⟨hNN'.1, lrTypeIN_symm (envClosed_of_envWfT hW) hW hN'N.2⟩
      · intro Γ M N P A h₁ h₂
        rw [lrTermSDI_lam_iff] at h₁ h₂ ⊢
        obtain ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, happ₁₂⟩ := h₁
        obtain ⟨A₂, B₂, _, hA₂, _, _, happ₂₃⟩ := h₂
        have heq : Expr.pi A₁ B₁ = Expr.pi A₂ B₂ :=
          whRed_normal_unique_of_envWfT hW hA₁ (fun _ h => whStep_pi_false h)
            hA₂ (fun _ h => whStep_pi_false h)
        injection heq with eA eB; subst eA; subst eB
        refine ⟨A₁, B₁, w₁, hA₁, hΓ₁, hB₁, fun s hs N₀ N₀' hN₀ hN₀' hrel => ?_⟩
        have hrelNN : ∀ u ∈ s.1, LRTermSDI E n Γ N₀ N₀ A₁ u :=
          fun u hu => (ih s hs u hu).2 (hrel u hu) ((ih s hs u hu).1 (hrel u hu))
        have h₁₂ := happ₁₂ s hs N₀ N₀ hN₀ hN₀ hrelNN
        have h₂₃ := happ₂₃ s hs N₀ N₀' hN₀ hN₀' hrel
        have hno : ∀ g', s.2 ≠ .lam g' := by
          rcases hcod s hs with hbot | hsort | ⟨a, f, hpi⟩
          · rw [hbot]; intro _ h; cases h
          · rw [hsort]; intro _ h; cases h
          · rw [hpi]; intro _ h; cases h
        exact lrTermSDI_noLam_trans hW hno h₁₂ h₂₃

/-- Symmetry of `LRTermSDI` across all `TypeValuedLamCpt` compacts at every `EnvWfT E`. -/
theorem lrTermSDI_typeValued_symm (hW : EnvWfT E) {c : CptI} (hc : TypeValuedLamCpt c)
    {Γ : LCtx} {M M' A : Expr Nat} (h : LRTermSDI E n Γ M M' A c) :
    LRTermSDI E n Γ M' M A c :=
  (lrTermSDI_typeValued_symm_and_trans hW hc).1 h

/-- Transitivity of `LRTermSDI` across all `TypeValuedLamCpt` compacts at every `EnvWfT E`. -/
theorem lrTermSDI_typeValued_trans (hW : EnvWfT E) {c : CptI} (hc : TypeValuedLamCpt c)
    {Γ : LCtx} {M N P A : Expr Nat}
    (h₁ : LRTermSDI E n Γ M N A c) (h₂ : LRTermSDI E n Γ N P A c) :
    LRTermSDI E n Γ M P A c :=
  (lrTermSDI_typeValued_symm_and_trans hW hc).2 h₁ h₂

/-- Under universe consistency `hSort`, `.pi (.sort (.succ .zero)) (.sort (.succ .zero))`
    (`Sort 1 → Sort 1`) is never a proposition
    (`¬ IsPropTyI E n Γ (.pi (.sort (.succ .zero)) (.sort (.succ .zero)))`). -/
theorem not_isPropTyI_pi_sort1_sort1
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (Γ : LCtx) :
    ¬ IsPropTyI E n Γ (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) := by
  rintro ⟨⟨hpi⟩, _⟩
  let ⟨u, v, hA, hB, hc⟩ := hasTyT_pi_inv hpi rfl
  have hcA := hasTyT_sort_inv hA rfl
  have hcB := hasTyT_sort_inv hB rfl
  have hu : eval (fun _ => some 0) u = some 2 :=
    (hSort hcA (fun _ => some 0)).symm
  have hv : eval (fun _ => some 0) v = some 2 :=
    (hSort hcB (fun _ => some 0)).symm
  have himax : eval (fun _ => some 0) (.imax u v) = some 0 :=
    hSort hc (fun _ => some 0)
  simp only [eval, hu, hv, Option.bind_some, Option.map_some] at himax
  cases himax

/-- Under universe consistency `hSort` and sort-Π disjointness `hdisj`, `LRTermD` is false on the
    diagonal of `polyPi = .lam (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))` at
    `polyPiCpt = .lam [([], .pi .bot [])]` in `Γ = []` — ruling out both the `LRTermDCore` branch
    and the outer `IsPropTyI` escape hatch on `#7652`'s `lamPiBot`. -/
theorem not_lrTermD_polyPi_of_not_pi_sort
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hdisj : ¬ Nonempty (TyConvT E n [] (.pi (.sort .zero) (.sort .zero)) (.sort .zero))) :
    ¬ LRTermD E n [] polyPi polyPi
        (.pi (.sort (.succ .zero)) (.sort (.succ .zero)))
        polyPiCpt := by
  rintro (hP | hcore)
  · exact not_isPropTyI_pi_sort1_sort1 hSort [] hP
  · exact not_lrTermDCore_polyPi_of_not_pi_sort hdisj hcore

/-- At `idPiProp = .pi (.sort .zero) (.bvar 0)` and `c = .lam [([.pi .bot []], d)]`,
    `LRTermDCore E n [] M M' idPiProp (.lam [([.pi .bot []], d)])` holds unconditionally for
    **every** `E, n, d` and **every** pair of expressions `M, M' : Expr Nat` (even untyped,
    unrelated terms!), because the demand `.pi .bot []` forces `WhRed E N (.pi D₁ C₁)` and hence
    `∀ l, N ≠ .sort l` (`whRed_sort_eq`), which together with `hN : HasTyT E n [] N (.sort .zero)`
    satisfies the `IsPropTyI E n [] (instantiate0 N (.bvar 0))` escape hatch in `LRTermDCore.lam`. -/
theorem lrTermDCore_idPiProp_lam_pi_total (E : ResolvedEnv) (n : Nat)
    (M M' : Expr Nat) (d : CptI) :
    LRTermDCore E n [] M M' idPiProp (.lam [([.pi .bot []], d)]) := by
  rw [idPiProp, lrTermDCore_lam_iff]
  refine ⟨.sort .zero, .bvar 0, .zero, .refl _,
    ⟨.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)⟩,
    ⟨.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl⟩,
    fun s hs N N' hN _ hrel => ?_⟩
  simp only [List.mem_singleton] at hs
  subst hs
  refine Or.inl ?_
  change IsPropTyI E n [] N
  refine ⟨⟨hN⟩, fun l hl => ?_⟩
  have hpi := hrel (.pi .bot []) (List.Mem.head _)
  rw [lrTermDCore_pi_iff] at hpi
  cases hpi.2 with
  | pi hNred _ _ _ _ _ _ =>
      rw [hl] at hNred
      exact nomatch whRed_sort_eq hNred

/-- Full `LRTermD` totality at `idPiProp` for every `M, M' : Expr Nat` and `c : CptI`. -/
theorem lrTermD_idPiProp_lam_pi_total (E : ResolvedEnv) (n : Nat)
    (M M' : Expr Nat) (d : CptI) :
    LRTermD E n [] M M' idPiProp (.lam [([.pi .bot []], d)]) :=
  Or.inr (lrTermDCore_idPiProp_lam_pi_total E n M M' d)

#print axioms lrTermSpineSplit
#print axioms approxI_pi_bot_of_whRed
#print axioms approxDI_pi_bot_of_whRed
#print axioms lrTermS_transport_of_botDI
#print axioms lrTermSTransportLam_of_botDI
#print axioms lrTermS_transport
#print axioms lrTermSTransportLam_of_typeSoundness
#print axioms LRTermSDI
#print axioms lrTermSDI_bot
#print axioms lrTermSDI_sort_iff
#print axioms lrTermSDI_pi_iff
#print axioms lrTermSDI_spine_iff
#print axioms lrTermSDI_lam_iff
#print axioms lrTermSDI_expand
#print axioms lrTermSDI_lam_at_sort_false
#print axioms lrTermSDI_spine_at_sort
#print axioms lrTypeIN_of_lrTermSDI_sort
#print axioms lrTermSDI_transport
#print axioms lrTermDCore_bot
#print axioms lrTermDCore_sort_iff
#print axioms lrTermDCore_pi_iff
#print axioms lrTermDCore_spine_iff
#print axioms lrTermDCore_lam_iff
#print axioms lrTermDCore_expand
#print axioms lrTypeIN_of_lrTermDCore_sort
#print axioms lrTermDCore_whRed_index_iff
#print axioms PropTyTransport
#print axioms lrTermDCore_transport
#print axioms lrTermD_transport
#print axioms LRTermDTransportLam
#print axioms lrTermDTransportLam_of_botDI
#print axioms not_isPropTyI_sort
#print axioms not_lrTermS_idPiProp_sortStep
#print axioms not_lrTermSDI_idPiProp_sortStep
#print axioms not_lrTermDCore_idPiProp_sortStep
#print axioms not_lrTermD_idPiProp_sortStep
#print axioms FundamentalTermS
#print axioms FundamentalTermSDI
#print axioms FundamentalTermD_DI
#print axioms not_fundamentalTermS
#print axioms not_fundamentalTermSDI
#print axioms not_fundamentalTermD
#print axioms not_fundamentalTermD_DI
#print axioms whStep_app_bvar_false
#print axioms whRed_app_bvar_eq
#print axioms not_botPiCpt_closedIrrPiCpt
#print axioms closedIrrPiSortLevel
#print axioms not_lrTypeIN_closedIrrPi
#print axioms not_lrTermI_closedIrrPi
#print axioms not_lrTermS_closedIrrPi
#print axioms not_lrTermSDI_closedIrrPi
#print axioms not_lrTermDCore_closedIrrPi
#print axioms not_lrTermD_closedIrrPi
#print axioms not_lrTermS_eta_etaIdPiPropFn
#print axioms not_lrTermDCore_etaIdPiPropFn_diag
#print axioms not_lrTermDCore_eta_etaIdPiPropFn
#print axioms hasTyT_sort_inv
#print axioms hasTyT_pi_inv
#print axioms not_isPropTyI_pi_sort0_sort0
#print axioms not_lrTermD_eta_etaIdPiPropFn
#print axioms lrTermS_weaken_botPiCpt
#print axioms lrTermSDI_weaken_botPiCpt
#print axioms lrTermDCore_weaken_botPiCpt
#print axioms lrTermS_subst_botPiCpt
#print axioms lrTermS_subst0_botPiCpt
#print axioms lrTermSDI_subst_botPiCpt
#print axioms lrTermSDI_subst0_botPiCpt
#print axioms lrTermDCore_subst_botPiCpt
#print axioms lrTermDCore_subst0_botPiCpt
#print axioms lrTermS_subst_sort_and_bvar
#print axioms lrTermSDI_subst_sort_and_bvar
#print axioms lrTermD_subst_bvar
#print axioms fundTermSDI_sorts
#print axioms fundTermD_DI_sorts
#print axioms fundConvSDI_of_whStep
#print axioms fundConvSDI_of_whRed
#print axioms fundConvSDI_delta
#print axioms fundConvSDI_iota
#print axioms fundConvD_DI_of_whStep
#print axioms fundConvD_DI_of_whRed
#print axioms fundConvD_DI_delta
#print axioms fundConvD_DI_iota
#print axioms lrTermD_botPiCpt_idPiProp
#print axioms lrTermD_botPiCpt_closedIrrPi
#print axioms FundamentalTermBotDI
#print axioms fundamentalLRINBotDI_of_fundamentalTermBotDI
#print axioms piRow_of_fundamentalTermBotDI
#print axioms not_tyConvT_pi_sort_of_fundamentalTermBotDI
#print axioms deltaConst_iff_transparent_of_bodyTransparent
#print axioms hasTyT_idPiProp_ctx
#print axioms isPropTyI_idPiProp
#print axioms lrTermDCore_dataSpine_args_vacuous
#print axioms lrTermDCore_spine_iff_simple
#print axioms not_lrTermD_etaIdPiPropFn_diag
#print axioms not_lrTermDCore_etaK_etaIdPiPropFn
#print axioms not_lrTermD_etaK_etaIdPiPropFn
#print axioms polyPi
#print axioms polyPiCpt
#print axioms hasTyT_polyPi
#print axioms approxI_polyPi
#print axioms approxDI_polyPi
#print axioms tyConvT_pi_sort_of_lrTermDCore_polyPi
#print axioms not_lrTermDCore_polyPi_of_not_pi_sort
#print axioms whRed_of_whNormal
#print axioms noLam_of_botPiCpt
#print axioms lrTermS_noLam_symm
#print axioms lrTermSDI_noLam_symm
#print axioms lrTermDCore_noLam_symm
#print axioms lrTermD_noLam_symm
#print axioms lrTermS_noLam_trans
#print axioms lrTermSDI_noLam_trans
#print axioms lrTermDCore_noLam_trans
#print axioms lrTermD_noLam_trans
#print axioms lrTermS_noLam_refl_left
#print axioms lrTermSDI_noLam_refl_left
#print axioms lrTermDCore_noLam_refl_left
#print axioms FirstOrderCpt
#print axioms firstOrderCpt_of_botPiCpt
#print axioms lrTermS_firstOrder_trans
#print axioms lrTermSDI_firstOrder_trans
#print axioms lrTermDCore_firstOrder_trans
#print axioms lrTermD_firstOrder_trans
#print axioms lrTermD_botPiCpt_symm
#print axioms lrTermD_botPiCpt_trans
#print axioms fundConvBotDI_symm
#print axioms fundConvBotDI_tyConv
#print axioms approxSubstDI
#print axioms fundamentalTermIS_of_envClosed
#print axioms fundamentalTermIS_of_envWfT
#print axioms fundamentalTermIS_DI
#print axioms not_hasTyT_sort_zero_of_sortRow
#print axioms isPropTyI_of_hasTyT_sort_zero
#print axioms isPropTyI_iff_hasTyT_sort_zero
#print axioms isPropTyI_of_hasTyT_sort_zero_botDI
#print axioms lift_sort_inv_term
#print axioms isPropTyI_weaken
#print axioms isPropTyI_weaken0
#print axioms isPropTyI_subst_of_sortRow
#print axioms isPropTyI_subst0_of_sortRow
#print axioms isPropTyI_subst_of_botDI
#print axioms isPropTyI_subst0_of_botDI
#print axioms isPropTyI_substLet_of_sortRow
#print axioms isPropTyI_substLet0_of_sortRow
#print axioms fundamentalTermDIS_of_sortRow
#print axioms fundamentalTermDIS_of_botDI
#print axioms approxDI_bot_bvar_inv
#print axioms approxDI_insert_bot_bvar_inv
#print axioms lrTermS_subst_bvar_all
#print axioms lrTermSDI_subst_bvar_all
#print axioms lrTermDCore_subst_bvar_all
#print axioms lrTermD_subst_bvar_all
#print axioms instantiate_foldApps_term
#print axioms whNormal_foldApps_of_rigidNonRec
#print axioms lrTermDCore_spine_subst_of_rigidNonRec
#print axioms lrTermD_spine_subst_of_rigidNonRec
#print axioms lrTermI_noLam_symm
#print axioms lrTermI_noLam_trans
#print axioms lrTermI_noLam_refl_left
#print axioms lrTermI_firstOrder_trans
#print axioms LRTermReflLeft
#print axioms lrTermI_trans_of_reflLeft
#print axioms lrTermS_trans_of_reflLeft
#print axioms lrTermSDI_trans_of_reflLeft
#print axioms lrTermDCore_trans_of_reflLeft
#print axioms lrTermD_trans_of_reflLeft
#print axioms TypeValuedLamCpt
#print axioms typeValuedLamCpt_of_noLam
#print axioms typeValuedLamCpt_of_botPiCpt
#print axioms lrTermI_typeValued_symm_and_trans
#print axioms lrTermI_typeValued_symm
#print axioms lrTermI_typeValued_trans
#print axioms lrTermS_typeValued_symm_and_trans
#print axioms lrTermS_typeValued_symm
#print axioms lrTermS_typeValued_trans
#print axioms lrTermSDI_typeValued_symm_and_trans
#print axioms lrTermSDI_typeValued_symm
#print axioms lrTermSDI_typeValued_trans
#print axioms not_isPropTyI_pi_sort1_sort1
#print axioms not_lrTermD_polyPi_of_not_pi_sort
#print axioms lrTermDCore_idPiProp_lam_pi_total
#print axioms lrTermD_idPiProp_lam_pi_total

end Rcic.Declarative.NativeValleys.PiModelDeltaIotaTermAudit


