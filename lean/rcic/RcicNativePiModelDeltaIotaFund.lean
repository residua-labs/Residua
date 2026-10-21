import rcic.RcicNativePiModelDeltaIotaConv

/-!
# RcicNativePiModelDeltaIotaFund — `ApproxDIK` Level Invariance, `botClosedExpr`, `ProbeCpt` PER & Constructor Clauses for `LRTermDSubK`, Full `.lam g` Index Transport, and `WhStepPiKClosed` Lift/Substitution Commutation

Builds on `RcicNativePiModelDeltaIota` (#7656), `RcicNativePiModelDeltaIotaTerm` (#7664), and
`RcicNativePiModelDeltaIotaConv` (#7669). All constructions are concrete `def` / `inductive` /
`theorem` declarations; zero `structure` or `class` declarations are introduced.

## Summary of Main Results

1. **§1. Universe-Level Invariance of `ApproxDIK` (`approxDIK_instantiateLevels_iff`,
   `semEqDIK_const_levels`), `botClosedExpr`, and Structural `BotPiCpt` / `ProbeCpt` Exclusions:**
   * Proves `approxDIK_instantiateLevels_swap`, `approxDIK_instantiateLevels_iff`,
     `approxDIK_const_levels`, and `semEqDIK_const_levels` (`ConvT.consts` soundness in `ApproxDIK`
     across all constant classes: `RigidConst`, `DeltaConst`, and `RecursorConst`, including
     `recursorK`).
   * Defines the closed `⊥`-only expression `botClosedExpr := .app (.sort .zero) (.sort .zero)`
     (`exprClosedAt_botClosedExpr`, `botClosedExpr_lift`, `botClosedExpr_instantiate`,
     `botClosedExpr_instantiateLevels`), proves that its only compact in `ApproxI ρ`, `ApproxDI E ρ`,
     and `ApproxDIK E ρ` is `.bot` for **every** environment `E` and **every** valuation `ρ : EnvI`
     (`approxI_botClosedExpr_iff`, `approxDI_botClosedExpr_iff`, `approxDIK_botClosedExpr_iff`,
     including `ρ = ctxEnvDIK E Γ`), and derives `semEqDIK_k_botClosedExpr_of_envWfT` (fieldful K in
     `SemEqDIK E ρ` for arbitrary `ρ : EnvI` with closed canonical fields).
   * Proves structural `BotPiCpt` exclusions in `ApproxDIK`:
     `approxDIK_lam_botPiCpt_eq_bot`, `approxDIK_rigidConst_botPiCpt_eq_bot`,
     `approxDIK_recursor_botPiCpt_eq_bot` (covering both `.recursor` and `.recursorK`),
     `approxDIK_const_body_none_botPiCpt_eq_bot`, and `not_approxDIK_pi_sort`.
   * Defines the probe compact fragment `ProbeCpt : CptI → Prop` (`.bot`, `.sort`, `.pi .bot []`),
     proves `botPiCpt_of_probeCpt` and `approxDIK_pi_probe_inv`, and proves soundness-free reverse
     adequacy `approxDIK_of_lrTermDSubKCore_probe`, `approxDIK_of_lrTermDSubK_probe_of_not_prop`,
     and `approxDIK_of_lrTermDSubK_probe_at_sort`.

2. **§2. Full PER (`lrTermDSubKCore_probe_symm`, `lrTermDSubKCore_probe_trans`), Sort-Index
   Irrelevance on `BotPiCpt`, and Full `.lam g` Index Transport (`lrTermDSubKCore_transport`,
   `lrTermDSubK_transport`):**
   * Proves `lrTermDSubKCore_botPiCpt_sort_index_irrel`, `lrTermDSubK_botPiCpt_sort_index_irrel`, and
     `lrTermDSubKCore_botPiCpt_transport_of_sort`.
   * Proves unconditional symmetry and transitivity of `LRTermDSubKCore` and `LRTermDSubK` on all
     `ProbeCpt` compacts at `EnvWfT E` and `CtxWfT E n Γ` (`lrTermDSubKCore_probe_symm`,
     `lrTermDSubK_probe_symm`, `lrTermDSubKCore_probe_trans`, `lrTermDSubK_probe_trans`, requiring
     **zero** `TypeSoundness`, **zero** `LRTermIndexTransport`, and **zero** `SortRow`).
   * Proves full index transport `lrTermDSubKCore_transport` and `lrTermDSubK_transport` across
     **all** compacts `c : CptI` (including `.lam g` and `.spine r args`) along `TyConvT E n Γ A A'`
     from `EnvWfT E`, `FundamentalLRINBotDIKCanon_letFree E n`, and `PropTyTransport E n`.

3. **§3. Constructor-by-Constructor `HasTyT` / `ConvT` Clauses for `LRTermDSubK` on `ProbeCpt`,
   Bidirectional `LRTermDSubKBi`, and 27-Constructor Reduction of
   `FundamentalTermDSubKProbe_letFree` to Application:**
   * Proves all `HasTyT` and `ConvT` constructor clauses on `ProbeCpt` (`fundTermDSubK_sort`,
     `fundTermDSubK_bvar`, `fundTermDSubK_lam`, `fundTermDSubK_const_of_body_none`,
     `fundTermDSubK_rigidConst`, `fundTermDSubK_recursor`, `fundTermDSubK_deltaConst`,
     `fundTermDSubK_pi_probe` — requiring **zero** induction hypotheses on `A` or `B`! —
     `fundTermDSubK_lit`, `fundTermDSubK_letE`, `fundTermDSubK_conv_probe`, `fundConvDSubK_refl`,
     `fundConvDSubK_probe_symm`, `fundConvDSubK_probe_trans`, `fundConvDSubK_lam`,
     `fundConvDSubK_pi_probe` — requiring **zero** semantic induction hypotheses on `A₁, A₂` or
     `B₁, B₂`! — `fundConvDSubK_letE`, `fundConvDSubK_consts_of_body_none`,
     `fundConvDSubK_rigidConsts`, `fundConvDSubK_recursorConsts`, `fundConvDSubK_deltaConsts`,
     `fundConvDSubK_eta`, `fundConvDSubK_tyConv_probe`).
   * Defines the bidirectional probe relation `LRTermDSubKBi` (`lrTermDSubKBi_symm`,
     `lrTermDSubKBi_trans`, `lrTermDSubKBi_whRedPiKCanon_expand`, `lrTermDSubKBi_eta`),
     `FundamentalTermDSubKProbe_letFree`, and `FundamentalTermDSubKBiProbe_letFree`, deriving
     `piRow_letFree_of_fundamentalTermDSubKProbe_letFree`,
     `piRow_of_fundamentalTermDSubKProbe_letFree : EnvWfT E → FundamentalTermDSubKProbe_letFree E n → PiRowField E n`,
     and `piRow_of_fundamentalTermDSubKBiProbe_letFree`.
   * Proves the 27-constructor mutual reduction theorem `fundamentalTermDSubKBiProbe_letFree_of_supply`
     (and `fundamentalTermDSubKProbe_letFree_of_supply`, `piRow_of_appLetProbeSupplyDSubKBi`)
     reducing `FundamentalTermDSubKBiProbe_letFree E n` and `PiRowField E n` to
     `AppLetProbeSupplyDSubKBi E n`.

4. **§4. `EnvI.bot` Lift/Substitution Invariance of `ApproxDIK`, Closed-Field Deterministic
   K-Readback `WhStepPiKClosed` / `WhRedPiKClosed`, and Unconditional Lift/Substitution Commutation:**
   * Proves `approxDIK_bot_lift_iff` (`ApproxDIK E EnvI.bot (lift k 1 e) c ↔ ApproxDIK E EnvI.bot e c`
     for all `k, e, c`) and `approxDIK_bot_subst_lift_iff` (`(∀ u, ApproxDIK E EnvI.bot a u →
     u = .bot) → (ApproxDIK E EnvI.bot (instantiate j (lift 0 j a) e) c ↔ ApproxDIK E EnvI.bot e c)`
     for all `j, e, c`, specialized to `j = 0`, `a = .bvar m`, and `a = botClosedExpr`).
   * Proves `whStepPiK_lift_of_envClosed`, `whRedPiK_lift_of_envClosed` (for all `k : Nat`),
     `whStepPiK_instantiate_of_botApprox`, and `whRedPiK_instantiate_of_botApprox` (for all `j : Nat`).
   * Defines `WhStepPiKClosed` / `WhRedPiKClosed` (fixing `w.fields = List.replicate w.fields.length botClosedExpr`),
     proves `whStepPiK_of_whStepPiKClosed`, `semEqDIK_whStepPiKClosed`, `semEqDIK_whRedPiKClosed`,
     **exact single-step determinism `whDetPiKClosed_of_envWfT`**, `whRedPiKClosed_normal_unique_of_envWfT`,
     0-field and fieldful K-reductions (`whRedPiKClosed_trueEnvU_kRecVar_sort`,
     `whRedPiKClosed_andEnvU_mixAndRedex_mixPi`), **unconditional `lift k 1` commutation for ALL
     `k : Nat` (including `k = 0`)** (`whStepPiKClosed_lift_of_envClosed`,
     `whRedPiKClosed_lift_of_envClosed`), and **unconditional `instantiate j (lift 0 j v)` commutation
     for ALL `j : Nat` (including `j = 0`) on `⊥`-approximated substituents**
     (`whStepPiKClosed_instantiate_of_botApprox`, `whRedPiKClosed_instantiate_of_botApprox`).
   * Defines `LRTypeINPiKClosed` and `LRTypeINBiDIKClosed`, proving `lrTypeINPiKClosed_symm`,
     `lrTypeINPiKClosed_trans_of_envWfT`, **unconditional weakening stability
     `lrTypeINPiKClosed_weaken_botPiCpt`, `lrTypeINPiKClosed_weaken0_botPiCpt`, and
     `lrTypeINBiDIKClosed_weaken0`**, and **unconditional `⊥`-substituent substitution stability
     `lrTypeINPiKClosed_subst_botPiCpt`, `lrTypeINPiKClosed_subst0_botPiCpt`, and
     `lrTypeINBiDIKClosed_subst0`**.

`closure_claim = 0`. Zero `sorry`, zero new axioms, zero `structure`/`class` declarations.
-/

namespace Rcic.Declarative.NativeValleys.PiModelDeltaIotaFundAudit

open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelIrrAudit
open Rcic.Declarative.NativeValleys.PiModelKAudit
open Rcic.Declarative.NativeValleys.PiModelTermAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaTermAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaConvAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ## §1. Universe-Level Invariance of `ApproxDIK`, `botClosedExpr`, and Structural `BotPiCpt` /
`ProbeCpt` Exclusions in `ApproxDIK` -/

/-- Universe-level swap invariance for `ApproxDIK`: replacing `instantiateLevels ls₁ e₀` by
    `instantiateLevels ls₂ e₀` preserves all compacts `c : CptI` (including `recursorK`). -/
theorem approxDIK_instantiateLevels_swap {E : ResolvedEnv} {ρ : EnvI} {e : Expr Nat} {c : CptI}
    (h : ApproxDIK E ρ e c) :
    ∀ {e₀ : Expr Nat} (ls₁ ls₂ : List Level),
      e = instantiateLevels ls₁ e₀ → ApproxDIK E ρ (instantiateLevels ls₂ e₀) c := by
  induction h with
  | bot => intro _ _ _ _; exact .bot _ _
  | @bvar ρ i c h =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .bvar h
  | sort =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .sort _ _
  | pi _ _ ihA ihB =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .pi (ihA ls₁ ls₂ rfl) (fun s hs => ihB s hs ls₁ ls₂ rfl)
  | lam _ ihb =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .lam (fun s hs => ihb s hs ls₁ ls₂ rfl)
  | app _ hs _ ihf iha =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .app (ihf ls₁ ls₂ rfl) hs (fun u hu => iha u hu ls₁ ls₂ rfl)
  | const _ r _ hrigid =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .const _ r _ hrigid
  | @delta ρ r ls m b c hdelta _ ih =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ with
      | const r₀ ls₀ =>
          cases heq
          exact .delta hdelta (ih _ (ls₀.map (instLevel ls₂)) rfl)
      | _ => cases heq
  | @recursor ρ w ls us_pre us_fields c hpre hflds _ ih =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ with
      | const r₀ ls₀ =>
          injection heq with hr₀ hls₀
          subst hr₀
          exact .recursor (ls₀.map (instLevel ls₂)) hpre hflds
            (ih ls (ls₀.map (instLevel ls₂)) rfl)
      | _ => cases heq
  | @recursorK ρ w ls us_pre u_maj c hk hpre hmaj _ ih =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ with
      | const r₀ ls₀ =>
          injection heq with hr₀ hls₀
          subst hr₀
          exact .recursorK (ls₀.map (instLevel ls₂)) hk hpre hmaj
            (ih ls (ls₀.map (instLevel ls₂)) rfl)
      | _ => cases heq
  | appSpine _ _ ihf iha =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ <;> cases heq
      exact .appSpine (ihf ls₁ ls₂ rfl) (iha ls₁ ls₂ rfl)
  | @letE ρ A v b c _ ih =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ with
      | letE A₀ v₀ b₀ =>
          cases heq
          exact .letE (ih (e₀ := .app (.lam A₀ b₀) v₀) ls₁ ls₂ rfl)
      | _ => cases heq
  | @lit ρ t c h =>
      intro e₀ ls₁ ls₂ heq
      cases e₀ with
      | lit t₀ =>
          cases heq
          exact .lit h
      | _ => cases heq

/-- Universe-level instantiation invariance of `ApproxDIK`. -/
theorem approxDIK_instantiateLevels_iff (E : ResolvedEnv) (ρ : EnvI) (ls : List Level)
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E ρ (instantiateLevels ls e) c ↔ ApproxDIK E ρ e c := by
  constructor
  · intro h
    have := approxDIK_instantiateLevels_swap h ls [] rfl
    rwa [instantiateLevels_nil] at this
  · intro h
    exact approxDIK_instantiateLevels_swap h [] ls (instantiateLevels_nil e).symm

/-- Constant universe-level invariance in `ApproxDIK` across all constant classes. -/
theorem approxDIK_const_levels {E : ResolvedEnv} {ρ : EnvI} {r : Nat} (ls₁ ls₂ : List Level)
    {c : CptI} (h : ApproxDIK E ρ (.const r ls₁) c) : ApproxDIK E ρ (.const r ls₂) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hrigid => exact .const _ r ls₂ hrigid
  | delta hdelta h => exact .delta hdelta (approxDIK_instantiateLevels_swap h ls₁ ls₂ rfl)
  | recursor _ hpre hflds h =>
      exact .recursor ls₂ hpre hflds (approxDIK_instantiateLevels_swap h ls₁ ls₂ rfl)
  | recursorK _ hk hpre hmaj h =>
      exact .recursorK ls₂ hk hpre hmaj (approxDIK_instantiateLevels_swap h ls₁ ls₂ rfl)

/-- Any two universe-level instantiations of the same constant `r` are semantically equal in
    `ApproxDIK` (`ConvT.consts` soundness in `ApproxDIK`). -/
theorem semEqDIK_const_levels (E : ResolvedEnv) (ρ : EnvI) (r : Nat) (ls₁ ls₂ : List Level) :
    SemEqDIK E ρ (.const r ls₁) (.const r ls₂) :=
  fun _ => ⟨approxDIK_const_levels ls₁ ls₂, approxDIK_const_levels ls₂ ls₁⟩

/-- Closed expression `.app (.sort .zero) (.sort .zero)` whose only compact in `ApproxI ρ`,
    `ApproxDI E ρ`, and `ApproxDIK E ρ` is `.bot` for **every** `E` and **every** `ρ : EnvI`,
    and which is definitionally invariant under `lift`, `instantiate`, and `instantiateLevels`. -/
def botClosedExpr : Expr Nat :=
  .app (.sort .zero) (.sort .zero)

theorem exprClosedAt_botClosedExpr (k : Nat) : exprClosedAt k botClosedExpr = true := rfl

theorem botClosedExpr_lift (c d : Nat) : lift c d botClosedExpr = botClosedExpr := rfl

theorem botClosedExpr_instantiate (j : Nat) (v : Expr Nat) :
    instantiate j v botClosedExpr = botClosedExpr := rfl

theorem botClosedExpr_instantiateLevels (ls : List Level) :
    instantiateLevels ls botClosedExpr = botClosedExpr := rfl

theorem replicate_botClosedExpr_map_lift (m c d : Nat) :
    (List.replicate m botClosedExpr).map (lift c d) = List.replicate m botClosedExpr := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ, List.map_cons, botClosedExpr_lift, ih]

theorem replicate_botClosedExpr_map_instantiate (m j : Nat) (v : Expr Nat) :
    (List.replicate m botClosedExpr).map (instantiate j v) = List.replicate m botClosedExpr := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ, List.map_cons, botClosedExpr_instantiate, ih]

/-- For every valuation `ρ : EnvI`, the only compact approximating `botClosedExpr` in `ApproxI ρ`
    is `.bot`. -/
theorem approxI_botClosedExpr_inv {ρ : EnvI} {c : CptI}
    (h : ApproxI ρ botClosedExpr c) : c = .bot := by
  rcases approxI_app_inv h with rfl | ⟨g, s, _, hf, _, _⟩ | ⟨r, args, u, _, hf, _⟩
  · rfl
  · rcases approxI_sort_inv hf with h0 | h0 <;> cases h0
  · rcases approxI_sort_inv hf with h0 | h0 <;> cases h0

theorem approxI_botClosedExpr_iff (ρ : EnvI) (c : CptI) :
    ApproxI ρ botClosedExpr c ↔ c = .bot :=
  ⟨approxI_botClosedExpr_inv, fun h => h ▸ .bot _ _⟩

/-- For every `E : ResolvedEnv` and `ρ : EnvI`, the only compact approximating `botClosedExpr` in
    `ApproxDI E ρ` is `.bot`. -/
theorem approxDI_botClosedExpr_inv {E : ResolvedEnv} {ρ : EnvI} {c : CptI}
    (h : ApproxDI E ρ botClosedExpr c) : c = .bot := by
  rcases approxDI_app_inv h with rfl | ⟨g, s, _, hf, _, _⟩ | ⟨r, args, u, _, hf, _⟩
  · rfl
  · rcases approxDI_sort_inv hf with h0 | h0 <;> cases h0
  · rcases approxDI_sort_inv hf with h0 | h0 <;> cases h0

theorem approxDI_botClosedExpr_iff (E : ResolvedEnv) (ρ : EnvI) (c : CptI) :
    ApproxDI E ρ botClosedExpr c ↔ c = .bot :=
  ⟨approxDI_botClosedExpr_inv, fun h => h ▸ .bot _ _⟩

/-- For every `E : ResolvedEnv` and `ρ : EnvI` (including `ctxEnvDIK E Γ`), the only compact
    approximating `botClosedExpr` in `ApproxDIK E ρ` is `.bot`. -/
theorem approxDIK_botClosedExpr_inv {E : ResolvedEnv} {ρ : EnvI} {c : CptI}
    (h : ApproxDIK E ρ botClosedExpr c) : c = .bot := by
  rcases approxDIK_app_inv h with rfl | ⟨g, s, _, hf, _, _⟩ | ⟨r, args, u, _, hf, _⟩
  · rfl
  · rcases approxDIK_sort_inv hf with h0 | h0 <;> cases h0
  · rcases approxDIK_sort_inv hf with h0 | h0 <;> cases h0

theorem approxDIK_botClosedExpr_iff (E : ResolvedEnv) (ρ : EnvI) (c : CptI) :
    ApproxDIK E ρ botClosedExpr c ↔ c = .bot :=
  ⟨approxDIK_botClosedExpr_inv, fun h => h ▸ .bot _ _⟩

/-- **Valuation-Universal Fieldful $K$ Soundness in `ApproxDIK` (`semEqDIK_k_botClosedExpr_of_envWfT`):**
    Because `botClosedExpr` has only `.bot` in `ApproxDIK E ρ` for **every** valuation `ρ : EnvI`
    (not just `EnvI.bot`, including `ctxEnvDIK E Γ`), any single-constructor `Prop` recursor
    elimination with `w.fields = List.replicate w.fields.length botClosedExpr` at any `x` without
    a constructor spine in `ApproxDIK E ρ` is `SemEqDIK E ρ`-equal to `iotaRhsOfS w`! -/
theorem semEqDIK_k_botClosedExpr_of_envWfT {E : ResolvedEnv} {ρ : EnvI}
    (w : IotaWitnessS E)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    (hflds : w.fields = List.replicate w.fields.length botClosedExpr)
    (x : Expr Nat)
    (hnoCtor : ∀ args, ¬ ApproxDIK E ρ x (.spine w.ctorRef args)) :
    SemEqDIK E ρ
      (recCall (.const w.recRef w.ls) w.preMajor x)
      (iotaRhsOfS w) :=
  semEqDIK_k_botFields w hk
    (fun f hf u hu => by
      rw [hflds] at hf
      rw [List.eq_of_mem_replicate hf] at hu
      exact approxDIK_botClosedExpr_inv hu)
    hnoCtor

/-! ### Structural `BotPiCpt` & `ProbeCpt` Exclusions in `ApproxDIK` and Reverse Adequacy -/

/-- Every `BotPiCpt` approximation of `.lam A b` in `ApproxDIK E ρ` is `.bot`. -/
theorem approxDIK_lam_botPiCpt_eq_bot {ρ : EnvI} {A b : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (h : ApproxDIK E ρ (.lam A b) c) : c = .bot := by
  rcases approxDIK_lam_inv h with rfl | ⟨f, rfl, _⟩
  · rfl
  · exact (not_botPiCpt_lam f hc).elim

/-- Every `BotPiCpt` approximation of a `RigidConst E r` in `ApproxDIK E ρ` is `.bot`. -/
theorem approxDIK_rigidConst_botPiCpt_eq_bot {ρ : EnvI} {r : Nat} {ls : List Level} {c : CptI}
    (hrig : RigidConst E r) (hc : BotPiCpt c) (h : ApproxDIK E ρ (.const r ls) c) : c = .bot := by
  rcases approxDIK_rigid_const_inv hrig h with rfl | rfl
  · rfl
  · exact (not_botPiCpt_spine r [] hc).elim

/-- Every `BotPiCpt` approximation of a recursor constant (`m.mclass = .recursorM`) in
    `ApproxDIK E ρ` is `.bot` (covering both `.recursor` and `.recursorK`!). -/
theorem approxDIK_recursor_botPiCpt_eq_bot {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {c : CptI}
    (hrec : E.members r = some m) (hrecK : m.mclass = .recursorM)
    (hc : BotPiCpt c) (h : ApproxDIK E ρ (.const r ls) c) : c = .bot := by
  rcases approxDIK_recursor_const_inv hrec hrecK h with
    rfl | ⟨w, us_pre, us_fields, c₀, _, _, _, _, rfl⟩ |
    ⟨w, us_pre, u_maj, c₀, _, _, _, _, _, rfl⟩
  · rfl
  · cases hlist : us_pre ++ [ctorDemand w.ctorRef w.nparams us_fields] with
    | nil =>
        have hlen := congrArg List.length hlist
        simp at hlen
    | cons u us =>
        rw [hlist] at hc
        exact (not_botPiCpt_curryStep u us c₀ hc).elim
  · cases hlist : us_pre ++ [u_maj] with
    | nil =>
        have hlen := congrArg List.length hlist
        simp at hlen
    | cons u us =>
        rw [hlist] at hc
        exact (not_botPiCpt_curryStep u us c₀ hc).elim

/-- Every `BotPiCpt` approximation of any body-less constant (`m.body = none`) in `ApproxDIK E ρ`
    is `.bot`. -/
theorem approxDIK_const_body_none_botPiCpt_eq_bot {ρ : EnvI} {r : Nat} {ls : List Level}
    {m : CheckedMember} {c : CptI}
    (hm : E.members r = some m) (hb : m.body = none)
    (hc : BotPiCpt c) (h : ApproxDIK E ρ (.const r ls) c) : c = .bot := by
  by_cases hrec : m.mclass = .recursorM
  · exact approxDIK_recursor_botPiCpt_eq_bot hm hrec hc h
  · exact approxDIK_rigidConst_botPiCpt_eq_bot (rigidConst_of_body_none hm hb hrec) hc h

/-- `.pi A B` never has compact `.sort` in `ApproxDIK E ρ`. -/
theorem not_approxDIK_pi_sort {E : ResolvedEnv} {ρ : EnvI} {A B : Expr Nat}
    (h : ApproxDIK E ρ (.pi A B) .sort) : False := by
  rcases approxDIK_pi_inv h with h0 | ⟨_, _, h0, _, _⟩ <;> cases h0

/-- The probe compacts `ProbeCpt`: `.bot`, `.sort`, and `.pi .bot []` — the exact compact fragment
    queried by `piRow` and `sortRow`. -/
inductive ProbeCpt : CptI → Prop
  | bot : ProbeCpt .bot
  | sort : ProbeCpt .sort
  | piBotNil : ProbeCpt (.pi .bot [])

theorem botPiCpt_of_probeCpt {c : CptI} (h : ProbeCpt c) : BotPiCpt c := by
  cases h with
  | bot => exact .bot
  | sort => exact .sort
  | piBotNil => exact botPiCpt_pi_bot_nil

/-- Any `ProbeCpt` compact approximating `.pi A B` in `ApproxDIK E ρ` is `.bot` or `.pi .bot []`. -/
theorem approxDIK_pi_probe_inv {E : ResolvedEnv} {ρ : EnvI} {A B : Expr Nat} {c : CptI}
    (hc : ProbeCpt c) (h : ApproxDIK E ρ (.pi A B) c) :
    c = .bot ∨ c = .pi .bot [] := by
  cases hc with
  | bot => exact Or.inl rfl
  | sort => exact (not_approxDIK_pi_sort h).elim
  | piBotNil => exact Or.inr rfl

/-- Extracting `LRTypeINPiKCanon E n Γ M M' c` from `LRTermDSubKCore E n Γ M M' A c` on any
    `ProbeCpt c`. -/
theorem lrTypeINPiKCanon_of_lrTermDSubKCore_probe {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c) (h : LRTermDSubKCore E n Γ M M' A c) :
    LRTypeINPiKCanon E n Γ M M' c := by
  cases hc with
  | bot => exact .bot _ _ _
  | sort => exact ((lrTermDSubKCore_sort_iff Γ M M' A).mp h).2
  | piBotNil =>
      rw [lrTermDSubKCore_pi_iff] at h
      rcases h with ⟨_, A₁, B₁, A₂, B₂, _, _, h1, h2, ⟨hΓ₁⟩, ⟨hcA⟩, ⟨hcB⟩, _, _, _, _⟩
      exact .pi h1 h2 hΓ₁ hcA hcB (.bot Γ A₁ A₂) (fun _ hs => (List.not_mem_nil _ hs).elim)

/-- **Soundness-Free Reverse Adequacy on `ProbeCpt` (`approxDIK_of_lrTermDSubKCore_probe`):**
    At every `EnvWfT E`, `LRTermDSubKCore E n Γ M M' A c` at a `ProbeCpt` compact `c` implies
    **both** `ApproxDIK E EnvI.bot M c` and `ApproxDIK E EnvI.bot M' c`! -/
theorem approxDIK_of_lrTermDSubKCore_probe (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c) (h : LRTermDSubKCore E n Γ M M' A c) :
    ApproxDIK E EnvI.bot M c ∧ ApproxDIK E EnvI.bot M' c :=
  approxDIK_of_lrTypeINPiKCanon_botPiCpt hW (botPiCpt_of_probeCpt hc)
    (lrTypeINPiKCanon_of_lrTermDSubKCore_probe hc h)

theorem approxDIK_of_lrTermDSubK_probe_of_not_prop (hW : EnvWfT E)
    {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hnp : ¬ IsPropTyI E n Γ A) (hc : ProbeCpt c) (h : LRTermDSubK E n Γ M M' A c) :
    ApproxDIK E EnvI.bot M c ∧ ApproxDIK E EnvI.bot M' c := by
  rcases h with hP | hcore
  · exact (hnp hP).elim
  · exact approxDIK_of_lrTermDSubKCore_probe hW hc hcore

theorem approxDIK_of_lrTermDSubK_probe_at_sort (hW : EnvWfT E)
    {Γ : LCtx} {M M' : Expr Nat} {w : Level} {c : CptI}
    (hc : ProbeCpt c) (h : LRTermDSubK E n Γ M M' (.sort w) c) :
    ApproxDIK E EnvI.bot M c ∧ ApproxDIK E EnvI.bot M' c :=
  approxDIK_of_lrTermDSubK_probe_of_not_prop hW (not_isPropTyI_sort E n Γ w) hc h

/-! ## §2. Full PER (`lrTermDSubKCore_probe_symm`, `lrTermDSubKCore_probe_trans`), Sort-Index
Irrelevance on `BotPiCpt`, and Full `.lam g` Index Transport for `LRTermDSubKCore` & `LRTermDSubK` -/

/-- On any `BotPiCpt` compact `c`, `LRTermDSubKCore` depends on its type index `A` only through
    `∃ l, WhRedPiKCanon E A (.sort l)`. -/
theorem lrTermDSubKCore_botPiCpt_transport_of_whRed_sort {Γ : LCtx} {M M' A B : Expr Nat}
    {l : Level} (hB : WhRedPiKCanon E B (.sort l)) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermDSubKCore E n Γ M M' A c) :
    LRTermDSubKCore E n Γ M M' B c := by
  cases hc with
  | bot => rw [lrTermDSubKCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKCore_sort_iff] at h ⊢
      exact ⟨⟨l, hB⟩, h.2⟩
  | pi =>
      rw [lrTermDSubKCore_pi_iff] at h ⊢
      exact ⟨⟨l, hB⟩, h.2⟩

/-- Sort-index irrelevance of `LRTermDSubKCore` across all `BotPiCpt` compacts. -/
theorem lrTermDSubKCore_botPiCpt_sort_index_irrel {Γ : LCtx} {M M' : Expr Nat}
    {w w' : Level} {c : CptI} (hc : BotPiCpt c) :
    LRTermDSubKCore E n Γ M M' (.sort w) c ↔ LRTermDSubKCore E n Γ M M' (.sort w') c :=
  ⟨lrTermDSubKCore_botPiCpt_transport_of_whRed_sort (.refl _) hc,
   lrTermDSubKCore_botPiCpt_transport_of_whRed_sort (.refl _) hc⟩

/-- Sort-index irrelevance of `LRTermDSubK` across all `BotPiCpt` compacts. -/
theorem lrTermDSubK_botPiCpt_sort_index_irrel {Γ : LCtx} {M M' : Expr Nat}
    {w w' : Level} {c : CptI} (hc : BotPiCpt c) :
    LRTermDSubK E n Γ M M' (.sort w) c ↔ LRTermDSubK E n Γ M M' (.sort w') c := by
  constructor
  · rintro (hP | hC)
    · exact (not_isPropTyI_sort E n Γ w hP).elim
    · exact Or.inr ((lrTermDSubKCore_botPiCpt_sort_index_irrel hc).mp hC)
  · rintro (hP | hC)
    · exact (not_isPropTyI_sort E n Γ w' hP).elim
    · exact Or.inr ((lrTermDSubKCore_botPiCpt_sort_index_irrel hc).mpr hC)

/-- Index transport of `LRTermDSubKCore` on any `BotPiCpt c` from `LRTypeINPiKCanon E n Γ A B .sort`. -/
theorem lrTermDSubKCore_botPiCpt_transport_of_sort {Γ : LCtx} {M M' A B : Expr Nat}
    (hAB : LRTypeINPiKCanon E n Γ A B .sort) {c : CptI} (hc : BotPiCpt c)
    (h : LRTermDSubKCore E n Γ M M' A c) :
    LRTermDSubKCore E n Γ M M' B c := by
  cases hAB with
  | sort _ hB => exact lrTermDSubKCore_botPiCpt_transport_of_whRed_sort hB hc h

/-- **Unconditional Symmetry of `LRTermDSubKCore` on `ProbeCpt` (`lrTermDSubKCore_probe_symm`):**
    Requires only `EnvWfT E` (with **zero** `TypeSoundness` or `SortRow` hypotheses). -/
theorem lrTermDSubKCore_probe_symm (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c) (h : LRTermDSubKCore E n Γ M M' A c) :
    LRTermDSubKCore E n Γ M' M A c := by
  cases hc with
  | bot => rw [lrTermDSubKCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKCore_sort_iff] at h ⊢
      exact ⟨h.1, lrTypeINPiKCanon_symm hW h.2⟩
  | piBotNil =>
      rw [lrTermDSubKCore_pi_iff] at h ⊢
      rcases h with ⟨hl, A₁, B₁, A₂, B₂, u₁, w₁, h1, h2, ⟨hΓ₁⟩, ⟨hcA⟩, ⟨hcB⟩, ⟨hA₁⟩, ⟨hB₁⟩, _, _⟩
      have hΓ : CtxWfT E n Γ := by
        cases hΓ₁ with
        | assumption _ _ _ hΓ₀ _ => exact hΓ₀
      obtain ⟨u₂, hA₂⟩ := tyConvT_endTyped hW hΓ hcA hA₁
      obtain ⟨hΓ₂, _, _, w₂, hB₂⟩ := codomain_transport_of_tyConvT hW hΓ hA₂ hcA hB₁ hcB
      exact ⟨hl, A₂, B₂, A₁, B₁, u₂, w₂, h2, h1, hΓ₂, ⟨hcA.symmT⟩,
        ⟨tyConvT_assump_dom hW hΓ hcA.symmT hcB.symmT⟩, ⟨hA₂⟩, hB₂,
        by rw [lrTermDSubKCore_bot_iff]; trivial,
        fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- **Unconditional Symmetry of `LRTermDSubK` on `ProbeCpt` (`lrTermDSubK_probe_symm`):** -/
theorem lrTermDSubK_probe_symm (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c) (h : LRTermDSubK E n Γ M M' A c) :
    LRTermDSubK E n Γ M' M A c := by
  rcases h with hP | hC
  · exact Or.inl hP
  · exact Or.inr (lrTermDSubKCore_probe_symm hW hc hC)

/-- **Unconditional Transitivity of `LRTermDSubKCore` on `ProbeCpt` (`lrTermDSubKCore_probe_trans`):**
    Requires only `EnvWfT E` (using `whRedPiKCanon_pi_unique_of_envWfT` and
    `lrTypeINPiKCanon_trans_of_envWfT` with **zero** `TypeSoundness` or `LRTermIndexTransport`). -/
theorem lrTermDSubKCore_probe_trans (hW : EnvWfT E) {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c)
    (h₁₂ : LRTermDSubKCore E n Γ M₁ M₂ A c)
    (h₂₃ : LRTermDSubKCore E n Γ M₂ M₃ A c) :
    LRTermDSubKCore E n Γ M₁ M₃ A c := by
  cases hc with
  | bot => rw [lrTermDSubKCore_bot_iff]; trivial
  | sort =>
      rw [lrTermDSubKCore_sort_iff] at h₁₂ h₂₃ ⊢
      exact ⟨h₁₂.1, lrTypeINPiKCanon_trans_of_envWfT hW h₁₂.2 h₂₃.2⟩
  | piBotNil =>
      rw [lrTermDSubKCore_pi_iff] at h₁₂ h₂₃ ⊢
      rcases h₁₂ with ⟨hl, A₁, B₁, A₂, B₂, u₁, w₁, hM₁, hM₂, ⟨hΓ₁⟩, ⟨hcA₁₂⟩, ⟨hcB₁₂⟩, ⟨hA₁⟩, ⟨hB₁⟩, _, _⟩
      rcases h₂₃ with ⟨_, A₂', B₂', A₃, B₃, _, _, hM₂', hM₃, _, ⟨hcA₂₃⟩, ⟨hcB₂₃⟩, _, _, _, _⟩
      obtain ⟨eA, eB⟩ := whRedPiKCanon_pi_unique_of_envWfT hW hM₂ hM₂'
      subst eA; subst eB
      have hΓ : CtxWfT E n Γ := by
        cases hΓ₁ with
        | assumption _ _ _ hΓ₀ _ => exact hΓ₀
      exact ⟨hl, A₁, B₁, A₃, B₃, u₁, w₁, hM₁, hM₃, ⟨hΓ₁⟩,
        ⟨.trans _ _ _ _ hcA₁₂ hcA₂₃⟩,
        ⟨.trans _ _ _ _ hcB₁₂ (tyConvT_assump_dom hW hΓ hcA₁₂ hcB₂₃)⟩,
        ⟨hA₁⟩, ⟨hB₁⟩,
        by rw [lrTermDSubKCore_bot_iff]; trivial,
        fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- **Unconditional Transitivity of `LRTermDSubK` on `ProbeCpt` (`lrTermDSubK_probe_trans`):** -/
theorem lrTermDSubK_probe_trans (hW : EnvWfT E) {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat} {c : CptI}
    (hc : ProbeCpt c)
    (h₁₂ : LRTermDSubK E n Γ M₁ M₂ A c)
    (h₂₃ : LRTermDSubK E n Γ M₂ M₃ A c) :
    LRTermDSubK E n Γ M₁ M₃ A c := by
  rcases h₁₂ with hP | hC₁₂
  · exact Or.inl hP
  · rcases h₂₃ with hP | hC₂₃
    · exact Or.inl hP
    · exact Or.inr (lrTermDSubKCore_probe_trans hW hc hC₁₂ hC₂₃)

/-- **Full Index Transport for `LRTermDSubKCore` Across All Compacts `c : CptI` (Including `.lam g`):**
    Transports `LRTermDSubKCore E n Γ M M' A c` to `LRTermDSubKCore E n Γ M M' A' c` along any
    `TyConvT E n Γ A A'` in a let-free context `LetFreeCtx Γ` using only `EnvWfT E`,
    `FundamentalLRINBotDIKCanon_letFree E n`, and `PropTyTransport E n`. -/
theorem lrTermDSubKCore_transport (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hlf : LetFreeCtx Γ)
    {A A' : Expr Nat} {u : Level}
    (_ : HasTyT E n Γ A (.sort u)) (hAA' : TyConvT E n Γ A A') {M M' : Expr Nat} :
    (c : CptI) → LRTermDSubKCore E n Γ M M' A c → LRTermDSubKCore E n Γ M M' A' c
  | .bot, _ => by rw [lrTermDSubKCore_bot_iff]; trivial
  | .sort, h => by
      rw [lrTermDSubKCore_sort_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hBot hΓ hlf hAA' .sort .sort (approxDIK_sort_of_whRedPiKCanon hW hl)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .pi a f, h => by
      rw [lrTermDSubKCore_pi_iff] at h ⊢
      obtain ⟨⟨l, hl⟩, h2⟩ := h
      have hs := hBot hΓ hlf hAA' .sort .sort (approxDIK_sort_of_whRedPiKCanon hW hl)
      cases hs with
      | sort _ hl' => exact ⟨⟨_, hl'⟩, h2⟩
  | .spine r args, h => by
      rw [lrTermDSubKCore_spine_iff] at h ⊢
      rcases h with ⟨⟨l, hl⟩, h2⟩ | ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2, ⟨hc⟩, hl1, hl2⟩
      · have hs := hBot hΓ hlf hAA' .sort .sort (approxDIK_sort_of_whRedPiKCanon hW hl)
        cases hs with
        | sort _ hl' => exact Or.inl ⟨⟨_, hl'⟩, h2⟩
      · exact Or.inr ⟨ls₁, ls₂, args₁, args₂, h1, h2, n1, n2,
          ⟨convT_of_tyConv hc hAA'⟩, hl1, hl2⟩
  | .lam g, h => by
      rw [lrTermDSubKCore_lam_iff] at h ⊢
      obtain ⟨A₁, B₁, w, hAred, ⟨cΓ₁⟩, ⟨cB₁⟩, happ⟩ := h
      have hAc : ApproxDIK E EnvI.bot A (.pi .bot []) :=
        approxDIK_whRedPiKCanon_back hW hAred (approxDIK_pi_bot_nil E EnvI.bot A₁ B₁)
      have hpi : LRTypeINPiKCanon E n Γ A A' (.pi .bot []) :=
        hBot hΓ hlf hAA' (.pi .bot []) botPiCpt_pi_bot_nil hAc
      cases hpi with
      | @pi _ _ _ A₁' B₁' A₂ B₂ _ _ h1 h2 _ hdom hcod _ _ =>
          obtain ⟨eA, eB⟩ := whRedPiKCanon_pi_unique_of_envWfT hW hAred h1
          subst eA; subst eB
          have hA₁ : ∃ u₁, Nonempty (HasTyT E n Γ A₁ (.sort u₁)) := by
            cases cΓ₁ with
            | assumption _ _ u₁ _ hA₁ => exact ⟨u₁, ⟨hA₁⟩⟩
          obtain ⟨u₁, ⟨hA₁⟩⟩ := hA₁
          obtain ⟨u₂, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          obtain ⟨hΓ₂, _, _, w₂, hB₂⟩ := codomain_transport_of_tyConvT hW hΓ hA₂ hdom cB₁ hcod
          have hdom_symm : TyConvT E n Γ A₂ A₁ := hdom.symmT
          refine ⟨A₂, B₂, w₂, h2, hΓ₂, hB₂, fun s hs N N' hN₂ hN'₂ hconv₂ hrel₂ => ?_⟩
          have hN₁ : HasTyT E n Γ N A₁ := hasTyT_of_tyConv hN₂ hdom_symm
          have hN'₁ : HasTyT E n Γ N' A₁ := hasTyT_of_tyConv hN'₂ hdom_symm
          have hconv₁ : ConvT E n Γ N N' A₁ := convT_of_tyConv hconv₂ hdom_symm
          have hrel₁ : ∀ u₀ ∈ s.1, IsPropTyI E n Γ A₁ ∨ LRTermDSubKCore E n Γ N N' A₁ u₀ := by
            intro u₀ hu₀
            rcases hrel₂ u₀ hu₀ with hP₂ | hcore₂
            · exact Or.inl (hProp hΓ hA₂ hdom_symm hP₂)
            · exact Or.inr (lrTermDSubKCore_transport hW hBot hProp hΓ hlf hA₂ hdom_symm u₀ hcore₂)
          have hB₁N : HasTyT E n Γ (instantiate0 N B₁) (.sort w) :=
            hasTyT_subst0_of_envWfT hW cB₁ hN₁
          have hB₁B₂N : TyConvT E n Γ (instantiate0 N B₁) (instantiate0 N B₂) :=
            tyConvT_subst0_of_envWfT hW hN₁ hcod
          rcases happ s hs N N' hN₁ hN'₁ hconv₁ hrel₁ with hP | hout₁
          · exact Or.inl (hProp hΓ hB₁N hB₁B₂N hP)
          · exact Or.inr (lrTermDSubKCore_transport hW hBot hProp hΓ hlf hB₁N hB₁B₂N s.2 hout₁)
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

/-- Full index transport for `LRTermDSubK` across **all** compacts `c : CptI` (including `.lam g`). -/
theorem lrTermDSubK_transport (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hlf : LetFreeCtx Γ)
    {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hAA' : TyConvT E n Γ A A') {M M' : Expr Nat}
    (c : CptI) (h : LRTermDSubK E n Γ M M' A c) :
    LRTermDSubK E n Γ M M' A' c := by
  rcases h with hP | hcore
  · exact Or.inl (hProp hΓ hA hAA' hP)
  · exact Or.inr (lrTermDSubKCore_transport hW hBot hProp hΓ hlf hA hAA' c hcore)

/-! ## §3. Constructor-by-Constructor `HasTyT` / `ConvT` Clauses for `LRTermDSubK` on `ProbeCpt`,
Bidirectional `LRTermDSubKBi`, and 27-Constructor Reduction of `FundamentalTermDSubKProbe_letFree` -/

/-- `HasTyT.sort` diagonal case for `LRTermDSubK` (unconditional across all compacts). -/
theorem fundTermDSubK_sort {Γ : LCtx} (l : Level) {c : CptI}
    (h : ApproxDIK E EnvI.bot (.sort l) c) :
    LRTermDSubK E n Γ (.sort l) (.sort l) (.sort (.succ l)) c := by
  rcases approxDIK_sort_inv h with rfl | rfl
  · exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)
  · refine Or.inr ?_
    rw [lrTermDSubKCore_sort_iff]
    exact ⟨⟨.succ l, .refl _⟩, .sort (.refl _) (.refl _)⟩

/-- `HasTyT.bvar` diagonal case for `LRTermDSubK` at `EnvI.bot` (unconditional across all compacts). -/
theorem fundTermDSubK_bvar {Γ : LCtx} (i : Nat) (A : Expr Nat) {c : CptI}
    (h : ApproxDIK E EnvI.bot (.bvar i) c) :
    LRTermDSubK E n Γ (.bvar i) (.bvar i) A c := by
  rcases approxDIK_bvar_inv h with rfl | rfl
  · exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)
  · exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- `HasTyT.lam` diagonal case for `LRTermDSubK` on any `BotPiCpt` compact (unconditional). -/
theorem fundTermDSubK_lam {Γ : LCtx} (A body B : Expr Nat) {c : CptI} (hc : BotPiCpt c)
    (h : ApproxDIK E EnvI.bot (.lam A body) c) :
    LRTermDSubK E n Γ (.lam A body) (.lam A body) (.pi A B) c := by
  rw [approxDIK_lam_botPiCpt_eq_bot hc h]
  exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- `HasTyT.const` diagonal case for `LRTermDSubK` on any body-less member (`m.body = none`) on
    any `BotPiCpt` compact (unconditional). -/
theorem fundTermDSubK_const_of_body_none {Γ : LCtx} {r : Nat} (ls : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = none)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDIK E EnvI.bot (.const r ls) c) :
    LRTermDSubK E n Γ (.const r ls) (.const r ls) A c := by
  rw [approxDIK_const_body_none_botPiCpt_eq_bot hm hb hc h]
  exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- `HasTyT.const` diagonal case for `LRTermDSubK` on any `RigidConst E r` on `BotPiCpt`
    (unconditional). -/
theorem fundTermDSubK_rigidConst {Γ : LCtx} {r : Nat} (ls : List Level) (A : Expr Nat)
    (hrig : RigidConst E r) {c : CptI} (hc : BotPiCpt c)
    (h : ApproxDIK E EnvI.bot (.const r ls) c) :
    LRTermDSubK E n Γ (.const r ls) (.const r ls) A c := by
  rw [approxDIK_rigidConst_botPiCpt_eq_bot hrig hc h]
  exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- `HasTyT.const` diagonal case for `LRTermDSubK` on any recursor (`m.mclass = .recursorM`) on
    `BotPiCpt` (unconditional). -/
theorem fundTermDSubK_recursor {Γ : LCtx} {r : Nat} (ls : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDIK E EnvI.bot (.const r ls) c) :
    LRTermDSubK E n Γ (.const r ls) (.const r ls) A c := by
  rw [approxDIK_recursor_botPiCpt_eq_bot hm hrec hc h]
  exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- `HasTyT.const` diagonal case for `LRTermDSubK` on a `DeltaConst E r m b`. -/
theorem fundTermDSubK_deltaConst {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b A : Expr Nat} (hdelta : DeltaConst E r m b)
    (ihb : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot (instantiateLevels ls b) c →
      LRTermDSubK E n Γ (instantiateLevels ls b) (instantiateLevels ls b) A c)
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E EnvI.bot (.const r ls) c) :
    LRTermDSubK E n Γ (.const r ls) (.const r ls) A c := by
  have hstep : WhRedPiKCanon E (.const r ls) (instantiateLevels ls b) :=
    .step (.of_whStep (.delta hdelta.1 hdelta.2.1)) (.refl _)
  exact lrTermDSubK_whRedPiKCanon_expand hstep hstep c
    (ihb c hc (approxDIK_delta_const_inv hdelta h))

/-- **`HasTyT.pi` Diagonal Case on `ProbeCpt` (`fundTermDSubK_pi_probe`, ZERO Induction Hypotheses):**
    On any `ProbeCpt` compact `c`, `LRTermDSubK E n Γ (.pi A B) (.pi A B) (.sort (.imax u v)) c`
    holds **directly from `hΓ`, `hA`, and `hB` with zero semantic induction hypotheses on `A` or `B`**! -/
theorem fundTermDSubK_pi_probe {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E EnvI.bot (.pi A B) c) :
    LRTermDSubK E n Γ (.pi A B) (.pi A B) (.sort (.imax u v)) c := by
  rcases approxDIK_pi_probe_inv hc h with rfl | rfl
  · exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)
  · refine Or.inr ?_
    rw [lrTermDSubKCore_pi_iff]
    exact ⟨⟨.imax u v, .refl _⟩, A, B, A, B, u, v, .refl _, .refl _,
      ⟨.assumption Γ A u hΓ hA⟩, ⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩,
      ⟨hA⟩, ⟨hB⟩, by rw [lrTermDSubKCore_bot_iff]; trivial,
      fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- `HasTyT.lit` diagonal case for `LRTermDSubK` on `ProbeCpt`. -/
theorem fundTermDSubK_lit {Γ : LCtx} (t : Nat) (T : Expr Nat)
    (ih : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot (natExpand t) c →
      LRTermDSubK E n Γ (natExpand t) (natExpand t) T c)
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E EnvI.bot (.lit t) c) :
    LRTermDSubK E n Γ (.lit t) (.lit t) T c := by
  have hstep : WhRedPiKCanon E (.lit t) (natExpand t) := .step (.of_whStep (.lit t)) (.refl _)
  exact lrTermDSubK_whRedPiKCanon_expand hstep hstep c
    (ih c hc ((approxDIK_lit E EnvI.bot t c).mp h))

/-- `HasTyT.letE` diagonal case for `LRTermDSubK` on `ProbeCpt`. -/
theorem fundTermDSubK_letE {Γ : LCtx} (A v b B : Expr Nat)
    (ih : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot (instantiate 0 v b) c →
      LRTermDSubK E n Γ (instantiate 0 v b) (instantiate 0 v b) (instantiate 0 v B) c)
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E EnvI.bot (.letE A v b) c) :
    LRTermDSubK E n Γ (.letE A v b) (.letE A v b) (instantiate 0 v B) c := by
  have hstep : WhRedPiKCanon E (.letE A v b) (instantiate 0 v b) :=
    .step (.of_whStep (.zeta A v b)) (.refl _)
  exact lrTermDSubK_whRedPiKCanon_expand hstep hstep c
    (ih c hc ((approxDIK_zeta E EnvI.bot A v b c).mp h))

/-- `HasTyT.conv` diagonal case for `LRTermDSubK` on `ProbeCpt` (via `lrTermDSubK_transport`). -/
theorem fundTermDSubK_conv_probe (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hlf : LetFreeCtx Γ)
    {e A B : Expr Nat} {u : Level} (hA : HasTyT E n Γ A (.sort u)) (hcAB : TyConvT E n Γ A B)
    (ih : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot e c → LRTermDSubK E n Γ e e A c)
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E EnvI.bot e c) :
    LRTermDSubK E n Γ e e B c :=
  lrTermDSubK_transport hW hBot hProp hΓ hlf hA hcAB c (ih c hc h)

/-! ### `ConvT` Constructor Cases for `LRTermDSubK` on `ProbeCpt` -/

theorem fundConvDSubK_refl {Γ : LCtx} {M A : Expr Nat}
    (hdiag : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot M c → LRTermDSubK E n Γ M M A c) :
    ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot M c → LRTermDSubK E n Γ M M A c :=
  hdiag

/-- **`ConvT.symm` on `ProbeCpt` WITHOUT `TypeSoundness` (`fundConvDSubK_probe_symm`):**
    Applies `lrTermDSubK_probe_symm` directly to `ih c hc hM`. -/
theorem fundConvDSubK_probe_symm (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (ih : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot M c → LRTermDSubK E n Γ M M' A c)
    {c : CptI} (hc : ProbeCpt c) (hM : ApproxDIK E EnvI.bot M c) :
    LRTermDSubK E n Γ M' M A c :=
  lrTermDSubK_probe_symm hW hc (ih c hc hM)

/-- On any `BotPiCpt c` with `c ≠ .bot`, `LRTermDSubKCore E n Γ M M' A c` forces
    `(∃ l, WhRedPiKCanon E A (.sort l))`. -/
theorem lrTermDSubKCore_botPiCpt_forces_sort {Γ : LCtx} {M M' A : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (hne : c ≠ .bot)
    (h : LRTermDSubKCore E n Γ M M' A c) :
    ∃ l, WhRedPiKCanon E A (.sort l) := by
  cases hc with
  | bot => exact (hne rfl).elim
  | sort => exact ((lrTermDSubKCore_sort_iff Γ M M' A).mp h).1
  | pi => exact ((lrTermDSubKCore_pi_iff Γ M M' A _ _).mp h).1

/-- On any `BotPiCpt c` with `c ≠ .bot`, `LRTermDSubKCore E n Γ M M' (.pi A B) c` is impossible
    (since `.pi A B` is `WhNormalPiKCanon` and never reduces to `.sort l`). -/
theorem not_lrTermDSubKCore_at_pi_of_botPiCpt_ne_bot {Γ : LCtx} {M M' A B : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (hne : c ≠ .bot) :
    ¬ LRTermDSubKCore E n Γ M M' (.pi A B) c := by
  intro h
  obtain ⟨l, hred⟩ := lrTermDSubKCore_botPiCpt_forces_sort hc hne h
  exact Expr.noConfusion (whRedPiKCanon_pi_eq hred)

/-- On any `BotPiCpt c`, if `LRTermDSubK E n Γ M M' (.pi A B) c` holds, then `c = .bot ∨
    IsPropTyI E n Γ (.pi A B)`, and therefore `LRTermDSubK E n Γ N N' (.pi A B) c` holds for
    **every** pair of expressions `N, N' : Expr Nat`. -/
theorem lrTermDSubK_at_pi_of_botPiCpt {Γ : LCtx} {M M' A B : Expr Nat} {c : CptI}
    (hc : BotPiCpt c) (h : LRTermDSubK E n Γ M M' (.pi A B) c)
    (N N' : Expr Nat) :
    LRTermDSubK E n Γ N N' (.pi A B) c := by
  cases hc with
  | bot => exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)
  | sort =>
      rcases h with hP | hC
      · exact Or.inl hP
      · exact (not_lrTermDSubKCore_at_pi_of_botPiCpt_ne_bot .sort (fun h0 => by cases h0) hC).elim
  | pi hca hbd hcf =>
      rcases h with hP | hC
      · exact Or.inl hP
      · exact (not_lrTermDSubKCore_at_pi_of_botPiCpt_ne_bot
          (.pi hca hbd hcf) (fun h0 => by cases h0) hC).elim

/-- **`ConvT.trans` on `ProbeCpt` WITHOUT `TypeSoundness` or `LRTermIndexTransport` (`fundConvDSubK_probe_trans`):**
    At every `EnvWfT E`, `approxDIK_of_lrTermDSubKCore_probe` reconstructs
    `ApproxDIK E EnvI.bot M₂ c` from `LRTermDSubKCore E n Γ M₁ M₂ A c` automatically! -/
theorem fundConvDSubK_probe_trans (hW : EnvWfT E)
    {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat}
    (h₁₂ : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot M₁ c → LRTermDSubK E n Γ M₁ M₂ A c)
    (h₂₃ : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot M₂ c → LRTermDSubK E n Γ M₂ M₃ A c)
    {c : CptI} (hc : ProbeCpt c) (h₁ : ApproxDIK E EnvI.bot M₁ c) :
    LRTermDSubK E n Γ M₁ M₃ A c := by
  rcases h₁₂ c hc h₁ with hP | hC₁₂
  · exact Or.inl hP
  · have h₂ : ApproxDIK E EnvI.bot M₂ c :=
      (approxDIK_of_lrTermDSubKCore_probe hW hc hC₁₂).2
    exact lrTermDSubK_probe_trans hW hc (Or.inr hC₁₂) (h₂₃ c hc h₂)

/-- `ConvT.lam` case for `LRTermDSubK` on any `BotPiCpt` compact (unconditional). -/
theorem fundConvDSubK_lam {Γ : LCtx} (A A' b b' B : Expr Nat)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDIK E EnvI.bot (.lam A b) c) :
    LRTermDSubK E n Γ (.lam A b) (.lam A' b') (.pi A B) c := by
  rw [approxDIK_lam_botPiCpt_eq_bot hc h]
  exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- **`ConvT.pi` Case on `ProbeCpt` (`fundConvDSubK_pi_probe`, ZERO Semantic Induction Hypotheses):**
    On any `ProbeCpt` compact `c`, `LRTermDSubK E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort (.imax u v)) c`
    holds **directly from `hΓ₁`, `hdom`, `hcod`, `hA₁`, and `hB₁` with zero semantic induction
    hypotheses on `A₁, A₂` or `B₁, B₂`**! -/
theorem fundConvDSubK_pi_probe {Γ : LCtx} {A₁ A₂ B₁ B₂ : Expr Nat} {u v : Level}
    (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
    (hdom : TyConvT E n Γ A₁ A₂)
    (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
    (hA₁ : HasTyT E n Γ A₁ (.sort u))
    (hB₁ : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort v))
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E EnvI.bot (.pi A₁ B₁) c) :
    LRTermDSubK E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort (.imax u v)) c := by
  rcases approxDIK_pi_probe_inv hc h with rfl | rfl
  · exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)
  · refine Or.inr ?_
    rw [lrTermDSubKCore_pi_iff]
    exact ⟨⟨.imax u v, .refl _⟩, A₁, B₁, A₂, B₂, u, v, .refl _, .refl _,
      ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩, ⟨hA₁⟩, ⟨hB₁⟩,
      by rw [lrTermDSubKCore_bot_iff]; trivial,
      fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-- `ConvT.letE` case for `LRTermDSubK` on `ProbeCpt`. -/
theorem fundConvDSubK_letE {Γ : LCtx} (A A' v v' b b' B : Expr Nat)
    (ih : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot (instantiate 0 v b) c →
      LRTermDSubK E n Γ (instantiate 0 v b) (instantiate 0 v' b') (instantiate 0 v B) c)
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E EnvI.bot (.letE A v b) c) :
    LRTermDSubK E n Γ (.letE A v b) (.letE A' v' b') (instantiate 0 v B) c := by
  have hL : WhRedPiKCanon E (.letE A v b) (instantiate 0 v b) :=
    .step (.of_whStep (.zeta A v b)) (.refl _)
  have hR : WhRedPiKCanon E (.letE A' v' b') (instantiate 0 v' b') :=
    .step (.of_whStep (.zeta A' v' b')) (.refl _)
  exact lrTermDSubK_whRedPiKCanon_expand hL hR c
    (ih c hc ((approxDIK_zeta E EnvI.bot A v b c).mp h))

/-- `ConvT.consts` case for `LRTermDSubK` on any body-less member (`m.body = none`) on `BotPiCpt`
    (unconditional). -/
theorem fundConvDSubK_consts_of_body_none {Γ : LCtx} {r : Nat} (ls ls' : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = none)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDIK E EnvI.bot (.const r ls) c) :
    LRTermDSubK E n Γ (.const r ls) (.const r ls') A c := by
  rw [approxDIK_const_body_none_botPiCpt_eq_bot hm hb hc h]
  exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- `ConvT.consts` case for `LRTermDSubK` on any `RigidConst E r` on `BotPiCpt` (unconditional). -/
theorem fundConvDSubK_rigidConsts {Γ : LCtx} {r : Nat} (ls ls' : List Level) (A : Expr Nat)
    (hrig : RigidConst E r) {c : CptI} (hc : BotPiCpt c)
    (h : ApproxDIK E EnvI.bot (.const r ls) c) :
    LRTermDSubK E n Γ (.const r ls) (.const r ls') A c := by
  rw [approxDIK_rigidConst_botPiCpt_eq_bot hrig hc h]
  exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- `ConvT.consts` case for `LRTermDSubK` on any recursor (`m.mclass = .recursorM`) on `BotPiCpt`
    (unconditional). -/
theorem fundConvDSubK_recursorConsts {Γ : LCtx} {r : Nat} (ls ls' : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
    {c : CptI} (hc : BotPiCpt c) (h : ApproxDIK E EnvI.bot (.const r ls) c) :
    LRTermDSubK E n Γ (.const r ls) (.const r ls') A c := by
  rw [approxDIK_recursor_botPiCpt_eq_bot hm hrec hc h]
  exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- `ConvT.consts` case for `LRTermDSubK` on a `DeltaConst E r m b` on `ProbeCpt`. -/
theorem fundConvDSubK_deltaConsts {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember} {b A : Expr Nat} (hdelta : DeltaConst E r m b)
    (ih : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot (instantiateLevels ls b) c →
      LRTermDSubK E n Γ (instantiateLevels ls b) (instantiateLevels ls' b) A c)
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E EnvI.bot (.const r ls) c) :
    LRTermDSubK E n Γ (.const r ls) (.const r ls') A c := by
  have hL : WhRedPiKCanon E (.const r ls) (instantiateLevels ls b) :=
    .step (.of_whStep (.delta hdelta.1 hdelta.2.1)) (.refl _)
  have hR : WhRedPiKCanon E (.const r ls') (instantiateLevels ls' b) :=
    .step (.of_whStep (.delta hdelta.1 hdelta.2.1)) (.refl _)
  exact lrTermDSubK_whRedPiKCanon_expand hL hR c
    (ih c hc (approxDIK_delta_const_inv hdelta h))

/-- `ConvT.eta` case for `LRTermDSubK` on any `BotPiCpt` compact (unconditional). -/
theorem fundConvDSubK_eta {Γ : LCtx} (f A B : Expr Nat)
    {c : CptI} (hc : BotPiCpt c)
    (h : ApproxDIK E EnvI.bot (.lam A (.app (lift 0 1 f) (.bvar 0))) c) :
    LRTermDSubK E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) c := by
  rw [approxDIK_lam_botPiCpt_eq_bot hc h]
  exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

/-- `ConvT.tyConv` case for `LRTermDSubK` on `ProbeCpt` (via `lrTermDSubK_transport`). -/
theorem fundConvDSubK_tyConv_probe (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hlf : LetFreeCtx Γ)
    {M M' A B : Expr Nat} {u : Level} (hA : HasTyT E n Γ A (.sort u)) (hcAB : TyConvT E n Γ A B)
    (ih : ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot M c → LRTermDSubK E n Γ M M' A c)
    {c : CptI} (hc : ProbeCpt c) (h : ApproxDIK E EnvI.bot M c) :
    LRTermDSubK E n Γ M M' B c :=
  lrTermDSubK_transport hW hBot hProp hΓ hlf hA hcAB c (ih c hc h)

/-! ### Bidirectional Probe-Compact Term Logical Relation `LRTermDSubKBi` -/

/-- Bidirectional `ProbeCpt`-restricted term logical relation over `ApproxDIK E EnvI.bot` and
    `LRTermDSubK`: for every `ProbeCpt c` approximating either `M` or `M'`,
    `LRTermDSubK E n Γ M M' A c` holds. -/
def LRTermDSubKBi (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) : Prop :=
  ∀ c, ProbeCpt c →
    (ApproxDIK E EnvI.bot M c ∨ ApproxDIK E EnvI.bot M' c) →
    LRTermDSubK E n Γ M M' A c

/-- **Unconditional Symmetry of `LRTermDSubKBi` at `EnvWfT E`** (with **zero** `TypeSoundness`
    or `LRTermIndexTransport`). -/
theorem lrTermDSubKBi_symm (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (h : LRTermDSubKBi E n Γ M M' A) :
    LRTermDSubKBi E n Γ M' M A :=
  fun c hc hor => lrTermDSubK_probe_symm hW hc (h c hc hor.symm)

/-- **Unconditional Transitivity of `LRTermDSubKBi` at `EnvWfT E`** (with **zero** `TypeSoundness`
    or `LRTermIndexTransport`): `approxDIK_of_lrTermDSubKCore_probe` reconstructs
    `ApproxDIK E EnvI.bot M₂ c` on the middle term whenever `¬ IsPropTyI E n Γ A`. -/
theorem lrTermDSubKBi_trans (hW : EnvWfT E) {Γ : LCtx} {M₁ M₂ M₃ A : Expr Nat}
    (h₁₂ : LRTermDSubKBi E n Γ M₁ M₂ A)
    (h₂₃ : LRTermDSubKBi E n Γ M₂ M₃ A) :
    LRTermDSubKBi E n Γ M₁ M₃ A := by
  intro c hc hor
  rcases hor with h₁ | h₃
  · rcases h₁₂ c hc (Or.inl h₁) with hP | hC₁₂
    · exact Or.inl hP
    · have h₂ : ApproxDIK E EnvI.bot M₂ c :=
        (approxDIK_of_lrTermDSubKCore_probe hW hc hC₁₂).2
      exact lrTermDSubK_probe_trans hW hc (Or.inr hC₁₂) (h₂₃ c hc (Or.inl h₂))
  · rcases h₂₃ c hc (Or.inr h₃) with hP | hC₂₃
    · exact Or.inl hP
    · have h₂ : ApproxDIK E EnvI.bot M₂ c :=
        (approxDIK_of_lrTermDSubKCore_probe hW hc hC₂₃).1
      exact lrTermDSubK_probe_trans hW hc (h₁₂ c hc (Or.inr h₂)) (Or.inr hC₂₃)

theorem lrTermDSubKBi_whRedPiKCanon_expand (hW : EnvWfT E) {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : WhRedPiKCanon E M X) (hX' : WhRedPiKCanon E M' X')
    (h : LRTermDSubKBi E n Γ X X' A) :
    LRTermDSubKBi E n Γ M M' A := by
  intro c hc hor
  have hor' : ApproxDIK E EnvI.bot X c ∨ ApproxDIK E EnvI.bot X' c :=
    hor.elim (fun hM => Or.inl ((semEqDIK_whRedPiKCanon hW hX c).mp hM))
             (fun hM' => Or.inr ((semEqDIK_whRedPiKCanon hW hX' c).mp hM'))
  exact lrTermDSubK_whRedPiKCanon_expand hX hX' c (h c hc hor')

theorem lrTermDSubKBi_of_whStepPiKCanon (hW : EnvWfT E) {Γ : LCtx} {M M' A : Expr Nat}
    (hs : WhStepPiKCanon E M M') (hdiag : LRTermDSubKBi E n Γ M' M' A) :
    LRTermDSubKBi E n Γ M M' A :=
  lrTermDSubKBi_whRedPiKCanon_expand hW (.step hs (.refl _)) (.refl _) hdiag

theorem lrTermDSubKBi_sorts (Γ : LCtx) (l₁ l₂ : Level) :
    LRTermDSubKBi E n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) := by
  intro c hc hor
  rcases hor with h | h
  · exact fundConvDSubK_sorts Γ l₁ l₂ c (botPiCpt_of_probeCpt hc) h
  · rcases approxDIK_sort_inv h with rfl | rfl
    · exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)
    · refine Or.inr ?_
      rw [lrTermDSubKCore_sort_iff]
      exact ⟨⟨.succ l₁, .refl _⟩, .sort (.refl _) (.refl _)⟩

theorem lrTermDSubKBi_sort_diag (Γ : LCtx) (l : Level) :
    LRTermDSubKBi E n Γ (.sort l) (.sort l) (.sort (.succ l)) :=
  lrTermDSubKBi_sorts Γ l l

theorem lrTermDSubKBi_bvar_diag (Γ : LCtx) (i : Nat) (A : Expr Nat) :
    LRTermDSubKBi E n Γ (.bvar i) (.bvar i) A :=
  fun _ _ hor => fundTermDSubK_bvar i A (hor.elim id id)

theorem lrTermDSubKBi_lam (Γ : LCtx) (A A' b b' B : Expr Nat) :
    LRTermDSubKBi E n Γ (.lam A b) (.lam A' b') (.pi A B) := by
  intro c hc hor
  rcases hor with h | h
  · exact fundConvDSubK_lam A A' b b' B (botPiCpt_of_probeCpt hc) h
  · rw [approxDIK_lam_botPiCpt_eq_bot (botPiCpt_of_probeCpt hc) h]
    exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

theorem lrTermDSubKBi_consts_of_body_none {Γ : LCtx} {r : Nat} (ls ls' : List Level)
    {m : CheckedMember} (A : Expr Nat)
    (hm : E.members r = some m) (hb : m.body = none) :
    LRTermDSubKBi E n Γ (.const r ls) (.const r ls') A := by
  intro c hc hor
  rcases hor with h | h
  · exact fundConvDSubK_consts_of_body_none ls ls' A hm hb (botPiCpt_of_probeCpt hc) h
  · rw [approxDIK_const_body_none_botPiCpt_eq_bot hm hb (botPiCpt_of_probeCpt hc) h]
    exact Or.inr (by rw [lrTermDSubKCore_bot_iff]; trivial)

theorem lrTermDSubKBi_deltaConsts (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    {m : CheckedMember} {b A : Expr Nat} (hdelta : DeltaConst E r m b)
    (ih : LRTermDSubKBi E n Γ (instantiateLevels ls b) (instantiateLevels ls' b) A) :
    LRTermDSubKBi E n Γ (.const r ls) (.const r ls') A :=
  lrTermDSubKBi_whRedPiKCanon_expand hW
    (.step (.of_whStep (.delta hdelta.1 hdelta.2.1)) (.refl _))
    (.step (.of_whStep (.delta hdelta.1 hdelta.2.1)) (.refl _)) ih

/-- **`ConvT.pi` in `LRTermDSubKBi` (`lrTermDSubKBi_pi`, ZERO Semantic Induction Hypotheses):** -/
theorem lrTermDSubKBi_pi {Γ : LCtx} {A₁ A₂ B₁ B₂ : Expr Nat} {u v : Level}
    (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
    (hdom : TyConvT E n Γ A₁ A₂)
    (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
    (hA₁ : HasTyT E n Γ A₁ (.sort u))
    (hB₁ : HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort v)) :
    LRTermDSubKBi E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort (.imax u v)) := by
  intro c hc hor
  have hpi : ApproxDIK E EnvI.bot (.pi A₁ B₁) c := by
    rcases hor with h₁ | h₂
    · exact h₁
    · rcases approxDIK_pi_probe_inv hc h₂ with rfl | rfl
      · exact .bot _ _
      · exact approxDIK_pi_bot_nil E EnvI.bot A₁ B₁
  exact fundConvDSubK_pi_probe hΓ₁ hdom hcod hA₁ hB₁ hc hpi

theorem lrTermDSubKBi_pi_diag {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)) :
    LRTermDSubKBi E n Γ (.pi A B) (.pi A B) (.sort (.imax u v)) :=
  lrTermDSubKBi_pi (.assumption Γ A u hΓ hA) (.refl Γ A) (.refl (.assumption A :: Γ) B) hA hB

/-- **`ConvT.eta` in `LRTermDSubKBi` (`lrTermDSubKBi_eta`):**
    Holds from `f`'s diagonal `LRTermDSubKBi E n Γ f f (.pi A B)` alone (using
    `lrTermDSubK_at_pi_of_botPiCpt` when the right compact `ApproxDIK E EnvI.bot f c` is given). -/
theorem lrTermDSubKBi_eta {Γ : LCtx} {f A B : Expr Nat}
    (hdiag : LRTermDSubKBi E n Γ f f (.pi A B)) :
    LRTermDSubKBi E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) := by
  intro c hc hor
  rcases hor with hlam | hf
  · exact fundConvDSubK_eta f A B (botPiCpt_of_probeCpt hc) hlam
  · exact lrTermDSubK_at_pi_of_botPiCpt (botPiCpt_of_probeCpt hc)
      (hdiag c hc (Or.inl hf)) (.lam A (.app (lift 0 1 f) (.bvar 0))) f

theorem lrTermDSubKBi_irr_of_sortRow
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    {Γ : LCtx} {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero)) :
    LRTermDSubKBi E n Γ p q P :=
  fun c _ _ => fundConvDSubK_irr_of_sortRow hSort hP c

theorem lrTermDSubKBi_tyConv (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hlf : LetFreeCtx Γ)
    {M M' A B : Expr Nat} {u : Level} (hA : HasTyT E n Γ A (.sort u)) (hcAB : TyConvT E n Γ A B)
    (ih : LRTermDSubKBi E n Γ M M' A) :
    LRTermDSubKBi E n Γ M M' B :=
  fun c hc hor => lrTermDSubK_transport hW hBot hProp hΓ hlf hA hcAB c (ih c hc hor)

/-- Probe-compact (`ProbeCpt`) fundamental supply for `LRTermDSubK` on `LetFreeCtx Γ`. -/
def FundamentalTermDSubKProbe_letFree (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
      ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot M c → LRTermDSubK E n Γ M M A c) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {M M' A : Expr Nat},
      HasTyT E n Γ M A → HasTyT E n Γ M' A → ConvT E n Γ M M' A →
      ∀ c, ProbeCpt c → ApproxDIK E EnvI.bot M c → LRTermDSubK E n Γ M M' A c)

/-- Bidirectional `LRTermDSubKBi` fundamental supply on `LetFreeCtx Γ`. -/
def FundamentalTermDSubKBiProbe_letFree (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {M A : Expr Nat}, HasTyT E n Γ M A → LRTermDSubKBi E n Γ M M A) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {M M' A : Expr Nat},
      HasTyT E n Γ M A → HasTyT E n Γ M' A → ConvT E n Γ M M' A →
      LRTermDSubKBi E n Γ M M' A)

theorem fundamentalTermDSubKProbe_letFree_of_biProbe_letFree
    (hF : FundamentalTermDSubKBiProbe_letFree E n) :
    FundamentalTermDSubKProbe_letFree E n :=
  ⟨fun {_} hΓ hlf {_ _} hM c hc hMc => hF.1 hΓ hlf hM c hc (Or.inl hMc),
   fun {_} hΓ hlf {_ _ _} hM hM' hconv c hc hMc => hF.2 hΓ hlf hM hM' hconv c hc (Or.inl hMc)⟩

theorem fundamentalTermDSubKProbe_letFree_of_botDIK_letFree
    (hF : FundamentalTermDSubKBotDIK_letFree E n) :
    FundamentalTermDSubKProbe_letFree E n :=
  ⟨fun {_} hΓ hlf {_ _} hM c hc hMc => hF.1 hΓ hlf hM c (botPiCpt_of_probeCpt hc) hMc,
   fun {_} hΓ hlf {_ _ _} hM hM' hconv c hc hMc =>
     hF.2 hΓ hlf hM hM' hconv c (botPiCpt_of_probeCpt hc) hMc⟩

/-- Extracting let-free `piRow` from `FundamentalTermDSubKProbe_letFree` (requiring only `ProbeCpt.piBotNil`). -/
theorem piRow_letFree_of_fundamentalTermDSubKProbe_letFree (hW : EnvWfT E)
    (hF : FundamentalTermDSubKProbe_letFree E n)
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
          (hF.1 hΓ hlf hX (.pi .bot []) .piBotNil hAc)
    | of X Y v hc =>
        intro _ _ hAc
        exact lrTypeINPiKCanon_pi_bot_nil_of_lrTermDSubK
          (hF.2 hΓ hlf (convEnds hW hΓ hc).1 (convEnds hW hΓ hc).2.1 hc
            (.pi .bot []) .piBotNil hAc)
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

/-- **Full `PiRowField E n` from `FundamentalTermDSubKProbe_letFree`:**
    Combines `piRow_letFree_of_fundamentalTermDSubKProbe_letFree` with the telescope let-expansion
    engine `piRow_of_letFree_piRow` to yield unrestricted `PiRowField E n` on **all** `CtxWfT E n Γ`! -/
theorem piRow_of_fundamentalTermDSubKProbe_letFree (hW : EnvWfT E)
    (hF : FundamentalTermDSubKProbe_letFree E n) : PiRowField E n :=
  fun {_} hΓ {_ _ _ _} h =>
    piRow_of_letFree_piRow hW
      (fun {_} hlf' hΓ' {_ _ _ _} h' =>
        piRow_letFree_of_fundamentalTermDSubKProbe_letFree hW hF hΓ' hlf' h')
      hΓ h

theorem piRow_of_fundamentalTermDSubKBiProbe_letFree (hW : EnvWfT E)
    (hF : FundamentalTermDSubKBiProbe_letFree E n) : PiRowField E n :=
  piRow_of_fundamentalTermDSubKProbe_letFree hW
    (fundamentalTermDSubKProbe_letFree_of_biProbe_letFree hF)

/-- The application / let-instantiation / delta-body obligation `AppLetProbeSupplyDSubKBi E n`:
    the exact remaining obligations after all other `HasTyT` and `ConvT` constructors (`sort`,
    `bvar`, `lam`, `pi`, `const (body = none)`, `lit`, `conv`, `refl`, `symm`, `trans`, `beta`,
    `zeta`, `zetaLocal`, `delta`, `iota`, `sorts`, `consts (body = none)`, `eta`, `irr`, `tyConv`)
    are closed on `ProbeCpt` by the theorems of §1–§3. -/
def AppLetProbeSupplyDSubKBi (E : ResolvedEnv) (n : Nat) : Prop :=
  -- 1. HasTyT.app
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {f a A B : Expr Nat}, HasTyT E n Γ f (.pi A B) → HasTyT E n Γ a A →
      LRTermDSubKBi E n Γ f f (.pi A B) → LRTermDSubKBi E n Γ a a A →
      LRTermDSubKBi E n Γ (.app f a) (.app f a) (instantiate 0 a B)) ∧
  -- 2. ConvT.app
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {f₁ f₂ a₁ a₂ A B : Expr Nat},
      ConvT E n Γ f₁ f₂ (.pi A B) → ConvT E n Γ a₁ a₂ A →
      LRTermDSubKBi E n Γ f₁ f₂ (.pi A B) → LRTermDSubKBi E n Γ a₁ a₂ A →
      LRTermDSubKBi E n Γ (.app f₁ a₁) (.app f₂ a₂) (instantiate 0 a₁ B)) ∧
  -- 3. HasTyT.letE / ConvT.letE / ConvT.beta / ConvT.zeta contractum instantiation
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {A₁ v₁ v₂ b₁ b₂ B : Expr Nat},
      HasTyT E n Γ v₁ A₁ → HasTyT E n Γ v₂ A₁ →
      LRTermDSubKBi E n Γ v₁ v₂ A₁ →
      LRTermDSubKBi E n Γ (instantiate 0 v₁ b₁) (instantiate 0 v₂ b₂) (instantiate 0 v₁ B)) ∧
  -- 4. Delta body diagonal & level-instantiation
  (∀ {Γ : LCtx}, CtxWfT E n Γ → LetFreeCtx Γ →
    ∀ {r : Nat} {ls₁ ls₂ : List Level} {m : CheckedMember} {b : Expr Nat},
      DeltaConst E r m b →
      LRTermDSubKBi E n Γ (instantiateLevels ls₁ b) (instantiateLevels ls₂ b)
        (instantiateLevels ls₁ m.mtype))

private theorem fundBiProbe_hasTyT (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    {Γ : LCtx} → {M A : Expr Nat} → HasTyT E n Γ M A →
      CtxWfT E n Γ → LetFreeCtx Γ → LRTermDSubKBi E n Γ M M A
  | Γ, _, _, .sort _ l, _, _ =>
      lrTermDSubKBi_sort_diag Γ l
  | Γ, _, _, .bvar _ i A _, _, _ =>
      lrTermDSubKBi_bvar_diag Γ i A
  | Γ, _, _, .const _ r ls m hm _ _, hΓ, hlf => by
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
        (fundBiProbe_hasTyT hW hBot hProp hSup hf hΓ hlf)
        (fundBiProbe_hasTyT hW hBot hProp hSup ha hΓ hlf)
  | _, _, _, .letE _ A _ v B b _ hv _, hΓ, hlf =>
      have hstep : WhRedPiKCanon E (.letE A v b) (instantiate 0 v b) :=
        .step (.of_whStep (.zeta A v b)) (.refl _)
      lrTermDSubKBi_whRedPiKCanon_expand hW hstep hstep
        (hSup.2.2.1 hΓ hlf hv hv (fundBiProbe_hasTyT hW hBot hProp hSup hv hΓ hlf))
  | _, _, _, .lit _ t _ hexp, hΓ, hlf =>
      have hstep : WhRedPiKCanon E (.lit t) (natExpand t) :=
        .step (.of_whStep (.lit t)) (.refl _)
      lrTermDSubKBi_whRedPiKCanon_expand hW hstep hstep
        (fundBiProbe_hasTyT hW hBot hProp hSup hexp hΓ hlf)
  | Γ, _, _, .conv _ _ A B u he hc, hΓ, hlf =>
      lrTermDSubKBi_tyConv hW hBot hProp hΓ hlf (convEnds hW hΓ hc).1 (.of Γ A B u hc)
        (fundBiProbe_hasTyT hW hBot hProp hSup he hΓ hlf)

private theorem fundBiProbe_convT (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    {Γ : LCtx} → {M M' A : Expr Nat} → ConvT E n Γ M M' A →
      CtxWfT E n Γ → LetFreeCtx Γ → LRTermDSubKBi E n Γ M M' A
  | _, _, _, _, .refl _ _ _ he, hΓ, hlf =>
      fundBiProbe_hasTyT hW hBot hProp hSup he hΓ hlf
  | _, _, _, _, .symm _ _ _ _ h, hΓ, hlf =>
      lrTermDSubKBi_symm hW (fundBiProbe_convT hW hBot hProp hSort hSup h hΓ hlf)
  | _, _, _, _, .trans _ _ _ _ _ h₁ h₂, hΓ, hlf =>
      lrTermDSubKBi_trans hW
        (fundBiProbe_convT hW hBot hProp hSort hSup h₁ hΓ hlf)
        (fundBiProbe_convT hW hBot hProp hSort hSup h₂ hΓ hlf)
  | _, _, _, _, .beta _ A b a _ _ _ _ ha, hΓ, hlf =>
      lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.beta A b a))
        (hSup.2.2.1 hΓ hlf ha ha (fundBiProbe_hasTyT hW hBot hProp hSup ha hΓ hlf))
  | _, _, _, _, .zeta _ A v b _ _ _ hv _, hΓ, hlf =>
      lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.zeta A v b))
        (hSup.2.2.1 hΓ hlf hv hv (fundBiProbe_hasTyT hW hBot hProp hSup hv hΓ hlf))
  | _, _, _, _, .zetaLocal _ i _ _ hval _ _, _, hlf => by
      rw [hlf i] at hval
      exact Option.noConfusion hval
  | _, _, _, _, .delta _ _ _ _ _ hres hbody _ _ _ hb, hΓ, hlf =>
      lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.delta hres hbody))
        (fundBiProbe_hasTyT hW hBot hProp hSup hb hΓ hlf)
  | _, _, _, _, .iota _ _ _ _ hI _ hrhs, hΓ, hlf =>
      lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.iota (derivedIotaU_ofDerivedIota hI)))
        (fundBiProbe_hasTyT hW hBot hProp hSup hrhs hΓ hlf)
  | _, _, _, _, .lit _ t _ _ hlit hexp, hΓ, hlf => by
      cases hlit
      exact lrTermDSubKBi_of_whStepPiKCanon hW (.of_whStep (.lit t))
        (fundBiProbe_hasTyT hW hBot hProp hSup hexp hΓ hlf)
  | _, _, _, _, .app _ _ _ _ _ _ _ hf ha, hΓ, hlf =>
      hSup.2.1 hΓ hlf hf ha
        (fundBiProbe_convT hW hBot hProp hSort hSup hf hΓ hlf)
        (fundBiProbe_convT hW hBot hProp hSort hSup ha hΓ hlf)
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
        (hSup.2.2.1 hΓ hlf hv₁ hv₂ (fundBiProbe_convT hW hBot hProp hSort hSup hcv hΓ hlf))
  | Γ, _, _, _, .sorts _ l₁ l₂ _, _, _ =>
      lrTermDSubKBi_sorts Γ l₁ l₂
  | _, _, _, _, .consts _ r ls₁ ls₂ m hm _ _ _ _, hΓ, hlf => by
      cases hb : m.body with
      | none => exact lrTermDSubKBi_consts_of_body_none ls₁ ls₂ _ hm hb
      | some b =>
          obtain ⟨hdelta, _⟩ := envWfT_member_body_closed hW r m b hm hb
          exact lrTermDSubKBi_deltaConsts hW hdelta (hSup.2.2.2 hΓ hlf hdelta)
  | _, _, _, _, .eta _ _ _ _ hf, hΓ, hlf =>
      lrTermDSubKBi_eta (fundBiProbe_hasTyT hW hBot hProp hSup hf hΓ hlf)
  | _, _, _, _, .irr _ _ _ _ hP _ _, _, _ =>
      lrTermDSubKBi_irr_of_sortRow hSort hP
  | Γ, _, _, _, .tyConv _ _ _ A A' u h hA, hΓ, hlf =>
      lrTermDSubKBi_tyConv hW hBot hProp hΓ hlf (convEnds hW hΓ hA).1 (.of Γ A A' u hA)
        (fundBiProbe_convT hW hBot hProp hSort hSup h hΓ hlf)

/-- **27-Constructor Reduction Theorem (`fundamentalTermDSubKBiProbe_letFree_of_supply`):**
    Closes all other `HasTyT` and `ConvT` constructors (`sort`, `bvar`, `lam`, `pi`,
    `const (body = none)`, `conv`, `refl`, `symm`, `trans`, `beta`, `zeta`, `zetaLocal`, `delta`,
    `iota`, `lit`, `sorts`, `consts`, `eta`, `irr`, `tyConv`) on `ProbeCpt` from
    `AppLetProbeSupplyDSubKBi E n` under `EnvWfT E`, `FundamentalLRINBotDIKCanon_letFree E n`,
    `PropTyTransport E n`, and `SortRow`! -/
theorem fundamentalTermDSubKBiProbe_letFree_of_supply (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    FundamentalTermDSubKBiProbe_letFree E n :=
  ⟨fun {_} hΓ hlf {_ _} hM => fundBiProbe_hasTyT hW hBot hProp hSup hM hΓ hlf,
   fun {_} hΓ hlf {_ _ _} _ _ hconv => fundBiProbe_convT hW hBot hProp hSort hSup hconv hΓ hlf⟩

theorem fundamentalTermDSubKProbe_letFree_of_supply (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    FundamentalTermDSubKProbe_letFree E n :=
  fundamentalTermDSubKProbe_letFree_of_biProbe_letFree
    (fundamentalTermDSubKBiProbe_letFree_of_supply hW hBot hProp hSort hSup)

/-- Direct bridge from `AppLetProbeSupplyDSubKBi E n` to full unrestricted `PiRowField E n`. -/
theorem piRow_of_appLetProbeSupplyDSubKBi (hW : EnvWfT E)
    (hBot : FundamentalLRINBotDIKCanon_letFree E n)
    (hProp : PropTyTransport E n)
    (hSort : ∀ {Δ : LCtx} {l₁ l₂ : Level}, TyConvT E n Δ (.sort l₁) (.sort l₂) → eqN l₁ l₂)
    (hSup : AppLetProbeSupplyDSubKBi E n) :
    PiRowField E n :=
  piRow_of_fundamentalTermDSubKBiProbe_letFree hW
    (fundamentalTermDSubKBiProbe_letFree_of_supply hW hBot hProp hSort hSup)

/-! ## §4. `EnvI.bot` Lift/Substitution Invariance of `ApproxDIK`, Closed-Field Deterministic
K-Readback `WhStepPiKClosed` / `WhRedPiKClosed`, and Unconditional Lift/Substitution Commutation -/

theorem envI_insert_bot_false (k i : Nat) (d : CptI) :
    EnvI.insert EnvI.bot k (EnvI.bot 0) i d ↔ EnvI.bot i d := by
  by_cases hij : i = k
  · subst hij; rw [EnvI.insert_self]; rfl
  · by_cases hlt : i < k
    · rw [EnvI.insert_lt _ hlt]
    · have hgt : k < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (Ne.symm hij)
      rw [EnvI.insert_gt _ hgt]; rfl

/-- **Unconditional `lift k 1` Invariance of `ApproxDIK E EnvI.bot` (`approxDIK_bot_lift_iff`):**
    For **every** environment `E`, cutoff `k : Nat` (including `k = 0`), expression `e : Expr Nat`,
    and compact `c : CptI`, `ApproxDIK E EnvI.bot (lift k 1 e) c ↔ ApproxDIK E EnvI.bot e c`. -/
theorem approxDIK_bot_lift_iff (E : ResolvedEnv) (k : Nat) (e : Expr Nat) (c : CptI) :
    ApproxDIK E EnvI.bot (lift k 1 e) c ↔ ApproxDIK E EnvI.bot e c := by
  constructor
  · intro h
    refine approxDIK_lift_elim e (k := k) (S := EnvI.bot 0) ?_
    exact approxDIK_mono_env (fun i d hd => (envI_insert_bot_false k i d).mpr hd) h
  · intro h
    refine approxDIK_mono_env (fun i d hd => (envI_insert_bot_false k i d).mp hd) ?_
    exact approxDIK_lift_intro h k (EnvI.bot 0)

theorem semEqDIK_bot_lift_iff (E : ResolvedEnv) (k : Nat) (a b : Expr Nat) :
    SemEqDIK E EnvI.bot (lift k 1 a) (lift k 1 b) ↔ SemEqDIK E EnvI.bot a b := by
  constructor
  · intro h c
    exact (approxDIK_bot_lift_iff E k a c).symm.trans
      ((h c).trans (approxDIK_bot_lift_iff E k b c))
  · intro h c
    exact (approxDIK_bot_lift_iff E k a c).trans
      ((h c).trans (approxDIK_bot_lift_iff E k b c).symm)

theorem approxDIK_bot_lift0_iff (E : ResolvedEnv) (j : Nat) (e : Expr Nat) (c : CptI) :
    ApproxDIK E EnvI.bot (lift 0 j e) c ↔ ApproxDIK E EnvI.bot e c := by
  constructor
  · intro h
    refine approxDIK_mono_env (fun _ _ hd => hd) (approxDIK_liftN_elim EnvI.bot j h)
  · intro h
    exact approxDIK_liftN_intro EnvI.bot j (approxDIK_mono_env (fun _ _ hd => hd) h)

/-- **Unconditional Substitution Invariance of `ApproxDIK E EnvI.bot` for `⊥`-Approximated
    Substituents (`approxDIK_bot_subst_lift_iff`):**
    Whenever `ha : ∀ u, ApproxDIK E EnvI.bot a u → u = .bot`, substituting `lift 0 j a` at any
    binder depth `j : Nat` (including `j = 0`, where `lift 0 0 a = a`) preserves all compacts in
    `ApproxDIK E EnvI.bot`! -/
theorem approxDIK_bot_subst_lift_iff {E : ResolvedEnv} {a : Expr Nat}
    (ha : ∀ u, ApproxDIK E EnvI.bot a u → u = .bot)
    (j : Nat) (e : Expr Nat) (c : CptI) :
    ApproxDIK E EnvI.bot (instantiate j (lift 0 j a) e) c ↔ ApproxDIK E EnvI.bot e c := by
  rw [approxDIK_subst_iff]
  constructor
  · refine approxDIK_mono_env_nonbot (fun i d hne hd => ?_)
    by_cases hij : i = j
    · subst hij
      rw [EnvI.insert_self] at hd
      have hd' : ApproxDIK E EnvI.bot a d := approxDIK_mono_env (fun _ _ h => h) hd
      exact (hne (ha d hd')).elim
    · by_cases hlt : i < j
      · rw [EnvI.insert_lt _ hlt] at hd; exact hd
      · have hgt : j < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (Ne.symm hij)
        rw [EnvI.insert_gt _ hgt] at hd; exact hd
  · exact approxDIK_mono_env_nonbot (fun _ _ hne hd => (hne hd).elim)

/-- `j = 0` specialization of `approxDIK_bot_subst_lift_iff`: for any `a` with `⊥`-only
    approximations at `EnvI.bot`, `ApproxDIK E EnvI.bot (instantiate 0 a e) c ↔ ApproxDIK E EnvI.bot e c`. -/
theorem approxDIK_bot_instantiate0_iff {E : ResolvedEnv} {a : Expr Nat}
    (ha : ∀ u, ApproxDIK E EnvI.bot a u → u = .bot)
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E EnvI.bot (instantiate 0 a e) c ↔ ApproxDIK E EnvI.bot e c := by
  have h := approxDIK_bot_subst_lift_iff ha 0 e c
  rwa [lift_zero_idx] at h

/-- For **any** `j : Nat`, substituting `botClosedExpr` at index `j` preserves all compacts in
    `ApproxDIK E EnvI.bot`. -/
theorem approxDIK_bot_instantiate_botClosedExpr_iff (E : ResolvedEnv) (j : Nat)
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E EnvI.bot (instantiate j botClosedExpr e) c ↔ ApproxDIK E EnvI.bot e c := by
  have h := approxDIK_bot_subst_lift_iff (E := E) (a := botClosedExpr)
    (fun _ hu => approxDIK_botClosedExpr_inv hu) j e c
  rwa [botClosedExpr_lift] at h

/-- For **any** `j, m : Nat`, substituting `lift 0 j (.bvar m) = .bvar (m + j)` at index `j`
    preserves all compacts in `ApproxDIK E EnvI.bot`. -/
theorem approxDIK_bot_subst_bvar_iff (E : ResolvedEnv) (m j : Nat)
    (e : Expr Nat) (c : CptI) :
    ApproxDIK E EnvI.bot (instantiate j (lift 0 j (.bvar m)) e) c ↔ ApproxDIK E EnvI.bot e c :=
  approxDIK_bot_subst_lift_iff
    (fun _ hu => by rcases approxDIK_bvar_inv hu with rfl | h0; rfl; exact h0) j e c

/-! ### `WhStepPiK` and `WhRedPiK` Commute with `lift k 1` and `instantiate j (lift 0 j v)` -/

theorem recCall_const_lift {E : ResolvedEnv} (k : Nat) (w : IotaWitnessS E) (x : Expr Nat) :
    lift k 1 (recCall (.const w.recRef w.ls) w.preMajor x) =
      recCall (.const (liftWitnessS k w).recRef (liftWitnessS k w).ls)
        (liftWitnessS k w).preMajor (lift k 1 x) := by
  simp only [recCall, liftWitnessS, foldApps_lift, lift, List.map_append,
    List.map_cons, List.map_nil]

theorem recCall_const_instantiate {E : ResolvedEnv} (j : Nat) (s : Expr Nat)
    (w : IotaWitnessS E) (x : Expr Nat) :
    instantiate j s (recCall (.const w.recRef w.ls) w.preMajor x) =
      recCall (.const (instWitnessS j s w).recRef (instWitnessS j s w).ls)
        (instWitnessS j s w).preMajor (instantiate j s x) := by
  simp only [recCall, instWitnessS, foldApps_instantiate, instantiate,
    List.map_append, List.map_cons, List.map_nil]

/-- **`WhStepPiK` Commutes with `lift k 1` for All `k : Nat` (`whStepPiK_lift_of_envClosed`):**
    Uses `approxDIK_bot_lift_iff` to transport both the `hflds` and `hx` premises of `iotaK` across
    `lift k 1` at **every** cutoff `k : Nat` (including `k = 0`)! -/
theorem whStepPiK_lift_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {a b : Expr Nat} (h : WhStepPiK E a b) (k : Nat) :
    WhStepPiK E (lift k 1 a) (lift k 1 b) := by
  induction h with
  | of_whStep hs =>
      exact .of_whStep (whStep_lift_of_envClosed hcl hs k)
  | iotaK w x hk hflds hx =>
      rw [recCall_const_lift k w x, ← iotaRhsOfS_lift k w]
      refine .iotaK (liftWitnessS k w) (lift k 1 x) hk ?_ ?_
      · intro f' hf' u hu
        simp only [liftWitnessS, List.mem_map] at hf'
        obtain ⟨f, hf, rfl⟩ := hf'
        exact hflds f hf u ((approxDIK_bot_lift_iff E k f u).mp hu)
      · intro args hsp
        exact hx args ((approxDIK_bot_lift_iff E k x (.spine w.ctorRef args)).mp hsp)
  | @appHead _ _ _ _ ih =>
      exact .appHead ih

theorem whRedPiK_lift_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {a b : Expr Nat} (h : WhRedPiK E a b) (k : Nat) :
    WhRedPiK E (lift k 1 a) (lift k 1 b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (whStepPiK_lift_of_envClosed hcl hs k) ih

/-- **`WhStepPiK` Commutes with `instantiate j (lift 0 j v)` for All `j : Nat` on `⊥`-Approximated
    Substituents (`whStepPiK_instantiate_of_botApprox`):** -/
theorem whStepPiK_instantiate_of_botApprox {E : ResolvedEnv} (hcl : EnvClosed E)
    {v : Expr Nat} (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    {a b : Expr Nat} (h : WhStepPiK E a b) (j : Nat) :
    WhStepPiK E (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b) := by
  induction h with
  | of_whStep hs =>
      exact .of_whStep (whStep_instantiate_of_envClosed hcl hs j (lift 0 j v))
  | iotaK w x hk hflds hx =>
      rw [recCall_const_instantiate j (lift 0 j v) w x,
        ← iotaRhsOfS_instantiate j (lift 0 j v) w]
      refine .iotaK (instWitnessS j (lift 0 j v) w) (instantiate j (lift 0 j v) x) hk ?_ ?_
      · intro f' hf' u hu
        simp only [instWitnessS, List.mem_map] at hf'
        obtain ⟨f, hf, rfl⟩ := hf'
        exact hflds f hf u ((approxDIK_bot_subst_lift_iff hv j f u).mp hu)
      · intro args hsp
        exact hx args ((approxDIK_bot_subst_lift_iff hv j x (.spine w.ctorRef args)).mp hsp)
  | @appHead _ _ _ _ ih =>
      exact .appHead ih

theorem whRedPiK_instantiate_of_botApprox {E : ResolvedEnv} (hcl : EnvClosed E)
    {v : Expr Nat} (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    {a b : Expr Nat} (h : WhRedPiK E a b) (j : Nat) :
    WhRedPiK E (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (whStepPiK_instantiate_of_botApprox hcl hv hs j) ih

/-! ### Closed-Field Deterministic K-Aware Readback `WhStepPiKClosed` / `WhRedPiKClosed` -/

/-- **Closed-Field Deterministic K-Aware Weak-Head Step (`WhStepPiKClosed E a b`):**
    Fixes the dummy field terms in `iotaKClosed` to
    `w.fields = List.replicate w.fields.length botClosedExpr`.
    Unlike `WhStepPiKCanon` (`w.fields = List.replicate w.fields.length (.bvar 0)`), `botClosedExpr`
    is closed at binder depth `0`, so `WhStepPiKClosed` is simultaneously:
    1. 100% single-step deterministic (`whDetPiKClosed_of_envWfT`),
    2. Sound in `ApproxDIK E EnvI.bot` (`semEqDIK_whStepPiKClosed`),
    3. Capable of reducing both 0-field `trueEnvU_kRecVar` and fieldful `mixAndRedex`,
    4. Unconditionally closed under `lift k 1` for **all** `k : Nat` (including `k = 0`), and
    5. Unconditionally closed under `instantiate j (lift 0 j v)` for **all** `j : Nat` (including
       `j = 0`) on any `⊥`-approximated substituent `v`! -/
inductive WhStepPiKClosed (E : ResolvedEnv) : Expr Nat → Expr Nat → Prop
  | of_whStep {a b : Expr Nat} (h : WhStep E a b) : WhStepPiKClosed E a b
  | iotaKClosed (w : IotaWitnessS E) (x : Expr Nat)
      (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
      (hflds : w.fields = List.replicate w.fields.length botClosedExpr)
      (hx : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w.ctorRef args)) :
      WhStepPiKClosed E (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOfS w)
  | appHead {f f' arg : Expr Nat} (h : WhStepPiKClosed E f f') :
      WhStepPiKClosed E (.app f arg) (.app f' arg)

/-- Every `WhStepPiKClosed` step embeds into `WhStepPiK` (via `approxDIK_botClosedExpr_inv`). -/
theorem whStepPiK_of_whStepPiKClosed {E : ResolvedEnv} {a b : Expr Nat}
    (h : WhStepPiKClosed E a b) : WhStepPiK E a b := by
  induction h with
  | of_whStep hs => exact .of_whStep hs
  | iotaKClosed w x hk hflds hx =>
      refine .iotaK w x hk (fun f hf u hu => ?_) hx
      rw [hflds] at hf
      rw [List.eq_of_mem_replicate hf] at hu
      exact approxDIK_botClosedExpr_inv hu
  | @appHead _ _ _ _ ih => exact .appHead ih

/-- Reflexive-transitive closure of `WhStepPiKClosed`. -/
inductive WhRedPiKClosed (E : ResolvedEnv) : Expr Nat → Expr Nat → Prop
  | refl (a : Expr Nat) : WhRedPiKClosed E a a
  | step {a b c : Expr Nat} (hs : WhStepPiKClosed E a b) (hr : WhRedPiKClosed E b c) :
      WhRedPiKClosed E a c

theorem whRedPiKClosed_trans {E : ResolvedEnv} {a b c : Expr Nat}
    (h₁ : WhRedPiKClosed E a b) (h₂ : WhRedPiKClosed E b c) : WhRedPiKClosed E a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem whRedPiKClosed_of_whRed {E : ResolvedEnv} {a b : Expr Nat}
    (h : WhRed E a b) : WhRedPiKClosed E a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step (.of_whStep hs) ih

theorem whRedPiK_of_whRedPiKClosed {E : ResolvedEnv} {a b : Expr Nat}
    (h : WhRedPiKClosed E a b) : WhRedPiK E a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step (whStepPiK_of_whStepPiKClosed hs) ih

theorem whRedPiKClosed_appHead {E : ResolvedEnv} {f f' arg : Expr Nat}
    (h : WhRedPiKClosed E f f') : WhRedPiKClosed E (.app f arg) (.app f' arg) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.appHead hs) ih

theorem semEqDIK_whStepPiKClosed {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hs : WhStepPiKClosed E a b) : SemEqDIK E EnvI.bot a b :=
  semEqDIK_whStepPiK hW (whStepPiK_of_whStepPiKClosed hs)

theorem semEqDIK_whRedPiKClosed {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hr : WhRedPiKClosed E a b) : SemEqDIK E EnvI.bot a b :=
  semEqDIK_whRedPiK hW (whRedPiK_of_whRedPiKClosed hr)

theorem approxDIK_whRedPiKClosed_back {E : ResolvedEnv} (hW : EnvWfT E) {a b : Expr Nat}
    (hr : WhRedPiKClosed E a b) {c : CptI} (hb : ApproxDIK E EnvI.bot b c) :
    ApproxDIK E EnvI.bot a c :=
  (semEqDIK_whRedPiKClosed hW hr c).mpr hb

theorem approxDIK_sort_of_whRedPiKClosed {E : ResolvedEnv} (hW : EnvWfT E)
    {a : Expr Nat} {l : Level}
    (hr : WhRedPiKClosed E a (.sort l)) : ApproxDIK E EnvI.bot a .sort :=
  approxDIK_whRedPiKClosed_back hW hr (.sort EnvI.bot l)

theorem whStepPiKClosed_sort_false {E : ResolvedEnv} {l : Level} {e : Expr Nat}
    (h : WhStepPiKClosed E (.sort l) e) : False :=
  whStepPiK_sort_false (whStepPiK_of_whStepPiKClosed h)

theorem whStepPiKClosed_pi_false {E : ResolvedEnv} {A B e : Expr Nat}
    (h : WhStepPiKClosed E (.pi A B) e) : False :=
  whStepPiK_pi_false (whStepPiK_of_whStepPiKClosed h)

theorem whStepPiKClosed_lam_false {E : ResolvedEnv} {A b e : Expr Nat}
    (h : WhStepPiKClosed E (.lam A b) e) : False :=
  whStepPiK_lam_false (whStepPiK_of_whStepPiKClosed h)

theorem whRedPiKClosed_sort_eq {E : ResolvedEnv} {l : Level} {e : Expr Nat}
    (h : WhRedPiKClosed E (.sort l) e) : e = .sort l :=
  whRedPiK_sort_eq (whRedPiK_of_whRedPiKClosed h)

theorem whRedPiKClosed_pi_eq {E : ResolvedEnv} {A B e : Expr Nat}
    (h : WhRedPiKClosed E (.pi A B) e) : e = .pi A B :=
  whRedPiK_pi_eq (whRedPiK_of_whRedPiKClosed h)

theorem not_whStepPiKClosed_recursor_prefix {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitnessS E) (ls : List Level) (xs : List (Expr Nat))
    (hlen : xs.length ≤ w.preMajor.length) {e : Expr Nat}
    (hs : WhStepPiKClosed E (foldApps (.const w.recRef ls) xs) e) : False :=
  not_whStepPiK_recursor_prefix hW w ls xs hlen (whStepPiK_of_whStepPiKClosed hs)

/-- Uniqueness of the `iotaKClosed` contractum from the redex expression alone. -/
theorem iotaKClosed_det {E : ResolvedEnv} (w₁ w₂ : IotaWitnessS E) (x₁ x₂ : Expr Nat)
    (hk₁ : piBody w₁.famMember.mtype = .sort .zero ∧ w₁.nMinors = 1)
    (hflds₁ : w₁.fields = List.replicate w₁.fields.length botClosedExpr)
    (hflds₂ : w₂.fields = List.replicate w₂.fields.length botClosedExpr)
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
  obtain ⟨hpreEq, _⟩ := List.append_inj hargs
    (by rw [(iotaWitnessS_preMajor_length_eq w₁ w₂ hrec).2])
  have hfldsEq : w₁.fields = w₂.fields := by
    rw [hflds₁, hflds₂, hfldsLenEq]
  unfold iotaRhsOfS
  rw [hpreEq, hfldsEq, hls, hschemaEq]

theorem whStep_and_whStepPiKClosed_det {E : ResolvedEnv} (hW : EnvWfT E)
    {a b c : Expr Nat} (h₁ : WhStep E a b) (h₂ : WhStepPiKClosed E a c) :
    b = c := by
  induction h₂ generalizing b with
  | of_whStep hs₂ =>
      exact whDet_of_envWfT hW h₁ hs₂
  | iotaKClosed w₂ x₂ hk₂ _ hx₂ =>
      exact (not_whStep_and_iotaK hW w₂ x₂ hk₂ hx₂ h₁).elim
  | @appHead f f' arg hf₂ ih =>
      generalize ha : Expr.app f arg = a₀ at h₁
      cases h₁ with
      | beta =>
          injection ha with hfEq _
          subst hfEq
          exact (whStepPiKClosed_lam_false hf₂).elim
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
              exact (not_whStepPiKClosed_recursor_prefix hW w₁ w₁.ls w₁.preMajor
                (Nat.le_refl _) hf₂).elim
      | appHead hs₁ =>
          injection ha with hfEq hargEq
          subst hfEq; subst hargEq
          exact congrArg (fun t => Expr.app t arg) (ih hs₁)

/-- **Exact Single-Step Determinism of `WhStepPiKClosed` (`whDetPiKClosed_of_envWfT`):**
    At every `EnvWfT E`, `WhStepPiKClosed E` is 100% single-step deterministic! -/
theorem whDetPiKClosed_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {a b c : Expr Nat} (h₁ : WhStepPiKClosed E a b) (h₂ : WhStepPiKClosed E a c) :
    b = c := by
  induction h₁ generalizing c with
  | of_whStep hs₁ =>
      exact whStep_and_whStepPiKClosed_det hW hs₁ h₂
  | iotaKClosed w₁ x₁ hk₁ hflds₁ hx₁ =>
      generalize ha : recCall (.const w₁.recRef w₁.ls) w₁.preMajor x₁ = a₀ at h₂
      cases h₂ with
      | of_whStep hs₂ =>
          subst ha
          exact (not_whStep_and_iotaK hW w₁ x₁ hk₁ hx₁ hs₂).elim
      | iotaKClosed w₂ x₂ _ hflds₂ _ =>
          exact iotaKClosed_det w₁ w₂ x₁ x₂ hk₁ hflds₁ hflds₂ ha
      | appHead hf₂ =>
          unfold recCall at ha
          rw [foldApps_snoc] at ha
          injection ha with hfEq _
          subst hfEq
          exact (not_whStepPiKClosed_recursor_prefix hW w₁ w₁.ls w₁.preMajor
            (Nat.le_refl _) hf₂).elim
  | @appHead f f' arg hf₁ ih =>
      generalize ha : Expr.app f arg = a₀ at h₂
      cases h₂ with
      | of_whStep hs₂ =>
          subst ha
          exact (whStep_and_whStepPiKClosed_det hW hs₂ (.appHead hf₁)).symm
      | iotaKClosed w₂ x₂ _ _ _ =>
          unfold recCall at ha
          rw [foldApps_snoc] at ha
          injection ha with hfEq _
          subst hfEq
          exact (not_whStepPiKClosed_recursor_prefix hW w₂ w₂.ls w₂.preMajor
            (Nat.le_refl _) hf₁).elim
      | appHead hf₂ =>
          injection ha with hfEq hargEq
          subst hfEq; subst hargEq
          exact congrArg (fun t => Expr.app t arg) (ih hf₂)

/-- Normal forms of `WhStepPiKClosed E`. -/
def WhNormalPiKClosed (E : ResolvedEnv) (a : Expr Nat) : Prop :=
  ∀ b, ¬ WhStepPiKClosed E a b

theorem whNormalPiKClosed_sort (E : ResolvedEnv) (l : Level) :
    WhNormalPiKClosed E (.sort l) :=
  fun _ h => whStepPiKClosed_sort_false h

theorem whNormalPiKClosed_pi (E : ResolvedEnv) (A B : Expr Nat) :
    WhNormalPiKClosed E (.pi A B) :=
  fun _ h => whStepPiKClosed_pi_false h

theorem whNormalPiKClosed_lam (E : ResolvedEnv) (A b : Expr Nat) :
    WhNormalPiKClosed E (.lam A b) :=
  fun _ h => whStepPiKClosed_lam_false h

theorem whRedPiKClosed_of_normal {E : ResolvedEnv} {X Y : Expr Nat}
    (hX : WhNormalPiKClosed E X) (h : WhRedPiKClosed E X Y) : Y = X := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hX _ hs).elim

theorem whRedPiKClosed_normal_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {a X Y : Expr Nat} (h₁ : WhRedPiKClosed E a X) (hX : WhNormalPiKClosed E X)
    (h₂ : WhRedPiKClosed E a Y) (hY : WhNormalPiKClosed E Y) : X = Y := by
  induction h₁ with
  | refl => exact (whRedPiKClosed_of_normal hX h₂).symm
  | step hs₁ _ ih =>
      cases h₂ with
      | refl => exact (hY _ hs₁).elim
      | step hs₂ hr₂ =>
          have e := whDetPiKClosed_of_envWfT hW hs₁ hs₂
          subst e
          exact ih hX hr₂

theorem whRedPiKClosed_pi_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {a A₁ B₁ A₂ B₂ : Expr Nat}
    (h₁ : WhRedPiKClosed E a (.pi A₁ B₁)) (h₂ : WhRedPiKClosed E a (.pi A₂ B₂)) :
    A₁ = A₂ ∧ B₁ = B₂ := by
  have e := whRedPiKClosed_normal_unique_of_envWfT hW h₁ (whNormalPiKClosed_pi E A₁ B₁)
    h₂ (whNormalPiKClosed_pi E A₂ B₂)
  injection e with eA eB
  exact ⟨eA, eB⟩

theorem whRedPiKClosed_sort_unique_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    {a : Expr Nat} {l₁ l₂ : Level}
    (h₁ : WhRedPiKClosed E a (.sort l₁)) (h₂ : WhRedPiKClosed E a (.sort l₂)) :
    l₁ = l₂ := by
  have e := whRedPiKClosed_normal_unique_of_envWfT hW h₁ (whNormalPiKClosed_sort E l₁)
    h₂ (whNormalPiKClosed_sort E l₂)
  injection e

theorem whStepPiKClosed_iotaKClosed_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) (x : Expr Nat)
    (hk : piBody w.famMember.mtype = .sort .zero ∧ w.nMinors = 1)
    (hflds : w.fields = List.replicate w.fields.length botClosedExpr)
    (hx : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine w.ctorRef args)) :
    WhStepPiKClosed E (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) := by
  obtain ⟨wS, hrec, hctor, hls, _, hpre, hfldsEq, _, _, hfamM, _, _, hnmin, _, _, hrhs⟩ :=
    iotaWitnessS_of_iotaWitness_envWfT hW w
  have hkS : piBody wS.famMember.mtype = .sort .zero ∧ wS.nMinors = 1 := by
    rw [hfamM, hnmin]; exact hk
  have hfldsS : wS.fields = List.replicate wS.fields.length botClosedExpr := by
    rw [hfldsEq]; exact hflds
  have hxS : ∀ args, ¬ ApproxDIK E EnvI.bot x (.spine wS.ctorRef args) := by
    rw [hctor]; exact hx
  have hs := WhStepPiKClosed.iotaKClosed wS x hkS hfldsS hxS
  rwa [hrec, hls, hpre, hrhs] at hs

/-- In `WhRedPiKClosed`, `trueEnvU_kRecVar` reduces in 1 `iotaKClosed` step to `.sort .zero`. -/
theorem whRedPiKClosed_trueEnvU_kRecVar_sort :
    WhRedPiKClosed trueEnvU trueEnvU_kRecVar (.sort .zero) :=
  .step (whStepPiKClosed_iotaKClosed_of_envWfT trueEnvUWfT wTrueRecU (.bvar 0) ⟨rfl, rfl⟩ rfl
    (fun args hsp => by rcases approxDIK_bvar_inv hsp with h0 | h0 <;> cases h0)) (.refl _)

/-- Closed-field witness `mixAndWClosed : IotaWitness andEnvU` with
    `fields = [botClosedExpr, botClosedExpr] = List.replicate 2 botClosedExpr`. -/
def mixAndWClosed : IotaWitness andEnvU :=
  { mixAndW with
    fields := [botClosedExpr, botClosedExpr]
    hlen := rfl
    hnpar := rfl }

/-- `iotaRhsOf mixAndWClosed = .app (.app mixAndMin botClosedExpr) botClosedExpr` reduces in two
    `WhStep.beta` steps to `mixPi = .pi (.sort .zero) (.sort .zero)`. -/
theorem whRed_andEnvU_mixAndClosedRhs_mixPi :
    WhRed andEnvU (iotaRhsOf mixAndWClosed) mixPi :=
  .step (.appHead (.beta (.bvar 4) (.lam (.bvar 4) mixPi) botClosedExpr))
    (.step (.beta (.bvar 3) mixPi botClosedExpr) (.refl mixPi))

/-- In `WhRedPiKClosed`, `mixAndRedex` reduces to `mixPi = .pi (.sort .zero) (.sort .zero)`! -/
theorem whRedPiKClosed_andEnvU_mixAndRedex_mixPi :
    WhRedPiKClosed andEnvU mixAndRedex mixPi :=
  .step (whStepPiKClosed_iotaKClosed_of_envWfT andEnvUWfT mixAndWClosed (.bvar 0) ⟨rfl, rfl⟩ rfl
    (fun args hsp => by rcases approxDIK_bvar_inv hsp with h0 | h0 <;> cases h0))
    (whRedPiKClosed_of_whRed whRed_andEnvU_mixAndClosedRhs_mixPi)

/-- **Unconditional `lift k 1` Commutation for `WhStepPiKClosed` at ALL `k : Nat` (Including `k = 0`!):**
    Because `botClosedExpr` is closed at depth `0` (`replicate_botClosedExpr_map_lift`),
    `WhStepPiKClosed` commutes with `lift k 1` for **every** cutoff `k : Nat` (unlike
    `WhStepPiKCanon`, which required `0 < c` when `w.fields ≠ []`)! -/
theorem whStepPiKClosed_lift_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {a b : Expr Nat} (h : WhStepPiKClosed E a b) (k : Nat) :
    WhStepPiKClosed E (lift k 1 a) (lift k 1 b) := by
  induction h with
  | of_whStep hs =>
      exact .of_whStep (whStep_lift_of_envClosed hcl hs k)
  | iotaKClosed w x hk hflds hx =>
      rw [recCall_const_lift k w x, ← iotaRhsOfS_lift k w]
      refine .iotaKClosed (liftWitnessS k w) (lift k 1 x) hk ?_ ?_
      · simp only [liftWitnessS, List.length_map]
        calc
          w.fields.map (lift k 1)
            = (List.replicate w.fields.length botClosedExpr).map (lift k 1) := by
                exact congrArg (List.map (lift k 1)) hflds
          _ = List.replicate w.fields.length botClosedExpr :=
                replicate_botClosedExpr_map_lift w.fields.length k 1
      · intro args hsp
        exact hx args ((approxDIK_bot_lift_iff E k x (.spine w.ctorRef args)).mp hsp)
  | @appHead _ _ _ _ ih =>
      exact .appHead ih

theorem whRedPiKClosed_lift_of_envClosed {E : ResolvedEnv} (hcl : EnvClosed E)
    {a b : Expr Nat} (h : WhRedPiKClosed E a b) (k : Nat) :
    WhRedPiKClosed E (lift k 1 a) (lift k 1 b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (whStepPiKClosed_lift_of_envClosed hcl hs k) ih

/-- **Unconditional `instantiate j (lift 0 j v)` Commutation for `WhStepPiKClosed` at ALL `j : Nat`
    (Including `j = 0`!) on `⊥`-Approximated Substituents:**
    Because `botClosedExpr` is closed at depth `0` (`replicate_botClosedExpr_map_instantiate`),
    `WhStepPiKClosed` commutes with `instantiate j (lift 0 j v)` for **every** `j : Nat` and any
    `v` with `∀ u, ApproxDIK E EnvI.bot v u → u = .bot`! -/
theorem whStepPiKClosed_instantiate_of_botApprox {E : ResolvedEnv} (hcl : EnvClosed E)
    {v : Expr Nat} (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    {a b : Expr Nat} (h : WhStepPiKClosed E a b) (j : Nat) :
    WhStepPiKClosed E (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b) := by
  induction h with
  | of_whStep hs =>
      exact .of_whStep (whStep_instantiate_of_envClosed hcl hs j (lift 0 j v))
  | iotaKClosed w x hk hflds hx =>
      rw [recCall_const_instantiate j (lift 0 j v) w x,
        ← iotaRhsOfS_instantiate j (lift 0 j v) w]
      refine .iotaKClosed (instWitnessS j (lift 0 j v) w)
        (instantiate j (lift 0 j v) x) hk ?_ ?_
      · simp only [instWitnessS, List.length_map]
        calc
          w.fields.map (instantiate j (lift 0 j v))
            = (List.replicate w.fields.length botClosedExpr).map (instantiate j (lift 0 j v)) := by
                exact congrArg (List.map (instantiate j (lift 0 j v))) hflds
          _ = List.replicate w.fields.length botClosedExpr :=
                replicate_botClosedExpr_map_instantiate w.fields.length j (lift 0 j v)
      · intro args hsp
        exact hx args ((approxDIK_bot_subst_lift_iff hv j x (.spine w.ctorRef args)).mp hsp)
  | @appHead _ _ _ _ ih =>
      exact .appHead ih

theorem whRedPiKClosed_instantiate_of_botApprox {E : ResolvedEnv} (hcl : EnvClosed E)
    {v : Expr Nat} (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    {a b : Expr Nat} (h : WhRedPiKClosed E a b) (j : Nat) :
    WhRedPiKClosed E (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (whStepPiKClosed_instantiate_of_botApprox hcl hv hs j) ih

/-! ### `LRTypeINPiKClosed` and `LRTypeINBiDIKClosed`: Symmetry, Transitivity, Weakening, and Substitution -/

/-- Type-level logical relation over `WhRedPiKClosed`. -/
inductive LRTypeINPiKClosed (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → CptI → Prop
  | bot (Γ : LCtx) (A A' : Expr Nat) :
      LRTypeINPiKClosed E n Γ A A' .bot
  | sort {Γ : LCtx} {A A' : Expr Nat} {l l' : Level}
      (h : WhRedPiKClosed E A (.sort l)) (h' : WhRedPiKClosed E A' (.sort l')) :
      LRTypeINPiKClosed E n Γ A A' .sort
  | pi {Γ : LCtx} {A A' A₁ B₁ A₂ B₂ : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (h : WhRedPiKClosed E A (.pi A₁ B₁))
      (h' : WhRedPiKClosed E A' (.pi A₂ B₂))
      (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
      (hdom : TyConvT E n Γ A₁ A₂)
      (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
      (ra : LRTypeINPiKClosed E n Γ A₁ A₂ a)
      (rf : ∀ s ∈ f, LRTypeINPiKClosed E n (.assumption A₁ :: Γ) B₁ B₂ s.2) :
      LRTypeINPiKClosed E n Γ A A' (.pi a f)
  | spine {Γ : LCtx} {A A' Y Y' : Expr Nat} {r : Nat} {args : List CptI}
      (h : WhRedPiKClosed E A Y) (h' : WhRedPiKClosed E A' Y')
      (hn : WhNormalPiKClosed E Y) (hn' : WhNormalPiKClosed E Y')
      (hc : TyConvT E n Γ Y Y') :
      LRTypeINPiKClosed E n Γ A A' (.spine r args)

theorem lrTypeINPiKClosed_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {M M' A A' : Expr Nat} {u : CptI}
    (hM : WhRedPiKClosed E M A) (hM' : WhRedPiKClosed E M' A')
    (h : LRTypeINPiKClosed E n Γ A A' u) :
    LRTypeINPiKClosed E n Γ M M' u := by
  cases h with
  | bot => exact .bot _ _ _
  | sort h₁ h₂ => exact .sort (whRedPiKClosed_trans hM h₁) (whRedPiKClosed_trans hM' h₂)
  | pi h₁ h₂ hΓ₁ hdom hcod ra rf =>
      exact .pi (whRedPiKClosed_trans hM h₁) (whRedPiKClosed_trans hM' h₂) hΓ₁ hdom hcod ra rf
  | spine h₁ h₂ hn hn' hc =>
      exact .spine (whRedPiKClosed_trans hM h₁) (whRedPiKClosed_trans hM' h₂) hn hn' hc

theorem approxDIK_of_lrTypeINPiKClosed_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A A' : Expr Nat} {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeINPiKClosed E n Γ A A' c) :
    ApproxDIK E EnvI.bot A c ∧ ApproxDIK E EnvI.bot A' c := by
  induction hc generalizing Γ A A' with
  | bot => exact ⟨.bot _ _, .bot _ _⟩
  | sort =>
      cases h with
      | sort hA hA' =>
          exact ⟨approxDIK_sort_of_whRedPiKClosed hW hA,
            approxDIK_sort_of_whRedPiKClosed hW hA'⟩
  | @pi a f _ hbd _ iha ihf =>
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ hA hA' _ _ _ ra rf =>
          obtain ⟨hAa, hA'a⟩ := iha ra
          have hBf : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) EnvI.bot) B₁ s.2 := by
            intro s hs
            rw [approxDIK_cons_botDemand_bot_iff (hbd s hs)]
            exact (ihf s hs (rf s hs)).1
          have hB'f : ∀ s ∈ f, ApproxDIK E (EnvI.cons (demand s.1) EnvI.bot) B₂ s.2 := by
            intro s hs
            rw [approxDIK_cons_botDemand_bot_iff (hbd s hs)]
            exact (ihf s hs (rf s hs)).2
          exact ⟨approxDIK_whRedPiKClosed_back hW hA (.pi hAa hBf),
            approxDIK_whRedPiKClosed_back hW hA' (.pi hA'a hB'f)⟩

theorem lrTypeINPiKClosed_ctx {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ Γ' : LCtx}
    (hctx : CtxConvT E n Γ Γ') (hΓ' : CtxWfT E n Γ') {A A' : Expr Nat} {c : CptI}
    (h : LRTypeINPiKClosed E n Γ A A' c) : LRTypeINPiKClosed E n Γ' A A' c := by
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

theorem lrTypeINPiKClosed_assump_dom {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) :
    {A₁ A₂ : Expr Nat} → TyConvT E n Γ A₁ A₂ → {u : Level} → HasTyT E n Γ A₁ (.sort u) →
    ∀ {B B' : Expr Nat} {c : CptI},
      LRTypeINPiKClosed E n (.assumption A₂ :: Γ) B B' c →
      LRTypeINPiKClosed E n (.assumption A₁ :: Γ) B B' c
  | _, _, .refl _ _, _, _, _, _, _, h => h
  | _, _, .of _ A₁ A₂ _ hc, _, hA₁, _, _, _, h =>
      let ends := convEnds hW hΓ hc
      lrTypeINPiKClosed_ctx hW
        (.assumption (ctxConvT_refl Γ) ends.2.1 ends.1 (.symm _ _ _ _ hc))
        (.assumption Γ A₁ _ hΓ hA₁) h
  | _, _, .trans _ A₁ _ A₂ c₁ c₂, _, hA₁, _, _, _, h =>
      let ⟨_, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA₁
      lrTypeINPiKClosed_assump_dom hW hΓ c₁ hA₁
        (lrTypeINPiKClosed_assump_dom hW hΓ c₂ hM h)

/-- Full symmetry of `LRTypeINPiKClosed` at `EnvWfT E`. -/
theorem lrTypeINPiKClosed_symm {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ : LCtx}
    {A A' : Expr Nat} {c : CptI} (h : LRTypeINPiKClosed E n Γ A A' c) :
    LRTypeINPiKClosed E n Γ A' A c := by
  induction h with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort h' h
  | @pi Γ A A' A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      cases hΓ₁ with
      | assumption _ _ _ hΓ hA₁ =>
          obtain ⟨v, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          have hΓ₂ : CtxWfT E n (.assumption A₂ :: Γ) := .assumption Γ A₂ v hΓ hA₂
          exact .pi h' h hΓ₂ hdom.symmT (tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT) iha
            (fun s hs => lrTypeINPiKClosed_assump_dom hW hΓ hdom.symmT hA₂ (ihf s hs))
  | spine h h' hn hn' hc => exact .spine h' h hn' hn hc.symmT

/-- **Unconditional Transitivity of `LRTypeINPiKClosed` at `EnvWfT E`
    (`lrTypeINPiKClosed_trans_of_envWfT`):** -/
theorem lrTypeINPiKClosed_trans_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A M B : Expr Nat} {c : CptI}
    (h₁ : LRTypeINPiKClosed E n Γ A M c) (h₂ : LRTypeINPiKClosed E n Γ M B c) :
    LRTypeINPiKClosed E n Γ A B c := by
  induction h₁ generalizing B with
  | bot => exact .bot _ _ _
  | sort hA _ =>
      cases h₂ with
      | sort _ hB => exact .sort hA hB
  | @pi Γ A M A₁ B₁ M₁ N₁ a f hA hM₁ hΓ₁ hdom₁ hcod₁ _ _ iha ihf =>
      cases h₂ with
      | @pi _ _ B M₂ N₂ A₂ B₂ _ _ hM₂ hB _ hdom₂ hcod₂ ra₂ rf₂ =>
          obtain ⟨eM, eN⟩ := whRedPiKClosed_pi_unique_of_envWfT hW hM₁ hM₂
          subst eM; subst eN
          cases hΓ₁ with
          | assumption _ _ _ hΓ hA₁ =>
              exact .pi hA hB (.assumption Γ A₁ _ hΓ hA₁)
                (.trans _ _ _ _ hdom₁ hdom₂)
                (.trans _ _ _ _ hcod₁ (tyConvT_assump_dom hW hΓ hdom₁ hcod₂))
                (iha ra₂)
                (fun s hs =>
                  ihf s hs (lrTypeINPiKClosed_assump_dom hW hΓ hdom₁ hA₁ (rf₂ s hs)))
  | spine hA hM₁ hnA hnM₁ hc₁ =>
      cases h₂ with
      | spine hM₂ hB hnM₂ hnB hc₂ =>
          have eY := whRedPiKClosed_normal_unique_of_envWfT hW hM₁ hnM₁ hM₂ hnM₂
          subst eY
          exact .spine hA hB hnA hnB (.trans _ _ _ _ hc₁ hc₂)

/-- **Unconditional Weakening Stability of `LRTypeINPiKClosed` on `BotPiCpt` Across ALL Cutoffs
    `k : Nat` (Including `k = 0`!):** -/
theorem lrTypeINPiKClosed_weaken_botPiCpt {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {c : CptI} (hc : BotPiCpt c) :
    ∀ {Γ : LCtx} {A A' : Expr Nat} (d : LocalDecl) (k : Nat),
      CtxWfT E n (insertAt d k Γ) →
      LRTypeINPiKClosed E n Γ A A' c →
      LRTypeINPiKClosed E n (insertAt d k Γ) (lift k 1 A) (lift k 1 A') c := by
  induction hc with
  | bot =>
      intro Γ A A' d k _ _
      exact .bot _ _ _
  | sort =>
      intro Γ A A' d k _ h
      cases h with
      | sort h₁ h₂ =>
          exact .sort (whRedPiKClosed_lift_of_envClosed hcl h₁ k)
            (whRedPiKClosed_lift_of_envClosed hcl h₂ k)
  | @pi a f _ _ _ iha ihf =>
      intro Γ A A' d k hΓ' h
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h₁ h₂ hΓ₁ hdom hcod ra rf =>
          have h₁' : WhRedPiKClosed E (lift k 1 A) (.pi (lift k 1 A₁) (lift (k + 1) 1 B₁)) :=
            whRedPiKClosed_lift_of_envClosed hcl h₁ k
          have h₂' : WhRedPiKClosed E (lift k 1 A') (.pi (lift k 1 A₂) (lift (k + 1) 1 B₂)) :=
            whRedPiKClosed_lift_of_envClosed hcl h₂ k
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
            (iha d k hΓ' ra)
            (fun s hs => by
              have hΓ₁_ins : CtxWfT E n (insertAt d (k + 1) (.assumption A₁ :: Γ)) := hΓ₁'
              exact ihf s hs d (k + 1) hΓ₁_ins (rf s hs))

/-- **Cutoff-`0` Weakening Stability of `LRTypeINPiKClosed` on `BotPiCpt`
    (`lrTypeINPiKClosed_weaken0_botPiCpt`):** -/
theorem lrTypeINPiKClosed_weaken0_botPiCpt {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {A A' : Expr Nat} {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeINPiKClosed E n Γ A A' c) :
    LRTypeINPiKClosed E n (d :: Γ) (lift 0 1 A) (lift 0 1 A') c :=
  lrTypeINPiKClosed_weaken_botPiCpt hcl hc d 0 hΓ' h

/-- **Unconditional Substitution Stability of `LRTypeINPiKClosed` on `BotPiCpt` for `⊥`-Approximated
    Substituents (`lrTypeINPiKClosed_subst_botPiCpt`):** -/
theorem lrTypeINPiKClosed_subst_botPiCpt {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {v : Expr Nat} (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot) (t : Expr Nat)
    {c : CptI} (hc : BotPiCpt c) :
    ∀ {Γ : LCtx} {A A' : Expr Nat} {j : Nat},
      Γ[j]? = some (.assumption t) →
      HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
      CtxWfT E n (substRemove v j Γ) →
      LRTypeINPiKClosed E n Γ A A' c →
      LRTypeINPiKClosed E n (substRemove v j Γ)
        (instantiate j (lift 0 j v) A) (instantiate j (lift 0 j v) A') c := by
  induction hc with
  | bot =>
      intro Γ A A' j _ _ _ _
      exact .bot _ _ _
  | sort =>
      intro Γ A A' j _ _ _ h
      cases h with
      | sort h₁ h₂ =>
          exact .sort (whRedPiKClosed_instantiate_of_botApprox hcl hv h₁ j)
            (whRedPiKClosed_instantiate_of_botApprox hcl hv h₂ j)
  | @pi a f _ _ _ iha ihf =>
      intro Γ A A' j hget hvty hΓ' h
      cases h with
      | @pi _ _ _ A₁ B₁ A₂ B₂ _ _ h₁ h₂ hΓ₁ hdom hcod ra rf =>
          have hlift : lift 0 1 (lift 0 j v) = lift 0 (j + 1) v :=
            lift_lift_merge 1 j 0 0 (by omega) (by omega) v
          have h₁' : WhRedPiKClosed E (instantiate j (lift 0 j v) A)
              (.pi (instantiate j (lift 0 j v) A₁) (instantiate (j + 1) (lift 0 (j + 1) v) B₁)) := by
            have h0 := whRedPiKClosed_instantiate_of_botApprox hcl hv h₁ j
            simpa only [instantiate, hlift] using h0
          have h₂' : WhRedPiKClosed E (instantiate j (lift 0 j v) A')
              (.pi (instantiate j (lift 0 j v) A₂) (instantiate (j + 1) (lift 0 (j + 1) v) B₂)) := by
            have h0 := whRedPiKClosed_instantiate_of_botApprox hcl hv h₂ j
            simpa only [instantiate, hlift] using h0
          have hA₁ : ∃ u, Nonempty (HasTyT E n Γ A₁ (.sort u)) := by
            cases hΓ₁ with
            | assumption _ _ u _ hA₁ => exact ⟨u, ⟨hA₁⟩⟩
          obtain ⟨u, ⟨hA₁⟩⟩ := hA₁
          have hΓ₁' : CtxWfT E n (substRemove v (j + 1) (.assumption A₁ :: Γ)) :=
            subst_arg_wf_assump hcl hinst hget hvty hΓ' hA₁
          have hget' : (LocalDecl.assumption A₁ :: Γ)[j + 1]? = some (.assumption t) := by
            rw [List.getElem?_cons_succ]; exact hget
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
          have hΓ₁'' : CtxWfT E n (.assumption (instantiate j (lift 0 j v) A₁) :: substRemove v j Γ) := by
            simpa only [substRemove_succ_cons, instDecl] using hΓ₁'
          exact .pi h₁' h₂' hΓ₁'' hdom' hcod'
            (iha hget hvty hΓ' ra)
            (fun s hs => by
              simpa only [substRemove_succ_cons, instDecl] using
                ihf s hs hget' hvty' hΓ₁' (rf s hs))

/-- Head (`j = 0`) specialization of `lrTypeINPiKClosed_subst_botPiCpt`. -/
theorem lrTypeINPiKClosed_subst0_botPiCpt {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t : Expr Nat}
    (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    (hvty : HasTyT E n Γ v t)
    {A A' : Expr Nat} {c : CptI} (hc : BotPiCpt c)
    (h : LRTypeINPiKClosed E n (.assumption t :: Γ) A A' c) :
    LRTypeINPiKClosed E n Γ (instantiate0 v A) (instantiate0 v A') c := by
  have hvty0 : HasTyT E n (substRemove v 0 (.assumption t :: Γ)) (lift 0 0 v) (lift 0 0 t) := by
    simpa only [substRemove, lift_zero_idx] using hvty
  have hget0 : (LocalDecl.assumption t :: Γ)[0]? = some (.assumption t) := by simp
  have h0 := lrTypeINPiKClosed_subst_botPiCpt
    (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hv t hc
    (Γ := .assumption t :: Γ) (j := 0) hget0 hvty0 hΓ h
  simpa only [substRemove, lift_zero_idx, instantiate0] using h0

/-- Bidirectional `BotPiCpt`-restricted type logical relation over `ApproxDIK E EnvI.bot` and
    `LRTypeINPiKClosed`. -/
def LRTypeINBiDIKClosed (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B : Expr Nat) : Prop :=
  ∀ c, BotPiCpt c →
    (ApproxDIK E EnvI.bot A c ∨ ApproxDIK E EnvI.bot B c) →
    LRTypeINPiKClosed E n Γ A B c

theorem lrTypeINBiDIKClosed_symm {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A B : Expr Nat} (h : LRTypeINBiDIKClosed E n Γ A B) :
    LRTypeINBiDIKClosed E n Γ B A :=
  fun c hc hBA => lrTypeINPiKClosed_symm hW (h c hc hBA.symm)

theorem lrTypeINBiDIKClosed_trans_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {A M B : Expr Nat}
    (h₁ : LRTypeINBiDIKClosed E n Γ A M) (h₂ : LRTypeINBiDIKClosed E n Γ M B) :
    LRTypeINBiDIKClosed E n Γ A B := by
  intro c hc hAB
  rcases hAB with hAc | hBc
  · have r₁ : LRTypeINPiKClosed E n Γ A M c := h₁ c hc (Or.inl hAc)
    have hMc : ApproxDIK E EnvI.bot M c :=
      (approxDIK_of_lrTypeINPiKClosed_botPiCpt hW hc r₁).2
    exact lrTypeINPiKClosed_trans_of_envWfT hW r₁ (h₂ c hc (Or.inl hMc))
  · have r₂ : LRTypeINPiKClosed E n Γ M B c := h₂ c hc (Or.inr hBc)
    have hMc : ApproxDIK E EnvI.bot M c :=
      (approxDIK_of_lrTypeINPiKClosed_botPiCpt hW hc r₂).1
    exact lrTypeINPiKClosed_trans_of_envWfT hW (h₁ c hc (Or.inr hMc)) r₂

/-- **Unconditional Head Weakening of `LRTypeINBiDIKClosed` (`lrTypeINBiDIKClosed_weaken0`):** -/
theorem lrTypeINBiDIKClosed_weaken0 {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {Γ : LCtx} {d : LocalDecl} (hΓ' : CtxWfT E n (d :: Γ))
    {A A' : Expr Nat} (h : LRTypeINBiDIKClosed E n Γ A A') :
    LRTypeINBiDIKClosed E n (d :: Γ) (lift 0 1 A) (lift 0 1 A') := by
  intro c hc hor
  have hor₀ : ApproxDIK E EnvI.bot A c ∨ ApproxDIK E EnvI.bot A' c :=
    hor.elim (fun hL => Or.inl ((approxDIK_bot_lift_iff E 0 A c).mp hL))
             (fun hR => Or.inr ((approxDIK_bot_lift_iff E 0 A' c).mp hR))
  exact lrTypeINPiKClosed_weaken0_botPiCpt hcl hΓ' hc (h c hc hor₀)

/-- **Unconditional Head Substitution of `LRTypeINBiDIKClosed` for `⊥`-Approximated Substituents
    (`lrTypeINBiDIKClosed_subst0`):** -/
theorem lrTypeINBiDIKClosed_subst0 {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {v t : Expr Nat}
    (hv : ∀ u, ApproxDIK E EnvI.bot v u → u = .bot)
    (hvty : HasTyT E n Γ v t)
    {A A' : Expr Nat}
    (h : LRTypeINBiDIKClosed E n (.assumption t :: Γ) A A') :
    LRTypeINBiDIKClosed E n Γ (instantiate0 v A) (instantiate0 v A') := by
  intro c hc hor
  have hor₀ : ApproxDIK E EnvI.bot A c ∨ ApproxDIK E EnvI.bot A' c :=
    hor.elim (fun hL => Or.inl ((approxDIK_bot_instantiate0_iff hv A c).mp hL))
             (fun hR => Or.inr ((approxDIK_bot_instantiate0_iff hv A' c).mp hR))
  exact lrTypeINPiKClosed_subst0_botPiCpt hW hΓ hv hvty hc (h c hc hor₀)

#print axioms approxDIK_instantiateLevels_swap
#print axioms approxDIK_instantiateLevels_iff
#print axioms approxDIK_const_levels
#print axioms semEqDIK_const_levels
#print axioms botClosedExpr
#print axioms exprClosedAt_botClosedExpr
#print axioms botClosedExpr_lift
#print axioms botClosedExpr_instantiate
#print axioms botClosedExpr_instantiateLevels
#print axioms replicate_botClosedExpr_map_lift
#print axioms replicate_botClosedExpr_map_instantiate
#print axioms approxI_botClosedExpr_inv
#print axioms approxI_botClosedExpr_iff
#print axioms approxDI_botClosedExpr_inv
#print axioms approxDI_botClosedExpr_iff
#print axioms approxDIK_botClosedExpr_inv
#print axioms approxDIK_botClosedExpr_iff
#print axioms semEqDIK_k_botClosedExpr_of_envWfT
#print axioms approxDIK_lam_botPiCpt_eq_bot
#print axioms approxDIK_rigidConst_botPiCpt_eq_bot
#print axioms approxDIK_recursor_botPiCpt_eq_bot
#print axioms approxDIK_const_body_none_botPiCpt_eq_bot
#print axioms not_approxDIK_pi_sort
#print axioms ProbeCpt
#print axioms botPiCpt_of_probeCpt
#print axioms approxDIK_pi_probe_inv
#print axioms lrTypeINPiKCanon_of_lrTermDSubKCore_probe
#print axioms approxDIK_of_lrTermDSubKCore_probe
#print axioms approxDIK_of_lrTermDSubK_probe_of_not_prop
#print axioms approxDIK_of_lrTermDSubK_probe_at_sort
#print axioms lrTermDSubKCore_botPiCpt_transport_of_whRed_sort
#print axioms lrTermDSubKCore_botPiCpt_sort_index_irrel
#print axioms lrTermDSubK_botPiCpt_sort_index_irrel
#print axioms lrTermDSubKCore_botPiCpt_transport_of_sort
#print axioms lrTermDSubKCore_probe_symm
#print axioms lrTermDSubK_probe_symm
#print axioms lrTermDSubKCore_probe_trans
#print axioms lrTermDSubK_probe_trans
#print axioms lrTermDSubKCore_transport
#print axioms lrTermDSubK_transport
#print axioms fundTermDSubK_sort
#print axioms fundTermDSubK_bvar
#print axioms fundTermDSubK_lam
#print axioms fundTermDSubK_const_of_body_none
#print axioms fundTermDSubK_rigidConst
#print axioms fundTermDSubK_recursor
#print axioms fundTermDSubK_deltaConst
#print axioms fundTermDSubK_pi_probe
#print axioms fundTermDSubK_lit
#print axioms fundTermDSubK_letE
#print axioms fundTermDSubK_conv_probe
#print axioms fundConvDSubK_refl
#print axioms fundConvDSubK_probe_symm
#print axioms lrTermDSubKCore_botPiCpt_forces_sort
#print axioms not_lrTermDSubKCore_at_pi_of_botPiCpt_ne_bot
#print axioms lrTermDSubK_at_pi_of_botPiCpt
#print axioms fundConvDSubK_probe_trans
#print axioms fundConvDSubK_lam
#print axioms fundConvDSubK_pi_probe
#print axioms fundConvDSubK_letE
#print axioms fundConvDSubK_consts_of_body_none
#print axioms fundConvDSubK_rigidConsts
#print axioms fundConvDSubK_recursorConsts
#print axioms fundConvDSubK_deltaConsts
#print axioms fundConvDSubK_eta
#print axioms fundConvDSubK_tyConv_probe
#print axioms LRTermDSubKBi
#print axioms lrTermDSubKBi_symm
#print axioms lrTermDSubKBi_trans
#print axioms lrTermDSubKBi_whRedPiKCanon_expand
#print axioms lrTermDSubKBi_of_whStepPiKCanon
#print axioms lrTermDSubKBi_sorts
#print axioms lrTermDSubKBi_sort_diag
#print axioms lrTermDSubKBi_bvar_diag
#print axioms lrTermDSubKBi_lam
#print axioms lrTermDSubKBi_consts_of_body_none
#print axioms lrTermDSubKBi_deltaConsts
#print axioms lrTermDSubKBi_pi
#print axioms lrTermDSubKBi_pi_diag
#print axioms lrTermDSubKBi_eta
#print axioms lrTermDSubKBi_irr_of_sortRow
#print axioms lrTermDSubKBi_tyConv
#print axioms FundamentalTermDSubKProbe_letFree
#print axioms FundamentalTermDSubKBiProbe_letFree
#print axioms fundamentalTermDSubKProbe_letFree_of_biProbe_letFree
#print axioms fundamentalTermDSubKProbe_letFree_of_botDIK_letFree
#print axioms piRow_letFree_of_fundamentalTermDSubKProbe_letFree
#print axioms piRow_of_fundamentalTermDSubKProbe_letFree
#print axioms piRow_of_fundamentalTermDSubKBiProbe_letFree
#print axioms AppLetProbeSupplyDSubKBi
#print axioms fundamentalTermDSubKBiProbe_letFree_of_supply
#print axioms fundamentalTermDSubKProbe_letFree_of_supply
#print axioms piRow_of_appLetProbeSupplyDSubKBi
#print axioms envI_insert_bot_false
#print axioms approxDIK_bot_lift_iff
#print axioms semEqDIK_bot_lift_iff
#print axioms approxDIK_bot_lift0_iff
#print axioms approxDIK_bot_subst_lift_iff
#print axioms approxDIK_bot_instantiate0_iff
#print axioms approxDIK_bot_instantiate_botClosedExpr_iff
#print axioms approxDIK_bot_subst_bvar_iff
#print axioms recCall_const_lift
#print axioms recCall_const_instantiate
#print axioms whStepPiK_lift_of_envClosed
#print axioms whRedPiK_lift_of_envClosed
#print axioms whStepPiK_instantiate_of_botApprox
#print axioms whRedPiK_instantiate_of_botApprox
#print axioms WhStepPiKClosed
#print axioms whStepPiK_of_whStepPiKClosed
#print axioms WhRedPiKClosed
#print axioms whRedPiKClosed_trans
#print axioms whRedPiKClosed_of_whRed
#print axioms whRedPiK_of_whRedPiKClosed
#print axioms whRedPiKClosed_appHead
#print axioms semEqDIK_whStepPiKClosed
#print axioms semEqDIK_whRedPiKClosed
#print axioms approxDIK_whRedPiKClosed_back
#print axioms approxDIK_sort_of_whRedPiKClosed
#print axioms whStepPiKClosed_sort_false
#print axioms whStepPiKClosed_pi_false
#print axioms whStepPiKClosed_lam_false
#print axioms whRedPiKClosed_sort_eq
#print axioms whRedPiKClosed_pi_eq
#print axioms not_whStepPiKClosed_recursor_prefix
#print axioms iotaKClosed_det
#print axioms whStep_and_whStepPiKClosed_det
#print axioms whDetPiKClosed_of_envWfT
#print axioms WhNormalPiKClosed
#print axioms whNormalPiKClosed_sort
#print axioms whNormalPiKClosed_pi
#print axioms whNormalPiKClosed_lam
#print axioms whRedPiKClosed_of_normal
#print axioms whRedPiKClosed_normal_unique_of_envWfT
#print axioms whRedPiKClosed_pi_unique_of_envWfT
#print axioms whRedPiKClosed_sort_unique_of_envWfT
#print axioms whStepPiKClosed_iotaKClosed_of_envWfT
#print axioms whRedPiKClosed_trueEnvU_kRecVar_sort
#print axioms mixAndWClosed
#print axioms whRed_andEnvU_mixAndClosedRhs_mixPi
#print axioms whRedPiKClosed_andEnvU_mixAndRedex_mixPi
#print axioms whStepPiKClosed_lift_of_envClosed
#print axioms whRedPiKClosed_lift_of_envClosed
#print axioms whStepPiKClosed_instantiate_of_botApprox
#print axioms whRedPiKClosed_instantiate_of_botApprox
#print axioms LRTypeINPiKClosed
#print axioms lrTypeINPiKClosed_expand
#print axioms approxDIK_of_lrTypeINPiKClosed_botPiCpt
#print axioms lrTypeINPiKClosed_ctx
#print axioms lrTypeINPiKClosed_assump_dom
#print axioms lrTypeINPiKClosed_symm
#print axioms lrTypeINPiKClosed_trans_of_envWfT
#print axioms lrTypeINPiKClosed_weaken_botPiCpt
#print axioms lrTypeINPiKClosed_weaken0_botPiCpt
#print axioms lrTypeINPiKClosed_subst_botPiCpt
#print axioms lrTypeINPiKClosed_subst0_botPiCpt
#print axioms LRTypeINBiDIKClosed
#print axioms lrTypeINBiDIKClosed_symm
#print axioms lrTypeINBiDIKClosed_trans_of_envWfT
#print axioms lrTypeINBiDIKClosed_weaken0
#print axioms lrTypeINBiDIKClosed_subst0

end Rcic.Declarative.NativeValleys.PiModelDeltaIotaFundAudit
