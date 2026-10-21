import rcic.RcicSynSRClEutConvb

/-!
# RcicSynSRClEutApp — row 15's app-app cell (cc 03:15Z): measurement first

Same method as the convB round, on `EutAppPorts`. The cell's own goal is
the conversion of the two RESULT-SORT typings' erasures (two typings of
DIFFERENT subjects — `instantiate0 a B₁` vs `B₂`): not an issuable edge.
The FUNCTION pair `.eut hf₁ hf₂` and the ARGUMENT pair `.cl ha₁ ha₂` ARE
edges — issued on-cone inside `eut_app_app_caseStepE` over the repaired
closure (`IssuesC.old` + the closer's own rank lemmas). The five retained
ports are measured NOT issuable: `piL`/`piR`/`instL`/`instR` are
`CL`-shaped but one endpoint is off the app payload grid (`wt` shapes);
`hbit` is a `.head`-shaped level fact, erasure-free, and at `σ := id` it
is exactly the eqN residue of the two domains' sort levels
(`levelIsZero` is eqN-exact) — type-uniqueness content (the forbidden
route). Named wall: `EutAppPorts` itself, restated at `tableOfI` as
`eutAppP_tableOfI`; not refuted; nonvacuous (`eutAppPorts_ident_sat`).
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- **The measurement (cc's step 1)**: the app-app `.eut` cell's goal is
    the conversion of the two result-sort typings' erasures — each `app`
    node's `reg.2` IS its own `hT` — two typings of DIFFERENT subjects,
    so the cell's own goal is not an erasure fact about two typings of
    one smaller subject. -/
theorem goal_eut_app_is_result_sort_erasure {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (.eut (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) S σ ρ) =
      ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ) (hT₂.eps σ ρ) := rfl

/-! ## The retained ports, measured -/

/-- `piL`'s goal (by `rfl`): the `ConvMod` between the erasures of
    `hf₁.reg.2` and the EXPLICIT Π-typing — two typings of ONE subject
    `.pi A₁ B₁` (`CL`-shaped), one endpoint on the payload grid
    (`reg.2 ≤ hf₁`), the other off it (the Π-surface typings
    `hA₁ hB₁` the app node does not carry). -/
theorem goal_app_piL_is_reg_pi_erasure {tbl : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A₁ B₁ : Expr Nat} {u₁ v₁ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁))
    (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (σ : Level → Level) (ρ : List Disp) :
    CL tbl σ ρ hf₁.reg.2 (TyP.pi E n Γ A₁ u₁ B₁ v₁ hA₁ hB₁) =
      ConvMod (EStep tbl) LvlEq (hf₁.reg.2.eps σ ρ)
        ((TyP.pi E n Γ A₁ u₁ B₁ v₁ hA₁ hB₁).eps σ ρ) := rfl

/-- `instL`'s goal (by `rfl`): the `ConvMod` between the erasures of the
    app node's OWN result-sort typing `hT₁` (a payload) and the `instEnd`
    composite (a rebuilt `esub`, never a `subAt` position) — two typings
    of ONE subject `instantiate0 a B₁`, one endpoint off the grid. -/
theorem goal_app_instL_is_instEnd_erasure {tbl : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a A₁ B₁ : Expr Nat} {u₁ v₁ w₁ : Level}
    (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (σ : Level → Level) (ρ : List Disp) :
    CL tbl σ ρ hT₁ (instEnd hB₁ ha₁ hA₁) =
      ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ)
        ((instEnd hB₁ ha₁ hA₁).eps σ ρ) := rfl

/-- The app node's payload grid (by `rfl`): exactly `{hf, ha, hT}`. The
    closer's own rank lemmas (`lexDM_both_wt_lt_left/right`,
    `TyP.wt_reg_le`) decrease a pair's key only when BOTH endpoints sit
    strictly under payloads. -/
theorem wt_app_payload_grid (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f a A₁ B₁ : Expr Nat} {w₁ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁)) :
    (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw
      = 1 + hf₁.wt Aw + ha₁.wt Aw + hT₁.wt Aw := rfl

/-- The explicit Π-typing's weight (by `rfl`) rides the Π-surface
    typings `hA₁ hB₁`, which the app node does NOT carry — there is no
    inequality linking this weight to the cell's, so the `piL`/`piR`
    issuance has no rank decrease by the closer's own lemmas. (This is
    exactly why the field's `appP` premise is existential over
    `hA₁ hB₁ hA₂ hB₂`.) -/
theorem wt_pi_surface_off_grid (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A₁ B₁ : Expr Nat} {u₁ v₁ : Level}
    (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁)) :
    (TyP.pi E n Γ A₁ u₁ B₁ v₁ hA₁ hB₁).wt Aw
      = 1 + hA₁.wt Aw + hB₁.wt Aw := rfl

/-! ## `hbit`: a `.head`-shaped level fact, not an erasure fact -/

/-- `hbit`'s Prop is exactly the `.head` query kind's goal (by `rfl`,
    any dummy conversion witnesses): the ONE existing kind whose goal has
    this shape. No `Issues` row issues a `.head` query from an app-app
    `.eut` cell, and the two domains `A₁ A₂` are different subjects, so
    `.bitCoh` (which requires one subject) cannot state it either. -/
theorem hbit_is_head_goal_shape {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {a b A₁ A₂ : Expr Nat} {u : Level} {u₁ u₂ : Level}
    (hc : CvP E n Γ a b (.sort u))
    (hA₁ : TyP E n Γ A₁ (.sort u₁)) (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (.head hc u₁ u₂ hA₁ hA₂ S σ ρ) =
      (levelIsZero (σ u₁) = levelIsZero (σ u₂)) := rfl

/-- `levelIsZero` is eqN-exact, so eqN-related levels always agree in
    zero-ness (the `zeroRank_eqN_invariant` key, at the decider). -/
theorem levelIsZero_eqN {u v : Level} (h : eqN u v) :
    levelIsZero u = levelIsZero v := by
  cases hA : levelIsZero u with
  | true =>
      have hB : levelIsZero v = true :=
        (levelIsZero_iff v).mpr
          (fun ρ => (h ρ).symm.trans ((levelIsZero_iff u).mp hA ρ))
      rw [hB]
  | false =>
      cases hB : levelIsZero v with
      | false => rfl
      | true =>
          exfalso
          have hA' : levelIsZero u = true :=
            (levelIsZero_iff u).mpr
              (fun ρ => (h ρ).trans ((levelIsZero_iff v).mp hB ρ))
          rw [hA] at hA'
          exact Bool.noConfusion hA'

/-! ## The cell over the repaired closure -/

/-- **The app-app cell over the repaired closure** (`DemandC`, cc 03:15Z):
    the FUNCTION pair `.eut hf₁ hf₂` and the ARGUMENT pair `.cl ha₁ ha₂`
    are issued on-cone (the LANDED `occ_eut`/`occ_cl` rows at
    `(0,[0])×(1,[0])`/`(0,[1])×(1,[1])`, rank by the closer's own
    `TyP.wt` shapes through `lexDM_wt_lt_pair`/`lexDM_combMeas_mono`);
    everything else the landed `eut_app_nodes_drop/keep` consumes is the
    ONE named wall `EutAppPorts` (its `hW` is table data — at the row
    instantiation `tbl := tableOfI hW` it is `tableWF_tableOfI_full`). -/
theorem eut_app_app_caseStepE (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {f a A₁ B₁ A₂ B₂ : Expr Nat} {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : EutAppPorts tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ hA₁ hB₁ hA₂ hB₂) :
    CaseStepC Aw tbl
      (.eut (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) S σ ρ) := by
  intro hq ih
  have hwf₁ : hf₁.wt Aw < (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hwf₂ : hf₂.wt Aw < (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hwa₁ : ha₁.wt Aw < (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hwa₂ : ha₂.wt Aw < (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlexf : LexDM (tyPairMeas Aw hf₁ hf₂)
      (tyPairMeas Aw (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂)) :=
    lexDM_wt_lt_pair Aw hf₁ hf₂ _ _ rfl rfl hwf₁ hwf₂
  have heutf := ih_localC Aw tbl hq ih (.eut hf₁ hf₂ S σ ρ)
    (IssuesC.old (Issues.occ_eut (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      (DemandC.ap hq).1.1 (DemandC.ap hq).2.1)) rfl
    (lexDM_combMeas_mono Aw _ hlexf)
  cases hu : levelIsZero (σ u₁) with
  | true =>
      exact eut_app_nodes_drop ports.hW σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂
        hA₁ hB₁ hA₂ hB₂ hu ports.hbit heutf ports.piL ports.piR
        ports.instL ports.instR
  | false =>
      have hlexa : LexDM (tyPairMeas Aw ha₁ ha₂)
          (tyPairMeas Aw (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
            (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂)) :=
        lexDM_wt_lt_pair Aw ha₁ ha₂ _ _ rfl rfl hwa₁ hwa₂
      have hcla := ih_localC Aw tbl hq ih (.cl ha₁ ha₂ S σ ρ)
        (IssuesC.old (Issues.occ_cl (k₁ := 0) (p₁ := [1]) (k₂ := 1) (p₂ := [1]) rfl rfl
          (DemandC.ap hq).1.2.1 (DemandC.ap hq).2.2.1)) rfl
        (lexDM_combMeas_mono Aw _ hlexa)
      exact eut_app_nodes_keep ports.hW σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂
        hA₁ hB₁ hA₂ hB₂ hu ports.hbit heutf hcla ports.piL ports.piR
        ports.instL ports.instR

/-! ## The named wall, and its nonvacuity -/

/-- The row-15 `appP` premise shape, exact, at `tbl := tableOfI hW` —
    the ONE named Prop the app-app cell retains. NOT claimed, NOT
    refuted: `hbit` is the type-uniqueness residue (a `LevelHom` fixes
    every closed level and `levelIsZero` is eqN-exact, so no on-cone
    falsity route exists without splitting eqN-related stored levels);
    `piL`/`piR`/`instL`/`instR` are off-grid `CL`-shaped pairings. -/
def eutAppP_tableOfI {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E' n Γ f (.pi A₁ B₁)) (ha₁ : TyP E' n Γ a A₁)
    (hT₁ : TyP E' n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E' n Γ f (.pi A₂ B₂)) (ha₂ : TyP E' n Γ a A₂)
    (hT₂ : TyP E' n Γ (instantiate0 a B₂) (.sort w₂))
    {σ : Level → Level} {ρ : List Disp},
    ∃ (u₁' v₁' u₂' v₂' : Level) (hA₁ : TyP E' n Γ A₁ (.sort u₁'))
      (hB₁ : TyP E' n (.assumption A₁ :: Γ) B₁ (.sort v₁'))
      (hA₂ : TyP E' n Γ A₂ (.sort u₂'))
      (hB₂ : TyP E' n (.assumption A₂ :: Γ) B₂ (.sort v₂')),
      EutAppPorts (tableOfI hW) σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ hA₁ hB₁ hA₂ hB₂

/-- The named wall is not vacuous: at the identical instance — the same
    `lam` function typing on both sides, `hT := instEnd hB ha hA` — every
    field holds definitionally (`reg` of a `lam` IS its explicit Π,
    `hbit` is `rfl`, the four `CL`s are reflexive). -/
theorem eutAppPorts_ident_sat {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B a : Expr Nat}
    {u v : Level} {σ : Level → Level} {ρ : List Disp}
    (hA : TyP E n Γ A (.sort u)) (hb : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) (ha : TyP E n Γ a A) :
    EutAppPorts tbl σ ρ
      (TyP.lam E n Γ A u body B v hA hb hB) ha (instEnd hB ha hA)
      (TyP.lam E n Γ A u body B v hA hb hB) ha (instEnd hB ha hA)
      hA hB hA hB :=
  ⟨hW, rfl, ConvMod.refl _, ConvMod.refl _, ConvMod.refl _, ConvMod.refl _⟩

/-! ## cc 05:45Z ask 1: is what remains (after `.eut hf₁ hf₂`) erased
Π-injectivity? Measured: NO — injectivity is LANDED and consumed by the
closer; what remains is the Π-PAIRING ConvMod (the input side of
injectivity) plus the instEnd bridges and `hbit`. -/

/-- Erasure Π-injectivity at `tbl := tableOfI hW` is SUPPLIED, not a
    wall: the landed `convE_pi_inv_wf` (`S0` §2.4 item 2, proven from
    landed confluence `confluent_eStep_wf`) applies with `TableWF` free
    via `tableWF_tableOfI_full`. So a Church–Rosser supply (glm-sr1's
    test) adds nothing to this cell; the hypothesized `ConvModPiInjW`
    wall would name an already-supplied fact. -/
theorem piInj_landed_at_tableOfI {E : ResolvedEnv} (hW : EnvWfT E)
    {A B A' B' : ETm}
    (h : ConvMod (EStep (tableOfI hW)) LvlEq (.pi A B) (.pi A' B')) :
    ConvMod (EStep (tableOfI hW)) LvlEq B B' :=
  (convE_pi_inv_wf (tableWF_tableOfI_full hW) h).2

/-- The closer consumes `piL ∘ heutf ∘ piR` as ONE `ConvMod` (its own
    proof body, extracted): given the issued `.eut hf₁ hf₂` edge, the two
    Π ports compose into the single Π-pairing ConvMod — the INPUT side of
    the (landed, see `piInj_landed_at_tableOfI`) erasure
    Π-injectivity. Drop branch (`levelIsZero (σ u₁) = true`). -/
theorem convPiDrop_of_piL_eut_piR {tbl : List CRule} {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    {σ : Level → Level} {ρ : List Disp}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁)) (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A₂ (.sort u₂)) (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂))
    (hu₁ : levelIsZero (σ u₁) = true) (hu₂ : levelIsZero (σ u₂) = true)
    (hpi₁ : CL tbl σ ρ hf₁.reg.2 (TyP.pi E n Γ A₁ u₁ B₁ v₁ hA₁ hB₁))
    (heutf : EUT tbl σ ρ hf₁ hf₂)
    (hpi₂ : CL tbl σ ρ (TyP.pi E n Γ A₂ u₂ B₂ v₂ hA₂ hB₂) hf₂.reg.2) :
    ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (piSlot true (hB₁.eps σ (.drop :: ρ))))
      (.pi (hA₂.eps σ ρ) (piSlot true (hB₂.eps σ (.drop :: ρ)))) := by
  have h1 : ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (piSlot true (hB₁.eps σ (.drop :: ρ)))) (hf₁.reg.2.eps σ ρ) := by
    have h := ConvMod.symm' LvlEq.symm' hpi₁
    simpa only [CL, eps_pi_drop hu₁] using h
  have h2 : ConvMod (EStep tbl) LvlEq
      (hf₂.reg.2.eps σ ρ) (.pi (hA₂.eps σ ρ) (piSlot true (hB₂.eps σ (.drop :: ρ)))) := by
    have h := ConvMod.symm' LvlEq.symm' hpi₂
    simpa only [CL, eps_pi_drop hu₂] using h
  exact h1.trans (heutf.trans h2)

/-- Keep-branch twin of `convPiDrop_of_piL_eut_piR` (`eps_pi_keep`: the
    codomain slot is the plain `.keep :: ρ` erasure, no `piSlot`). -/
theorem convPiKeep_of_piL_eut_piR {tbl : List CRule} {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    {σ : Level → Level} {ρ : List Disp}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁)) (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A₂ (.sort u₂)) (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂))
    (hu₁ : levelIsZero (σ u₁) = false) (hu₂ : levelIsZero (σ u₂) = false)
    (hpi₁ : CL tbl σ ρ hf₁.reg.2 (TyP.pi E n Γ A₁ u₁ B₁ v₁ hA₁ hB₁))
    (heutf : EUT tbl σ ρ hf₁ hf₂)
    (hpi₂ : CL tbl σ ρ (TyP.pi E n Γ A₂ u₂ B₂ v₂ hA₂ hB₂) hf₂.reg.2) :
    ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (hB₁.eps σ (.keep :: ρ)))
      (.pi (hA₂.eps σ ρ) (hB₂.eps σ (.keep :: ρ))) := by
  have h1 : ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (hB₁.eps σ (.keep :: ρ))) (hf₁.reg.2.eps σ ρ) := by
    have h := ConvMod.symm' LvlEq.symm' hpi₁
    simpa only [CL, eps_pi_keep hu₁] using h
  have h2 : ConvMod (EStep tbl) LvlEq
      (hf₂.reg.2.eps σ ρ) (.pi (hA₂.eps σ ρ) (hB₂.eps σ (.keep :: ρ))) := by
    have h := ConvMod.symm' LvlEq.symm' hpi₂
    simpa only [CL, eps_pi_keep hu₂] using h
  exact h1.trans (heutf.trans h2)

/-- The drop cell from the ONE Π-pairing `ConvMod` + the instEnd
    bridges + `hbit`: the issued `.eut hf₁ hf₂` edge and the `piL`/`piR`
    ports are consumed EXACTLY as that one ConvMod (they are absent
    here). Π-injectivity inside is landed (`convE_pi_inv_wf`). This is
    `eut_app_nodes_drop`'s tail with `heutf`/`hpi₁`/`hpi₂` removed. -/
theorem eut_app_drop_of_convPi {tbl : List CRule} (hW : TableWF tbl)
    (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat}
    {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁)) (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A₂ (.sort u₂)) (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂))
    (hu₁ : levelIsZero (σ u₁) = true) (hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂))
    (hconvPi : ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (piSlot true (hB₁.eps σ (.drop :: ρ))))
      (.pi (hA₂.eps σ ρ) (piSlot true (hB₂.eps σ (.drop :: ρ)))))
    (hinst₁ : CL tbl σ ρ hT₁ (instEnd hB₁ ha₁ hA₁))
    (hinst₂ : CL tbl σ ρ (instEnd hB₂ ha₂ hA₂) hT₂) :
    EUT tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  have hu₂ : levelIsZero (σ u₂) = true := hbit.symm.trans hu₁
  have hBconv := convMod_unpiSlot hW.closed (convE_pi_inv_wf hW hconvPi).2
  have h1 : ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ) (hB₁.eps σ (.drop :: ρ)) := by
    simpa only [CL, instEnd_eps_drop hB₁ ha₁ hA₁ hu₁] using hinst₁
  have h2 : ConvMod (EStep tbl) LvlEq (hB₂.eps σ (.drop :: ρ)) (hT₂.eps σ ρ) := by
    simpa only [CL, instEnd_eps_drop hB₂ ha₂ hA₂ hu₂] using hinst₂
  exact h1.trans (hBconv.trans h2)

/-- Keep-branch twin: from the ONE Π-pairing `ConvMod` (`.keep :: ρ`
    shape) + the instEnd bridges + `hbit` + the issued argument edge
    `hcla : CL ha₁ ha₂` (on-cone in `eut_app_app_caseStepE`). The `hmid`
    step is `eut_app_nodes_keep`'s own `convMod_inst_body` ∘
    `convMod_inst_repl` — the value/codomain congruence, TableClosed. -/
theorem eut_app_keep_of_convPi {tbl : List CRule} (hW : TableWF tbl)
    (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat}
    {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁)) (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A₂ (.sort u₂)) (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂))
    (hu₁ : levelIsZero (σ u₁) = false) (hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂))
    (hconvPi : ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (hB₁.eps σ (.keep :: ρ)))
      (.pi (hA₂.eps σ ρ) (hB₂.eps σ (.keep :: ρ))))
    (hcla : CL tbl σ ρ ha₁ ha₂)
    (hinst₁ : CL tbl σ ρ hT₁ (instEnd hB₁ ha₁ hA₁))
    (hinst₂ : CL tbl σ ρ (instEnd hB₂ ha₂ hA₂) hT₂) :
    EUT tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  have hu₂ : levelIsZero (σ u₂) = false := hbit.symm.trans hu₁
  have hBconv := (convE_pi_inv_wf hW hconvPi).2
  have hmid : ConvMod (EStep tbl) LvlEq
      (ETm.inst 0 (ha₁.eps σ ρ) (hB₁.eps σ (.keep :: ρ)))
      (ETm.inst 0 (ha₂.eps σ ρ) (hB₂.eps σ (.keep :: ρ))) :=
    (convMod_inst_body hW.closed hBconv 0 (ha₁.eps σ ρ)).trans
      (convMod_inst_repl hW.closed hcla (hB₂.eps σ (.keep :: ρ)) 0)
  have h1 : ConvMod (EStep tbl) LvlEq
      (hT₁.eps σ ρ) (ETm.inst 0 (ha₁.eps σ ρ) (hB₁.eps σ (.keep :: ρ))) := by
    simpa only [CL, instEnd_eps_keep hB₁ ha₁ hA₁ hu₁] using hinst₁
  have h2 : ConvMod (EStep tbl) LvlEq
      (ETm.inst 0 (ha₂.eps σ ρ) (hB₂.eps σ (.keep :: ρ))) (hT₂.eps σ ρ) := by
    simpa only [CL, instEnd_eps_keep hB₂ ha₂ hA₂ hu₂] using hinst₂
  exact h1.trans (hmid.trans h2)

#print axioms Rcic.Syn.goal_eut_app_is_result_sort_erasure
#print axioms Rcic.Syn.goal_app_piL_is_reg_pi_erasure
#print axioms Rcic.Syn.goal_app_instL_is_instEnd_erasure
#print axioms Rcic.Syn.wt_app_payload_grid
#print axioms Rcic.Syn.wt_pi_surface_off_grid
#print axioms Rcic.Syn.hbit_is_head_goal_shape
#print axioms Rcic.Syn.levelIsZero_eqN
#print axioms Rcic.Syn.eut_app_app_caseStepE
#print axioms Rcic.Syn.eutAppP_tableOfI
#print axioms Rcic.Syn.eutAppPorts_ident_sat
#print axioms Rcic.Syn.piInj_landed_at_tableOfI
#print axioms Rcic.Syn.convPiDrop_of_piL_eut_piR
#print axioms Rcic.Syn.convPiKeep_of_piL_eut_piR
#print axioms Rcic.Syn.eut_app_drop_of_convPi
#print axioms Rcic.Syn.eut_app_keep_of_convPi

end Rcic.Syn
