import rcic.RcicSynSRBetaZetaStepW
import rcic.RcicSynSRBetaZetaEpsWWedge
import rcic.RcicSynBelowCToRows

/-!
# The boundary: recovering the eps-stated goals from the epsW pack

The top-level sortRow goal (`sortRow_of_suppliers_tableOfI` and its consumers)
extracts from `AllBelowScoped` at the canonical display `S.can σ`, over the
derivations the enriched native spine supplies. On that class the eps-stated
goals follow from the epsW-stated ones wherever `epsW_eq_eps_closed` reaches:
a `ClosedWf` endpoint at a shaped display. Deliverables:

* `dispShape_can` — the canonical display is always shaped.
* `es_of_allBelowScopedW` / `cl_…` / `eut_…` / `pbit_…` — the four extractors,
  `ClosedWf`-conditioned per endpoint.
* `TyCvP.AllCW` / `endpointsR_closed` / `esChain_of_allBelowScopedW` — the
  ESChain assembler carrying per-link endpoint `ClosedWf`.
* `sortRow_of_allBelowScopedW` — the eps-stated `eqN u v` from the epsW pack;
  the per-link `ClosedWf` conditions are exactly `closedWf_enrichConvT`
  (helper-ClosedWf of the enrichment constructors), the named open discharge.
* The kernel facts: the canonical-display wedge point where `epsW ≠ eps`
  (`boundary_epsW_ne_eps`), and `not_assumpPref_wkZetaNode` — that point is
  NOT in the `BelowScoped` class, so the in-class unconditional transfer
  (an AP×inline co-induction) stays open, honestly. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the canonical display is shaped -/

/-- `S.can σ` is a shaped display of `Γ` (the canonical disposition of the
    scoped context's own witnesses). -/
theorem dispShape_can {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) : DispShape Γ (S.can σ) :=
  dispShape_of_ctxP σ (enrichCtxWfT_of_envWfT S.env S.ctx)

/-! ## §2 the extractors, `ClosedWf`-conditioned -/

/-- `ES` at the canonical display from `ESW`, when both endpoints are
    `ClosedWf` (then `epsW` **is** `eps` at every shaped display). -/
theorem es_of_allBelowScopedW {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScopedW Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {a b T : Expr Nat}
    (h : CvP E n Γ a b T) (hAP : h.AssumpPref)
    (hdl : h.dl.ClosedWf) (hdr : h.dr.ClosedWf) : ES tbl σ (S.can σ) h := by
  have hw := (hBel ((cvMeas Aw h).1, (cvMeas Aw h).2 + 1)).es h hAP S σ hσ
    (lexDM_succ_snd (cvMeas Aw h))
  have hl := epsW_eq_eps_closed h.dl hdl σ (S.can σ) (dispShape_can S σ)
  have hr := epsW_eq_eps_closed h.dr hdr σ (S.can σ) (dispShape_can S σ)
  unfold ESW at hw
  rw [hl, hr] at hw
  exact hw

/-- `CL` at the canonical display from `CLW`, both endpoints `ClosedWf`. -/
theorem cl_of_allBelowScopedW {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScopedW Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
    (hc₁ : D₁.ClosedWf) (hc₂ : D₂.ClosedWf) : CL tbl σ (S.can σ) D₁ D₂ := by
  have hw := (hBel ((tyPairMeas Aw D₁ D₂).1, (tyPairMeas Aw D₁ D₂).2 + 1)).cl
    D₁ D₂ h₁ h₂ S σ hσ (lexDM_succ_snd (tyPairMeas Aw D₁ D₂))
  have hl := epsW_eq_eps_closed D₁ hc₁ σ (S.can σ) (dispShape_can S σ)
  have hr := epsW_eq_eps_closed D₂ hc₂ σ (S.can σ) (dispShape_can S σ)
  unfold CLW at hw
  rw [hl, hr] at hw
  exact hw

/-- `EUT` at the canonical display from `EUTW`, both reg endpoints
    `ClosedWf`. -/
theorem eut_of_allBelowScopedW {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScopedW Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
    (hc₁ : D₁.reg.2.ClosedWf) (hc₂ : D₂.reg.2.ClosedWf) :
    EUT tbl σ (S.can σ) D₁ D₂ := by
  have hw := (hBel ((tyPairMeas Aw D₁ D₂).1, (tyPairMeas Aw D₁ D₂).2 + 1)).eut
    D₁ D₂ h₁ h₂ S σ hσ (lexDM_succ_snd (tyPairMeas Aw D₁ D₂))
  have hl := epsW_eq_eps_closed D₁.reg.2 hc₁ σ (S.can σ) (dispShape_can S σ)
  have hr := epsW_eq_eps_closed D₂.reg.2 hc₂ σ (S.can σ) (dispShape_can S σ)
  unfold EUTW at hw
  rw [hl, hr] at hw
  exact hw

/-- `PBit` at the canonical display from `PBitW`, the derivation `ClosedWf`. -/
theorem pbit_of_allBelowScopedW {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {Aw : Nat → Nat} {tbl : List CRule} (hBel : AllBelowScopedW Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    (hD : D.AssumpPref) (hDT : DT.AssumpPref)
    (hc : D.ClosedWf) : PBit σ (S.can σ) D DT := by
  have hw := (hBel ((tyPairMeas Aw D DT).1, (tyPairMeas Aw D DT).2 + 1)).pb
    D DT hD hDT S σ hσ (lexDM_succ_snd (tyPairMeas Aw D DT))
  have hl := epsW_eq_eps_closed D hc σ (S.can σ) (dispShape_can S σ)
  unfold PBitW at hw
  rw [hl] at hw
  exact hw

/-! ## §3 the chain, carrying per-link endpoint `ClosedWf` -/

/-- Endpoint closedness along a `TyCvP` chain, mirroring `AllAP`. -/
def TyCvP.AllCW {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {A B : Expr Nat} → TyCvP E n Γ A B → Prop
  | _, _, .refl _ _ => True
  | _, _, .of _ _ _ _ h => h.dl.ClosedWf ∧ h.dr.ClosedWf
  | _, _, .trans _ _ _ _ c₁ c₂ => c₁.AllCW ∧ c₂.AllCW

/-- The `endpointsR` reading, carrying `ClosedWf` alongside `AssumpPref`. -/
def TyCvP.endpointsRC {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {A B : Expr Nat} → (c : TyCvP E n Γ A B) → c.AllAP → c.AllCW →
      PSum (A = B)
        ((uR : Level) ×' (dR : TyP E n Γ B (.sort uR)) ×' dR.AssumpPref ×' dR.ClosedWf)
  | _, _, .refl _ _, _, _ => .inl rfl
  | _, _, .of _ _ _ _ h, hAP, hcc => .inr ⟨_, h.dr, assumpPref_dr hAP, hcc.2⟩
  | _, _, .trans _ _ _ _ c₁ c₂, hc, hcc =>
      match h1 : endpointsRC c₁ hc.1 hcc.1, h2 : endpointsRC c₂ hc.2 hcc.2 with
      | .inl h₁, .inl h₂ => .inl (h₁.trans h₂)
      | .inl _, .inr q => .inr q
      | .inr ⟨uR₁, dR₁, hd₁⟩, .inl h₂ =>
          .inr ⟨uR₁, tyCast h₂ rfl dR₁, assumpPref_tyCast h₂ rfl hd₁.1,
            closedWf_tyCast h₂ rfl hd₁.2⟩
      | .inr _, .inr q => .inr q

/-- **The scoped ESChain assembler at `epsW`.** Same shape as the landed
    `esChain_of_allBelowScoped`; each `.of` link's `ES`/`CL` answers come from
    the epsW pack through the `ClosedWf`-conditioned extractors, so the chain
    carries `AllCW` (and the outer endpoints' `ClosedWf`) as hypotheses. -/
theorem esChain_of_allBelowScopedW {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScopedW Eₐ Aw tbl) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (S : ScopedCtx Eₐ E n Γ) {σ : Level → Level} (hσ : LevelHom σ) :
    ∀ {A B T₁ T₂ : Expr Nat} (c : TyCvP E n Γ A B), c.AllAP → c.AllCW →
      (dA : TyP E n Γ A T₁) → dA.AssumpPref → dA.ClosedWf →
      (dB : TyP E n Γ B T₂) → dB.AssumpPref → dB.ClosedWf →
      TyCvP.ESChain tbl σ (S.can σ) c dA dB
  | _, _, _, _, .refl _ _, _, _, dA, hA, hcA, dB, hB, hcB =>
      .refl dA dB
        (cl_of_allBelowScopedW hBel S hσ dA dB hA hB hcA hcB)
  | _, _, _, _, .of _ _ _ _ h, hAP, hcc, dA, hA, hcA, dB, hB, hcB =>
      .of h dA dB
        (cl_of_allBelowScopedW hBel S hσ dA h.dl hA (assumpPref_dl hAP) hcA hcc.1)
        (es_of_allBelowScopedW hBel S hσ h hAP hcc.1 hcc.2)
        (cl_of_allBelowScopedW hBel S hσ h.dr dB (assumpPref_dr hAP) hB hcc.2 hcB)
  | _, _, _, _, .trans _ _ _ _ c₁ c₂, hc, hcc, dA, hA, hcA, dB, hB, hcB =>
      match h1 : TyCvP.endpointsRC c₁ hc.1 hcc.1 with
      | .inl hAB =>
          have hdA' : (tyCast hAB rfl dA).AssumpPref := assumpPref_tyCast hAB rfl hA
          have hcA' : (tyCast hAB rfl dA).ClosedWf := closedWf_tyCast hAB rfl hcA
          .trans c₁ c₂ dA (tyCast hAB rfl dA) dB
            (esChain_of_allBelowScopedW hBel S hσ c₁ hc.1 hcc.1 dA hA hcA
              (tyCast hAB rfl dA) hdA' hcA')
            (esChain_of_allBelowScopedW hBel S hσ c₂ hc.2 hcc.2
              (tyCast hAB rfl dA) hdA' hcA' dB hB hcB)
      | .inr ⟨_, dR₁, hdR₁⟩ =>
          .trans c₁ c₂ dA dR₁ dB
            (esChain_of_allBelowScopedW hBel S hσ c₁ hc.1 hcc.1 dA hA hcA dR₁ hdR₁.1 hdR₁.2)
            (esChain_of_allBelowScopedW hBel S hσ c₂ hc.2 hcc.2 dR₁ hdR₁.1 hdR₁.2 dB hB hcB)

/-! ## §4 the sortRow boundary -/

/-- The eps-stated `sortRow` goal from the epsW pack: exactly
    `sortRow_of_allBelowScoped`'s shape, with the per-link endpoint `ClosedWf`
    of the enriched chain made an explicit hypothesis. Discharging that
    hypothesis for the enrichment (`closedWf_enrichConvT` — the helper-ClosedWf
    of `betaLeftP`/`instEnd`/`trZeta`/… , mutual with `enrichHasTyT`) is the
    named open gap; `closedWf_enrichHasTyT` already covers every endpoint the
    enrichment reads off a plain `HasTyT`. -/
theorem sortRow_of_allBelowScopedW {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScopedW Eₐ Aw tbl) (hTbl : TableWF tbl)
    (hW : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level}
    (h : TyConvT E n Γ (.sort u) (.sort v))
    (hCW : (enrichTyConvT_of_envWfT hW hΓ h).AllCW) : eqN u v :=
  let S : ScopedCtx Eₐ E n Γ := ⟨hW, hext, hΓ⟩
  sortRow_of_tyCvP_esChain_id hTbl (enrichTyConvT_of_envWfT hW hΓ h) (S.can id)
    (esChain_of_allBelowScopedW hBel S levelHom_id _
      (enrichTyConvT_of_envWfT_allAP hW (memberSortP_of_envWfT_ap hW) hΓ h) hCW
      (TyP.sort E n Γ u (.succ u) (eqN_refl _)) trivial trivial
      (TyP.sort E n Γ v (.succ v) (eqN_refl _)) trivial trivial)

/-! ## §5 the boundary's kernel facts -/

/-- The wedge context is a genuine well-formed native context. -/
def wkZetaCtxWfT (E : ResolvedEnv) (n : Nat) : CtxWfT E n wkZetaCtx :=
  CtxWfT.letBinding [.assumption (.sort (.succ .zero)),
      .assumption (.sort (.succ .zero))]
    (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 1)
    (CtxWfT.assumption [.assumption (.sort (.succ .zero))]
      (.sort (.succ .zero)) (.succ (.succ .zero))
      (CtxWfT.assumption [] (.sort (.succ .zero)) (.succ (.succ .zero))
        (CtxWfT.nil)
        (HasTyT.sort [] (.succ .zero)))
      (HasTyT.sort [.assumption (.sort (.succ .zero))] (.succ .zero)))
    (HasTyT.sort [.assumption (.sort (.succ .zero)),
      .assumption (.sort (.succ .zero))] (.succ .zero))
    (HasTyT.bvar [.assumption (.sort (.succ .zero)),
      .assumption (.sort (.succ .zero))] 1 (.sort (.succ .zero)) rfl)

/-- The scoped home of the wedge: a genuine `ScopedCtx` at `emptyEnv`. -/
def wkZetaScoped : ScopedCtx emptyEnv emptyEnv 0 wkZetaCtx :=
  ⟨EnvWfT.empty, envExt_refl emptyEnv, wkZetaCtxWfT emptyEnv 0⟩

/-- The scoped canonical display of the wedge context IS the canonical Entry
    disposition the refutations use. -/
theorem wkZetaScoped_can :
    wkZetaScoped.can id = (wkZetaCtxP emptyEnv 0).disp id := rfl

/-- **The boundary kernel fact.** An inhabited scoped point — a `ScopedCtx`,
    `LevelHom id`, `DispFor`-valid canonical display — where `epsW` and `eps`
    genuinely differ on a derivation endpoint. This is where an unconditional
    `AllBelowScopedW → AllBelowScoped` transfer would have to do real work:
    the display is canonical, the erasures are not equal. -/
theorem boundary_epsW_ne_eps :
    (wkZetaNode emptyEnv 0).dl.epsW id (wkZetaScoped.can id) ≠
      (wkZetaNode emptyEnv 0).dl.eps id (wkZetaScoped.can id) := by
  rw [wkZetaScoped_can]
  rw [epsW_wkZetaNode_dl_general emptyEnv 0]
  have hl : (wkZetaNode emptyEnv 0).dl.eps id ((wkZetaCtxP emptyEnv 0).disp id)
      = ETm.bvar 2 := rfl
  rw [hl]
  decide

/-- The wedge node is **not** in the `BelowScoped` class: `CvP.wk` at `c = 1`
    over a `.letBinding` at `0` fails `AssumptionPrefix`, hence `AssumpPref`.
    The in-class unconditional transfer (an AP×inline co-induction) is the
    honest open boundary; no in-class `epsW ≠ eps` point is known. -/
theorem not_assumpPref_wkZetaNode (E : ResolvedEnv) (n : Nat) :
    ¬ (wkZetaNode E n).AssumpPref := by
  intro h
  obtain ⟨hap, _⟩ := h
  exact not_assumptionPrefix_zetaLetCtx_one hap

end Rcic.Syn

#print axioms Rcic.Syn.dispShape_can
#print axioms Rcic.Syn.es_of_allBelowScopedW
#print axioms Rcic.Syn.cl_of_allBelowScopedW
#print axioms Rcic.Syn.eut_of_allBelowScopedW
#print axioms Rcic.Syn.pbit_of_allBelowScopedW
#print axioms Rcic.Syn.TyCvP.endpointsRC
#print axioms Rcic.Syn.esChain_of_allBelowScopedW
#print axioms Rcic.Syn.sortRow_of_allBelowScopedW
#print axioms Rcic.Syn.wkZetaScoped_can
#print axioms Rcic.Syn.boundary_epsW_ne_eps
#print axioms Rcic.Syn.not_assumpPref_wkZetaNode
