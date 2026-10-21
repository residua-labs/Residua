import rcic.RcicSynStepPortsClEut
import rcic.RcicSynSortPBit
import rcic.RcicSynPack
import rcic.RcicSynTableOfIFull
import rcic.RcicSynSRClEutEutCase
import rcic.RcicSynSREut
import rcic.RcicSynSRClEutLhomStep

/-!
# RcicSynSRClEutLhomEut — the SIGMA GAP on row 15 (`eut_case`), supplier side

`es_eut_field`'s port premises quantify over ARBITRARY `σ : Level → Level`.
The consumer (`step_of_suppliers`, via `Demand.hom`) only instantiates
`LevelHom σ` — `RcicSynSRClEutLhomStep` patches the field application — so
the supplier is restated here under that exact hypothesis (new name
`es_eut_field_lhom`; the landed statement is untouched): every port premise
is gated `LevelHom σ`, and the conclusion holds at every `LevelHom σ`.

Verdicts at `tbl := tableOfI hW` under the gate:

* `lamP` stays REFUTED — the #7781 fixtures (`hs0s`/`hs1s`, `σ := id`,
  `ρ := []`) carry `levelHom_id`, so the gated supply is false by the same
  closed instance (`eutLamP_lhom_tableOfI_empty_refuted`). This is NOT a
  strawman: the refuting `σ` is a `LevelHom`.
* `piP` is NOT refuted at the gate: #7788's distinguishing fixture closes
  (`sreutσ` is not a `LevelHom`; at one, `cohB` is `eqN`-transported by
  `LevelHom.eqN_map` — `sortCoh_of_eqN_lhom`). The gated wall is #7788's
  landed `eutPiP_wall`, imported, not restated.
* `eutOther` restated under the gate as `eutResidualWallLhom` (the #7788
  `eutResidualWall` restricted to `LevelHom σ`), tooth included.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins (two hs0s hs1s)

variable {E : ResolvedEnv} {Eₐ : ResolvedEnv}

/-- **`eut_case` gated**: the exact `es_eut_field` port bundle with every
    `σ`-quantified premise restricted to `LevelHom σ`, concluding the gated
    field shape `GatedEutCase` — the constraint every demanded `.eut` cell
    carries. -/
theorem es_eut_field_lhom (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (convL : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat}
        {u : Level} (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        EutConvLPorts tbl σ ρ h hc)
    (convR : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat}
        {u : Level} (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        EutConvRPorts tbl σ ρ h hc)
    (piP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
        {u₁ u₂ v₁ v₂ : Level}
        (hA₁ : TyP E n Γ A (.sort u₁))
        (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
        (hA₂ : TyP E n Γ A (.sort u₂))
        (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        EutPiPorts tbl σ ρ hA₁ hB₁ hA₂ hB₂)
    (lamP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B₁ B₂ : Expr Nat}
        {u₁ : Level} {v₁ v₂ : Level}
        (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
        (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        EutLamPorts tbl σ ρ u₁ hB₁ hB₂)
    (appP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
        {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
        (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
        (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
        (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
        (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        ∃ (u₁' v₁' u₂' v₂' : Level) (hA₁ : TyP E n Γ A₁ (.sort u₁'))
          (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁'))
          (hA₂ : TyP E n Γ A₂ (.sort u₂'))
          (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂')),
          EutAppPorts tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ hA₁ hB₁ hA₂ hB₂)
    (letP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
        {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
        (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
        (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
        (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
        (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
        (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
        (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        EutLetEPorts tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂)
    (constP : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
        {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
        (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
        (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        EutConstPorts Aw tbl σ ρ r hT₁ hT₂)
    (eutOther : ∀ {E : ResolvedEnv} {n : Nat}
        {Γ Γ₁ Γ₂ : LCtx} {e e₁ e₂ T₁ T₂ : Expr Nat}
        {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
        (D₁ : TyP E n Γ₁ e₁ T₁) (D₂ : TyP E n Γ₂ e₂ T₂)
        (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
        (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (hσ : LevelHom σ)
        (ρ : List Disp),
        eutResidualTag D₁.headTag D₂.headTag = true →
        CaseStep Aw tbl (.eut (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ)) :
    GatedEutCase Aw tbl Eₐ := by
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ hσ ρ
  -- Same constCell bridge as the landed proof, with the gate carried at the
  -- fixed outer `σ`; `portsFn` needs no gate of its own (σ is fixed here).
  have constCell : ∀ {r ls ls₁ ls₂ : _} {m₁ m₂ : CheckedMember}
      {u₁ u₂ : Level}
      (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
      (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
      (hT₁ : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁))
      (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
      (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
      (hT₂ : TyP E n Γ (instantiateLevels ls₂ m₂.mtype) (.sort u₂))
      (S' : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ' : Level → Level) (_hσ' : LevelHom σ')
      (ρ' : List Disp),
      (∀ {u₁' u₂' : Level}
        (hT₁' : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁'))
        (hT₂' : TyP E n Γ (instantiateLevels ls₂ m₁.mtype) (.sort u₂')),
        EutConstPorts Aw tbl σ' ρ' r hT₁' hT₂') →
      CaseStep Aw tbl (.eut (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁
          hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S' σ' ρ') := by
    intro r ls ls₁ ls₂ m₁ m₂ u₁ u₂ hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ S' σ' _hσ' ρ' portsFn
    have hm : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
    subst hm
    exact eut_const_const_caseStep_of_port Aw tbl hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ S' σ' ρ' (portsFn hT₁ hT₂)
  -- double convoy, exactly the landed `aux`: the gate flows through the
  -- outer `σ`; only the ported arms change (each now passes `hσ`).
  have aux : ∀ {Γ₁ Γ₂ : LCtx} {e₁ e₂ T₁ T₂ : Expr Nat}
      (D₁' : TyP E n Γ₁ e₁ T₁) (D₂' : TyP E n Γ₂ e₂ T₂)
      (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
      {D₁'' : TyP E n Γ e T₁} {D₂'' : TyP E n Γ e T₂}
      (_ : D₁'' = hΓ₁ ▸ he₁ ▸ D₁') (_ : D₂'' = hΓ₂ ▸ he₂ ▸ D₂'),
      CaseStep Aw tbl (.eut D₁'' D₂'' S σ ρ) := by
    intro Γ₁ Γ₂ e₁ e₂ T₁ T₂ D₁' D₂' hΓ₁ he₁ hΓ₂ he₂
    revert hΓ₁ he₁ hΓ₂ he₂
    cases D₁' <;> cases D₂' <;> intro hΓ₁ he₁ hΓ₂ he₂ D₁'' D₂'' hcast₁ hcast₂ <;>
      subst he₂ <;> subst hΓ₂ <;> subst hcast₂ <;> subst hcast₁ <;> first
        | subst hΓ₁; cases he₁
          first
            | exact eut_conv_left_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convL _ _ hσ)
            | exact eut_conv_right_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convR _ _ hσ)
            | exact eut_sort_sort_caseStep Aw tbl _ _ S σ ρ
            | exact eut_bvar_bvar_caseStep Aw tbl _ _ _ _ S σ ρ
            | exact eut_lit_lit_caseStep Aw tbl _ _ S σ ρ
            | exact eut_pi_pi_caseStep_of_ports Aw tbl _ _ _ _ S σ ρ
                (piP _ _ _ _ hσ)
            | exact eut_lam_lam_caseStep_of_ports Aw tbl _ _ _ _ _ _ S σ ρ
                (lamP _ _ hσ)
            | obtain ⟨u₁', v₁', u₂', v₂', hA₁, hB₁, hA₂, hB₂, ports⟩ :=
                appP _ _ _ _ _ _ hσ
              exact eut_app_app_caseStep_of_ports Aw tbl _ _ _ _ _ _
                hA₁ hB₁ hA₂ hB₂ S σ ρ ports
            | exact eut_letE_letE_caseStep_of_ports Aw tbl _ _ _ _ _ _ _ _
                S σ ρ (letP _ _ _ _ _ _ _ _ hσ)
            | refine constCell _ _ _ _ _ _ _ _ _ _ S σ hσ ρ ?_
              exact fun hT₁' hT₂' => constP hT₁' hT₂' hσ
            | refine eutOther _ _ rfl rfl rfl rfl S σ hσ ρ ?_; rfl
        | exact eut_conv_right_caseStep_of_ports Aw tbl _ _ _ S σ ρ
            (convR _ _ hσ)
        | subst hΓ₁
          refine eutOther _ _ rfl he₁ rfl rfl S σ hσ ρ ?_; rfl
        | cases hΓ₁; cases he₁
          first
            | exact eut_conv_left_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convL _ _ hσ)
            | exact eut_conv_right_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convR _ _ hσ)
            | refine eutOther _ _ rfl rfl rfl rfl S σ hσ ρ ?_; rfl
        | cases hΓ₁
          refine eutOther _ _ rfl he₁ rfl rfl S σ hσ ρ ?_; rfl
        | subst he₁
          first
            | exact eut_conv_left_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convL _ _ hσ)
            | exact eut_conv_right_caseStep_of_ports Aw tbl _ _ _ S σ ρ
                (convR _ _ hσ)
            | refine eutOther _ _ hΓ₁ rfl rfl rfl S σ hσ ρ ?_; rfl
        | exact Expr.noConfusion he₁
        | refine eutOther _ _ hΓ₁ he₁ rfl rfl S σ hσ ρ ?_; rfl
  exact aux D₁ D₂ rfl rfl rfl rfl rfl rfl

/-! ## Verdicts at `tableOfI hW` under the gate -/

/-- The gated `lamP` premise shape at `tbl := tableOfI hW` — row 15's
    missing lemma restated under `LevelHom σ`. REFUTED below: the #7781
    refuting instance carries a `LevelHom` σ (`id`), so the gate does not
    save the supply. -/
def eutLamP_lhom_tableOfI (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B₁ B₂ : Expr Nat}
    {u₁ v₁ v₂ : Level}
    (hB₁ : TyP E' n (.assumption A :: Γ) B₁ (.sort v₁))
    (hB₂ : TyP E' n (.assumption A :: Γ) B₂ (.sort v₂))
    {σ : Level → Level} {ρ : List Disp}, LevelHom σ →
    EutLamPorts (tableOfI hW) σ ρ u₁ hB₁ hB₂

/-- **Row 15 gated verdict: the gated `lamP` supply is FALSE** at
    `tableOfI` — the refuting σ is `id`, a `LevelHom`; every input a closed
    inhabited term (`hs0s`/`hs1s`/`two`/`[]`). Not a strawman. -/
theorem eutLamP_lhom_tableOfI_empty_refuted :
    ¬ eutLamP_lhom_tableOfI EnvWfT.empty :=
  fun h => eutLamPorts_tableOfI_empty_refuted EnvWfT.empty
    (h hs0s hs1s levelHom_id)

/-- `SortCoh` at the gate is `eqN`-transported: the σ-distinguisher is GONE
    at `LevelHom σ`. The gated `piP` wall (#7788's landed `eutPiP_wall`,
    imported here) carries exactly the sort-uniqueness content `eqN v₁ v₂`,
    nothing more. -/
theorem sortCoh_of_eqN_lhom {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B : Expr Nat} {v₁ v₂ : Level} {σ : Level → Level}
    (hσ : LevelHom σ) (h : eqN v₁ v₂)
    (hB₁ : TyP E' n (.assumption A :: Γ) B (.sort v₁))
    (hB₂ : TyP E' n (.assumption A :: Γ) B (.sort v₂)) :
    SortCoh σ hB₁ hB₂ := hσ.eqN_map h

/-- Row 15's gated residual wall, ONE named Prop: #7788's `eutResidualWall`
    (the `eutOther` shape at `tableOfI`) restricted to the `LevelHom σ` every
    demanded `.eut` cell carries. Retained (not claimed); diagonal tooth
    below. -/
def eutResidualWallLhom (Aw : Nat → Nat) (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ Γ₁ Γ₂ : LCtx} {e e₁ e₂ T₁ T₂ : Expr Nat}
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
    (D₁ : TyP E' n Γ₁ e₁ T₁) (D₂ : TyP E' n Γ₂ e₂ T₂)
    (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp),
    eutResidualTag D₁.headTag D₂.headTag = true →
    CaseStep Aw (tableOfI hW)
      (.eut (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ)

/-- Tooth: the gated residual wall's conclusion is inhabited on the `wk`/`wk`
    diagonal at the gated `σ := id` (#7788's `eutResidualWall_diag_sat`
    instantiated at a `LevelHom`). -/
theorem eutResidualWallLhom_diag_sat (Aw : Nat → Nat) (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (d : LocalDecl) (c : Nat)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (ρ : List Disp) :
    CaseStep Aw (tableOfI hW)
      (.eut (TyP.wk _ _ _ _ _ d c D) (TyP.wk _ _ _ _ _ d c D) S id ρ) :=
  eutResidualWall_diag_sat Aw hW D d c S id ρ

#print axioms es_eut_field_lhom
#print axioms eutLamP_lhom_tableOfI
#print axioms eutLamP_lhom_tableOfI_empty_refuted
#print axioms sortCoh_of_eqN_lhom
#print axioms eutResidualWallLhom
#print axioms eutResidualWallLhom_diag_sat

end Rcic.Syn
