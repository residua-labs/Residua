import rcic.RcicSynStepPortsClEut
import rcic.RcicSynSortPBit
import rcic.RcicErasedMajorMode
import rcic.RcicSynTableOfIFull
import rcic.RcicSynClosedCleut
import rcic.RcicSynSRClEutClCase
import rcic.RcicSynSRClEutLhomStep

/-!
# RcicSynSRClEutLhomCl — the SIGMA GAP on row 14 (`cl_case`), supplier side

`es_cl_field`'s port premises quantify over ARBITRARY `σ : Level → Level`;
the consumer only instantiates `LevelHom σ` (`Demand.hom`, patched in
`RcicSynSRClEutLhomStep`). The supplier is restated here under that exact
hypothesis (new name `es_cl_field_lhom`; the landed statement is untouched).

Verdicts at `tbl := tableOfI hW` under the gate:

* `constCl` is NOT refuted at the gate: #7781's distinguishing `sr3σ` is not
  a `LevelHom`. At one, `hbit` is `eqN`-transported
  (`clConstPorts_of_eqN_lhom`) — the σ-distinguisher is GONE; the gated wall
  `clConstP_lhom_tableOfI` carries exactly the sort-level uniqueness content
  (`eqN u₁ u₂` for two typings of the same member type), tooth included.
* `clOther` restated under the gate as `clResidualWallLhom`, diagonal tooth
  at a `LevelHom` σ.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv} {Eₐ : ResolvedEnv}

/-- **`cl_case` gated**: the exact `es_cl_field` port bundle with every
    `σ`-quantified premise restricted to `LevelHom σ`, concluding the gated
    field shape `GatedClCase`. -/
theorem es_cl_field_lhom (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (piCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
        {u₁ v₁ v₂ : Level}
        (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
        (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        ClPiPorts tbl σ ρ u₁ hB₁ hB₂)
    (lamCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat}
        {u₁ : Level}
        (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
        (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        ClLamPorts tbl σ ρ u₁ hb₁ hb₂)
    (appCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
        {f a A₁ B₁ A₂ B₂ : Expr Nat}
        (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
        (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        ClAppPorts tbl σ ρ hf₁ ha₁ hf₂ ha₂)
    (letCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
        (hv₁ : TyP E n Γ v A)
        (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
        (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂) (hv₂ : TyP E n Γ v A)
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        ClLetEPorts tbl σ ρ hv₁ hb₁ hb₂ hv₂)
    (constCl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
        {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
        (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
        (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
        {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp},
        ClConstPorts tbl σ ρ hT₁ hT₂)
    (clOther : ∀ {E : ResolvedEnv} {n : Nat}
        {Γ Γ₁ Γ₂ : LCtx} {e e₁ e₂ T₁ T₂ : Expr Nat}
        {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
        (D₁ : TyP E n Γ₁ e₁ T₁) (D₂ : TyP E n Γ₂ e₂ T₂)
        (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
        (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (hσ : LevelHom σ)
        (ρ : List Disp),
        clResidualTag D₁.headTag D₂.headTag = true →
        CaseStep Aw tbl (.cl (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ)) :
    GatedClCase Aw tbl Eₐ := by
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ hσ ρ
  -- Same constCell bridge as the landed proof, gate carried at the fixed
  -- outer `σ`.
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
        ClConstPorts tbl σ' ρ' hT₁' hT₂') →
      CaseStep Aw tbl (.cl (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁
          hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S' σ' ρ') := by
    intro r ls ls₁ ls₂ m₁ m₂ u₁ u₂ hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ S' σ' _hσ' ρ' portsFn
    have hm : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
    subst hm
    exact cl_const_const_caseStep_of_port Aw tbl hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ S' σ' ρ' (portsFn hT₁ hT₂)
  -- double convoy, exactly the landed `aux`; only the ported arms change.
  have aux : ∀ {Γ₁ Γ₂ : LCtx} {e₁ e₂ T₁ T₂ : Expr Nat}
      (D₁' : TyP E n Γ₁ e₁ T₁) (D₂' : TyP E n Γ₂ e₂ T₂)
      (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
      {D₁'' : TyP E n Γ e T₁} {D₂'' : TyP E n Γ e T₂}
      (_ : D₁'' = hΓ₁ ▸ he₁ ▸ D₁') (_ : D₂'' = hΓ₂ ▸ he₂ ▸ D₂'),
      CaseStep Aw tbl (.cl D₁'' D₂'' S σ ρ) := by
    intro Γ₁ Γ₂ e₁ e₂ T₁ T₂ D₁' D₂' hΓ₁ he₁ hΓ₂ he₂
    revert hΓ₁ he₁ hΓ₂ he₂
    cases D₁' <;> cases D₂' <;> intro hΓ₁ he₁ hΓ₂ he₂ D₁'' D₂'' hcast₁ hcast₂ <;>
      subst he₂ <;> subst hΓ₂ <;> subst hcast₂ <;> subst hcast₁ <;> first
        | subst hΓ₁; cases he₁
          first
            | exact cl_conv_left_caseStep Aw tbl _ _ _ S σ ρ
            | exact cl_conv_right_caseStep Aw tbl _ _ _ S σ ρ
            | exact cl_sort_sort_caseStep Aw tbl _ _ S σ ρ
            | exact cl_bvar_bvar_caseStep Aw tbl _ _ _ _ S σ ρ
            | exact cl_lit_lit_caseStep Aw tbl _ _ S σ ρ
            | refine cl_pi_pi_caseStep_of_ports Aw tbl _ _ _ _ S σ ρ ?_
              exact piCl _ _ hσ
            | refine cl_lam_lam_caseStep_of_ports Aw tbl _ _ _ _ _ _ S σ ρ ?_
              exact lamCl _ _ hσ
            | refine cl_app_app_caseStep_of_ports Aw tbl _ _ _ _ _ _ S σ ρ ?_
              exact appCl _ _ _ _ hσ
            | refine cl_letE_letE_caseStep_of_ports Aw tbl _ _ _ _ _ _ _ _ S σ ρ ?_
              exact letCl _ _ _ _ hσ
            | refine constCell _ _ _ _ _ _ _ _ _ _ S σ hσ ρ ?_
              exact fun hT₁' hT₂' => constCl hT₁' hT₂' hσ
            | refine clOther _ _ rfl rfl rfl rfl S σ hσ ρ ?_; rfl
        | exact cl_conv_right_caseStep Aw tbl _ _ _ S σ ρ
        | subst hΓ₁
          refine clOther _ _ rfl he₁ rfl rfl S σ hσ ρ ?_; rfl
        | cases hΓ₁; cases he₁
          first
            | exact cl_conv_left_caseStep Aw tbl _ _ _ S σ ρ
            | exact cl_conv_right_caseStep Aw tbl _ _ _ S σ ρ
            | refine clOther _ _ rfl rfl rfl rfl S σ hσ ρ ?_; rfl
        | cases hΓ₁
          refine clOther _ _ rfl he₁ rfl rfl S σ hσ ρ ?_; rfl
        | subst he₁
          first
            | exact cl_conv_left_caseStep Aw tbl _ _ _ S σ ρ
            | exact cl_conv_right_caseStep Aw tbl _ _ _ S σ ρ
            | refine clOther _ _ hΓ₁ rfl rfl rfl S σ hσ ρ ?_; rfl
        | exact Expr.noConfusion he₁
        | refine clOther _ _ hΓ₁ he₁ rfl rfl S σ hσ ρ ?_; rfl
  exact aux D₁ D₂ rfl rfl rfl rfl rfl rfl

/-! ## Verdicts at `tableOfI hW` under the gate -/

/-- `hbit` at the gate is `eqN`-transported: the σ-distinguisher is GONE at
    `LevelHom σ`. The gated `constCl` wall carries exactly the sort-level
    uniqueness content (`eqN u₁ u₂` for two typings of the same member
    type), nothing more. Table-independent. -/
theorem clConstPorts_of_eqN_lhom (tbl : List CRule)
    {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    {σ : Level → Level} {ρ : List Disp} (hσ : LevelHom σ) (h : eqN u₁ u₂)
    (hT₁ : TyP E' n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E' n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂)) :
    ClConstPorts tbl σ ρ hT₁ hT₂ :=
  ⟨fun _ => levelIsZero_eqN_congr (hσ.eqN_map h)⟩

/-- The gated `constCl` premise shape at `tbl := tableOfI hW` — row 14's
    missing lemma restated under `LevelHom σ`. NOT refuted at the gate
    (#7781's distinguishing `sr3σ` is not a `LevelHom`); retained, with the
    residual content named by `clConstPorts_of_eqN_lhom` above. -/
def clConstP_lhom_tableOfI (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hT₁ : TyP E' n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E' n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    {σ : Level → Level} {ρ : List Disp}, LevelHom σ →
    ClConstPorts (tableOfI hW) σ ρ hT₁ hT₂

/-- Tooth: the gated wall's conclusion is inhabited at an identical closed
    instance (`sr3hT₁` on both sides, `σ := id`, `ρ := []`). -/
theorem clConstP_lhom_tableOfI_ident_sat (hW : EnvWfT emptyEnv) :
    ClConstPorts (tableOfI hW) id [] sr3hT₁ sr3hT₁ :=
  ⟨fun _ => rfl⟩

/-- Row 14's gated residual wall, ONE named Prop: the `clOther` shape at
    `tableOfI` restricted to the `LevelHom σ` every demanded `.cl` cell
    carries. Retained; diagonal tooth below. -/
def clResidualWallLhom (Aw : Nat → Nat) (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ Γ₁ Γ₂ : LCtx} {e e₁ e₂ T₁ T₂ : Expr Nat}
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
    (D₁ : TyP E' n Γ₁ e₁ T₁) (D₂ : TyP E' n Γ₂ e₂ T₂)
    (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp),
    clResidualTag D₁.headTag D₂.headTag = true →
    CaseStep Aw (tableOfI hW)
      (.cl (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ)

/-- Tooth: the gated residual wall's conclusion is inhabited on the `wk`/`wk`
    diagonal at the gated `σ := id` (`cl_residual_cell_sat` instantiated at a
    `LevelHom`). -/
theorem clResidualWallLhom_diag_sat (Aw : Nat → Nat) (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (d : LocalDecl) (c : Nat)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (ρ : List Disp) :
    CaseStep Aw (tableOfI hW)
      (.cl (TyP.wk _ _ _ _ _ d c D) (TyP.wk _ _ _ _ _ d c D) S id ρ) :=
  cl_residual_cell_sat Aw (tableOfI hW) D d c S id ρ

#print axioms es_cl_field_lhom
#print axioms clConstPorts_of_eqN_lhom
#print axioms clConstP_lhom_tableOfI
#print axioms clConstP_lhom_tableOfI_ident_sat
#print axioms clResidualWallLhom
#print axioms clResidualWallLhom_diag_sat

end Rcic.Syn
