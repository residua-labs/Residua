import rcic.RcicSynSRBetaZetaStepWBoundary
import rcic.RcicSynSRBetaZetaZlTooth

/-!
# Rows 2/3/4 as `StepSuppliersW` fields at `tableOfI hW`

The three glm-sr1 census rows restated at `GoalW`, with the retained walls as
exact named `epsW` props and the fields supplied from them at
`tbl := tableOfI hW`:

* **Row 3 (`es_zeta`)** — `ZetaSurfaceClWallW`/`ZetaReductClWallW` (the two
  (d) `CLW` ports, fresh surfaces) + `zeta_caseStepW_of_port_cls` +
  `esW_zeta_field_of_walls`. Status: OPEN walls, field supplied from them.
* **Row 4 (`es_zetaLocal`)** — `ZetaLocalPortsW` + `zetaLocal_caseStepW_of_ports`
  + `esW_zetaLocal_field_of_walls`. The `hres` port is restated ON the routed
  cone (`ZetaLocalResConvWallRoutedW`: `LevelHom σ` + `RoutedDisp σ E n Γ ρ`);
  its canonical-instance holds (`zl_res_convW_canon`) and the ρ-side
  refutation family (`.keep` at the let position) is entirely off-cone
  (`zl_routed_no_keep_at_zetaCtx`). The wall itself stays OPEN — closing it
  needs the typing-erasure coherence at routed displays (any two typings of
  the stored value at the same routed display erase convertibly), named here.
* **Row 2 (`es_beta`)** — `BetaBodyClWallW`/`BetaReductClWallW`/
  `BetaBodyTagWallW`, the exact epsW restatements. The eps refutations
  (`beta_body_cl_refuted`, `beta_reduct_cl_refuted`) do not transfer: their
  own fixtures now SATISFY the W-walls (`beta_body_clW_fixture_holds`,
  `beta_reduct_clW_fixture_holds` — the seeds `clw_beta_*`). Status: OPEN.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 the clause equations at `epsW` -/

/-- `eps_let_clause` at `epsW` (the `letE` arm is `eps` verbatim). -/
theorem epsW_let_clause {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {value B body : Expr Nat} {w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.letE E n Γ A u value B body w hA hv hb hT).epsW σ ρ =
      match hv.epsW σ ρ with
      | .star => hb.epsW σ (.drop :: ρ)
      | ev => hb.epsW σ (.inline ev :: ρ) := rfl

/-- `eps_lsub` (the node equation) at `epsW` (the `lsub` arm is `eps`
    verbatim). -/
theorem epsW_lsub_node {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat}
    {j : Nat} {u : Level} {D : TyP E n Γ e A} {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).epsW σ ρ =
      match hv.epsW σ ρ with
      | .star => D.epsW σ (insertDisp .drop j ρ)
      | ev => D.epsW σ (insertDisp (.inline (localize (countKeep (ρ.take j)) ev)) j ρ) := rfl

/-- `letSub_eps` at `epsW`. -/
theorem letSub_epsW {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body B value : Expr Nat} {u : Level}
    (hb : TyP E n (.letBinding A value :: Γ) body B) (hv : TyP E n Γ value A)
    (hA : TyP E n Γ A (.sort u)) (σ : Level → Level) (ρ : List Disp) :
    (letSub hb hv hA).epsW σ ρ =
      match hv.epsW σ ρ with
      | .star => hb.epsW σ (.drop :: ρ)
      | ev => hb.epsW σ (.inline ev :: ρ) := by
  rw [letSub, epsW_tyCast, epsW_lsub_node, epsW_castLift0]
  rfl

/-! ## §1 row 3: `es_zeta` at `GoalW` -/

/-- `es_zeta` at `ESW`. -/
theorem esW_zeta {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    {mid : ETm}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (hL : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ) mid)
    (hR : ConvMod (EStep tbl) LvlEq mid (dr.epsW σ ρ)) :
    ESW tbl σ ρ (CvP.zeta E n Γ A value body B u hA hv hb dl dr) := by
  simpa [ESW, CvP.dl, CvP.dr] using (hL.trans hR)

/-- **Row 3 wall 1** — `zeta_surface_cl` restated at `CLW`: the letE-headed
    surface `CL`, freshly built (`TyP.letE … dl.reg.1 hA hv hb dl.reg.2`),
    at arbitrary `σ`/`ρ`. No `wk` is involved in the surface itself; the
    wall is the same `(d)` port as at `eps`, unrefuted. -/
def ZetaSurfaceClWallW (Aw : Nat → Nat) (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (σ : Level → Level) (ρ : List Disp),
    CLW tbl σ ρ dl (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2)

/-- **Row 3 wall 2** — `zeta_reduct_cl` restated at `CLW`: the `letSub`
    reduct `CL` against the arbitrary reduct typing `dr`. -/
def ZetaReductClWallW (Aw : Nat → Nat) (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (σ : Level → Level) (ρ : List Disp),
    CLW tbl σ ρ (letSub hb hv hA) dr

/-- `zeta_caseStep_of_port_cls` at `GoalW`: the field from exactly the two
    `CLW` ports, composed by `esW_zeta` through `epsW_let_clause` and
    `letSub_epsW` (the same re-frame that made `eps_let_clause`/`letSub_eps`
    compose at `eps`). -/
theorem zeta_caseStepW_of_port_cls {Eₐ : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule}
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hL : CLW tbl σ ρ dl (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2))
    (hR : CLW tbl σ ρ (letSub hb hv hA) dr) :
    CaseStepW Aw tbl (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ) :=
  fun _ _ => by
    refine esW_zeta (mid := (letSub hb hv hA).epsW σ ρ) hA hv hb dl dr ?_ ?_
    · have hL' : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ)
        ((TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2).epsW σ ρ) := hL
      exact ((epsW_let_clause hA hv hb dl.reg.2 σ ρ).trans
        (letSub_epsW hb hv hA σ ρ).symm) ▸ hL'
    · exact hR

/-- **Row 3 supplied from its walls** at `tbl := tableOfI hW`: the
    `StepSuppliersW.es_zeta` field, premise-free in `hW` and the field data
    alone, conditional on exactly the two named OPEN walls above. -/
theorem esW_zeta_field_of_walls {E : ResolvedEnv} (hW : EnvWfT E) {Aw : Nat → Nat}
    (hs : ZetaSurfaceClWallW Aw (tableOfI hW))
    (hr : ZetaReductClWallW Aw (tableOfI hW)) :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A value body B : Expr Nat} {u : Level}
      (hA : TyP E' n Γ A (.sort u)) (hv : TyP E' n Γ value A)
      (hb : TyP E' n (.letBinding A value :: Γ) body B)
      (dl : TyP E' n Γ (.letE A value body) (instantiate0 value B))
      (dr : TyP E' n Γ (instantiate0 value body) (instantiate0 value B))
      (S : ScopedCtx E E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
      CaseStepW Aw (tableOfI hW)
        (.es (CvP.zeta E' n Γ A value body B u hA hv hb dl dr) S σ ρ) := by
  intro _ _ _ _ _ _ _ _ _ _ _ hA hv hb dl dr S σ ρ
  exact zeta_caseStepW_of_port_cls hA hv hb dl dr S σ ρ (hs hA hv hb dl dr σ ρ)
    (hr hA hv hb dl dr σ ρ)

/-! ## §2 row 4: `es_zetaLocal` at `GoalW` -/

/-- `zetaLocal_issued_value_cl` at `CLW` (the IH edge `Issues.zetaLocal_cl`
    is eps-free). -/
theorem zetaLocal_issued_value_clW {Eₐ : ResolvedEnv} (Aw : Nat → Nat)
    (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ))
    (ih : StepIHW Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)) :
    CLW tbl σ ρ hv dr :=
  ih_localW Aw tbl hq ih (.cl hv dr S σ ρ) Issues.zetaLocal_cl rfl
    (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) rfl hv dr
        (by simp only [CvP.wt]; omega) (by simp only [CvP.wt]; omega))))

/-- `ZetaLocalPorts` at `epsW`. -/
structure ZetaLocalPortsW (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) : Prop where
  surfaceCl : CLW tbl σ ρ dl (zetaLocalBvarSurface hty dl)
  slotCoh :
    (levelIsZero (σ dl.reg.1) = true ∧ PBitW σ ρ hv dl.reg.2) ∨
      (levelIsZero (σ dl.reg.1) = false ∧
        ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.epsW σ ρ))

/-- `zetaLocal_caseStep_of_ports` at `GoalW`. -/
theorem zetaLocal_caseStepW_of_ports {Eₐ : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {i : Nat} {A v : Expr Nat}
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
      (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (_ports : ZetaLocalPortsW tbl σ ρ hty hv dl),
      CaseStepW Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) := by
  intro E₀ n₀ Γ₀ E n Γ i A v hval hty hv dl dr S σ ρ ports hq ih
  have hcl_hv_dr : CLW tbl σ ρ hv dr :=
    zetaLocal_issued_value_clW Aw tbl hval hty hv dl dr S σ ρ hq ih
  have hsurf : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ)
      ((zetaLocalBvarSurface hty dl).epsW σ ρ) :=
    ports.surfaceCl
  show ESW tbl σ ρ _
  unfold CLW at hcl_hv_dr
  unfold ESW
  simp only [CvP.dl, CvP.dr]
  rcases ports.slotCoh with ⟨hu, hpb⟩ | ⟨hu, hres⟩
  · have hbvar_star : (zetaLocalBvarSurface hty dl).epsW σ ρ = .star := by
      simp [zetaLocalBvarSurface, TyP.epsW, hu]
    have hv_star : hv.epsW σ ρ = .star := hpb.mpr hu
    rw [hbvar_star, ← hv_star] at hsurf
    exact hsurf.trans hcl_hv_dr
  · have hbvar_rel : (zetaLocalBvarSurface hty dl).epsW σ ρ = resolve ρ i := by
      simp [zetaLocalBvarSurface, TyP.epsW, hu]
    rw [hbvar_rel] at hsurf
    exact (hsurf.trans hres).trans hcl_hv_dr

/-! ### the `hres` port on the routed cone -/

/-- **Row 4's `zetaLocal_res_conv`, restated on the routed cone:** the
    `∀ ρ` wrap replaced by `RoutedDisp σ E n Γ ρ` (the displays the routed
    derivation actually produces) and the σ-side by the cone's own
    `LevelHom σ` (`P2Query.Hom` of an `.es` query). -/
def ZetaLocalResConvWallRoutedW (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp)
    (_hρ : RoutedDisp σ E n Γ ρ),
    levelIsZero (σ dl.reg.1) = false →
    ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.epsW σ ρ)

/-- The canonical-instance evidence, at `epsW`: at the canonical Entry
    disposition of `zetaCtx` (the cone's `canon` base), `resolve` returns
    exactly the stored value's `epsW` and the wall's goal is reflexivity —
    the value-is-a-sort tooth does not survive the cone. -/
theorem zl_res_convW_canon :
    ConvMod (EStep (tableOfI EnvWfT.empty)) LvlEq
      (resolve ((zetaCtxP emptyEnv 0).disp id) 0)
      (zrHv.epsW id ((zetaCtxP emptyEnv 0).disp id)) :=
  ConvMod.refl _

/-- The ρ-side refutation family is entirely off-cone: no routed display of
    `zetaCtx` carries `.keep` at the let-binding position 0
    (`routedDisp_let_noKeep`), so the landed refutation's `[.keep]`
    exploitation cannot recur inside the cone. -/
theorem zl_routed_no_keep_at_zetaCtx {σ : Level → Level}
    (hρ : RoutedDisp σ emptyEnv 0 zetaCtx ρ) : ρ[0]? ≠ some .keep :=
  fun hkeep => (routedDisp_let_noKeep hρ).2 0 (.sort (.succ .zero)) (.sort .zero)
    (rfl : zetaCtx[0]? = some (.letBinding (.sort (.succ .zero)) (.sort .zero))) hkeep

/-- `zetaLocal_issued_reg_pb` at `PBitW` (the `Issues.occ_pb` edge is
    eps-free). -/
theorem zetaLocal_issued_reg_pbW {Eₐ : ResolvedEnv} (Aw : Nat → Nat)
    (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (pReg : List Nat)
    (hocc :
      P2Query.subAt (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2))
    (hq : Demand (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ))
    (ih : StepIHW Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)) :
    PBitW σ ρ hv dl.reg.2 := by
  obtain ⟨hapv, hapdl, -⟩ := hq.ap
  have hreg_wt : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  exact ih_issueW Aw tbl hq ih (.pb hv dl.reg.2 S σ ρ)
    (Issues.occ_pb (k₁ := 0) (p₁ := [0]) (k₂ := 0) (p₂ := pReg)
      rfl hocc hapv (assumpPref_reg hapdl))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.zetaLocal E n Γ i A v hval hty hv dl dr)
        rfl hv dl.reg.2
        (by simp only [CvP.wt]; omega)
        (by simp only [CvP.wt]; omega)))))

/-- **Row 4's field at `GoalW`** — the per-node ports shape of the landed
    `es_zetaLocal_field`: `CLW[hv, dr]` still from `StepIHW`, the `PBitW`
    leg from `StepIHW` under the occurrence condition, and the two retained
    (d) ports — the res-conv one already on the routed cone (the `Demand` of
    an `.es` query carries `RoutedDisp`, so the cone restriction loses
    nothing the demand actually supplies). -/
theorem esW_zetaLocal_field_portsW {Eₐ : ResolvedEnv} (Aw : Nat → Nat)
    (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hsurf : CLW tbl σ ρ dl (zetaLocalBvarSurface hty dl))
    (hregOcc : levelIsZero (σ dl.reg.1) = true →
      ∃ pReg : List Nat,
        P2Query.subAt (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
          0 pReg = some (.ty dl.reg.2))
    (hres : levelIsZero (σ dl.reg.1) = false →
      ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.epsW σ ρ)) :
    CaseStepW Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) := by
  intro hq ih
  refine zetaLocal_caseStepW_of_ports hval hty hv dl dr S σ ρ
    ⟨hsurf, ?_⟩ hq ih
  rcases Bool.eq_false_or_eq_true (levelIsZero (σ dl.reg.1)) with hu | hu
  · obtain ⟨pReg, hocc⟩ := hregOcc hu
    exact Or.inl ⟨hu,
      zetaLocal_issued_reg_pbW Aw tbl hval hty hv dl dr S σ ρ pReg hocc hq ih⟩
  · exact Or.inr ⟨hu, hres hu⟩

/-- **Row 4's surface wall** as ONE named `∀`-Prop (the exact missing
    lemma at `epsW`). -/
def ZetaLocalSurfaceClWallW (Aw : Nat → Nat) (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hty : lookupType Γ i = some A) (hv : TyP E n Γ v A)
    (dl : TyP E n Γ (.bvar i) A) (σ : Level → Level) (ρ : List Disp),
    CLW tbl σ ρ dl (zetaLocalBvarSurface hty dl)

/-- **Row 4's occurrence wall** (the landed `hregOcc` port, verbatim at
    `epsW`; eps-free). -/
def ZetaLocalRegOccWallW (Eₐ : ResolvedEnv) (Aw : Nat → Nat) (tbl : List CRule) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    levelIsZero (σ dl.reg.1) = true →
    ∃ pReg : List Nat,
      P2Query.subAt (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
        0 pReg = some (.ty dl.reg.2)

/-- **Row 4 supplied from its walls** at `tbl := tableOfI hW`: the exact
    `StepSuppliersW.es_zetaLocal` field type, from the surface wall, the
    occurrence wall, and the routed-cone res-conv wall. -/
theorem esW_zetaLocal_field_of_walls {E : ResolvedEnv} (hW : EnvWfT E)
    {Aw : Nat → Nat}
    (hs : ZetaLocalSurfaceClWallW Aw (tableOfI hW))
    (hocc : ZetaLocalRegOccWallW E Aw (tableOfI hW))
    (hres : ZetaLocalResConvWallRoutedW (tableOfI hW)) :
    ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {i : Nat} {A v : Expr Nat}
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
      (hv : TyP E' n Γ v A) (dl : TyP E' n Γ (.bvar i) A) (dr : TyP E' n Γ v A)
      (S : ScopedCtx E E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
      (hq : Demand (.es (CvP.zetaLocal E' n Γ i A v hval hty hv dl dr) S σ ρ))
      (ih : StepIHW Aw (tableOfI hW)
        (.es (CvP.zetaLocal E' n Γ i A v hval hty hv dl dr) S σ ρ)),
      GoalW (tableOfI hW) (.es (CvP.zetaLocal E' n Γ i A v hval hty hv dl dr) S σ ρ) := by
  intro E₀ n₀ Γ₀ E' n Γ i A v hval hty hv dl dr S σ ρ hq ih
  exact esW_zetaLocal_field_portsW Aw (tableOfI hW) hval hty hv dl dr S σ ρ
    (hs hty hv dl σ ρ) (hocc hval hty hv dl dr S σ ρ)
    (hres hval hty hv dl dr σ hq.hom ρ hq.routed) hq ih

/-! ## §3 row 2: the beta walls at `epsW` -/

/-- **Row 2 wall 1** — `beta_body_cl` restated at `CLW`: the read's body CL
    one binder up. At `eps` this wall is FALSE (`beta_body_cl_refuted`,
    `tableOfI EnvWfT.empty`); at `epsW` its refuting fixture holds
    (`beta_body_clW_fixture_holds` below) — the wall itself stays OPEN. -/
def BetaBodyClWallW (tbl : List CRule) : Prop :=
  ∀ {Aw : Nat → Nat} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp)
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g),
    CLW tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) g.hbody hbody

/-- **Row 2 wall 3** — `beta_reduct_cl` restated at `CLW`. -/
def BetaReductClWallW (tbl : List CRule) : Prop :=
  ∀ {Aw : Nat → Nat} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp)
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g),
    CLW tbl σ ρ (instEnd hbody harg hA) dr

/-- **Row 2 wall 2** — `beta_body_tag` restated at `epsW`. -/
def BetaBodyTagWallW (tbl : List CRule) : Prop :=
  ∀ {Aw : Nat → Nat} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp)
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g),
    (g.hbody.epsW σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hbody.epsW σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- The `beta_body_cl` refuting fixture now SATISFIES the `epsW` wall
    instance (`clw_beta_body_epsW`: both endpoints erase to the honest
    `.bvar 2` — the double-lift is gone). -/
theorem beta_body_clW_fixture_holds :
    CLW (tableOfI EnvWfT.empty) id
      (binderDisp (levelIsZero (id (.succ (.succ .zero)))) :: zlRho)
      bGot.hbody bHBody :=
  clw_beta_body_epsW

/-- The `beta_reduct_cl` refuting fixture now SATISFIES the `epsW` wall
    instance (`clw_beta_reduct_epsW`). -/
theorem beta_reduct_clW_fixture_holds :
    CLW (tableOfI EnvWfT.empty) id zlRho
      (instEnd bHBody bHArg bHA) bDr :=
  clw_beta_reduct_epsW

/-- The #7802 OPEN item `eps_wk_zero_liftIfKeep` at `epsW`: at cutoff `0`
    there is no position below the cutoff to re-frame, so `wkInnerDisp` IS
    `removeAt` and the c=0 specialization is the lifted (or untouched)
    child erasure exactly as at `eps`. -/
theorem wkInnerDisp_zero (d' : Disp) (ρ' : List Disp) :
    wkInnerDisp (d' :: ρ') 0 = ρ' := by
  cases d' with
  | keep => simp only [wkInnerDisp, List.getElem?_cons_zero, wkInnerGo]
  | drop => simp only [wkInnerDisp, List.getElem?_cons_zero, removeAt]
  | inline v => simp only [wkInnerDisp, List.getElem?_cons_zero, removeAt]

theorem epsW_wk_zero_liftIfKeep {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (dF : LocalDecl) (hv : TyP E n Γ e A) (μ' : Level → Level) (d' : Disp) (ρ' : List Disp) :
    (TyP.wk E n Γ e A dF 0 hv).epsW μ' (d' :: ρ') = liftIfKeep d' (hv.epsW μ' ρ') := by
  cases d' with
  | keep =>
      rw [epsW_wk_keep (hk := (by simp : ((.keep : Disp) :: ρ')[0]? = some .keep)),
        wkInnerDisp_zero]
      rfl
  | drop =>
      rw [epsW_wk_not_keep (hk := Or.inr (Or.inl (by simp)))]
      rfl
  | inline v =>
      rw [epsW_wk_not_keep (hk := Or.inr (Or.inr ⟨v, by simp⟩))]
      rfl

end Rcic.Syn

#print axioms Rcic.Syn.epsW_let_clause
#print axioms Rcic.Syn.epsW_lsub_node
#print axioms Rcic.Syn.letSub_epsW
#print axioms Rcic.Syn.esW_zeta
#print axioms Rcic.Syn.ZetaSurfaceClWallW
#print axioms Rcic.Syn.ZetaReductClWallW
#print axioms Rcic.Syn.zeta_caseStepW_of_port_cls
#print axioms Rcic.Syn.esW_zeta_field_of_walls
#print axioms Rcic.Syn.zetaLocal_issued_value_clW
#print axioms Rcic.Syn.ZetaLocalPortsW
#print axioms Rcic.Syn.zetaLocal_caseStepW_of_ports
#print axioms Rcic.Syn.ZetaLocalResConvWallRoutedW
#print axioms Rcic.Syn.zl_res_convW_canon
#print axioms Rcic.Syn.zl_routed_no_keep_at_zetaCtx
#print axioms Rcic.Syn.zetaLocal_issued_reg_pbW
#print axioms Rcic.Syn.esW_zetaLocal_field_portsW
#print axioms Rcic.Syn.ZetaLocalSurfaceClWallW
#print axioms Rcic.Syn.ZetaLocalRegOccWallW
#print axioms Rcic.Syn.esW_zetaLocal_field_of_walls
#print axioms Rcic.Syn.BetaBodyClWallW
#print axioms Rcic.Syn.BetaReductClWallW
#print axioms Rcic.Syn.BetaBodyTagWallW
#print axioms Rcic.Syn.beta_body_clW_fixture_holds
#print axioms Rcic.Syn.beta_reduct_clW_fixture_holds
#print axioms Rcic.Syn.wkInnerDisp_zero
#print axioms Rcic.Syn.epsW_wk_zero_liftIfKeep
