import rcic.RcicSynSRClEutEswEut
import rcic.RcicSynSRClEutEswCl

/-!
# RcicSynSRClEutConvb — row 15's convB repair: the `.eut` issuance (cc 00:40Z)

cc 2026-10-21 00:40Z ruling on #7810: the `.cl` route's goal is the
SUBJECT erasure; the codomain conversion is EUT's goal (via `reg`). So
the lam-lam `.eut` cell issues the EXISTING `.eut` query on the SAME
body pair `(hb₁, hb₂)` at `ρ⁺ := binderDisp (levelIsZero (σ u₁)) :: ρ`
(rank: the body is a strict subterm, same lemmas as the `.cl` round),
and the row-15 lam-lam field (`convB` at `ρ⁺`) is derived from that
issued EUT edge. Kernel-checked (`closure_claim = 0`):

1. `IssuesC` = the landed `Issues` rows plus THREE rows — the lam-lam
   `.eut` cell issues `.eut hb₁ hb₂ S σ ρ⁺` AND the two reg-`CL` edges
   `.cl hB₁ hb₁.reg.2 S σ ρ⁺`, `.cl hb₂.reg.2 hB₂ S σ ρ⁺`: exactly S10
   §5.1's binder-view requests, the same five the landed
   `eut_lam_lam_of_local_calls` consumes. `DemandC` closes demand under
   them; AP/LevelHom/RoutedDisp preserved (reg side: `assumpPref_reg`;
   the extended display is exactly `RoutedDisp.assumption`'s step).
2. The rank decreases in the LANDED key for all three: `.eut`'s local
   key is the same `combMeas (tyPairMeas …)` shape as `.cl`'s, so
   `lexKey_eut_lam_eut` is the body-weight argument verbatim; the reg
   edges ride `TyP.wt_reg_le` (`hb.reg.2.wt ≤ hb.wt < lam.wt`) through
   `lexDM_both_wt_lt_left/right`. `solve_of_stepC` lifts over
   `keyLT_wf` unchanged. `eut_lam_eut_ih`: the issued EUT edge is
   exactly what the cell's own IH answers.
3. THE MEASUREMENT (cc's step 2, rerun on the right query): the issued
   `.eut` goal is the conversion of the two types' erasures THROUGH
   `reg` of the body typings — `goal_eut_is_reg_body_erasure` is `rfl`
   — which is NOT YET `convB`: `convB` erases through the lam
   constructors' EXPLICIT codomain typings `hBᵢ` (`goal_cl_is_body_erasure`
   records the superseded `.cl` round: that goal was the SUBJECT
   erasure). The exact gap is ONE Prop — `ConvBOfEutBody` — and it is
   DISCHARGED by the two reg-`CL` issued edges (`convB_of_eut_regCl`,
   `ConvMod.trans`). Hence `eut_lam_lam_caseStepE`: the row-15 lam-lam
   `CaseStepC` with NO bridge premise — everything the landed cell
   consumes is on-cone (domain ports via the landed `occ_bitCoh`/
   `occ_cl`, `TableClosed` from `TableWF` at `tableOfI`).
4. The `.convB` refutations are RETRACTED as off-cone and kept renamed
   as controls (`convb_offcone_goalCV_false`,
   `convb_offcone_clw_false`): they measure the raw conversion's falsity
   at #7800's fixture, which no cell pairing can state (the issued kinds
   unify the subjects); they are NOT refutations of any on-cone demand.
   No on-cone refutation of any issued edge is claimed or needed: the
   three edges are consumed, not refuted, by the discharged cell below.
5. W-regime: `ConvBSupplyW` (every issued conversion answered at `epsW`)
   discharges #7804's surviving wall `eut_case_wallW`
   (`eut_case_wallW_of_convBSupplyW`); `ConvBSupplyW` is itself false at
   the off-cone fixture pairing.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins

/-- The repaired issue relation (cc 00:40Z): the landed `Issues` rows,
    plus THREE rows issued from the lam-lam `.eut` cell at the extended
    display `ρ⁺ := binderDisp (levelIsZero (σ u₁)) :: ρ` — the EXISTING
    `.eut` query on the BODY pair `(hb₁, hb₂)` (the codomain conversion
    is EUT's goal), and the two reg-`CL` edges pairing each lam's
    EXPLICIT codomain typing `hBᵢ` with `hbᵢ.reg.2` (the same judgment
    through the body typing's regularity). All existing kinds; all pair
    two typings of ONE smaller subject. -/
inductive IssuesC {Eₐ : ResolvedEnv} : P2Query Eₐ → P2Query Eₐ → Prop where
  | old {q q' : P2Query Eₐ} (h : Issues q q') : IssuesC q q'
  | eut_lam_eut {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
      (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
      (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
      (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
      (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesC (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ)
        (.eut hb₁ hb₂ S σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
  | eut_lam_regCl_l {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
      (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
      (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
      (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
      (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesC (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ)
        (.cl hB₁ hb₁.reg.2 S σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
  | eut_lam_regCl_r {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
      (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
      (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
      (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
      (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesC (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ)
        (.cl hb₂.reg.2 hB₂ S σ (binderDisp (levelIsZero (σ u₁)) :: ρ))

/-- The demand closure under `IssuesC`: the landed `Demand` rows, plus
    issuance. No root constructor mentions the body pair or either reg
    pair — the three issued edges are only ever demanded by issuance. -/
inductive DemandC {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop where
  | old {q : P2Query Eₐ} (h : Demand q) : DemandC q
  | issued (issuer target : P2Query Eₐ) :
      DemandC issuer → IssuesC issuer target → DemandC target

/-- Every C-issued query's derivations are `AssumpPref` once the
    issuer's are: the landed rows by `Issues.ap`; the body typings are
    the second `AssumpPref` components of the two lam typings, the
    explicit codomain typings the third, and reg preserves it
    (`assumpPref_reg`). -/
theorem IssuesC.ap {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.AP)
    (e : IssuesC q q') : q'.AP := by
  cases e with
  | old h => exact Issues.ap hi h
  | eut_lam_eut hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ =>
      simp only [P2Query.AP] at hi ⊢
      exact ⟨hi.1.2.1, hi.2.2.1⟩
  | eut_lam_regCl_l hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ =>
      simp only [P2Query.AP] at hi ⊢
      exact ⟨hi.1.2.2, assumpPref_reg hi.1.2.1⟩
  | eut_lam_regCl_r hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ =>
      simp only [P2Query.AP] at hi ⊢
      exact ⟨assumpPref_reg hi.2.2.1, hi.2.2.2⟩

/-- Every C-issued query's level map is a `LevelHom` once the issuer's
    is (the rows issue at the issuer's own `σ`). -/
theorem IssuesC.hom {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.Hom)
    (e : IssuesC q q') : q'.Hom := by
  cases e with
  | old h => exact Issues.hom hi h
  | eut_lam_eut hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ => exact hi
  | eut_lam_regCl_l hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ => exact hi
  | eut_lam_regCl_r hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ => exact hi

/-- Every C-issued query's display is routed once the issuer's is: the
    extended display is exactly `RoutedDisp.assumption`'s step, witnessed
    by the domain typing the row already carries. -/
theorem IssuesC.routed {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hr : q.Routed)
    (e : IssuesC q q') : q'.Routed := by
  cases e with
  | old h => exact Issues.routed hr h
  | eut_lam_eut hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ =>
      simp only [P2Query.Routed]
      exact RoutedDisp.assumption (P2Query.routed_site hr) hA₁
  | eut_lam_regCl_l hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ =>
      simp only [P2Query.Routed]
      exact RoutedDisp.assumption (P2Query.routed_site hr) hA₁
  | eut_lam_regCl_r hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ =>
      simp only [P2Query.Routed]
      exact RoutedDisp.assumption (P2Query.routed_site hr) hA₁

/-- The C closure preserves `AP`. -/
theorem DemandC.ap {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandC q) : q.AP := by
  induction hq with
  | old h => exact Demand.ap h
  | issued _ _ _ e ih => exact IssuesC.ap ih e

/-- The C closure preserves `LevelHom`. -/
theorem DemandC.hom {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandC q) : q.Hom := by
  induction hq with
  | old h => exact Demand.hom h
  | issued _ _ _ e ih => exact IssuesC.hom ih e

/-- The C closure preserves routedness. -/
theorem DemandC.routed {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandC q) : q.Routed := by
  induction hq with
  | old h => exact Demand.routed h
  | issued _ _ _ e ih => exact IssuesC.routed ih e

/-! ## The rank edges (the LANDED key) -/

/-- **The body-pair row's local key strictly decreases**: the issued
    `.eut` query's local key (`combMeas` of `tyPairMeas hb₁ hb₂` —
    `.eut`'s local key has exactly `.cl`'s shape) is strictly below the
    `.eut` lam pair's — the body typings are strict subderivations
    (`TyP.wt` of `lam` is `1 + hA + hb + hB`), via the closer's own
    rank lemmas `lexDM_wt_lt_pair` and `lexDM_combMeas_mono`. -/
theorem lexKey_eut_lam_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.eut hb₁ hb₂ S σ (binderDisp (levelIsZero (σ u₁)) :: ρ)).localKey Aw)
      ((P2Query.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ).localKey Aw) := by
  have hw₁ : hb₁.wt Aw < (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hb₂.wt Aw < (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hb₁ hb₂)
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂)) :=
    lexDM_wt_lt_pair Aw hb₁ hb₂ _ _ rfl rfl hw₁ hw₂
  exact lexDM_combMeas_mono Aw _ hlex

/-- **The left reg-`CL` row's local key strictly decreases**: both
    `hB₁` (carried by the lam constructor, `TyP.wt(lam) = 1 + hA + hb +
    hB`) and `hb₁.reg.2` (regularity is never heavier than the node,
    `TyP.wt_reg_le`, so `≤ hb₁.wt < lam.wt`) are strictly under the
    left lam — `lexDM_both_wt_lt_left`. -/
theorem lexKey_eut_lam_regCl_l (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl hB₁ hb₁.reg.2 S σ (binderDisp (levelIsZero (σ u₁)) :: ρ)).localKey Aw)
      ((P2Query.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ).localKey Aw) := by
  have hwB₁ : hB₁.wt Aw < (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hwb₁ : hb₁.wt Aw < (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hwreg₁ : hb₁.reg.2.wt Aw < (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁).wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hb₁) hwb₁
  exact lexDM_combMeas_mono Aw _
    (lexDM_both_wt_lt_left Aw hB₁ hb₁.reg.2 _ _ rfl hwB₁ hwreg₁)

/-- **The right reg-`CL` row's local key strictly decreases**:
    symmetric, both endpoints strictly under the RIGHT lam —
    `lexDM_both_wt_lt_right`. -/
theorem lexKey_eut_lam_regCl_r (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    LexDM ((P2Query.cl hb₂.reg.2 hB₂ S σ (binderDisp (levelIsZero (σ u₁)) :: ρ)).localKey Aw)
      ((P2Query.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ).localKey Aw) := by
  have hwB₂ : hB₂.wt Aw < (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hwb₂ : hb₂.wt Aw < (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hwreg₂ : hb₂.reg.2.wt Aw < (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂).wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hb₂) hwb₂
  exact lexDM_combMeas_mono Aw _
    (lexDM_both_wt_lt_right Aw hb₂.reg.2 hB₂ _ _ rfl hwreg₂ hwB₂)

/-- **All three rows' ranks decrease** (the well-foundedness
    deliverable, in the LANDED `Before` order): same frame (the rows
    keep the issuer's frame, so `originalPrefixLength` is unchanged),
    strictly smaller local keys. -/
theorem beforeC_eut_lam_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.eut hb₁ hb₂ S σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
      (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ) :=
  before_of_same_prefix Aw rfl (lexKey_eut_lam_eut Aw hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ)

theorem beforeC_eut_lam_regCl_l (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl hB₁ hb₁.reg.2 S σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
      (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ) :=
  before_of_same_prefix Aw rfl (lexKey_eut_lam_regCl_l Aw hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ)

theorem beforeC_eut_lam_regCl_r (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl hb₂.reg.2 hB₂ S σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
      (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ) :=
  before_of_same_prefix Aw rfl (lexKey_eut_lam_regCl_r Aw hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ)

/-! ## The C step obligation -/

/-- `StepIH` over the C demand closure (the `ResolvedView` half of
    `Answer` carries no information — `trivialView` — so the C step
    owes the `Goal` half directly). -/
abbrev StepIHC (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  ∀ q' : P2Query Eₐ, DemandC q' → Before Aw q' q → Goal tbl q'

/-- The per-case step obligation over the C closure (`CaseStep`'s
    shape). -/
abbrev CaseStepC (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  DemandC q → StepIHC Aw tbl q → Goal tbl q

/-- The semantic answer of a C-issued strictly-smaller sub-request. -/
theorem ih_issueC {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {q : P2Query Eₐ} (hq : DemandC q) (ih : StepIHC Aw tbl q)
    (q' : P2Query Eₐ) (e : IssuesC q q') (hb : Before Aw q' q) : Goal tbl q' :=
  ih q' (.issued q q' hq e) hb

/-- An IH call on a C-issued sub-request in the **same frame** at a
    strictly smaller local key. -/
theorem ih_localC {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {q : P2Query Eₐ} (hq : DemandC q) (ih : StepIHC Aw tbl q)
    (q' : P2Query Eₐ) (e : IssuesC q q')
    (hp : q'.originalPrefixLength = q.originalPrefixLength)
    (hk : LexDM (q'.localKey Aw) (q.localKey Aw)) : Goal tbl q' :=
  ih_issueC Aw tbl hq ih q' e (before_of_same_prefix Aw hp hk)

/-- The fixpoint lift over the C closure — `solve_of_step` verbatim
    over `DemandC` and the LANDED rank: the ONLY recursion entry is the
    goal at a strictly smaller rank key (`keyLT_wf`), so the repaired
    closure is well-founded exactly because `beforeC_eut_lam_eut`,
    `beforeC_eut_lam_regCl_l` and `beforeC_eut_lam_regCl_r` decrease. -/
theorem solve_of_stepC {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : ∀ q : P2Query Eₐ, DemandC q →
      (∀ q' : P2Query Eₐ, DemandC q' → Before Aw q' q → Goal tbl q') →
      Goal tbl q) :
    ∀ q : P2Query Eₐ, DemandC q → Goal tbl q := by
  have allAt : ∀ k : Key, ∀ q : P2Query Eₐ, q.rank Aw = k → DemandC q → Goal tbl q :=
    keyLT_wf.fix (fun k ih q hkey hq =>
      step q hq (fun q' hq' hlt =>
        ih (q'.rank Aw) (by unfold Before at hlt; rwa [hkey] at hlt) q' rfl hq'))
  intro q hq
  exact allAt (q.rank Aw) q rfl hq

/-! ## The issued edges at the cell, and the measurement (cc's step 2) -/

/-- The issued EUT edge is exactly what the cell's own IH answers: at
    the lam-lam `.eut` query, the C-step's induction hypothesis supplies
    `EUT` on the body pair at the extended display (the row is
    `IssuesC.eut_lam_eut`, the rank decrease `beforeC_eut_lam_eut`). -/
theorem eut_lam_eut_ih {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : DemandC (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ))
    (ih : StepIHC Aw tbl (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ)) :
    EUT tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hb₁ hb₂ :=
  ih_localC Aw tbl hq ih (.eut hb₁ hb₂ S σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
    (IssuesC.eut_lam_eut hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ) rfl
    (lexKey_eut_lam_eut Aw hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ)

/-- **The superseded `.cl` round's measurement, kept as the record**:
    a `.cl` goal at the body pair IS the SUBJECT-erasure conversion —
    `CL` unfolds (by `rfl`) to a `ConvMod` between `hb₁.eps` and
    `hb₂.eps`, the erasures of the two BODY typings — and is NOT the
    erasure conversion of the two TYPES: that is `EUT`'s goal, which
    erases `reg` (the type's own sort typing; `RcicSynPack.lean:63`).
    This is why cc's step-2 check killed the `.cl` issuance. -/
theorem goal_cl_is_body_erasure {Eₐ : ResolvedEnv} {tbl : List CRule}
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A body B₁ : Expr Nat}
    (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hb₂ : TyP E n (.assumption A :: Γ) body B₁)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (.cl hb₁ hb₂ S σ ρ) =
      ConvMod (EStep tbl) LvlEq (hb₁.eps σ ρ) (hb₂.eps σ ρ) := rfl

/-- **The `.eut` round's measurement (cc's step 2, rerun)**: the issued
    `.eut` goal at the body pair is the conversion of the two TYPES'
    erasures THROUGH `reg` of the body typings — `EUT` unfolds (by
    `rfl`) to a `ConvMod` between `hb₁.reg.2.eps` and `hb₂.reg.2.eps`.
    This is the codomain conversion cc ruled it to be — but it is NOT
    YET `convB` syntactically: `convB` (in `eut_lam_nodes`) erases the
    codomains through the lam constructors' EXPLICIT typings
    `hB₁`/`hB₂`. Same erasable terms, different derivations. The exact
    gap is `ConvBOfEutBody`, discharged just below. -/
theorem goal_eut_is_reg_body_erasure {Eₐ : ResolvedEnv} {tbl : List CRule}
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat}
    (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Goal tbl (.eut hb₁ hb₂ S σ ρ) =
      ConvMod (EStep tbl) LvlEq (hb₁.reg.2.eps σ ρ) (hb₂.reg.2.eps σ ρ) := rfl

/-- The exact gap between the issued EUT edge and `convB`, as ONE named
    Prop (cc 00:40Z): from the EUT edge on the body pair — which erases
    the codomains through `hbᵢ.reg.2` — the binder-crossed codomain
    conversion through the lam constructors' EXPLICIT `hBᵢ` that the
    cell consumes. Not a landed lemma and not a restatement (the two
    conversions erase the same terms through different derivations —
    see `goal_eut_is_reg_body_erasure`); DISCHARGED from the two reg-`CL`
    issued edges by `convB_of_eut_regCl` below. -/
def ConvBOfEutBody (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat}
    (u₁ v₁ v₂ : Level)
    (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂)) : Prop :=
  EUT tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hb₁ hb₂ →
    ConvMod (EStep tbl) LvlEq
      (hB₁.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
      (hB₂.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))

/-- **The gap DISCHARGED on-cone**: `ConvBOfEutBody` follows from the
    two reg-`CL` issued edges by `ConvMod.trans` —
    `hB₁.eps ~ hb₁.reg.2.eps` (left reg-CL), `hb₁.reg.2.eps ~
    hb₂.reg.2.eps` (the issued EUT edge), `hb₂.reg.2.eps ~ hB₂.eps`
    (right reg-CL). This is exactly the landed closer's own composition
    (`eut_lam_lam_of_local_calls`, S10 §5.1). -/
theorem convB_of_eut_regCl (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ v₂ : Level}
    (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (hcl₁ : CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hB₁ hb₁.reg.2)
    (hcl₂ : CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hb₂.reg.2 hB₂) :
    ConvBOfEutBody tbl σ ρ u₁ v₁ v₂ hb₁ hB₁ hb₂ hB₂ := by
  intro heut
  exact hcl₁.trans (heut.trans hcl₂)

/-- **The row-15 lam-lam field, DISCHARGED** (cc 00:40Z): the
    `CaseStepC` at the lam-lam `.eut` query with NO bridge premise.
    Everything the landed cell (`eut_lam_nodes`) consumes is on-cone:
    the domain `BitCoh`/`CL` ride the landed `occ_bitCoh`/`occ_cl` rows
    through `IssuesC.old`; `convB` is the issued EUT edge on the body
    pair composed with the two issued reg-`CL` edges
    (`convB_of_eut_regCl`); `TableClosed` is table data, supplied by
    `TableWF` at `tableOfI`. -/
theorem eut_lam_lam_caseStepE (Aw : Nat → Nat) (tbl : List CRule)
    (hTC : TableClosed tbl)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStepC Aw tbl
      (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ) := by
  intro hq ih
  have hwA₁ : hA₁.wt Aw < (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hwA₂ : hA₂.wt Aw < (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlexA : LexDM (tyPairMeas Aw hA₁ hA₂)
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂)) :=
    lexDM_wt_lt_pair Aw hA₁ hA₂ _ _ rfl rfl hwA₁ hwA₂
  have hap : hA₁.AssumpPref ∧ hA₂.AssumpPref :=
    ⟨(DemandC.ap hq).1.1, (DemandC.ap hq).2.1⟩
  have hbit := ih_localC Aw tbl hq ih (.bitCoh hA₁ hA₂ S σ ρ)
    (IssuesC.old (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hap.1 hap.2)) rfl (lexDM_combMeas_mono Aw _ hlexA)
  have hclA := ih_localC Aw tbl hq ih (.cl hA₁ hA₂ S σ ρ)
    (IssuesC.old (Issues.occ_cl (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hap.1 hap.2)) rfl (lexDM_combMeas_mono Aw _ hlexA)
  have hcl₁ := ih_localC Aw tbl hq ih (.cl hB₁ hb₁.reg.2 S σ
      (binderDisp (levelIsZero (σ u₁)) :: ρ))
    (IssuesC.eut_lam_regCl_l hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ) rfl
    (lexKey_eut_lam_regCl_l Aw hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ)
  have hcl₂ := ih_localC Aw tbl hq ih (.cl hb₂.reg.2 hB₂ S σ
      (binderDisp (levelIsZero (σ u₁)) :: ρ))
    (IssuesC.eut_lam_regCl_r hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ) rfl
    (lexKey_eut_lam_regCl_r Aw hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ)
  exact eut_lam_nodes tbl hTC σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ hbit hclA
    (convB_of_eut_regCl tbl σ ρ hb₁ hB₁ hb₂ hB₂ hcl₁ hcl₂
      (eut_lam_eut_ih Aw tbl hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ S σ ρ hq ih))

/-! ## OFF-CONE CONTROLS (retracted; cc 23:55Z) -/

/-- **CONTROL ONLY — OFF THE DEMAND CONE** (cc 23:55Z review of #7810):
    the `.convB` query language of the retracted repair, kept so the
    controls below stay constructible. The constructor pairs the two
    codomain typings with NO common subject — no cell can issue it (the
    closer only ever issues conversions of two typings of ONE smaller
    subject, and `.cl` cannot even state this pairing because it unifies
    the subjects). Nothing in the repaired route above uses it. -/
inductive P2QueryCV (Eₐ : ResolvedEnv) : Type where
  | convB {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {A B₁ B₂ : Expr Nat} {u₁ v₁ v₂ : Level}
      (hA₁ : TyP E n Γ A (.sort u₁))
      (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
      (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      P2QueryCV Eₐ

/-- **CONTROL ONLY** — the `.convB` goal: the raw binder-crossed
    codomain-typing conversion. -/
def GoalCV (tbl : List CRule) {Eₐ : ResolvedEnv} : P2QueryCV Eₐ → Prop
  | .convB (u₁ := u₁) _ hB₁ hB₂ _ σ ρ =>
      ConvMod (EStep tbl) LvlEq
        (hB₁.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
        (hB₂.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))

/-- **CONTROL ONLY — RETRACTED as off-cone** (was
    `convb_issued_goalCV_refuted`): the raw conversion IS false at
    #7800's fixture (`σ := id`, `hs0s`/`hs1s`, every `tableOfI hW`,
    every frame `S`) — but the pairing has no common body, so no
    lam-lam cell, and no demand closure, can reach it. It measures the
    conversion's falsity, NOT an on-cone refutation; the on-cone
    lam-lam cell is DISCHARGED (`eut_lam_lam_caseStepE`), and the raw
    pairing it falsifies is not that cell's demand. -/
theorem convb_offcone_goalCV_false {E Eₐ : ResolvedEnv} (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀) :
    ¬ GoalCV (tableOfI hW) (.convB hs1 hs0s hs1s S id []) := by
  intro hcl
  have hsort : ConvMod (EStep (tableOfI hW)) LvlEq (.sort .zero) (.sort (.succ .zero)) :=
    hcl
  exact Rcic.Syn.not_eqN_zero_succ .zero
    (eqN_of_convE_sort_wf (tableWF_tableOfI_full hW) hsort)

/-- **CONTROL ONLY — RETRACTED as off-cone** (was
    `convb_issued_clw_refuted`): the same reading under `epsW` (the
    fixture's `.sort`-leaf arms make `epsW` verbatim `eps`), any display
    tail. Same status: measures the raw conversion, not an on-cone
    demand. -/
theorem convb_offcone_clw_false {E : ResolvedEnv} (hW : EnvWfT E) (ρ : List Disp) :
    ¬ ConvMod (EStep (tableOfI hW)) LvlEq
      (hs0s.epsW id (binderDisp (levelIsZero two) :: ρ))
      (hs1s.epsW id (binderDisp (levelIsZero two) :: ρ)) := by
  intro hcl
  have hsort : ConvMod (EStep (tableOfI hW)) LvlEq (.sort .zero) (.sort (.succ .zero)) :=
    hcl
  exact Rcic.Syn.not_eqN_zero_succ .zero
    (eqN_of_convE_sort_wf (tableWF_tableOfI_full hW) hsort)

/-! ## The W-regime wall from the issued supply -/

/-- The W-regime global supply of the wall's content: every
    binder-crossed codomain conversion, answered at `epsW` (stated as
    the raw `ConvMod` of the two `epsW` erasures — `CLW`'s statement
    pairs two typings of ONE subject, which the codomain pair is not).
    Strictly weaker than the wall (no domain, body, or gating premises),
    and itself false only at the off-cone pairing (`convb_offcone_clw_false`)
    — it measures the wall's content read globally, not an issued edge. -/
def ConvBSupplyW (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B₁ B₂ : Expr Nat} {u₁ v₁ v₂ : Level}
    (hB₁ : TyP E' n (.assumption A :: Γ) B₁ (.sort v₁))
    (hB₂ : TyP E' n (.assumption A :: Γ) B₂ (.sort v₂))
    {σ : Level → Level} {ρ : List Disp},
    ConvMod (EStep (tableOfI hW)) LvlEq
      (hB₁.epsW σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
      (hB₂.epsW σ (binderDisp (levelIsZero (σ u₁)) :: ρ))

/-- #7804's surviving wall `eut_case_wallW` follows from the W-regime
    global supply plus the table's own `TableClosed` — the wall's
    `hTC`/`convB` fields are exactly the supply's content. -/
theorem eut_case_wallW_of_convBSupplyW {E : ResolvedEnv} (hW : EnvWfT E)
    (hsup : ConvBSupplyW hW) : eut_case_wallW hW := by
  intro E' n Γ A body B₁ B₂ u₁ v₁ u₂ v₂ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ σ ρ hσ
  exact ⟨(tableWF_tableOfI_full hW).closed, hsup hB₁ hB₂⟩

#print axioms Rcic.Syn.IssuesC
#print axioms Rcic.Syn.DemandC
#print axioms Rcic.Syn.IssuesC.ap
#print axioms Rcic.Syn.IssuesC.hom
#print axioms Rcic.Syn.IssuesC.routed
#print axioms Rcic.Syn.DemandC.ap
#print axioms Rcic.Syn.DemandC.hom
#print axioms Rcic.Syn.DemandC.routed
#print axioms Rcic.Syn.lexKey_eut_lam_eut
#print axioms Rcic.Syn.lexKey_eut_lam_regCl_l
#print axioms Rcic.Syn.lexKey_eut_lam_regCl_r
#print axioms Rcic.Syn.beforeC_eut_lam_eut
#print axioms Rcic.Syn.beforeC_eut_lam_regCl_l
#print axioms Rcic.Syn.beforeC_eut_lam_regCl_r
#print axioms Rcic.Syn.StepIHC
#print axioms Rcic.Syn.CaseStepC
#print axioms Rcic.Syn.ih_issueC
#print axioms Rcic.Syn.ih_localC
#print axioms Rcic.Syn.solve_of_stepC
#print axioms Rcic.Syn.eut_lam_eut_ih
#print axioms Rcic.Syn.goal_cl_is_body_erasure
#print axioms Rcic.Syn.goal_eut_is_reg_body_erasure
#print axioms Rcic.Syn.ConvBOfEutBody
#print axioms Rcic.Syn.convB_of_eut_regCl
#print axioms Rcic.Syn.eut_lam_lam_caseStepE
#print axioms Rcic.Syn.P2QueryCV
#print axioms Rcic.Syn.GoalCV
#print axioms Rcic.Syn.convb_offcone_goalCV_false
#print axioms Rcic.Syn.convb_offcone_clw_false
#print axioms Rcic.Syn.ConvBSupplyW
#print axioms Rcic.Syn.eut_case_wallW_of_convBSupplyW

end Rcic.Syn
