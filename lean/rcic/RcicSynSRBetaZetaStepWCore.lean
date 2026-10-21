import rcic.RcicSynSRBetaZetaEpsWSubst
import rcic.RcicSynSRClEutEswW
import rcic.RcicSynStepSkeleton

/-!
# StepSuppliersW core: the epsW goal layer and its composer mirrors

The `Goal`/`CaseStep`/`Answer`/`Step` layer of the step skeleton, restated at
the display-aware erasure: `ES`→`ESW`, `CL`→`CLW`, `EUT`→`EUTW`,
`PBit`→`PBitW` (`mixed` carries `CLW ∧ EUTW`). The eps-free goals (`CTS`,
`BitCoh`, `head`, `slot`, `observation`, `obsPair`) are unchanged. The
ES-constructor composers (`refl`/`symm`/`trans`/`tyConv`/`irr`/`sorts`,
iota-proof-of-pbits) and the reg-sort/EUT/CL composers
(`reg_epsW_of_isSortOrPiHead`, `sortCoh_of_eutW_clW`, `cts_of_eutW_clW`,
`bitCoh_of_eutW_clW`) are endpoint-generic mirrors of the landed eps lemmas;
every epsW transport they need is already on this branch (`esW_*`,
`epsW_wk_keep/not_keep_of_ne`, `lsub_epsW_eq`). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the epsW goal layer -/

/- `EUTW` is not redefined here: the identical declaration landed on main
(`RcicSynSRClEutEswW`, batch 235) and is imported above — composition
only, one definition per name. -/

/-- `PBit` restated with the display-aware erasure. -/
def PBitW (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (_DT : TyP E n Γ T (.sort s)) : Prop :=
  D.epsW σ ρ = .star ↔ levelIsZero (σ s) = true

/-- `Goal` restated at `epsW`: the erasure-judgment tags swap to their `W`
    versions; every eps-free tag is verbatim. -/
def GoalW (tbl : List CRule) {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop
  | .es h _ σ ρ => ESW tbl σ ρ h
  | .cl D₁ D₂ _ σ ρ => CLW tbl σ ρ D₁ D₂
  | .eut D₁ D₂ _ σ ρ => EUTW tbl σ ρ D₁ D₂
  | .cts h DX _ _ => CTS h DX
  | .pb D DT _ σ ρ => PBitW σ ρ D DT
  | .bitCoh D₁ D₂ _ σ _ => BitCoh σ D₁ D₂
  | .mixed D₁ D₂ _ σ ρ => CLW tbl σ ρ D₁ D₂ ∧ EUTW tbl σ ρ D₁ D₂
  | .head _ uL uR _ _ _ σ _ => levelIsZero (σ uL) = levelIsZero (σ uR)
  | .slot u uD _ _ ls _ σ _ => levelIsZero (σ u) = levelIsZero (σ (instLevel ls uD))
  | .observation D θ φ ψ pos _ _ _ => ObsGoal D θ φ ψ pos
  | .obsPair D₁ D₂ _ θ _ =>
      lvlForall2 eqN (D₁.outLevels θ) (D₂.outLevels θ) ∧
      lvlForall2 (fun a b => levelIsZero a = levelIsZero b) (D₁.gateLevels θ) (D₂.gateLevels θ)

/-- `Answer` restated at `GoalW`. -/
abbrev AnswerW (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  Nonempty (ResolvedView Aw q) ∧ GoalW tbl q

/-- The strict-below hypothesis of the `epsW` recursion. -/
abbrev StepIHW (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : Prop :=
  ∀ q' : P2Query Eₐ, Demand q' → Before Aw q' q → AnswerW Aw tbl q'

/-- `CaseStep` restated at `GoalW`. -/
abbrev CaseStepW (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : Prop :=
  Demand q → StepIHW Aw tbl q → GoalW tbl q

/-- `Step` restated at `GoalW`. -/
abbrev StepW (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ q : P2Query Eₐ, Demand q →
    (∀ q' : P2Query Eₐ, Demand q' → Before Aw q' q → AnswerW Aw tbl q') →
    AnswerW Aw tbl q

/-- `ih_issue` at `GoalW`. -/
theorem ih_issueW {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule) {q : P2Query Eₐ}
    (hq : Demand q) (ih : StepIHW Aw tbl q) (q' : P2Query Eₐ) (e : Issues q q')
    (hb : Before Aw q' q) : GoalW tbl q' :=
  (ih q' (.issued q q' hq e) hb).2

/-- `ih_local` at `GoalW`. -/
theorem ih_localW {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule) {q : P2Query Eₐ}
    (hq : Demand q) (ih : StepIHW Aw tbl q) (q' : P2Query Eₐ) (e : Issues q q')
    (hp : q'.originalPrefixLength = q.originalPrefixLength)
    (hk : LexDM (q'.localKey Aw) (q.localKey Aw)) : GoalW tbl q' :=
  ih_issueW Aw tbl hq ih q' e (before_of_same_prefix Aw hp hk)

/-! ## §2 the ES-constructor composers at `epsW` (endpoint-generic mirrors) -/

/-- `es_refl` at `ESW`. -/
theorem esW_refl {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a A : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (ht : TyP E n Γ a A) (dl dr : TyP E n Γ a A)
    (hcl : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ) (dr.epsW σ ρ)) :
    ESW tbl σ ρ (CvP.refl E n Γ a A ht dl dr) := by
  simpa [ESW, CvP.dl, CvP.dr] using hcl

/-- `es_symm` at `ESW`. -/
theorem esW_symm {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b A : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n Γ a b A) (dl : TyP E n Γ b A) (dr : TyP E n Γ a A)
    (ih : ESW tbl σ ρ h)
    (hL : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ) (h.dr.epsW σ ρ))
    (hR : ConvMod (EStep tbl) LvlEq (h.dl.epsW σ ρ) (dr.epsW σ ρ)) :
    ESW tbl σ ρ (CvP.symm E n Γ a b A h dl dr) := by
  have ih' : ConvMod (EStep tbl) LvlEq (h.dl.epsW σ ρ) (h.dr.epsW σ ρ) := ih
  simpa [ESW, CvP.dl, CvP.dr] using
    (hL.trans ((ConvMod.symm' LvlEq.symm' ih').trans hR))

/-- `es_trans` at `ESW`. -/
theorem esW_trans {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b c A : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (h1 : CvP E n Γ a b A) (h2 : CvP E n Γ b c A)
    (dl : TyP E n Γ a A) (dr : TyP E n Γ c A)
    (ih1 : ESW tbl σ ρ h1) (ih2 : ESW tbl σ ρ h2)
    (cL : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ) (h1.dl.epsW σ ρ))
    (cM : ConvMod (EStep tbl) LvlEq (h1.dr.epsW σ ρ) (h2.dl.epsW σ ρ))
    (cR : ConvMod (EStep tbl) LvlEq (h2.dr.epsW σ ρ) (dr.epsW σ ρ)) :
    ESW tbl σ ρ (CvP.trans E n Γ a b c A h1 h2 dl dr) := by
  have ih1' : ConvMod (EStep tbl) LvlEq (h1.dl.epsW σ ρ) (h1.dr.epsW σ ρ) := ih1
  have ih2' : ConvMod (EStep tbl) LvlEq (h2.dl.epsW σ ρ) (h2.dr.epsW σ ρ) := ih2
  simpa [ESW, CvP.dl, CvP.dr] using
    (cL.trans (ih1'.trans (cM.trans (ih2'.trans cR))))

/-- `es_tyConv` at `ESW`. -/
theorem esW_tyConv {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b A A' : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n Γ a b A) (hA : CvP E n Γ A A' (.sort u))
    (dl : TyP E n Γ a A') (dr : TyP E n Γ b A')
    (ih : ESW tbl σ ρ h)
    (cL : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ) (h.dl.epsW σ ρ))
    (cR : ConvMod (EStep tbl) LvlEq (h.dr.epsW σ ρ) (dr.epsW σ ρ)) :
    ESW tbl σ ρ (CvP.tyConv E n Γ a b A A' u h hA dl dr) := by
  have ih' : ConvMod (EStep tbl) LvlEq (h.dl.epsW σ ρ) (h.dr.epsW σ ρ) := ih
  simpa [ESW, CvP.dl, CvP.dr] using (cL.trans (ih'.trans cR))

/-- `es_irr_star` at `ESW`. -/
theorem esW_irr_star {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {P p q : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (hP : TyP E n Γ P (.sort .zero)) (hp : TyP E n Γ p P) (hq : TyP E n Γ q P)
    (dl : TyP E n Γ p P) (dr : TyP E n Γ q P)
    (hl : dl.epsW σ ρ = .star) (hr : dr.epsW σ ρ = .star) :
    ESW tbl σ ρ (CvP.irr E n Γ P p q hP hp hq dl dr) := by
  simp only [ESW, CvP.dl, CvP.dr, hl, hr]
  exact .refl _

/-- `es_sorts` at `ESW`. -/
theorem esW_sorts {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {l₁ l₂ : Level} {σ : Level → Level} {ρ : List Disp}
    (hσ : ∀ {l l' : Level}, eqN l l' → eqN (σ l) (σ l'))
    (h : eqN l₁ l₂) (dl : TyP E n Γ (.sort l₁) (.sort (.succ l₁)))
    (dr : TyP E n Γ (.sort l₂) (.sort (.succ l₁)))
    (hL : LvlEq (dl.epsW σ ρ) (.sort (σ l₁)))
    (hR : LvlEq (.sort (σ l₂)) (dr.epsW σ ρ)) :
    ESW tbl σ ρ (CvP.sorts E n Γ l₁ l₂ h dl dr) := by
  have hmid : LvlEq (.sort (σ l₁)) (.sort (σ l₂)) := .sort (hσ h)
  simpa [ESW, CvP.dl, CvP.dr] using
    ((ConvMod.eqv hL).trans ((ConvMod.eqv hmid).trans (ConvMod.eqv hR)))

/-- `es_iota_proof_of_pbits` at `ESW`: the proof-result branch of `iota`. -/
theorem esW_iota_proof_of_pbitWs (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T) (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (hu : levelIsZero (σ hlhs.reg.1) = true)
    (pL : PBitW σ ρ dl hlhs.reg.2) (pR : PBitW σ ρ dr hlhs.reg.2) :
    ESW tbl σ ρ (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) := by
  have hL := pL.mpr hu
  have hR := pR.mpr hu
  simpa [ESW, CvP.dl, CvP.dr, hL, hR] using (ConvMod.refl _)

/-! ## §3 the reg-sort decomposition and the EUT/CL composers at `epsW` -/

/-- `TyP.sort`'s `epsW` is `.sort (σ u)` (`rfl`: the base arm is `eps` verbatim). -/
theorem epsW_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u : Level} {σ : Level → Level}
    {ρ : List Disp} :
    (TyP.sort E n Γ u (.succ u) (eqN_refl _)).epsW σ ρ = .sort (σ u) := rfl

/-- `reg_eps_of_isSortOrPiHead` at `epsW`: the decomposition recursion runs
    verbatim at the display-aware erasure (the `wk`/`esub`/`lsub` steps use the
    `epsW` arm equations). -/
theorem reg_epsW_of_isSortOrPiHead :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e S : Expr Nat} →
    (D : TyP E n Γ e S) → D.isSortOrPiHead = true →
    ∃ w : Level, S = .sort w ∧ ∀ (σ : Level → Level) (ρ : List Disp),
      D.reg.2.epsW σ ρ = .sort (σ w)
  | _, _, _, _, _, .sort _ _ _ _ k _, _ => ⟨k, rfl, fun _ _ => rfl⟩
  | _, _, _, _, _, .pi _ _ _ _ u _ v _ _, _ => ⟨.imax u v, rfl, fun _ _ => rfl⟩
  | _, _, _, _, _, .bvar .., h => Bool.noConfusion h
  | _, _, _, _, _, .const .., h => Bool.noConfusion h
  | _, _, _, _, _, .lam .., h => Bool.noConfusion h
  | _, _, _, _, _, .app .., h => Bool.noConfusion h
  | _, _, _, _, _, .letE .., h => Bool.noConfusion h
  | _, _, _, _, _, .lit .., h => Bool.noConfusion h
  | _, _, _, _, _, .conv .., h => Bool.noConfusion h
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D, h => by
      obtain ⟨w, rfl, heps⟩ := reg_epsW_of_isSortOrPiHead D h
      refine ⟨w, rfl, fun σ ρ => ?_⟩
      simp only [TyP.reg]
      by_cases hk : ρ[c]? = some .keep
      · rw [epsW_wk_keep hk, heps σ (wkInnerDisp ρ c)]
        rfl
      · rw [epsW_wk_not_keep_of_ne hk, heps σ (removeAt ρ c)]
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ _ _, h => by
      obtain ⟨w, rfl, heps⟩ := reg_epsW_of_isSortOrPiHead D h
      refine ⟨w, rfl, fun σ ρ => ?_⟩
      simp only [TyP.reg, TyP.epsW]
      cases levelIsZero (σ u) with
      | true => exact heps σ (insertDisp .drop j ρ)
      | false =>
          rw [heps σ (insertDisp .keep j ρ)]
          rfl
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D hget hv hvT, h => by
      obtain ⟨w, rfl, heps⟩ := reg_epsW_of_isSortOrPiHead D h
      refine ⟨w, rfl, fun σ ρ => ?_⟩
      simp only [TyP.reg]
      rw [lsub_epsW_eq D.reg.2 hget hv hvT]
      exact heps σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.epsW σ ρ)) j ρ)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, h => by
      obtain ⟨w₀, rfl, heps⟩ := reg_epsW_of_isSortOrPiHead D h
      refine ⟨instLevel ls w₀, rfl, fun σ ρ => ?_⟩
      simp only [TyP.reg, TyP.epsW]
      exact heps (fun l => σ (instLevel ls l)) ρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, h => by
      obtain ⟨w, rfl, heps⟩ := reg_epsW_of_isSortOrPiHead D h
      exact ⟨w, rfl, fun σ ρ => heps σ ρ⟩
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, h => by
      obtain ⟨w, rfl, heps⟩ := reg_epsW_of_isSortOrPiHead D h
      exact ⟨w, rfl, fun σ ρ => heps σ ρ⟩

/-- `reg_eps_sort_of_isSortOrPiHead` at `epsW`. -/
theorem reg_epsW_sort_of_isSortOrPiHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T : Expr Nat} {u : Level} (D : TyP E n Γ T (.sort u))
    (h : D.isSortOrPiHead = true) (σ : Level → Level) (ρ : List Disp) :
    D.reg.2.epsW σ ρ = .sort (σ u) := by
  obtain ⟨w, hw, heps⟩ := reg_epsW_of_isSortOrPiHead D h
  cases Expr.sort.inj hw
  exact heps σ ρ

/-- `cl_reg_sort_of_isSortOrPiHead` at `CLW`. -/
theorem clW_reg_sort_of_isSortOrPiHead (tbl : List CRule) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {T : Expr Nat} {u : Level} (D : TyP E n Γ T (.sort u))
    (h : D.isSortOrPiHead = true) (σ : Level → Level) (ρ : List Disp) :
    CLW tbl σ ρ D.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)) := by
  unfold CLW
  rw [reg_epsW_sort_of_isSortOrPiHead D h σ ρ, epsW_sort]
  exact .refl _

/-- `sortCoh_of_eut_cl` at the `epsW` endpoints. -/
theorem sortCoh_of_eutW_clW {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (heut : EUTW tbl σ ρ D₁ D₂)
    (hL : CLW tbl σ ρ D₁.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
    (hR : CLW tbl σ ρ D₂.reg.2 (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    SortCoh σ D₁ D₂ := by
  have hL' : ConvMod (EStep tbl) LvlEq (D₁.reg.2.epsW σ ρ) (.sort (σ u)) := by
    simpa only [CLW, epsW_sort] using hL
  have hR' : ConvMod (EStep tbl) LvlEq (D₂.reg.2.epsW σ ρ) (.sort (σ v)) := by
    simpa only [CLW, epsW_sort] using hR
  exact eqN_of_convE_sort_wf hW
    ((ConvMod.symm' LvlEq.symm' hL').trans (heut.trans hR'))

/-- `bitCoh_of_eut_cl` at the `epsW` endpoints. -/
theorem bitCoh_of_eutW_clW {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (heut : EUTW tbl σ ρ D₁ D₂)
    (hL : CLW tbl σ ρ D₁.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
    (hR : CLW tbl σ ρ D₂.reg.2 (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    BitCoh σ D₁ D₂ :=
  bitCoh_of_sortCoh (sortCoh_of_eutW_clW hW D₁ D₂ σ ρ heut hL hR)

/-- `cts_of_eut_cl` at the `epsW` endpoints. -/
theorem cts_of_eutW_clW {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (ρ : List Disp)
    (heut : EUTW tbl id ρ h.dl DX)
    (hL : CLW tbl id ρ h.dl.reg.2 (TyP.sort E n Γ w (.succ w) (eqN_refl _)))
    (hR : CLW tbl id ρ DX.reg.2 (TyP.sort E n Γ s (.succ s) (eqN_refl _))) :
    CTS h DX :=
  cts_of_sortCoh_id h DX (sortCoh_of_eutW_clW hW h.dl DX id ρ heut hL hR)

end Rcic.Syn

#print axioms Rcic.Syn.GoalW
#print axioms Rcic.Syn.esW_refl
#print axioms Rcic.Syn.esW_symm
#print axioms Rcic.Syn.esW_trans
#print axioms Rcic.Syn.esW_tyConv
#print axioms Rcic.Syn.esW_irr_star
#print axioms Rcic.Syn.esW_sorts
#print axioms Rcic.Syn.esW_iota_proof_of_pbitWs
#print axioms Rcic.Syn.reg_epsW_of_isSortOrPiHead
#print axioms Rcic.Syn.clW_reg_sort_of_isSortOrPiHead
#print axioms Rcic.Syn.sortCoh_of_eutW_clW
#print axioms Rcic.Syn.bitCoh_of_eutW_clW
#print axioms Rcic.Syn.cts_of_eutW_clW






