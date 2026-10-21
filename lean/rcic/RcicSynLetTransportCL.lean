import rcic.RcicSynPiWalk

/-!
# Syntactic sortRow, build step 3aw — `CvP.iota` proof/relevant arms, `TyP.letE` coherence, and transport `CL` / `EUT`

`research/rcic/semantic/S3_ES_ARMS.md` §49.

1. **§1 `CvP.iota` proof-erasure and relevant arms**:
   - `iota_dl_proof` and `iota_dr_proof`: when `levelIsZero (σ hlhs.reg.1) = true`,
     `Bel.pb` on `(dl, hlhs.reg.2)` and `(dr, hlhs.reg.2)` forces both
     `dl.eps σ ρ = .star` and `dr.eps σ ρ = .star`.
   - `es_of_below_iota_proof`: when `levelIsZero (σ hlhs.reg.1) = true` (including
     K-style `iotaStarK` on single-constructor `Prop` families and any small
     elimination into `Prop`), `ES tbl σ ρ (CvP.iota ...)` holds by `.refl .star`
     with **zero table rules**.
   - `iota_hlhs_not_star` and `iota_hrhs_not_star`: when `levelIsZero (σ hlhs.reg.1) = false`,
     `hlhs.eps σ ρ ≠ .star` and `hrhs.eps σ ρ ≠ .star`.

2. **§2 `TyP.letE` `CL` and `EUT` coherence (direct and via Option L-inline-at-0 `letSub`)**:
   - `cl_letE_nodes_drop` and `cl_letE_nodes_inline_eq`: direct `CL` on two `TyP.letE`
     nodes when both values erase to `★` or to the same non-`★` value `ev`.
   - `cl_letE_left_iff_letSub`, `cl_letE_right_iff_letSub`, and `cl_letE_nodes_iff_letSub`:
     under Option L-inline-at-0 (`letSub_eps_eq_letE`), `CL` of `TyP.letE` reduces
     to `CL` of `letSub hb hv hA` in `Γ` at `(σ, ρ)` with **zero `.letBinding`
     context extension**.
   - `eut_letE_nodes`: `EUT` on two `TyP.letE` nodes from `ConvMod` of their
     instantiated body-type sort typings `hT₁, hT₂`.

3. **§3 Same-constructor `EUT` coherence (`bvar`, `const`, `app`, `lit`, `conv`)**:
   - `eut_bvar_nodes`, `eut_const_nodes`, `eut_app_nodes`, `eut_lit_nodes`,
     `eut_conv_left`, `eut_conv_right`.

4. **§4 Transport `CL` and `EUT` coherence (`ewk`, `cctx`, `linst`, `wk`, `esub`, `lsub`)**:
   - `cl_ewk_left`, `cl_ewk_right`, `eut_ewk_left`, `eut_ewk_right`,
     `cl_cctx_left`, `cl_cctx_right`, `eut_cctx_left`, `eut_cctx_right`,
     `cl_linst_both`, `eut_linst_both`,
     `cl_wk_not_keep_both`, `cl_wk_keep_both`, `eut_wk_not_keep_both`, `eut_wk_keep_both`,
     `cl_esub_drop_both`, `cl_esub_keep_both`, `eut_esub_drop_both`, `eut_esub_keep_both`,
     `cl_lsub_drop_both`, `cl_lsub_inline_eq_both`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `CvP.iota`: proof-erasure and relevant arms -/

/-- When the return sort of `CvP.iota` is `Prop` under `σ` (`levelIsZero (σ hlhs.reg.1) = true`),
    `Bel.pb dl hlhs.reg.2` forces `dl.eps σ ρ = .star`. -/
theorem iota_dl_proof (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hlhs.reg.1) = true)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr))) :
    dl.eps σ ρ = .star := by
  let hnode := CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr
  have ht : hnode.isTransport = false := rfl
  have hwlhs : hlhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwreg : hlhs.reg.2.wt Aw < hnode.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hlhs) hwlhs
  exact (Bel.pb dl hlhs.reg.2 σ ρ hρ
    (lex_of_dm (dmStep_pair_below Aw hnode ht dl hlhs.reg.2 hwl hwreg))).mpr hu

/-- When the return sort of `CvP.iota` is `Prop` under `σ` (`levelIsZero (σ hlhs.reg.1) = true`),
    `Bel.pb dr hlhs.reg.2` forces `dr.eps σ ρ = .star`. -/
theorem iota_dr_proof (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hlhs.reg.1) = true)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr))) :
    dr.eps σ ρ = .star := by
  let hnode := CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr
  have ht : hnode.isTransport = false := rfl
  have hwlhs : hlhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwreg : hlhs.reg.2.wt Aw < hnode.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hlhs) hwlhs
  exact (Bel.pb dr hlhs.reg.2 σ ρ hρ
    (lex_of_dm (dmStep_pair_below Aw hnode ht dr hlhs.reg.2 hwr hwreg))).mpr hu

/-- `ES` for `CvP.iota` when the return sort is `Prop` under `σ` (`levelIsZero (σ hlhs.reg.1) = true`,
    including `iotaStarK` on single-constructor `Prop` families and small elimination into `Prop`):
    both endpoints erase to `★`, requiring **zero table rules**. -/
theorem es_of_below_iota_proof (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hlhs.reg.1) = true)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr))) :
    ES tbl σ ρ (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) := by
  have hL := iota_dl_proof Aw tbl h hlhs hrhs dl dr σ ρ hρ hu Bel
  have hR := iota_dr_proof Aw tbl h hlhs hrhs dl dr σ ρ hρ hu Bel
  simp only [ES, CvP.dl, CvP.dr, hL, hR]
  exact .refl _

/-- On a relevant return sort (`levelIsZero (σ hlhs.reg.1) = false`), `hlhs.eps σ ρ ≠ .star`. -/
theorem iota_hlhs_not_star (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hlhs.reg.1) = false)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr))) :
    hlhs.eps σ ρ ≠ .star := by
  let hnode := CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr
  have ht : hnode.isTransport = false := rfl
  have hwlhs : hlhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwreg : hlhs.reg.2.wt Aw < hnode.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hlhs) hwlhs
  have hpb := Bel.pb hlhs hlhs.reg.2 σ ρ hρ
    (lex_of_dm (dmStep_pair_below Aw hnode ht hlhs hlhs.reg.2 hwlhs hwreg))
  intro hs
  exact Bool.noConfusion (hu.symm.trans (hpb.mp hs))

/-- On a relevant return sort (`levelIsZero (σ hlhs.reg.1) = false`), `hrhs.eps σ ρ ≠ .star`. -/
theorem iota_hrhs_not_star (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hlhs.reg.1) = false)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr))) :
    hrhs.eps σ ρ ≠ .star := by
  let hnode := CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr
  have ht : hnode.isTransport = false := rfl
  have hwlhs : hlhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwrhs : hrhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwreg : hlhs.reg.2.wt Aw < hnode.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hlhs) hwlhs
  have hpb := Bel.pb hrhs hlhs.reg.2 σ ρ hρ
    (lex_of_dm (dmStep_pair_below Aw hnode ht hrhs hlhs.reg.2 hwrhs hwreg))
  intro hs
  exact Bool.noConfusion (hu.symm.trans (hpb.mp hs))

/-! ## §2 `TyP.letE` `CL` and `EUT` coherence (direct and via Option L-inline-at-0 `letSub`) -/

/-- `CL` on two `TyP.letE` nodes when both let-values erase to `★`. -/
theorem cl_letE_nodes_drop (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (hs₁ : hv₁.eps σ ρ = .star) (hs₂ : hv₂.eps σ ρ = .star)
    (hclb : CL tbl σ (.drop :: ρ) hb₁ hb₂) :
    CL tbl σ ρ
      (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
      (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) := by
  unfold CL at hclb ⊢
  simp only [TyP.eps, hs₁, hs₂]
  exact hclb

/-- `CL` on two `TyP.letE` nodes when both let-values erase to the same non-`★` term `ev`. -/
theorem cl_letE_nodes_inline_eq (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    {ev : ETm}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (hev₁ : hv₁.eps σ ρ = ev) (hev₂ : hv₂.eps σ ρ = ev) (hne : ev ≠ .star)
    (hclb : CL tbl σ (.inline ev :: ρ) hb₁ hb₂) :
    CL tbl σ ρ
      (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
      (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) := by
  unfold CL at hclb ⊢
  simp only [TyP.eps, hev₁, hev₂]
  cases ev <;> first | exact absurd rfl hne | exact hclb

/-- Under Option L-inline-at-0 (`letSub_eps_eq_letE`), `CL` with a `TyP.letE` on the left
    is equivalent to `CL` with `letSub hb hv hA` at `(σ, ρ)` (zero `.letBinding` extension). -/
theorem cl_letE_left_iff_letSub (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B T₂ : Expr Nat} {u w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A)
    (hb : TyP E n (.letBinding A v :: Γ) b B)
    (hT : TyP E n Γ (instantiate0 v B) (.sort w))
    (D₂ : TyP E n Γ (.letE A v b) T₂) :
    CL tbl σ ρ (TyP.letE E n Γ A u v B b w hA hv hb hT) D₂ ↔
      ConvMod (EStep tbl) LvlEq ((letSub hb hv hA).eps σ ρ) (D₂.eps σ ρ) := by
  unfold CL
  rw [letSub_eps_eq_letE hA hv hb hT σ ρ]

/-- Under Option L-inline-at-0 (`letSub_eps_eq_letE`), `CL` with a `TyP.letE` on the right
    is equivalent to `CL` with `letSub hb hv hA` at `(σ, ρ)` (zero `.letBinding` extension). -/
theorem cl_letE_right_iff_letSub (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b T₁ B : Expr Nat} {u w : Level}
    (D₁ : TyP E n Γ (.letE A v b) T₁)
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A)
    (hb : TyP E n (.letBinding A v :: Γ) b B)
    (hT : TyP E n Γ (instantiate0 v B) (.sort w)) :
    CL tbl σ ρ D₁ (TyP.letE E n Γ A u v B b w hA hv hb hT) ↔
      ConvMod (EStep tbl) LvlEq (D₁.eps σ ρ) ((letSub hb hv hA).eps σ ρ) := by
  unfold CL
  rw [letSub_eps_eq_letE hA hv hb hT σ ρ]

/-- Under Option L-inline-at-0 (`letSub_eps_eq_letE`), `CL` on two `TyP.letE` nodes
    is equivalent to `CL tbl σ ρ (letSub hb₁ hv₁ hA₁) (letSub hb₂ hv₂ hA₂)` in `Γ`. -/
theorem cl_letE_nodes_iff_letSub (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂)) :
    CL tbl σ ρ
      (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
      (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) ↔
      CL tbl σ ρ (letSub hb₁ hv₁ hA₁) (letSub hb₂ hv₂ hA₂) := by
  unfold CL
  rw [letSub_eps_eq_letE hA₁ hv₁ hb₁ hT₁ σ ρ, letSub_eps_eq_letE hA₂ hv₂ hb₂ hT₂ σ ρ]

/-- `EUT` on two `TyP.letE` nodes from `ConvMod` of their type sort typings `hT₁, hT₂`. -/
theorem eut_letE_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (hconv : ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ) (hT₂.eps σ ρ)) :
    EUT tbl σ ρ
      (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
      (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) :=
  hconv

/-! ## §3 Same-constructor `EUT` coherence (`bvar`, `const`, `app`, `lit`, `conv`) -/

/-- `EUT` on two `TyP.bvar` nodes at index `i` from `ConvMod` of `hA₁.eps` and `hA₂.eps`. -/
theorem eut_bvar_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A₁ A₂ : Expr Nat} {u₁ u₂ : Level}
    (hlook₁ : lookupType Γ i = some A₁) (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hlook₂ : lookupType Γ i = some A₂) (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (hconv : ConvMod (EStep tbl) LvlEq (hA₁.eps σ ρ) (hA₂.eps σ ρ)) :
    EUT tbl σ ρ (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁) (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂) :=
  hconv

/-- `EUT` on two `TyP.const` nodes at `(r, ls)` from `ConvMod` of `hT₁.eps` and `hT₂.eps`. -/
theorem eut_const_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₁ ls₂ : List Level}
    {m₁ m₂ : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁))
    (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m₂.mtype) (.sort u₂))
    (hconv : ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ) (hT₂.eps σ ρ)) :
    EUT tbl σ ρ
      (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
      (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) :=
  hconv

/-- `EUT` on two `TyP.app` nodes from `ConvMod` of `hT₁.eps` and `hT₂.eps`. -/
theorem eut_app_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hconv : ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ) (hT₂.eps σ ρ)) :
    EUT tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) :=
  hconv

/-- `EUT` on two `TyP.lit` nodes is identical to `EUT` on their expansions. -/
theorem eut_lit_nodes (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T₁ T₂ : Expr Nat}
    (hexp₁ : TyP E n Γ (natExpand t) T₁) (hexp₂ : TyP E n Γ (natExpand t) T₂) :
    EUT tbl σ ρ (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂) ↔
      EUT tbl σ ρ hexp₁ hexp₂ :=
  Iff.rfl

/-- `EUT` on `TyP.conv` on the left follows from `ES tbl σ ρ hc`, `CL tbl σ ρ hc.dl h.reg.2`,
    and `EUT tbl σ ρ h D₂`. -/
theorem eut_conv_left (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B T₂ : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) (D₂ : TyP E n Γ e T₂)
    (hes : ES tbl σ ρ hc)
    (hcl : CL tbl σ ρ hc.dl h.reg.2)
    (heut : EUT tbl σ ρ h D₂) :
    EUT tbl σ ρ (TyP.conv E n Γ e A B u h hc) D₂ := by
  unfold EUT at heut ⊢
  unfold ES at hes
  unfold CL at hcl
  simp only [TyP.reg]
  exact (ConvMod.symm' LvlEq.symm' hes).trans (hcl.trans heut)

/-- `EUT` on `TyP.conv` on the right follows from `EUT tbl σ ρ D₁ h`, `CL tbl σ ρ h.reg.2 hc.dl`,
    and `ES tbl σ ρ hc`. -/
theorem eut_conv_right (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ A B : Expr Nat} {u : Level}
    (D₁ : TyP E n Γ e T₁) (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (heut : EUT tbl σ ρ D₁ h)
    (hcl : CL tbl σ ρ h.reg.2 hc.dl)
    (hes : ES tbl σ ρ hc) :
    EUT tbl σ ρ D₁ (TyP.conv E n Γ e A B u h hc) := by
  unfold EUT at heut ⊢
  unfold ES at hes
  unfold CL at hcl
  simp only [TyP.reg]
  exact heut.trans (hcl.trans hes)

/-! ## §4 Transport `CL` and `EUT` coherence (`ewk`, `cctx`, `linst`, `wk`, `esub`, `lsub`) -/

theorem cl_ewk_left (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (hext : EnvExt E₀ E) (D₁ : TyP E₀ n Γ e T₁) (D₂ : TyP E n Γ e T₂) :
    CL tbl σ ρ (TyP.ewk E₀ E n Γ e T₁ hext D₁) D₂ ↔
      ConvMod (EStep tbl) LvlEq (D₁.eps σ ρ) (D₂.eps σ ρ) :=
  Iff.rfl

theorem cl_ewk_right (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (hext : EnvExt E₀ E) (D₂ : TyP E₀ n Γ e T₂) :
    CL tbl σ ρ D₁ (TyP.ewk E₀ E n Γ e T₂ hext D₂) ↔
      ConvMod (EStep tbl) LvlEq (D₁.eps σ ρ) (D₂.eps σ ρ) :=
  Iff.rfl

theorem eut_ewk_left (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (hext : EnvExt E₀ E) (D₁ : TyP E₀ n Γ e T₁) (D₂ : TyP E n Γ e T₂) :
    EUT tbl σ ρ (TyP.ewk E₀ E n Γ e T₁ hext D₁) D₂ ↔
      ConvMod (EStep tbl) LvlEq (D₁.reg.2.eps σ ρ) (D₂.reg.2.eps σ ρ) :=
  Iff.rfl

theorem eut_ewk_right (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (hext : EnvExt E₀ E) (D₂ : TyP E₀ n Γ e T₂) :
    EUT tbl σ ρ D₁ (TyP.ewk E₀ E n Γ e T₂ hext D₂) ↔
      ConvMod (EStep tbl) LvlEq (D₁.reg.2.eps σ ρ) (D₂.reg.2.eps σ ρ) :=
  Iff.rfl

theorem cl_cctx_left (tbl : List CRule) (σ : Level → Level) (ρ' : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ A A' : Expr Nat} {u : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA : CvP E n Γ A A' (.sort u))
    (D₂ : TyP E n (.assumption A' :: Γ) e T₂) :
    CL tbl σ ρ' (TyP.cctx E n Γ e T₁ A A' u D₁ hA) D₂ ↔
      ConvMod (EStep tbl) LvlEq (D₁.eps σ ρ') (D₂.eps σ ρ') :=
  Iff.rfl

theorem cl_cctx_right (tbl : List CRule) (σ : Level → Level) (ρ' : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ A A' : Expr Nat} {u : Level}
    (D₁ : TyP E n (.assumption A' :: Γ) e T₁)
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA : CvP E n Γ A A' (.sort u)) :
    CL tbl σ ρ' D₁ (TyP.cctx E n Γ e T₂ A A' u D₂ hA) ↔
      ConvMod (EStep tbl) LvlEq (D₁.eps σ ρ') (D₂.eps σ ρ') :=
  Iff.rfl

theorem eut_cctx_left (tbl : List CRule) (σ : Level → Level) (ρ' : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ A A' : Expr Nat} {u : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA : CvP E n Γ A A' (.sort u))
    (D₂ : TyP E n (.assumption A' :: Γ) e T₂) :
    EUT tbl σ ρ' (TyP.cctx E n Γ e T₁ A A' u D₁ hA) D₂ ↔
      ConvMod (EStep tbl) LvlEq (D₁.reg.2.eps σ ρ') (D₂.reg.2.eps σ ρ') :=
  Iff.rfl

theorem eut_cctx_right (tbl : List CRule) (σ : Level → Level) (ρ' : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ A A' : Expr Nat} {u : Level}
    (D₁ : TyP E n (.assumption A' :: Γ) e T₁)
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA : CvP E n Γ A A' (.sort u)) :
    EUT tbl σ ρ' D₁ (TyP.cctx E n Γ e T₂ A A' u D₂ hA) ↔
      ConvMod (EStep tbl) LvlEq (D₁.reg.2.eps σ ρ') (D₂.reg.2.eps σ ρ') :=
  Iff.rfl

theorem cl_linst_both (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    {ls : List Level} (hls₁ hls₂ : levelsBounded n ls = true) (hlen₁ hlen₂ : ls.length = a')
    (D₁ : TyP E a' Γ e T₁) (D₂ : TyP E a' Γ e T₂) :
    CL tbl σ ρ
      (TyP.linst E a' n Γ e T₁ ls hls₁ hlen₁ D₁)
      (TyP.linst E a' n Γ e T₂ ls hls₂ hlen₂ D₂) ↔
      CL tbl (fun l => σ (instLevel ls l)) ρ D₁ D₂ :=
  Iff.rfl

theorem eut_linst_both (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    {ls : List Level} (hls₁ hls₂ : levelsBounded n ls = true) (hlen₁ hlen₂ : ls.length = a')
    (D₁ : TyP E a' Γ e T₁) (D₂ : TyP E a' Γ e T₂) :
    EUT tbl σ ρ
      (TyP.linst E a' n Γ e T₁ ls hls₁ hlen₁ D₁)
      (TyP.linst E a' n Γ e T₂ ls hls₂ hlen₂ D₂) ↔
      EUT tbl (fun l => σ (instLevel ls l)) ρ D₁ D₂ :=
  Iff.rfl

theorem cl_wk_not_keep_both {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} {d : LocalDecl} {c : Nat} {σ : Level → Level} {ρ : List Disp}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (ih : CL tbl σ (removeAt ρ c) D₁ D₂) :
    CL tbl σ ρ (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂) := by
  simpa only [CL, eps_wk_not_keep (D := D₁) hk, eps_wk_not_keep (D := D₂) hk] using ih

theorem cl_wk_keep_both {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} {d : LocalDecl} {c : Nat} {σ : Level → Level} {ρ : List Disp}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (hk : ρ[c]? = some .keep)
    (ih : CL tbl σ (removeAt ρ c) D₁ D₂) :
    CL tbl σ ρ (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂) := by
  simpa only [CL, eps_wk_keep (D := D₁) hk, eps_wk_keep (D := D₂) hk]
    using convMod_lift hcl ih (countKeep (ρ.take c)) 1

theorem eut_wk_not_keep_both {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} {d : LocalDecl} {c : Nat} {σ : Level → Level} {ρ : List Disp}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (ih : EUT tbl σ (removeAt ρ c) D₁ D₂) :
    EUT tbl σ ρ (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂) := by
  simpa only [EUT, TyP.reg, eps_wk_not_keep (D := D₁.reg.2) hk, eps_wk_not_keep (D := D₂.reg.2) hk]
    using ih

theorem eut_wk_keep_both {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} {d : LocalDecl} {c : Nat} {σ : Level → Level} {ρ : List Disp}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (hk : ρ[c]? = some .keep)
    (ih : EUT tbl σ (removeAt ρ c) D₁ D₂) :
    EUT tbl σ ρ (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂) := by
  simpa only [EUT, TyP.reg, eps_wk_keep (D := D₁.reg.2) hk, eps_wk_keep (D := D₂.reg.2) hk]
    using convMod_lift hcl ih (countKeep (ρ.take c)) 1

theorem cl_esub_drop_both {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ t v : Expr Nat} {j : Nat} {u₁ u₂ : Level} {σ : Level → Level} {ρ : List Disp}
    (D₁ : TyP E n Γ e T₁) (hget₁ : Γ[j]? = some (.assumption t))
    (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₁))
    (D₂ : TyP E n Γ e T₂) (hget₂ : Γ[j]? = some (.assumption t))
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₂))
    (hu₁ : levelIsZero (σ u₁) = true) (hu₂ : levelIsZero (σ u₂) = true)
    (ih : CL tbl σ (insertDisp .drop j ρ) D₁ D₂) :
    CL tbl σ ρ
      (TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
      (TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂) := by
  simpa only [CL, eps_esub_drop (D := D₁) hu₁, eps_esub_drop (D := D₂) hu₂] using ih

theorem cl_esub_keep_both {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ t v : Expr Nat} {j : Nat} {u₁ u₂ : Level} {σ : Level → Level} {ρ : List Disp}
    (D₁ : TyP E n Γ e T₁) (hget₁ : Γ[j]? = some (.assumption t))
    (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₁))
    (D₂ : TyP E n Γ e T₂) (hget₂ : Γ[j]? = some (.assumption t))
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₂))
    (hu₁ : levelIsZero (σ u₁) = false) (hu₂ : levelIsZero (σ u₂) = false)
    (ihD : CL tbl σ (insertDisp .keep j ρ) D₁ D₂)
    (ihv : CL tbl σ ρ hv₁ hv₂) :
    CL tbl σ ρ
      (TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
      (TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂) := by
  unfold CL at ihD ihv ⊢
  rw [eps_esub_keep (D := D₁) hu₁, eps_esub_keep (D := D₂) hu₂]
  exact (convMod_inst_body hcl ihD (countKeep (ρ.take j)) (hv₁.eps σ ρ)).trans
    (convMod_inst_repl hcl ihv (D₂.eps σ (insertDisp .keep j ρ)) (countKeep (ρ.take j)))

theorem eut_esub_drop_both {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ t v : Expr Nat} {j : Nat} {u₁ u₂ : Level} {σ : Level → Level} {ρ : List Disp}
    (D₁ : TyP E n Γ e T₁) (hget₁ : Γ[j]? = some (.assumption t))
    (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₁))
    (D₂ : TyP E n Γ e T₂) (hget₂ : Γ[j]? = some (.assumption t))
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₂))
    (hu₁ : levelIsZero (σ u₁) = true) (hu₂ : levelIsZero (σ u₂) = true)
    (ih : EUT tbl σ (insertDisp .drop j ρ) D₁ D₂) :
    EUT tbl σ ρ
      (TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
      (TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂) := by
  simpa only [EUT, TyP.reg, eps_esub_drop (D := D₁.reg.2) hu₁, eps_esub_drop (D := D₂.reg.2) hu₂]
    using ih

theorem eut_esub_keep_both {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ t v : Expr Nat} {j : Nat} {u₁ u₂ : Level} {σ : Level → Level} {ρ : List Disp}
    (D₁ : TyP E n Γ e T₁) (hget₁ : Γ[j]? = some (.assumption t))
    (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₁))
    (D₂ : TyP E n Γ e T₂) (hget₂ : Γ[j]? = some (.assumption t))
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₂))
    (hu₁ : levelIsZero (σ u₁) = false) (hu₂ : levelIsZero (σ u₂) = false)
    (ihD : EUT tbl σ (insertDisp .keep j ρ) D₁ D₂)
    (ihv : CL tbl σ ρ hv₁ hv₂) :
    EUT tbl σ ρ
      (TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
      (TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂) := by
  unfold EUT at ihD ⊢
  unfold CL at ihv
  simp only [TyP.reg]
  rw [eps_esub_keep (D := D₁.reg.2) hu₁, eps_esub_keep (D := D₂.reg.2) hu₂]
  exact (convMod_inst_body hcl ihD (countKeep (ρ.take j)) (hv₁.eps σ ρ)).trans
    (convMod_inst_repl hcl ihv (D₂.reg.2.eps σ (insertDisp .keep j ρ)) (countKeep (ρ.take j)))

theorem cl_lsub_drop_both {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ t v : Expr Nat} {j : Nat} {u₁ u₂ : Level} {σ : Level → Level} {ρ : List Disp}
    (D₁ : TyP E n Γ e T₁) (hget₁ : Γ[j]? = some (.letBinding t v))
    (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₁))
    (D₂ : TyP E n Γ e T₂) (hget₂ : Γ[j]? = some (.letBinding t v))
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₂))
    (hs₁ : hv₁.eps σ ρ = .star) (hs₂ : hv₂.eps σ ρ = .star)
    (ih : CL tbl σ (insertDisp .drop j ρ) D₁ D₂) :
    CL tbl σ ρ
      (TyP.lsub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
      (TyP.lsub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂) := by
  unfold CL at ih ⊢
  simp only [eps_lsub, hs₁, hs₂]
  exact ih

theorem cl_lsub_inline_eq_both {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ t v : Expr Nat} {j : Nat} {u₁ u₂ : Level} {σ : Level → Level} {ρ : List Disp}
    {ev : ETm}
    (D₁ : TyP E n Γ e T₁) (hget₁ : Γ[j]? = some (.letBinding t v))
    (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₁))
    (D₂ : TyP E n Γ e T₂) (hget₂ : Γ[j]? = some (.letBinding t v))
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₂))
    (hev₁ : hv₁.eps σ ρ = ev) (hev₂ : hv₂.eps σ ρ = ev) (hne : ev ≠ .star)
    (ih : CL tbl σ (insertDisp (.inline (localize (countKeep (ρ.take j)) ev)) j ρ) D₁ D₂) :
    CL tbl σ ρ
      (TyP.lsub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
      (TyP.lsub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂) := by
  unfold CL at ih ⊢
  simp only [eps_lsub, hev₁, hev₂]
  cases ev <;> first | exact absurd rfl hne | exact ih

end Rcic.Syn
