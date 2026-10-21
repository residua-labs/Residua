import rcic.RcicSynLetSub
import rcic.RcicSynLetInline
import rcic.RcicSynEtaMeet
import rcic.RcicSynTagCoh

/-!
# BelowC §8 + §3.2 — the two let-branch finishes and the η consumer

`research/rcic/sortrow/BELOWC_FAILED_READERS_AND_LET_BODY.md` §8 and §3.2,
as local compositions: each row takes the port answers as hypotheses
(`PB[·,T0]`, `CL`, `TagCoh`) and never the current ES. `closure_claim` stays 0.

* **§8.1 proof-result branch.** `w := hb.dr.reg.1`, `H := hb.dr.reg.2`,
  `T0 := letSub H hv.dl hA.dl` types the ascribed type `instantiate0 v B` at
  `sort w`. `wt T0 = 1 + wt H + wt hv.dl + wt hA.dl < N` (regularity ≤ node,
  endpoint < premise). At `bit(μ w) = true` the two `PB` answers star both
  endpoints and `ES` closes by reflexivity — the gate is `w`, not `T0.reg.1`.
  `L0 := letSub hb.dr hv.dl hA.dl` is the left-let materialization of the
  right body (`letSub_eps` gives the left-let display); `PB[L0,T0]` and
  `PB[dr,T0]` close the three-leg right continuation.

* **§8.2 unchanged declaration.** When `A' = A` and `v' = v` syntactically,
  `Cr := TyP.letE … hA.dl hv.dl hb.dr dr.reg.2` re-types the right subject.
  `wt Cr = 1 + wt hA.dl + wt hv.dl + wt hb.dr + wt dr.reg.2 < N`.
  `eps_let_clause` turns the `CL[Cr, dr]` answer into the right-let
  continuation display. The equality test is answer-free.

* **§3.2 η consumer.** `zHg` is the existing `etaArg` — `bvar 0` under the
  binder against the domain's weakened sort typing (`wt = 2 + wt Hg.H < Nη`).
  Ports `CL[hf, wkAtZero dr]`, `CL[ha, zHg]`, `TagCoh[ha, zHg]` (subjects
  `lift 0 1 f`, `bvar 0`). The three-case finish: drop closes by the
  function `CL`; keep with `X ≠ ★` lands the variable `CL` on `bvar 0` and
  congruence gives the erased redex; keep with `X = ★` is
  `convMod_star_of_lift` under the actual `TableWF`.

The `Tag` port is the `TagCoh` diagonal `TagCoh σ ρ σ ρ` from
`RcicSynTagCoh` — proof-status agreement of two typings of one subject.
`etaArg`'s erasures are `eta_arg_drop`/`eta_arg_rel` — reused, not re-proved.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §8.1 the proof-result let branch -/

/-- `T0` — `letSub` of the right body's regularity at the left value/domain.
    It types the shared ascription `instantiate0 v B` at `sort w`,
    `w := hb.dr.reg.1`. -/
def letProofResult {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B) :
    TyP E n Γ (instantiate0 v B) (.sort hb.dr.reg.1) :=
  letSub hb.dr.reg.2 hv.dl hA.dl

/-- `wt T0 = 1 + wt H + wt hv.dl + wt hA.dl`. -/
theorem letProofResult_wt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B) :
    (letProofResult hA hv hb).wt Aw =
      1 + hb.dr.reg.2.wt Aw + hv.dl.wt Aw + hA.dl.wt Aw :=
  letSub_wt Aw hb.dr.reg.2 hv.dl hA.dl

/-- `wt T0 < N`: `wt H ≤ wt hb.dr < wt hb` (`wt_reg_le`, `wt_dr_lt`), and the
    two left endpoints sit strictly under their premises (`wt_dl_lt`). -/
theorem letProofResult_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)) :
    (letProofResult hA hv hb).wt Aw <
      (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr).wt Aw := by
  have hreg := TyP.wt_reg_le Aw hb.dr
  have hbdr := CvP.wt_dr_lt Aw hb
  have hvdl := CvP.wt_dl_lt Aw hv
  have hAdl := CvP.wt_dl_lt Aw hA
  have _hdl := TyP.wt_pos Aw dl
  have _hdr := TyP.wt_pos Aw dr
  simp only [letProofResult, letSub_wt, CvP.wt]
  omega

/-- `T0`'s assumption prefix: `assumpPref_reg` for the regularity leg, the
    endpoint APs for the other two. -/
theorem letProofResult_assumpPref {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (hbP : hb.dr.AssumpPref) (hvP : hv.dl.AssumpPref) (hAP : hA.dl.AssumpPref) :
    (letProofResult hA hv hb).AssumpPref :=
  assumpPref_letSub (assumpPref_reg hbP) hvP hAP

/-- `L0` — the left-let materialization of the right body `b'`, against the
    left value/domain. Fully below `N`. -/
def letBodyLeftSub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B) :
    TyP E n Γ (instantiate0 v b') (instantiate0 v B) :=
  letSub hb.dr hv.dl hA.dl

theorem letBodyLeftSub_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)) :
    (letBodyLeftSub hA hv hb).wt Aw <
      (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr).wt Aw := by
  have hbdr := CvP.wt_dr_lt Aw hb
  have hvdl := CvP.wt_dl_lt Aw hv
  have hAdl := CvP.wt_dl_lt Aw hA
  have _hdl := TyP.wt_pos Aw dl
  have _hdr := TyP.wt_pos Aw dr
  simp only [letBodyLeftSub, letSub_wt, CvP.wt]
  omega

theorem letBodyLeftSub_assumpPref {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (hbP : hb.dr.AssumpPref) (hvP : hv.dl.AssumpPref) (hAP : hA.dl.AssumpPref) :
    (letBodyLeftSub hA hv hb).AssumpPref :=
  assumpPref_letSub hbP hvP hAP

/-- `letSub_eps` identifies `L0.eps` with `hb.dr` at the left-let display. -/
theorem letBodyLeftSub_eps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (σ : Level → Level) (ρ : List Disp) :
    (letBodyLeftSub hA hv hb).eps σ ρ =
      match hv.dl.eps σ ρ with
      | .star => hb.dr.eps σ (.drop :: ρ)
      | ev => hb.dr.eps σ (.inline ev :: ρ) :=
  letSub_eps hb.dr hv.dl hA.dl σ ρ

/-- §8.1 finish: at `bit(μ w) = true` the two `PB[·, T0]` answers star both
    endpoints and `ES` closes by reflexivity. The gate is `w`. -/
theorem es_letE_proof_of_pbits (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (hu : levelIsZero (σ hb.dr.reg.1) = true)
    (pL : PBit σ ρ dl (letProofResult hA hv hb))
    (pR : PBit σ ρ dr (letProofResult hA hv hb)) :
    ES tbl σ ρ (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) := by
  have hL := pL.mpr hu
  have hR := pR.mpr hu
  simp only [ES, CvP.dl, CvP.dr, hL, hR]
  exact .refl _

/-- The three-leg right continuation in the proof-result branch: `PB[L0,T0]`
    and `PB[dr,T0]` star both sides. -/
theorem letE_proof_right_leg (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (hu : levelIsZero (σ hb.dr.reg.1) = true)
    (pL : PBit σ ρ (letBodyLeftSub hA hv hb) (letProofResult hA hv hb))
    (pR : PBit σ ρ dr (letProofResult hA hv hb)) :
    ConvMod (EStep tbl) LvlEq
      ((letBodyLeftSub hA hv hb).eps σ ρ) (dr.eps σ ρ) := by
  rw [pL.mpr hu, pR.mpr hu]
  exact .refl _

/-- The same leg displayed as the left-let clause (`letSub_eps`). -/
theorem letE_proof_right_leg_display (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (hu : levelIsZero (σ hb.dr.reg.1) = true)
    (pL : PBit σ ρ (letBodyLeftSub hA hv hb) (letProofResult hA hv hb))
    (pR : PBit σ ρ dr (letProofResult hA hv hb)) :
    ConvMod (EStep tbl) LvlEq
      (match hv.dl.eps σ ρ with
       | .star => hb.dr.eps σ (.drop :: ρ)
       | ev => hb.dr.eps σ (.inline ev :: ρ))
      (dr.eps σ ρ) := by
  rw [← letBodyLeftSub_eps hA hv hb σ ρ]
  exact letE_proof_right_leg tbl σ ρ hA hv hb dr hu pL pR

/-! ## §8.2 the unchanged-declaration branch -/

/-- `Cr` — after the answer-free `A' = A`, `v' = v` casts, `TyP.letE` of the
    left domain/value typings, the right body, and `dr`'s regularity. -/
def letSameDeclRight {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (hAeq : A' = A) (hveq : v' = v) :
    TyP E n Γ (.letE A' v' b') (instantiate0 v B) := by
  subst A' v'
  exact TyP.letE E n Γ A u v B b' dr.reg.1 hA.dl hv.dl hb.dr dr.reg.2

/-- `wt Cr = 1 + wt hA.dl + wt hv.dl + wt hb.dr + wt dr.reg.2 < N`. -/
theorem letSameDeclRight_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (hAeq : A' = A) (hveq : v' = v) :
    (letSameDeclRight hA hv hb dr hAeq hveq).wt Aw <
      (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr).wt Aw := by
  subst A' v'
  have hreg := TyP.wt_reg_le Aw dr
  have hbdr := CvP.wt_dr_lt Aw hb
  have hvdl := CvP.wt_dl_lt Aw hv
  have hAdl := CvP.wt_dl_lt Aw hA
  have _hdl := TyP.wt_pos Aw dl
  show (TyP.letE E n Γ A u v B b' dr.reg.1 hA.dl hv.dl hb.dr dr.reg.2).wt Aw < _
  simp only [TyP.wt, CvP.wt]
  omega

/-- `Cr`'s assumption prefix is the conjunction of the four
    original/regularity AP proofs. -/
theorem letSameDeclRight_assumpPref {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (hAeq : A' = A) (hveq : v' = v)
    (hAP : hA.dl.AssumpPref) (hvP : hv.dl.AssumpPref)
    (hbP : hb.dr.AssumpPref) (hTP : dr.reg.2.AssumpPref) :
    (letSameDeclRight hA hv hb dr hAeq hveq).AssumpPref := by
  subst A' v'
  show (TyP.letE E n Γ A u v B b' dr.reg.1 hA.dl hv.dl hb.dr dr.reg.2).AssumpPref
  exact ⟨hAP, hvP, hbP, hTP⟩

/-- `eps_let_clause` turns `CL[Cr, dr]` into the right-let continuation:
    `ConvMod` of the left-let display (premise endpoints `hv.dl`, `hb.dr`)
    against `dr.eps`. -/
theorem letSameDeclRight_continuation (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (hAeq : A' = A) (hveq : v' = v)
    (h : CL tbl σ ρ (letSameDeclRight hA hv hb dr hAeq hveq) dr) :
    ConvMod (EStep tbl) LvlEq
      (match hv.dl.eps σ ρ with
       | .star => hb.dr.eps σ (.drop :: ρ)
       | ev => hb.dr.eps σ (.inline ev :: ρ))
      (dr.eps σ ρ) := by
  subst A' v'
  have h' : ConvMod (EStep tbl) LvlEq
      ((TyP.letE E n Γ A u v B b' dr.reg.1 hA.dl hv.dl hb.dr dr.reg.2).eps σ ρ)
      (dr.eps σ ρ) := h
  rw [eps_let_clause] at h'
  exact h'

/-! ## §3.2 the η consumer -/

/-- `zHg` is `etaArg hA` — the small `bvar 0` typing under the binder.
    `wt = 2 + wt hA` (one `wk`, one `bvar`). -/
theorem etaVarTy_wt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} (hA : TyP E n Γ A (.sort u)) :
    (etaArg hA).wt Aw = 2 + hA.wt Aw := by
  simp only [etaArg, wkAtZero, TyP.wt]
  omega

/-- `wt zHg < Nη`, given the domain source's bound `wt Hg.H < wt dl`. -/
theorem etaVarTy_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u : Level}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u)) (hH : hA.wt Aw < dl.wt Aw) :
    (etaArg hA).wt Aw < (CvP.eta E n Γ f A B h dl dr).wt Aw := by
  rw [etaVarTy_wt]
  have _h1 := TyP.wt_pos Aw h
  have _h2 := TyP.wt_pos Aw dr
  simp only [CvP.wt]
  omega

/-- Its AP is `assumpPref_wkAtZero` of the domain typing's. -/
theorem etaVarTy_assumpPref {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} (hA : TyP E n Γ A (.sort u))
    (hP : hA.AssumpPref) :
    (etaArg hA).AssumpPref :=
  assumpPref_wkAtZero hP

/-- η, proof domain (`bit(μ u) = true`, binder drops): `TagCoh` makes
    `Y = ★`, the clause reduces to `X`, and the function `CL` finishes. -/
theorem es_eta_zvar_drop {tbl : List CRule} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f A B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    {Tf Ta : Expr Nat}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hf : TyP E n (.assumption A :: Γ) (lift 0 1 f) Tf)
    (ha : TyP E n (.assumption A :: Γ) (.bvar 0) Ta)
    (hu : levelIsZero (σ u) = true)
    (hW : dl.eps σ ρ =
      appClause (hf.eps σ (.drop :: ρ)) (ha.eps σ (.drop :: ρ)))
    (hCLf : CL tbl σ (.drop :: ρ) hf (wkAtZero (A := A) dr))
    (_hCLa : CL tbl σ (.drop :: ρ) ha (etaArg hA))
    (hTag : TagCoh σ (.drop :: ρ) σ (.drop :: ρ) ha (etaArg hA)) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) := by
  have hY : ha.eps σ (.drop :: ρ) = .star :=
    hTag.mpr (eta_arg_drop hA σ ρ hu)
  have hX : ConvMod (EStep tbl) LvlEq (hf.eps σ (.drop :: ρ)) (dr.eps σ ρ) := by
    have hcl := hCLf
    unfold CL at hcl
    rwa [eta_fun_drop] at hcl
  refine es_eta_meet_drop h dl dr ?_ hX
  rw [hW, hY, appClause_right_star]

/-- η, relevant domain (`bit(μ u) = false`, binder keeps, variable `bvar 0`):
    `X ≠ ★` gives the erased redex by congruence and `es_eta` steps it;
    `X = ★` makes the clause `★` and `convMod_star_of_lift` lands `★ ↔* F`
    under the actual `TableWF`. -/
theorem es_eta_zvar_keep {tbl : List CRule} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f A B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    {Tf Ta : Expr Nat}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (hf : TyP E n (.assumption A :: Γ) (lift 0 1 f) Tf)
    (ha : TyP E n (.assumption A :: Γ) (.bvar 0) Ta)
    (hTW : TableWF tbl)
    (hu : levelIsZero (σ u) = false)
    (hW : dl.eps σ ρ =
      lamClause (appClause (hf.eps σ (.keep :: ρ)) (ha.eps σ (.keep :: ρ))))
    (hCLf : CL tbl σ (.keep :: ρ) hf (wkAtZero (A := A) dr))
    (hCLa : CL tbl σ (.keep :: ρ) ha (etaArg hA))
    (hTag : TagCoh σ (.keep :: ρ) σ (.keep :: ρ) ha (etaArg hA)) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) := by
  have hz : (etaArg hA).eps σ (.keep :: ρ) = .bvar 0 := eta_arg_rel hA σ ρ hu
  have hYb : ConvMod (EStep tbl) LvlEq (ha.eps σ (.keep :: ρ)) (.bvar 0) := by
    have hcl := hCLa
    unfold CL at hcl
    rwa [hz] at hcl
  have hYs : ha.eps σ (.keep :: ρ) ≠ .star := by
    intro hY
    have hz2 : (etaArg hA).eps σ (.keep :: ρ) = .star := hTag.mp hY
    rw [hz] at hz2
    exact absurd hz2 (by rintro ⟨⟩)
  have hXf : ConvMod (EStep tbl) LvlEq
      (hf.eps σ (.keep :: ρ)) ((dr.eps σ ρ).lift 0 1) := by
    have hcl := hCLf
    unfold CL at hcl
    rwa [eta_fun_keep] at hcl
  by_cases hX : hf.eps σ (.keep :: ρ) = .star
  · rw [hX] at hW hXf
    have hLs : dl.eps σ ρ = .star := hW
    have hS : ConvMod (EStep tbl) LvlEq .star (dr.eps σ ρ) :=
      convMod_star_of_lift hTW hXf
    simpa only [ES, CvP.dl, CvP.dr, hLs] using hS
  · have happ :
        appClause (hf.eps σ (.keep :: ρ)) (ha.eps σ (.keep :: ρ)) =
          .app (hf.eps σ (.keep :: ρ)) (ha.eps σ (.keep :: ρ)) :=
      appClause_app hX hYs
    have hlam :
        lamClause (.app (hf.eps σ (.keep :: ρ)) (ha.eps σ (.keep :: ρ))) =
          .lam (.app (hf.eps σ (.keep :: ρ)) (ha.eps σ (.keep :: ρ))) :=
      lamClause_of_ne (by rintro ⟨⟩)
    have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
        (.lam (.app ((dr.eps σ ρ).lift 0 1) (.bvar 0))) := by
      rw [hW, happ, hlam]
      exact convMod_lam
        ((convMod_app (.refl _) hYb).trans (convMod_app hXf (.refl _)))
    exact es_eta h dl dr hL (.refl _)

end Rcic.Syn

#print axioms Rcic.Syn.letProofResult
#print axioms Rcic.Syn.letProofResult_wt
#print axioms Rcic.Syn.letProofResult_wt_lt
#print axioms Rcic.Syn.letProofResult_assumpPref
#print axioms Rcic.Syn.letBodyLeftSub
#print axioms Rcic.Syn.letBodyLeftSub_wt_lt
#print axioms Rcic.Syn.letBodyLeftSub_assumpPref
#print axioms Rcic.Syn.letBodyLeftSub_eps
#print axioms Rcic.Syn.es_letE_proof_of_pbits
#print axioms Rcic.Syn.letE_proof_right_leg
#print axioms Rcic.Syn.letE_proof_right_leg_display
#print axioms Rcic.Syn.letSameDeclRight
#print axioms Rcic.Syn.letSameDeclRight_wt_lt
#print axioms Rcic.Syn.letSameDeclRight_assumpPref
#print axioms Rcic.Syn.letSameDeclRight_continuation
#print axioms Rcic.Syn.etaVarTy_wt
#print axioms Rcic.Syn.etaVarTy_wt_lt
#print axioms Rcic.Syn.etaVarTy_assumpPref
#print axioms Rcic.Syn.es_eta_zvar_drop
#print axioms Rcic.Syn.es_eta_zvar_keep
