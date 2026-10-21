import rcic.RcicSynMember
import rcic.RcicSynEtaMeet
import rcic.RcicSynLetInline

/-!
# Syntactic sortRow, build step 3as — `delta`, `beta`, `app`, and `lam` `ES` arms from `Below`

`research/rcic/semantic/S3_ES_ARMS.md` §45. Continuing the remaining `ES` arms
after step 3ar (`RcicSynLetInline`):

1. **`CvP.delta` (`delta_dl_proof`, `delta_dl_rel`, `delta_hb_star`,
   `es_of_below_delta_proof`, `es_of_below_delta_rel`, `wkClosed`,
   `deltaBodyInst`, `delta_body_cl`, `es_of_below_delta_table`)**:
   - `CvP.delta`'s left endpoint `dl` needs **no reader walk**:
     `canonL := TyP.const E n Γ r ls ls m hb.reg.1 hres hlen hwf (eqNList_refl ls) hb.reg.2`
     has weight `1 + hb.reg.2.wt Aw + Aw r < hnode.wt Aw` by `TyP.wt_reg_le Aw hb`
     and `TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩`. Thus `cl_under` gives
     `delta_dl_proof` (`dl.eps ↔* ★` when `levelIsZero (σ hb.reg.1) = true`)
     and `delta_dl_rel` (`dl.eps ↔* .const r (ls.map σ)` when
     `levelIsZero (σ hb.reg.1) = false`).
   - On a proof constant (`levelIsZero (σ hb.reg.1) = true`), `Bel.pb hb hb.reg.2`
     gives `hb.eps σ ρ = .star` (`delta_hb_star`), so `es_of_below_delta_proof`
     discharges `ES` with **zero table rule premise**.
   - On a relevant constant (`levelIsZero (σ hb.reg.1) = false`), `wkClosed`
     weakens the level-instantiated closed member body typing
     `D_b : TyP E m.arity [] b m.mtype` (`D_b.wt Aw ≤ Aw r`) to `Γ`
     (`deltaBodyInst`) without adding atoms (`atoms_deltaBodyInst`) and preserving
     `AssumpPref` (`assumpPref_deltaBodyInst`) and closed erasure
     (`eps_deltaBodyInst`), so `cl_under_atoms` gives `delta_body_cl` and
     `es_of_below_delta_table` discharges `ES` from a bare `CRule` in `tbl`.

2. **`CvP.beta` (`beta_got_body_cl`, `beta_got_arg_cl`,
   `es_of_below_beta_got_drop`, `es_of_below_beta_got_keep`,
   `es_of_below_beta_got_keep_star`)**:
   - `CL` does not require matching ascribed types (`D₁ : TyP E n Γ e T₁`,
     `D₂ : TyP E n Γ e T₂`). When `readRedex` reads `dl` into
     `g : RedexGot Aw (dl.wt Aw) E n Γ A body arg`, `g.hbody` and `hbody` both
     type `body` in `.assumption A :: Γ` with atoms `< hnode.wt Aw`, and `g.harg`
     and `harg` both type `arg` in `Γ` with atoms `< hnode.wt Aw`. Thus
     `cl_under_atoms` gives `beta_got_body_cl` and `beta_got_arg_cl` with zero
     `piInv`, discharging `es_of_below_beta_got_drop`,
     `es_of_below_beta_got_keep`, and `es_of_below_beta_got_keep_star`.

3. **`CvP.app` (`app_dr_fun_cl`, `app_dr_arg_cl`, `es_of_below_app_got_rel`,
   `es_of_below_app_got_arg_star`, `es_of_below_app_got_fun_star`)**:
   - When `readApp` reads `dr` into `gR : AppGot Aw (dr.wt Aw) E n Γ g b`,
     `gR.hf` and `h1.dr` both type `g` in `Γ` and `gR.ha` and `h2.dr` both type
     `b` in `Γ` with atoms `< hnode.wt Aw`. Thus `cl_under_atoms` gives
     `app_dr_fun_cl` and `app_dr_arg_cl` with **zero `piInv` or `instEnd`**,
     discharging `es_of_below_app_got_rel`, `es_of_below_app_got_arg_star`,
     and `es_of_below_app_got_fun_star`.

4. **`CvP.lam` (`lam_dl_body_cl`, `lam_dr_body_cl`,
   `es_of_below_lam_got_drop`, `es_of_below_lam_got_keep`)**:
   - When `readLam` reads `dl` into `gL : LamGot Aw (dl.wt Aw) E n Γ A b`,
     `gL.hbody` and `hb.dl` both type `b` in `.assumption A :: Γ` with atoms
     `< hnode.wt Aw`, so `cl_under_atoms` gives `lam_dl_body_cl` and discharges
     `es_of_below_lam_got_drop` and `es_of_below_lam_got_keep`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `CvP.delta`: canonical left endpoint, `deltaBodyInst`, and `ES` arms -/

/-- `CvP.delta`'s left endpoint `dl` is `CL` to the canonical `TyP.const` built
    from `hb.reg`: on a proof constant (`levelIsZero (σ hb.reg.1) = true`),
    `dl.eps σ ρ ↔* ★` with no reader walk. -/
theorem delta_dl_proof (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = true)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) .star := by
  let hnode := CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canonL := TyP.const E n Γ r ls ls m hb.reg.1 hres hlen hwf (eqNList_refl ls) hb.reg.2
  have hwcL : canonL.wt Aw < hnode.wt Aw := by
    have hreg := TyP.wt_reg_le Aw hb
    have hAw : Aw r < dl.wt Aw := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
    have hpos := TyP.wt_pos Aw dr
    simp only [TyP.wt, CvP.wt]
    omega
  have hLraw := cl_under Aw tbl hnode ht Bel dl canonL σ ρ hρ hwl hwcL
  simpa only [CL, eps_const_proof hu] using hLraw

/-- On a relevant constant (`levelIsZero (σ hb.reg.1) = false`), `CvP.delta`'s
    left endpoint `dl` satisfies `dl.eps σ ρ ↔* .const r (ls.map σ)` with no
    reader walk. -/
theorem delta_dl_rel (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.const r (ls.map σ)) := by
  let hnode := CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canonL := TyP.const E n Γ r ls ls m hb.reg.1 hres hlen hwf (eqNList_refl ls) hb.reg.2
  have hwcL : canonL.wt Aw < hnode.wt Aw := by
    have hreg := TyP.wt_reg_le Aw hb
    have hAw : Aw r < dl.wt Aw := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
    have hpos := TyP.wt_pos Aw dr
    simp only [TyP.wt, CvP.wt]
    omega
  have hLraw := cl_under Aw tbl hnode ht Bel dl canonL σ ρ hρ hwl hwcL
  simpa only [CL, eps_const_rel hu] using hLraw

/-- On a proof constant (`levelIsZero (σ hb.reg.1) = true`), `Bel.pb hb hb.reg.2`
    gives `hb.eps σ ρ = .star`. -/
theorem delta_hb_star (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = true)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    hb.eps σ ρ = .star := by
  let hnode := CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwreg : hb.reg.2.wt Aw < hnode.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hb) hwb
  exact (Bel.pb hb hb.reg.2 σ ρ hρ
    (lex_of_dm (dmStep_pair_below Aw hnode ht hb hb.reg.2 hwb hwreg))).mpr hu

/-- `ES` for `CvP.delta` on a proof constant (`levelIsZero (σ hb.reg.1) = true`):
    both endpoints are convertible to `★`, requiring **zero table rules**. -/
theorem es_of_below_delta_proof (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = true)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) := by
  have hL := delta_dl_proof Aw tbl hres hbody htrp hlen hwf hb dl dr σ ρ hρ hu Bel
  have hstar := delta_hb_star Aw tbl hres hbody htrp hlen hwf hb dl dr σ ρ hρ hu Bel
  have hR := delta_dr Aw tbl hres hbody htrp hlen hwf hb dl dr σ ρ hρ Bel
  rw [hstar] at hR
  simpa only [ES, CvP.dl, CvP.dr] using hL.trans hR

/-- `ES` for `CvP.delta` on a relevant constant (`levelIsZero (σ hb.reg.1) = false`),
    discharging `hL` via `delta_dl_rel`. -/
theorem es_of_below_delta_rel (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr)))
    {rhs : ETm}
    (hstep : EStep tbl (.const r (ls.map σ)) rhs)
    (hrhs : ConvMod (EStep tbl) LvlEq rhs (hb.eps σ ρ)) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) :=
  es_of_below_delta_of_lhs Aw tbl hres hbody htrp hlen hwf hb dl dr σ ρ hρ Bel
    (delta_dl_rel Aw tbl hres hbody htrp hlen hwf hb dl dr σ ρ hρ hu Bel)
    hstep hrhs

/-- Weaken a typing `D : TyP E n [] e T` of a closed term and closed type
    (`lift 0 1 e = e`, `lift 0 1 T = T`) into an arbitrary context `Γ` by
    repeated cutoff-`0` weakenings. -/
def wkClosed {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    (hcle : lift 0 1 e = e) (hclT : lift 0 1 T = T) :
    (Γ : LCtx) → TyP E n [] e T → TyP E n Γ e T
  | [], D => D
  | d :: Γ, D =>
      tyCast hcle hclT
        (tyCastCtx (insertAt_zero d Γ)
          (TyP.wk E n Γ e T d 0 (wkClosed hcle hclT Γ D)))

theorem atoms_wkClosed (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    (hcle : lift 0 1 e = e) (hclT : lift 0 1 T = T) :
    (Γ : LCtx) → (D : TyP E n [] e T) →
      (wkClosed hcle hclT Γ D).atoms Aw = D.atoms Aw
  | [], _ => rfl
  | _ :: Γ, D => by
      rw [wkClosed, atoms_tyCast, atoms_tyCastCtx]
      exact atoms_wkClosed Aw hcle hclT Γ D

theorem assumpPref_wkClosed {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    (hcle : lift 0 1 e = e) (hclT : lift 0 1 T = T) :
    (Γ : LCtx) → {D : TyP E n [] e T} → D.AssumpPref →
      (wkClosed hcle hclT Γ D).AssumpPref
  | [], _, hD => hD
  | _ :: Γ, _, hD =>
      assumpPref_tyCast _ _
        (assumpPref_tyCastCtx _
          ⟨assumptionPrefix_zero Γ, assumpPref_wkClosed hcle hclT Γ hD⟩)

theorem eps_wkClosed {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    (hcle : lift 0 1 e = e) (hclT : lift 0 1 T = T) :
    (Γ : LCtx) → (D : TyP E n [] e T) → (σ : Level → Level) →
      (D.eps σ []).lift 0 1 = D.eps σ [] →
      (ρ : List Disp) → ρ.length = Γ.length →
      (wkClosed hcle hclT Γ D).eps σ ρ = D.eps σ []
  | [], _, _, _, [], _ => rfl
  | [], _, _, _, _ :: _, hlen => nomatch hlen
  | _ :: _, _, _, _, [], hlen => nomatch hlen
  | _ :: Γ₀, D, σ, hlift, disp :: ρ₀, hlen => by
      have ih := eps_wkClosed hcle hclT Γ₀ D σ hlift ρ₀ (Nat.succ.inj hlen)
      rw [wkClosed, eps_tyCast, eps_tyCastCtx]
      cases disp <;>
        simp only [TyP.eps, List.getElem?_cons_zero, List.get?_cons_zero,
          removeAt_zero, List.take_zero, countKeep, ih, hlift]

/-- Level-instantiated and weakened closed member body typing
    `D_b : TyP E m.arity [] b m.mtype` in context `Γ`. -/
def deltaBodyInst {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (Γ : LCtx) (D_b : TyP E m.arity [] b m.mtype) :
    TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype) :=
  have hcl_b : lift 0 1 (instantiateLevels ls b) = instantiateLevels ls b :=
    (lift_instantiateLevels ls 1 b 0).trans
      (congrArg (instantiateLevels ls) ((envClosed_of_envWfT hE r m hres).2 b hbody 0))
  have hcl_T : lift 0 1 (instantiateLevels ls m.mtype) = instantiateLevels ls m.mtype :=
    (lift_instantiateLevels ls 1 m.mtype 0).trans
      (congrArg (instantiateLevels ls) ((envClosed_of_envWfT hE r m hres).1 0))
  wkClosed hcl_b hcl_T Γ (TyP.linst E m.arity n [] b m.mtype ls hwf hlen D_b)

theorem atoms_deltaBodyInst (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (Γ : LCtx) (D_b : TyP E m.arity [] b m.mtype) :
    (deltaBodyInst hE hres hbody hlen hwf Γ D_b).atoms Aw = D_b.atoms Aw := by
  unfold deltaBodyInst
  rw [atoms_wkClosed]
  rfl

theorem assumpPref_deltaBodyInst {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (Γ : LCtx) {D_b : TyP E m.arity [] b m.mtype} (hD : D_b.AssumpPref) :
    (deltaBodyInst hE hres hbody hlen hwf Γ D_b).AssumpPref :=
  assumpPref_wkClosed _ _ Γ hD

theorem eps_deltaBodyInst {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (Γ : LCtx) (D_b : TyP E m.arity [] b m.mtype)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hlift : (D_b.eps (fun l => σ (instLevel ls l)) []).lift 0 1 =
      D_b.eps (fun l => σ (instLevel ls l)) []) :
    (deltaBodyInst hE hres hbody hlen hwf Γ D_b).eps σ ρ =
      D_b.eps (fun l => σ (instLevel ls l)) [] := by
  unfold deltaBodyInst
  exact eps_wkClosed _ _ Γ (TyP.linst E m.arity n [] b m.mtype ls hwf hlen D_b)
    σ hlift ρ hρ.length_eq

/-- Under `D_b.wt Aw ≤ Aw r`, every atom of `deltaBodyInst` is `< Aw r < dl.wt Aw < hnode.wt Aw`,
    so `cl_under_atoms` gives `CL` of `deltaBodyInst` against `hb`. -/
theorem delta_body_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (hDb : D_b.wt Aw ≤ Aw r)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    CL tbl σ ρ (deltaBodyInst hE hres hbody hlen hwf Γ D_b) hb := by
  let hnode := CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hAw : Aw r < hnode.wt Aw := by
    have hlt := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
    simp only [CvP.wt]
    omega
  refine cl_under_atoms Aw tbl hnode ht Bel
    (deltaBodyInst hE hres hbody hlen hwf Γ D_b) hb σ ρ hρ ?_ ?_
  · intro y hy
    rw [atoms_deltaBodyInst] at hy
    exact atoms_lt_of_wt_lt Aw D_b (Nat.lt_of_le_of_lt hDb hAw) y hy
  · intro y hy
    exact atoms_lt_of_wt_lt Aw hb hwb y hy

/-- Full `ES` for `CvP.delta` on a relevant constant from a bare `CRule` in `tbl`
    whose right-hand side is the closed erasure of `D_b`. -/
theorem es_of_below_delta_table (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (hDb : D_b.wt Aw ≤ Aw r)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hlift : (D_b.eps (fun l => σ (instLevel ls l)) []).lift 0 1 =
      D_b.eps (fun l => σ (instLevel ls l)) [])
    {crule : CRule} (hcrule : crule ∈ tbl) (hhead : crule.head = r)
    (hmaj : crule.major = none) (hnargs : crule.nargs (ls.map σ) = 0)
    (hrhs_eq : crule.rhs (ls.map σ) [] = D_b.eps (fun l => σ (instLevel ls l)) [])
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) := by
  have hcl := delta_body_cl Aw tbl hE hres hbody htrp hlen hwf hb dl dr D_b hDb σ ρ hρ Bel
  unfold CL at hcl
  rw [eps_deltaBodyInst hE hres hbody hlen hwf Γ D_b σ ρ hρ hlift] at hcl
  have hcroot : CRoot tbl (.const r (ls.map σ)) (crule.rhs (ls.map σ) []) := by
    have h0 : ([] : List ETm).length = crule.nargs (ls.map σ) := hnargs.symm
    have hstep := CRoot.bare (tbl := tbl) hcrule hmaj (ls.map σ) [] h0
    simpa only [ETm.appN, hhead] using hstep
  rw [hrhs_eq] at hcroot
  exact es_of_below_delta_rel Aw tbl hres hbody htrp hlen hwf hb dl dr σ ρ hρ hu Bel
    (.inl (.cr hcroot)) hcl

/-! ## §2 `CvP.beta`: `RedexGot` coherence and `ES` arms from `Below` -/

/-- When `readRedex` yields `g : RedexGot Aw (dl.wt Aw) E n Γ A body arg`,
    `g.hbody` and `hbody` both type `body` in `.assumption A :: Γ` with atoms
    `< hnode.wt Aw`, so `cl_under_atoms` gives `CL` of `g.hbody` and `hbody`
    with **zero `piInv`**. -/
theorem beta_got_body_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (σ : Level → Level) (ρ' : List Disp)
    (hρ' : DispFor σ E n (.assumption A :: Γ) ρ')
    (Bel : Below Aw tbl (cvMeas Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr))) :
    CL tbl σ ρ' g.hbody hbody := by
  let hnode := CvP.beta E n Γ A body arg B u hA hbody harg dl dr
  have ht : hnode.isTransport = false := rfl
  have hdl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwb : hbody.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  refine cl_under_atoms Aw tbl hnode ht Bel g.hbody hbody σ ρ' hρ' ?_ ?_
  · intro y hy
    exact Nat.lt_trans (g.ltB y hy) hdl
  · intro y hy
    exact atoms_lt_of_wt_lt Aw hbody hwb y hy

/-- `g.harg` and `harg` both type `arg` in `Γ` with atoms `< hnode.wt Aw`,
    so `cl_under_atoms` gives `CL` of `g.harg` and `harg` with **zero `piInv`**. -/
theorem beta_got_arg_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr))) :
    CL tbl σ ρ g.harg harg := by
  let hnode := CvP.beta E n Γ A body arg B u hA hbody harg dl dr
  have ht : hnode.isTransport = false := rfl
  have hdl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwa : harg.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  refine cl_under_atoms Aw tbl hnode ht Bel g.harg harg σ ρ hρ ?_ ?_
  · intro y hy
    exact Nat.lt_trans (g.ltA y hy) hdl
  · intro y hy
    exact atoms_lt_of_wt_lt Aw harg hwa y hy

/-- `ES` for `CvP.beta` on a proof domain (`levelIsZero (σ u) = true`) when
    `dl` erases to `redexClauseOf g σ ρ` with `levelIsZero (σ g.u) = true`
    and `g.harg.eps σ ρ = .star`. -/
theorem es_of_below_beta_got_drop (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = true) (hgu : levelIsZero (σ g.u) = true)
    (hW : dl.eps σ ρ = redexClauseOf g σ ρ)
    (ha_star : g.harg.eps σ ρ = .star)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr))) :
    ES tbl σ ρ (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) := by
  have hb_cl := beta_got_body_cl Aw tbl hA hbody harg dl dr g σ (.drop :: ρ)
    (dispFor_assumption_drop hρ hA hu) Bel
  unfold CL at hb_cl
  have hdl_eq : dl.eps σ ρ = g.hbody.eps σ (.drop :: ρ) := by
    rw [hW]
    unfold redexClauseOf
    rw [hgu, binderDisp_drop, ha_star]
    simp only [redexClause, lamErasure, appClause_right_star]
  rw [← hdl_eq] at hb_cl
  exact es_of_below_beta_drop Aw tbl hA hbody harg dl dr σ ρ hρ hu Bel hb_cl

/-- `ES` for `CvP.beta` on a relevant domain (`levelIsZero (σ u) = false`) when
    `dl` erases to `redexClauseOf g σ ρ` with `levelIsZero (σ g.u) = false`,
    `g.hbody.eps σ (.keep :: ρ) ≠ .star`, and `g.harg.eps σ ρ ≠ .star`. -/
theorem es_of_below_beta_got_keep (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = false) (hgu : levelIsZero (σ g.u) = false)
    (hW : dl.eps σ ρ = redexClauseOf g σ ρ)
    (hb_ne : g.hbody.eps σ (.keep :: ρ) ≠ .star)
    (ha_ne : g.harg.eps σ ρ ≠ .star)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr))) :
    ES tbl σ ρ (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) := by
  have hb_cl := beta_got_body_cl Aw tbl hA hbody harg dl dr g σ (.keep :: ρ)
    (dispFor_assumption_keep hρ hA hu) Bel
  have ha_cl := beta_got_arg_cl Aw tbl hA hbody harg dl dr g σ ρ hρ Bel
  unfold CL at hb_cl ha_cl
  have hlam_ne : ETm.lam (g.hbody.eps σ (.keep :: ρ)) ≠ .star := by
    intro h; cases h
  have hdl_eq : dl.eps σ ρ =
      .app (.lam (g.hbody.eps σ (.keep :: ρ))) (g.harg.eps σ ρ) := by
    rw [hW]
    unfold redexClauseOf
    rw [hgu, binderDisp_keep]
    simp only [redexClause, lamErasure, lamClause_of_ne hb_ne,
      appClause_app hlam_ne ha_ne]
  have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (.app (.lam (hbody.eps σ (.keep :: ρ))) (harg.eps σ ρ)) := by
    rw [hdl_eq]
    exact convMod_app (convMod_lam hb_cl) ha_cl
  exact es_of_below_beta_keep Aw tbl hA hbody harg dl dr σ ρ hρ hu Bel hL

/-- `ES` for `CvP.beta` on a relevant domain (`levelIsZero (σ u) = false`) when
    the body is a proof (`g.hbody.eps σ (.keep :: ρ) = .star` and
    `hbody.eps σ (.keep :: ρ) = .star`): both `dl.eps` and `instEnd` erase to `★`. -/
theorem es_of_below_beta_got_keep_star (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = false) (hgu : levelIsZero (σ g.u) = false)
    (hW : dl.eps σ ρ = redexClauseOf g σ ρ)
    (hgb_star : g.hbody.eps σ (.keep :: ρ) = .star)
    (hb_star : hbody.eps σ (.keep :: ρ) = .star)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr))) :
    ES tbl σ ρ (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) := by
  have hR := beta_dr_keep Aw tbl hA hbody harg dl dr σ ρ hρ hu Bel
  rw [hb_star] at hR
  have hinst : ETm.inst 0 (harg.eps σ ρ) .star = .star := rfl
  rw [hinst] at hR
  have hdl_star : dl.eps σ ρ = .star := by
    rw [hW]
    unfold redexClauseOf
    rw [hgu, binderDisp_keep, hgb_star]
    rfl
  simpa only [ES, CvP.dl, CvP.dr, hdl_star] using hR

/-! ## §3 `CvP.app`: right endpoint `AppGot` coherence and `ES` arms from `Below` -/

/-- When `readApp` reads `dr` into `gR : AppGot Aw (dr.wt Aw) E n Γ g b`,
    `h1.dr` and `gR.hf` both type `g` in `Γ` with atoms `< hnode.wt Aw`.
    Because `CL` does not require matching ascribed types, `cl_under_atoms`
    gives `CL` of `h1.dr` and `gR.hf` with **zero `piInv` or `instEnd`**. -/
theorem app_dr_fun_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (gR : AppGot Aw (dr.wt Aw) E n Γ g b)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr))) :
    CL tbl σ ρ h1.dr gR.hf := by
  let hnode := CvP.app E n Γ f g a b A B h1 h2 dl dr
  have ht : hnode.isTransport = false := rfl
  have hdr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hw1r : h1.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw h1
    simp only [CvP.wt]; omega
  refine cl_under_atoms Aw tbl hnode ht Bel h1.dr gR.hf σ ρ hρ ?_ ?_
  · intro y hy
    exact atoms_lt_of_wt_lt Aw h1.dr hw1r y hy
  · intro y hy
    exact Nat.lt_trans (gR.ltF y hy) hdr

/-- `h2.dr` and `gR.ha` both type `b` in `Γ` with atoms `< hnode.wt Aw`,
    so `cl_under_atoms` gives `CL` of `h2.dr` and `gR.ha` with **zero `piInv` or `instEnd`**. -/
theorem app_dr_arg_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (gR : AppGot Aw (dr.wt Aw) E n Γ g b)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr))) :
    CL tbl σ ρ h2.dr gR.ha := by
  let hnode := CvP.app E n Γ f g a b A B h1 h2 dl dr
  have ht : hnode.isTransport = false := rfl
  have hdr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hw2r : h2.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw h2
    simp only [CvP.wt]; omega
  refine cl_under_atoms Aw tbl hnode ht Bel h2.dr gR.ha σ ρ hρ ?_ ?_
  · intro y hy
    exact atoms_lt_of_wt_lt Aw h2.dr hw2r y hy
  · intro y hy
    exact Nat.lt_trans (gR.ltA y hy) hdr

/-- `ES` for `CvP.app` when both applications are relevant (`h1.dl.eps ≠ ★`,
    `h2.dl.eps ≠ ★`, `gR.hf.eps ≠ ★`, `gR.ha.eps ≠ ★`) and `dr` erases to
    `appClauseOf gR σ ρ`. -/
theorem es_of_below_app_got_rel (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (gR : AppGot Aw (dr.wt Aw) E n Γ g b)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hf_ne : h1.dl.eps σ ρ ≠ .star) (ha_ne : h2.dl.eps σ ρ ≠ .star)
    (hgf_ne : gR.hf.eps σ ρ ≠ .star) (hga_ne : gR.ha.eps σ ρ ≠ .star)
    (hW : dr.eps σ ρ = appClauseOf gR σ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr))) :
    ES tbl σ ρ (CvP.app E n Γ f g a b A B h1 h2 dl dr) := by
  have hf_cl := app_dr_fun_cl Aw tbl h1 h2 dl dr gR σ ρ hρ Bel
  have ha_cl := app_dr_arg_cl Aw tbl h1 h2 dl dr gR σ ρ hρ Bel
  unfold CL at hf_cl ha_cl
  have hdr_eq : dr.eps σ ρ = .app (gR.hf.eps σ ρ) (gR.ha.eps σ ρ) := by
    rw [hW]
    exact appClause_app hgf_ne hga_ne
  have hR : ConvMod (EStep tbl) LvlEq
      (.app (h1.dr.eps σ ρ) (h2.dr.eps σ ρ)) (dr.eps σ ρ) := by
    rw [hdr_eq]
    exact convMod_app hf_cl ha_cl
  exact es_of_below_app_of_dr Aw tbl h1 h2 dl dr σ ρ hρ hf_ne ha_ne Bel hR

/-- `ES` for `CvP.app` when the arguments are proofs (`h2.dl.eps = ★` and
    `gR.ha.eps = ★`) and `dr` erases to `appClauseOf gR σ ρ`. -/
theorem es_of_below_app_got_arg_star (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (gR : AppGot Aw (dr.wt Aw) E n Γ g b)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (ha_star : h2.dl.eps σ ρ = .star) (hga_star : gR.ha.eps σ ρ = .star)
    (hW : dr.eps σ ρ = appClauseOf gR σ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr))) :
    ES tbl σ ρ (CvP.app E n Γ f g a b A B h1 h2 dl dr) := by
  have hf_cl := app_dr_fun_cl Aw tbl h1 h2 dl dr gR σ ρ hρ Bel
  unfold CL at hf_cl
  have hdr_eq : dr.eps σ ρ = gR.hf.eps σ ρ := by
    rw [hW]
    unfold appClauseOf
    rw [hga_star, appClause_right_star]
  rw [← hdr_eq] at hf_cl
  exact es_of_below_app_star_of_dr Aw tbl h1 h2 dl dr σ ρ hρ ha_star Bel hf_cl

/-- `ES` for `CvP.app` when the functions erase to `★` (`h1.dl.eps = ★` and
    `gR.hf.eps = ★`) and `dr` erases to `appClauseOf gR σ ρ`. -/
theorem es_of_below_app_got_fun_star (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (gR : AppGot Aw (dr.wt Aw) E n Γ g b)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hf_star : h1.dl.eps σ ρ = .star) (hgf_star : gR.hf.eps σ ρ = .star)
    (hW : dr.eps σ ρ = appClauseOf gR σ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr))) :
    ES tbl σ ρ (CvP.app E n Γ f g a b A B h1 h2 dl dr) := by
  have hL := app_dl Aw tbl h1 h2 dl dr σ ρ hρ Bel
  rw [hf_star] at hL
  have hdr_star : dr.eps σ ρ = .star := by
    rw [hW]
    unfold appClauseOf
    rw [hgf_star]
    rfl
  simpa only [ES, CvP.dl, CvP.dr, hdr_star] using hL

/-! ## §4 `CvP.lam`: `LamGot` coherence and `ES` arms from `Below` -/

/-- When `readLam` reads `dl` into `gL : LamGot Aw (dl.wt Aw) E n Γ A b`,
    `gL.hbody` and `hb.dl` both type `b` in `.assumption A :: Γ` with atoms
    `< hnode.wt Aw`, so `cl_under_atoms` gives `CL` of `gL.hbody` and `hb.dl`. -/
theorem lam_dl_body_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (gL : LamGot Aw (dl.wt Aw) E n Γ A b)
    (σ : Level → Level) (ρ' : List Disp)
    (hρ' : DispFor σ E n (.assumption A :: Γ) ρ')
    (Bel : Below Aw tbl (cvMeas Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr))) :
    CL tbl σ ρ' gL.hbody hb.dl := by
  let hnode := CvP.lam E n Γ A A' b b' B u hA hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hdl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwbl : hb.dl.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dl_lt Aw hb
    simp only [CvP.wt]; omega
  refine cl_under_atoms Aw tbl hnode ht Bel gL.hbody hb.dl σ ρ' hρ' ?_ ?_
  · intro y hy
    exact Nat.lt_trans (gL.lt y hy) hdl
  · intro y hy
    exact atoms_lt_of_wt_lt Aw hb.dl hwbl y hy

/-- `ES` for `CvP.lam` on a proof domain (`levelIsZero (σ u) = true`) when
    `dl` erases to `lamClauseOf gL σ ρ` with `levelIsZero (σ gL.u) = true`. -/
theorem es_of_below_lam_got_drop (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (gL : LamGot Aw (dl.wt Aw) E n Γ A b)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = true) (hgu : levelIsZero (σ gL.u) = true)
    (hWL : dl.eps σ ρ = lamClauseOf gL σ ρ)
    (hR : ConvMod (EStep tbl) LvlEq (hb.dr.eps σ (.drop :: ρ)) (dr.eps σ ρ))
    (Bel : Below Aw tbl (cvMeas Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr))) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  have hL_cl := lam_dl_body_cl Aw tbl hA hb dl dr gL σ (.drop :: ρ)
    (dispFor_assumption_drop hρ hA.dl hu) Bel
  unfold CL at hL_cl
  have hdl_eq : dl.eps σ ρ = gL.hbody.eps σ (.drop :: ρ) := by
    rw [hWL]
    unfold lamClauseOf
    rw [hgu, binderDisp_drop]
    rfl
  rw [← hdl_eq] at hL_cl
  exact es_of_below_lam_drop Aw tbl hA hb dl dr σ ρ hρ hu Bel hL_cl hR

/-- `ES` for `CvP.lam` on a relevant domain (`levelIsZero (σ u) = false`) when
    `dl` erases to `lamClauseOf gL σ ρ` with `levelIsZero (σ gL.u) = false`
    and `gL.hbody.eps σ (.keep :: ρ) ≠ .star`. -/
theorem es_of_below_lam_got_keep (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (gL : LamGot Aw (dl.wt Aw) E n Γ A b)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = false) (hgu : levelIsZero (σ gL.u) = false)
    (hWL : dl.eps σ ρ = lamClauseOf gL σ ρ)
    (hgb_ne : gL.hbody.eps σ (.keep :: ρ) ≠ .star)
    (hR : ConvMod (EStep tbl) LvlEq (.lam (hb.dr.eps σ (.keep :: ρ))) (dr.eps σ ρ))
    (Bel : Below Aw tbl (cvMeas Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr))) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  have hL_cl := lam_dl_body_cl Aw tbl hA hb dl dr gL σ (.keep :: ρ)
    (dispFor_assumption_keep hρ hA.dl hu) Bel
  unfold CL at hL_cl
  have hdl_eq : dl.eps σ ρ = .lam (gL.hbody.eps σ (.keep :: ρ)) := by
    rw [hWL]
    unfold lamClauseOf
    rw [hgu, binderDisp_keep]
    exact lamClause_of_ne hgb_ne
  have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.lam (hb.dl.eps σ (.keep :: ρ))) := by
    rw [hdl_eq]
    exact convMod_lam hL_cl
  exact es_of_below_lam_keep Aw tbl hA hb dl dr σ ρ hρ hu Bel hL hR

end Rcic.Syn

#print axioms Rcic.Syn.delta_dl_proof
#print axioms Rcic.Syn.delta_dl_rel
#print axioms Rcic.Syn.delta_hb_star
#print axioms Rcic.Syn.es_of_below_delta_proof
#print axioms Rcic.Syn.es_of_below_delta_rel
#print axioms Rcic.Syn.wkClosed
#print axioms Rcic.Syn.atoms_wkClosed
#print axioms Rcic.Syn.assumpPref_wkClosed
#print axioms Rcic.Syn.eps_wkClosed
#print axioms Rcic.Syn.deltaBodyInst
#print axioms Rcic.Syn.atoms_deltaBodyInst
#print axioms Rcic.Syn.assumpPref_deltaBodyInst
#print axioms Rcic.Syn.eps_deltaBodyInst
#print axioms Rcic.Syn.delta_body_cl
#print axioms Rcic.Syn.es_of_below_delta_table
#print axioms Rcic.Syn.beta_got_body_cl
#print axioms Rcic.Syn.beta_got_arg_cl
#print axioms Rcic.Syn.es_of_below_beta_got_drop
#print axioms Rcic.Syn.es_of_below_beta_got_keep
#print axioms Rcic.Syn.es_of_below_beta_got_keep_star
#print axioms Rcic.Syn.app_dr_fun_cl
#print axioms Rcic.Syn.app_dr_arg_cl
#print axioms Rcic.Syn.es_of_below_app_got_rel
#print axioms Rcic.Syn.es_of_below_app_got_arg_star
#print axioms Rcic.Syn.es_of_below_app_got_fun_star
#print axioms Rcic.Syn.lam_dl_body_cl
#print axioms Rcic.Syn.es_of_below_lam_got_drop
#print axioms Rcic.Syn.es_of_below_lam_got_keep
