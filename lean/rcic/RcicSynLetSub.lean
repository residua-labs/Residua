import rcic.RcicSynErase
import rcic.RcicSynInstEnd

/-!
# Syntactic sortRow, build step 3ac — let-substitution of zeta's reduct

`research/rcic/semantic/S3_ES_ARMS.md` §28. `CvP.zeta`'s right endpoint types
`instantiate0 value body`. The body is under `.letBinding`, so `instEnd`
does not apply: `TyP.esub` removes an assumption. `TyP.lsub` removes the let
and inlines the value. `letSub` is that transport at cutoff 0, cast across
`lift 0 0`.

Erasure follows the value, not the domain bit. `★` sends the body under
`drop`; any other erasure sends it under `inline`. That is `zeta_dl`'s
clause, so `CL` of `letSub` against the stored reduct is the right-hand
coherence of `es_zeta`. The left-hand coherence is `zeta_dl`. The `EStep`
between them is the mutual fix.

A recursive expansion that copies the value at each variable can build a
rule-node atom heavier than the `zeta` node. `lsub` flattens: its atoms are
the body's, the value's and the domain's, each already under the node.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the let at index 0 -/

theorem letBinding_get0 (A value : Expr Nat) (Γ : LCtx) :
    (.letBinding A value :: Γ)[0]? = some (.letBinding A value) := by
  rw [← List.get?_eq_getElem?]
  exact List.get?_cons_zero

/-- `body : B` under `letBinding A value :: Γ`, instantiated at `value`. -/
def letSub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body B value : Expr Nat} {u : Level}
    (hb : TyP E n (.letBinding A value :: Γ) body B) (hv : TyP E n Γ value A)
    (hA : TyP E n Γ A (.sort u)) :
    TyP E n Γ (instantiate0 value body) (instantiate0 value B) :=
  tyCast (instantiate0_lift0 value body) (instantiate0_lift0 value B)
    (TyP.lsub E n (.letBinding A value :: Γ) body B A value 0 u hb
      (letBinding_get0 A value Γ) (castLift0 hv) (sortLift0 hA))

theorem letSub_wt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body B value : Expr Nat} {u : Level}
    (hb : TyP E n (.letBinding A value :: Γ) body B) (hv : TyP E n Γ value A)
    (hA : TyP E n Γ A (.sort u)) :
    (letSub hb hv hA).wt Aw = 1 + hb.wt Aw + hv.wt Aw + hA.wt Aw := by
  rw [letSub, wt_tyCast, TyP.wt, wt_castLift0, wt_sortLift0]

theorem letSub_eps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body B value : Expr Nat} {u : Level}
    (hb : TyP E n (.letBinding A value :: Γ) body B) (hv : TyP E n Γ value A)
    (hA : TyP E n Γ A (.sort u)) (σ : Level → Level) (ρ : List Disp) :
    (letSub hb hv hA).eps σ ρ =
      match hv.eps σ ρ with
      | .star => hb.eps σ (.drop :: ρ)
      | ev => hb.eps σ (.inline ev :: ρ) := by
  rw [letSub, eps_tyCast, eps_lsub, eps_castLift0]
  rfl

/-! ## §2 `zeta`, the reduct -/

/-- The reduct of `zeta` is `letSub` of the body at the value. Its erasure is
    the same clause `zeta_dl` reads off the `let`. -/
theorem zeta_dr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.zeta E n Γ A value body B u hA hv hb dl dr))) :
    ConvMod (EStep tbl) LvlEq
      (match hv.eps σ ρ with
        | .star => hb.eps σ (.drop :: ρ)
        | ev => hb.eps σ (.inline ev :: ρ))
      (dr.eps σ ρ) := by
  let hnode := CvP.zeta E n Γ A value body B u hA hv hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwc : (letSub hb hv hA).wt Aw < hnode.wt Aw := by
    have _hpos := TyP.wt_pos Aw dl
    rw [letSub_wt]
    simp only [CvP.wt]
    omega
  have hC := cl_under Aw tbl hnode ht Bel (letSub hb hv hA) dr σ ρ hρ hwc hwr
  simpa only [CL, letSub_eps] using hC

end Rcic.Syn

#print axioms Rcic.Syn.letBinding_get0
#print axioms Rcic.Syn.letSub_wt
#print axioms Rcic.Syn.letSub_eps
#print axioms Rcic.Syn.zeta_dr
