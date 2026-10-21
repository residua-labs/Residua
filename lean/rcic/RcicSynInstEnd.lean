import rcic.RcicSynCanon
import rcic.RcicSynCtxSet

/-!
# Syntactic sortRow, build step 3u — the instantiated endpoint

`research/rcic/semantic/S3_ES_ARMS.md` §20. `fsub` and `beta` store an
endpoint whose term is `instantiate0 v body`. The canonical typing of that
term is one `TyP.esub` at cutoff 0 (`instEnd`), cast by `lift 0 0 = id`.

A proof domain erases the `esub` to the body under `drop`. A relevant domain
erases it to `ETm.inst 0` of the replacement at the body under `keep`.
`countKeep (ρ.take 0)` is `0`. `CL` against the stored endpoint is
`cl_under`: the `esub` weighs `1 + wt(body) + wt(replacement) + wt(domain)`,
which sits under the rule node.

`es_of_below_fsub` is the whole arm. Both endpoints are `instEnd`, so the
two proof-bits are the same `u`. `ES(hab)` moves the replacement, and
`convMod_inst_repl` needs `TableClosed`. `beta_dr_drop` / `beta_dr_keep`
are the reduct half of `es_beta_drop` / `es_beta_rel`. The redex half is
not in this module: a canonical `app` of a `lam` is one atom, the sum of
its components, and that sum is not bounded by the `beta` node.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 casts -/

theorem instantiate0_lift0 (v e : Expr Nat) :
    instantiate 0 (lift 0 0 v) e = instantiate0 v e := by
  simp only [instantiate0]
  exact congrArg (fun r => instantiate 0 r e) (lift_zero_idx 0 v)

theorem assumption_get0 (A : Expr Nat) (Γ : LCtx) :
    (.assumption A :: Γ)[0]? = some (.assumption A) := by
  rw [← List.get?_eq_getElem?]
  exact List.get?_cons_zero

theorem wt_tyCast (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' T T' : Expr Nat} (he : e = e') (hT : T = T') (D : TyP E n Γ e T) :
    (tyCast he hT D).wt Aw = D.wt Aw := by
  cases he
  cases hT
  rfl

theorem eps_tyCast {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' T T' : Expr Nat} (he : e = e') (hT : T = T') (D : TyP E n Γ e T)
    (σ : Level → Level) (ρ : List Disp) :
    (tyCast he hT D).eps σ ρ = D.eps σ ρ := by
  cases he
  cases hT
  rfl

/-- `lift 0 0` is the identity, so a typing at `v` is a typing at `lift 0 0 v`. -/
def castLift0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {v t : Expr Nat}
    (D : TyP E n Γ v t) : TyP E n Γ (lift 0 0 v) (lift 0 0 t) :=
  tyCast (lift_zero_idx 0 v).symm (lift_zero_idx 0 t).symm D

theorem wt_castLift0 (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v t : Expr Nat} (D : TyP E n Γ v t) :
    (castLift0 D).wt Aw = D.wt Aw :=
  wt_tyCast Aw _ _ D

theorem eps_castLift0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {v t : Expr Nat}
    (D : TyP E n Γ v t) (σ : Level → Level) (ρ : List Disp) :
    (castLift0 D).eps σ ρ = D.eps σ ρ :=
  eps_tyCast _ _ D σ ρ

/-- The domain sort is `sort u` after `lift 0 0`. -/
def sortLift0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) : TyP E n Γ (lift 0 0 A) (.sort u) :=
  tyCast rfl (lift_zero_idx 0 (.sort u)) (castLift0 hA)

theorem wt_sortLift0 (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} (hA : TyP E n Γ A (.sort u)) :
    (sortLift0 hA).wt Aw = hA.wt Aw := by
  rw [sortLift0, wt_tyCast, wt_castLift0]

/-! ## §2 the `esub` at cutoff 0 -/

/-- `B : S` under `assumption A :: Γ`, instantiated at `v : A`. -/
def instEnd {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) :
    TyP E n Γ (instantiate0 v B) (instantiate0 v S) :=
  tyCast (instantiate0_lift0 v B) (instantiate0_lift0 v S)
    (TyP.esub E n (.assumption A :: Γ) B S A v 0 u hB (assumption_get0 A Γ)
      (castLift0 hv) (sortLift0 hA))

theorem instEnd_wt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) :
    (instEnd hB hv hA).wt Aw = 1 + hB.wt Aw + hv.wt Aw + hA.wt Aw := by
  rw [instEnd, wt_tyCast, TyP.wt, wt_castLift0, wt_sortLift0]

theorem instEnd_eps_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true) :
    (instEnd hB hv hA).eps σ ρ = hB.eps σ (.drop :: ρ) := by
  rw [instEnd, eps_tyCast]
  rw [eps_esub_drop (hu := hu), insertDisp_zero]

theorem instEnd_eps_keep {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = false) :
    (instEnd hB hv hA).eps σ ρ =
      ETm.inst 0 (hv.eps σ ρ) (hB.eps σ (.keep :: ρ)) := by
  rw [instEnd, eps_tyCast]
  rw [eps_esub_keep (hu := hu), insertDisp_zero, List.take_zero, eps_castLift0]
  rfl

/-! ## §3 `fsub` -/

/-- Both stored endpoints are `CL` to `instEnd`. The domain bit is `u` on
    both sides. A proof domain sends both erasures to the body under `drop`.
    A relevant domain sends them to `inst 0` of the two replacements, and
    `ES(hab)` identifies those replacements. -/
theorem es_of_below_fsub (Aw : Nat → Nat) (tbl : List CRule) (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B S a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a S))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a S))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.fsub E n Γ A B S a b u hB hA hab dl dr))) :
    ES tbl σ ρ (CvP.fsub E n Γ A B S a b u hB hA hab dl dr) := by
  let hnode := CvP.fsub E n Γ A B S a b u hB hA hab dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwh : hab.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canonL := instEnd hB hab.dl hA
  let canonR := instEnd hB hab.dr hA
  have hwcL : canonL.wt Aw < hnode.wt Aw := by
    have hlt := CvP.wt_dl_lt Aw hab
    have hpos := TyP.wt_pos Aw dl
    rw [instEnd_wt]
    simp only [CvP.wt]
    omega
  have hwcR : canonR.wt Aw < hnode.wt Aw := by
    have hlt := CvP.wt_dr_lt Aw hab
    have hpos := TyP.wt_pos Aw dr
    rw [instEnd_wt]
    simp only [CvP.wt]
    omega
  have hLraw := cl_under Aw tbl hnode ht Bel dl canonL σ ρ hρ hwl hwcL
  have hRraw := cl_under Aw tbl hnode ht Bel canonR dr σ ρ hρ hwcR hwr
  match hzu : levelIsZero (σ u) with
  | true =>
      have hLe := instEnd_eps_drop hB hab.dl hA (σ := σ) (ρ := ρ) hzu
      have hRe := instEnd_eps_drop hB hab.dr hA (σ := σ) (ρ := ρ) hzu
      refine es_fsub_drop hB hA hab dl dr ?_ ?_
      · simpa only [CL, hLe] using hLraw
      · simpa only [CL, hRe] using hRraw
  | false =>
      have hLe := instEnd_eps_keep hB hab.dl hA (σ := σ) (ρ := ρ) hzu
      have hRe := instEnd_eps_keep hB hab.dr hA (σ := σ) (ρ := ρ) hzu
      refine es_fsub_keep (ea := hab.dl.eps σ ρ) (eb := hab.dr.eps σ ρ)
        hcl hB hA hab dl dr ?_ ?_ ?_
      · simpa only [CL, hLe] using hLraw
      · simpa only [CL, hRe] using hRraw
      · exact Bel.es hab σ ρ hρ (lex_of_dm (dmStep_cv_below Aw hnode ht hab hwh))

/-! ## §4 `beta`, the reduct -/

/-- The reduct of `beta` is `instEnd` of the body at the argument. A proof
    domain erases it to the body under `drop`, which is `es_beta_drop`'s
    right-hand coherence. -/
theorem beta_dr_drop (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = true)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr))) :
    ConvMod (EStep tbl) LvlEq (hbody.eps σ (.drop :: ρ)) (dr.eps σ ρ) := by
  let hnode := CvP.beta E n Γ A body arg B u hA hbody harg dl dr
  have ht : hnode.isTransport = false := rfl
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canon := instEnd hbody harg hA
  have hwc : canon.wt Aw < hnode.wt Aw := by
    have hpos := TyP.wt_pos Aw dl
    rw [instEnd_wt]
    simp only [CvP.wt]
    omega
  have hC := cl_under Aw tbl hnode ht Bel canon dr σ ρ hρ hwc hwr
  have he := instEnd_eps_drop hbody harg hA (σ := σ) (ρ := ρ) hu
  simpa only [CL, he] using hC

/-- A relevant domain erases the same `instEnd` to `ETm.inst 0` of the
    argument at the body under `keep`. That is `es_beta_rel`'s right-hand
    coherence. -/
theorem beta_dr_keep (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = false)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr))) :
    ConvMod (EStep tbl) LvlEq
      (ETm.inst 0 (harg.eps σ ρ) (hbody.eps σ (.keep :: ρ))) (dr.eps σ ρ) := by
  let hnode := CvP.beta E n Γ A body arg B u hA hbody harg dl dr
  have ht : hnode.isTransport = false := rfl
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canon := instEnd hbody harg hA
  have hwc : canon.wt Aw < hnode.wt Aw := by
    have hpos := TyP.wt_pos Aw dl
    rw [instEnd_wt]
    simp only [CvP.wt]
    omega
  have hC := cl_under Aw tbl hnode ht Bel canon dr σ ρ hρ hwc hwr
  have he := instEnd_eps_keep hbody harg hA (σ := σ) (ρ := ρ) hu
  simpa only [CL, he] using hC

end Rcic.Syn

#print axioms Rcic.Syn.instantiate0_lift0
#print axioms Rcic.Syn.assumption_get0
#print axioms Rcic.Syn.wt_tyCast
#print axioms Rcic.Syn.eps_tyCast
#print axioms Rcic.Syn.castLift0
#print axioms Rcic.Syn.wt_castLift0
#print axioms Rcic.Syn.eps_castLift0
#print axioms Rcic.Syn.sortLift0
#print axioms Rcic.Syn.wt_sortLift0
#print axioms Rcic.Syn.instEnd
#print axioms Rcic.Syn.instEnd_wt
#print axioms Rcic.Syn.instEnd_eps_drop
#print axioms Rcic.Syn.instEnd_eps_keep
#print axioms Rcic.Syn.es_of_below_fsub
#print axioms Rcic.Syn.beta_dr_drop
#print axioms Rcic.Syn.beta_dr_keep
