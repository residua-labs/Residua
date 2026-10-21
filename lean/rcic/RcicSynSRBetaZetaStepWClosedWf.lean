import rcic.RcicSynSRBetaZetaStepWBoundary

/-!
# `closedWf_enrichConvT` — the boundary's named open discharge, minus the walker

`sortRow_of_allBelowScopedW` carries `hCW : (enrichTyConvT_of_envWfT …).AllCW`
— per-link endpoint `ClosedWf` of the enriched chain. This module reduces
that hypothesis to a single environment-level contract:

* `LetCtxConvP.ClosedWf hlet` — `hlet`'s outputs are `ClosedWf` whenever the
  input body derivation is. Every enrichment constructor is discharged
  unconditionally against the landed `closedWf_enrichHasTyT` (`betaLeftP`,
  `trZeta`, `appRightP`, `lamRightP`, `piRightP`, `etaLeftP`, `letSurfL/R`,
  `letRightP` helper lemmas here; `instEnd`/`trLetE`/`trLetNorm`/`wkAtZero`
  landed; `sorts`/`consts`/`zetaLocal`/`delta` endpoints are `ClosedWf`-free).
* `closedWf_enrichConvT` — both endpoints of every enriched conversion are
  `ClosedWf`, given the contract.
* `closedWf_enrichTyConvT_of_envWfT` — the chain's `AllCW` follows, and
  `sortRow_of_allBelowScopedW_letCW` gives the eps-stated `sortRow` goal
  from `hBel` plus exactly that one contract.

The residue, named: `letCtxConvP_of_envWfT` (the `EnvWfT`-supplied oracle,
`tyCctxLetAt` at an empty skeleton) satisfying `LetCtxConvP.ClosedWf` —
a ClosedWf-preservation theorem for the let-slot walker `tyAtLet`
(`RcicSynWalkLet`), which rebuilds the body derivation under `setLetB`
through the `Skels` transport layer. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the oracle contract -/

/-- `ClosedWf`-preservation contract for `hlet : LetCtxConvP E n`: the
    retyped body is `ClosedWf` whenever the input body is (the conversion
    inputs need nothing — `ClosedWf` never looks at them). -/
def LetCtxConvP.ClosedWf {E : ResolvedEnv} {n : Nat} (hlet : LetCtxConvP E n) : Prop :=
  ∀ {Γ : LCtx} {A A' v v' e T : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {D : TyP E n (.letBinding A v :: Γ) e T},
    D.ClosedWf → (hlet hA hv D).ClosedWf

/-! ## §2 the helper lemmas -/

/-- `betaLeftP` is `ClosedWf` in its evaluated children. -/
theorem closedWf_betaLeftP {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hbody : TyP E n (.assumption A :: Γ) body B}
    {harg : TyP E n Γ arg A}
    (hbodyW : hbody.ClosedWf) (hargW : harg.ClosedWf) :
    (betaLeftP hA hbody harg).ClosedWf :=
  ⟨hbodyW, hargW⟩

/-- `trZeta`'s endpoints are `ClosedWf` in its inputs. -/
theorem closedWf_trZeta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    (hvW : hv.ClosedWf) (hbW : hb.ClosedWf) :
    (trZeta hA hv hb).dl.ClosedWf ∧ (trZeta hA hv hb).dr.ClosedWf :=
  ⟨closedWf_trLetE hA hvW hbW, closedWf_trLetNorm hA hvW hbW⟩

/-- `appRightP` is `TyP.conv` around an application: `ClosedWf` reads the
    two function/argument right endpoints. -/
theorem closedWf_appRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g A B a b : Expr Nat}
    {h1 : CvP E n Γ f g (.pi A B)} {h2 : CvP E n Γ a b A}
    (h1r : h1.dr.ClosedWf) (h2r : h2.dr.ClosedWf) :
    (appRightP h1 h2).ClosedWf :=
  ⟨h1r, h2r⟩

/-- `lamRightP` is `TyP.conv` around a re-contexted λ: `ClosedWf` reads the
    body's right endpoint. -/
theorem closedWf_lamRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    {h1 : CvP E n Γ A A' (.sort u)} {h2 : CvP E n (.assumption A :: Γ) b b' B}
    (h2r : h2.dr.ClosedWf) :
    (lamRightP h1 h2).ClosedWf :=
  h2r

/-- `piRightP` is a Π of the re-contexted codomain. -/
theorem closedWf_piRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    {h1 : CvP E n Γ A A' (.sort u)} {h2 : CvP E n (.assumption A :: Γ) B B' (.sort v)}
    (h1r : h1.dr.ClosedWf) (h2r : h2.dr.ClosedWf) :
    (piRightP h1 h2).ClosedWf :=
  ⟨h1r, h2r⟩

/-- `etaLam` is `ClosedWf` in the function's typing. -/
theorem closedWf_etaLam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    {h : TyP E n Γ f (.pi A B)}
    {hA : TyP E n Γ A (.sort u)} {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
    (hW : h.ClosedWf) :
    (etaLam h hA hB).ClosedWf := by
  have h3 : (TyP.app E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)
      (lift 0 1 A) (lift 1 1 B) v (wkAtZero (A := A) h)
      (TyP.bvar E n (.assumption A :: Γ) 0 (lift 0 1 A) u
        (lookup_assumption_zero A Γ) (wkAtZero (A := A) hA))
      (tyCast (instantiate_bvar_lift_id 0 B).symm rfl hB)).ClosedWf :=
    ⟨closedWf_wkAtZero hW, trivial⟩
  have h4 : (tyCast rfl (instantiate_bvar_lift_id 0 B)
      (TyP.app E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)
        (lift 0 1 A) (lift 1 1 B) v (wkAtZero (A := A) h)
        (TyP.bvar E n (.assumption A :: Γ) 0 (lift 0 1 A) u
          (lookup_assumption_zero A Γ) (wkAtZero (A := A) hA))
        (tyCast (instantiate_bvar_lift_id 0 B).symm rfl hB))).ClosedWf :=
    closedWf_tyCast rfl (instantiate_bvar_lift_id 0 B) h3
  exact h4

/-- `etaLeftP` is `ClosedWf` in the function's typing. -/
theorem closedWf_etaLeftP {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {hf : TyP E n Γ f (.pi A B)} (hfW : hf.ClosedWf) :
    (etaLeftP hf).ClosedWf :=
  closedWf_etaLam hfW

/-- `letSurfL` is `trLetE` of the left endpoints. -/
theorem closedWf_letSurfL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b B : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb_l : TyP E n (.letBinding A v :: Γ) b B}
    (hvl : hv.dl.ClosedWf) (hbl : hb_l.ClosedWf) :
    (letSurfL hA hv hb_l).ClosedWf :=
  closedWf_trLetE hA.dl hvl hbl

/-- `letSurfR` is `TyP.conv` around `trLetE` of the right endpoints (the
    congruence itself is never read by `ClosedWf`). -/
theorem closedWf_letSurfR {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b' B : Expr Nat} {u w : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb_r' : TyP E n (.letBinding A' v' :: Γ) b' B}
    {hcongr_symm : CvP E n Γ (instantiate0 v' B) (instantiate0 v B) (.sort w)}
    (hvr : hv.dr.ClosedWf) (hbr : hb_r'.ClosedWf) :
    (letSurfR hA hv hb_r' hcongr_symm).ClosedWf :=
  closedWf_trLetE hA.dr hvr hbr

/-- `letRightP` needs exactly the `hlet` contract (plus the two right
    endpoints it reads). -/
theorem closedWf_letRightP {E : ResolvedEnv} {n : Nat} (hlet : LetCtxConvP E n)
    (hCW : LetCtxConvP.ClosedWf hlet)
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb : CvP E n (.letBinding A v :: Γ) b b' B}
    (hvr : hv.dr.ClosedWf) (hbr : hb.dr.ClosedWf) :
    (letRightP hlet hA hv hb).ClosedWf :=
  closedWf_letSurfR hvr (hCW hbr)

/-! ## §3 the enrichment discharge -/

/-- Both endpoints of every enriched conversion are `ClosedWf`, given the
    `hlet` contract — the `ConvT` arm of the landed `closedWf_enrichHasTyT`.
    Every constructor is structural except `letE`'s right endpoint, which is
    exactly the contract. -/
theorem closedWf_enrichConvT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E)
    (hlet : LetCtxConvP E n) (hCW : LetCtxConvP.ClosedWf hlet) :
    ∀ {Γ : LCtx} {a b T : Expr Nat} (h : ConvT E₁ n Γ a b T) (C : CtxP E n Γ),
      (enrichConvT hcl hext hm hlet C h).dl.ClosedWf
        ∧ (enrichConvT hcl hext hm hlet C h).dr.ClosedWf
  | _, _, _, _, .refl _ _ _ h, C =>
      ⟨closedWf_enrichHasTyT hcl hext hm hlet C h,
        closedWf_enrichHasTyT hcl hext hm hlet C h⟩
  | _, _, _, _, .symm _ _ _ _ h, C => ⟨closedWf_enrichConvT hcl hext hm hlet hCW h C |>.2,
      closedWf_enrichConvT hcl hext hm hlet hCW h C |>.1⟩
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, C =>
      ⟨closedWf_enrichConvT hcl hext hm hlet hCW h1 C |>.1,
        closedWf_enrichConvT hcl hext hm hlet hCW h2 C |>.2⟩
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg, C =>
      ⟨closedWf_betaLeftP
          (closedWf_enrichHasTyT hcl hext hm hlet _ hbody)
          (closedWf_enrichHasTyT hcl hext hm hlet C harg),
        closedWf_instEnd
          (closedWf_enrichHasTyT hcl hext hm hlet _ hbody)
          (closedWf_enrichHasTyT hcl hext hm hlet C harg)⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb, C =>
      closedWf_trZeta
        (closedWf_enrichHasTyT hcl hext hm hlet C hv)
        (closedWf_enrichHasTyT hcl hext hm hlet _ hb)
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv, C =>
      ⟨trivial, closedWf_enrichHasTyT hcl hext hm hlet C hv⟩
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb, C =>
      ⟨trivial, closedWf_enrichHasTyT hcl hext hm hlet C hb⟩
  | _, _, _, _, .iota _ _ _ _ _ hlhs hrhs, C =>
      ⟨closedWf_enrichHasTyT hcl hext hm hlet C hlhs,
        closedWf_enrichHasTyT hcl hext hm hlet C hrhs⟩
  | _, _, _, _, .lit _ _ _ _ (.of _) hexp, C =>
      ⟨closedWf_enrichHasTyT hcl hext hm hlet C hexp,
        closedWf_enrichHasTyT hcl hext hm hlet C hexp⟩
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, C =>
      ⟨⟨closedWf_enrichConvT hcl hext hm hlet hCW h1 C |>.1,
        closedWf_enrichConvT hcl hext hm hlet hCW h2 C |>.1⟩,
        closedWf_appRightP (closedWf_enrichConvT hcl hext hm hlet hCW h1 C |>.2)
          (closedWf_enrichConvT hcl hext hm hlet hCW h2 C |>.2)⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb, C =>
      ⟨closedWf_enrichConvT hcl hext hm hlet hCW hb _ |>.1,
        closedWf_lamRightP (closedWf_enrichConvT hcl hext hm hlet hCW hb _ |>.2)⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, C =>
      ⟨⟨closedWf_enrichConvT hcl hext hm hlet hCW hA C |>.1,
        closedWf_enrichConvT hcl hext hm hlet hCW hB _ |>.1⟩,
        closedWf_piRightP (closedWf_enrichConvT hcl hext hm hlet hCW hA C |>.2)
          (closedWf_enrichConvT hcl hext hm hlet hCW hB _ |>.2)⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb, C =>
      ⟨closedWf_letSurfL (closedWf_enrichConvT hcl hext hm hlet hCW hv C |>.1)
          (closedWf_enrichConvT hcl hext hm hlet hCW hb _ |>.1),
        closedWf_letRightP hlet hCW (closedWf_enrichConvT hcl hext hm hlet hCW hv C |>.2)
          (closedWf_enrichConvT hcl hext hm hlet hCW hb _ |>.2)⟩
  | _, _, _, _, .sorts _ _ _ _, _ => ⟨trivial, trivial⟩
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _, _ => ⟨trivial, trivial⟩
  | _, _, _, _, .eta _ _ _ _ h, C =>
      ⟨closedWf_etaLeftP (closedWf_enrichHasTyT hcl hext hm hlet C h),
        closedWf_enrichHasTyT hcl hext hm hlet C h⟩
  | _, _, _, _, .irr _ _ _ _ hP hp hq, C =>
      ⟨closedWf_enrichHasTyT hcl hext hm hlet C hp,
        closedWf_enrichHasTyT hcl hext hm hlet C hq⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, C =>
      ⟨closedWf_enrichConvT hcl hext hm hlet hCW h C |>.1,
        closedWf_enrichConvT hcl hext hm hlet hCW h C |>.2⟩

/-- The enriched chain's `AllCW` follows from the one `hlet` contract. -/
theorem closedWf_enrichTyConvT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E)
    (hlet : LetCtxConvP E n) (hCW : LetCtxConvP.ClosedWf hlet) :
    ∀ {Γ : LCtx} {A B : Expr Nat} (h : TyConvT E₁ n Γ A B) (C : CtxP E n Γ),
      (enrichTyConvT hcl hext hm hlet C h).AllCW
  | _, _, _, .refl _ _, _ => trivial
  | _, _, _, .of _ _ _ _ h, C =>
      closedWf_enrichConvT hcl hext hm hlet hCW h C
  | _, _, _, .trans _ _ _ _ h1 h2, C =>
      ⟨closedWf_enrichTyConvT hcl hext hm hlet hCW h1 C,
        closedWf_enrichTyConvT hcl hext hm hlet hCW h2 C⟩

/-! ## §4 the boundary at one contract -/

/-- `AllCW` of the `EnvWfT`-fronted enrichment under the `EnvWfT`-supplied
    oracle's contract. -/
theorem closedWf_enrichTyConvT_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (h : TyConvT E n Γ A B)
    (hCW : LetCtxConvP.ClosedWf (letCtxConvP_of_envWfT (n := n) hW)) :
    (enrichTyConvT_of_envWfT hW hΓ h).AllCW :=
  closedWf_enrichTyConvT (envClosed_of_envWfT hW) (envExt_refl E)
    (memberSortP_of_envWfT hW) (letCtxConvP_of_envWfT (n := n) hW) hCW h
    (enrichCtxWfT_of_envWfT hW hΓ)

/-- **The boundary at one contract.** The eps-stated `sortRow` goal from the
    epsW pack, unconditionally in the derivation: the per-link `hCW` of
    `sortRow_of_allBelowScopedW` is discharged by `closedWf_enrichConvT`
    down to the single named residue — `LetCtxConvP.ClosedWf
    (letCtxConvP_of_envWfT hW)`, the let-slot walker's ClosedWf-preservation
    (`tyCctxLetAt`/`tyAtLet` over the `Skels` transport layer). -/
theorem sortRow_of_allBelowScopedW_letCW {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} (hBel : AllBelowScopedW Eₐ Aw tbl) (hTbl : TableWF tbl)
    (hW : EnvWfT E) (hext : EnvExt E Eₐ) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} (h : TyConvT E n Γ (.sort u) (.sort v))
    (hletCW : LetCtxConvP.ClosedWf (letCtxConvP_of_envWfT (n := n) hW)) : eqN u v :=
  sortRow_of_allBelowScopedW hBel hTbl hW hext hΓ h
    (closedWf_enrichTyConvT_of_envWfT hW hΓ h hletCW)

end Rcic.Syn

#print axioms Rcic.Syn.LetCtxConvP.ClosedWf
#print axioms Rcic.Syn.closedWf_betaLeftP
#print axioms Rcic.Syn.closedWf_trZeta
#print axioms Rcic.Syn.closedWf_appRightP
#print axioms Rcic.Syn.closedWf_lamRightP
#print axioms Rcic.Syn.closedWf_piRightP
#print axioms Rcic.Syn.closedWf_etaLam
#print axioms Rcic.Syn.closedWf_etaLeftP
#print axioms Rcic.Syn.closedWf_letSurfL
#print axioms Rcic.Syn.closedWf_letSurfR
#print axioms Rcic.Syn.closedWf_letRightP
#print axioms Rcic.Syn.closedWf_enrichConvT
#print axioms Rcic.Syn.closedWf_enrichTyConvT
#print axioms Rcic.Syn.closedWf_enrichTyConvT_of_envWfT
#print axioms Rcic.Syn.sortRow_of_allBelowScopedW_letCW
