import rcic.RcicSynLetBridge
import rcic.RcicSynLetInline
import rcic.RcicSynLetSub

/-!
# Wall 2 (changed-declaration letRight), step 6 — the right surface and the final composition

`research/rcic/sortrow/BELOWC_SEMANTIC_WALLS.md` Part III, "Right surface" and §0.

For the original `CvP.letE hA hv hb dl dr`, `D := hb.dr`, `L := letCtxConvP_of_cvWalkHyp w`,
`D' := L hA hv D : b' : B` under `letBinding A' v'`:

* `U := TyP.letE hA.dr V' D' T'` with `V' := TyP.conv hv.dr hA : v' : A'` and
  `T' := letSub H' V' hA.dr` for `H' := L hA hv D.reg.2`, the un-inlined let at the changed
  declaration, typed at `B[v']`. `U.eps μ ρ = D'.eps μ δR` (`eps_letRightSurface`): the let
  clause inlines `V'`'s erasure, which is `hv.dr`'s.
* `LetBridgeAnswers`: exactly the smaller answers of Part III at the top level — `ES[hv]`,
  `PB[hv.dl, hA.dl]`, `PB[hv.dr, hA.dl]` (the initial value relation), the body's per-node
  answers `BodyAnswers` at the root stage, and the right-surface MixedCL `U.eps ≈ dr.eps`
  (`dr` has the same subject with ascription `B[v]`; CL allows different ascriptions, so no
  ζ/letE/ζ round trip). No field is equivalent to the goal.
* `letE_dr_of_letBridge`: the `hR` argument of the landed `es_of_below_letE_of_dr`,
  `D.eps μ δL ≈ D'.eps μ δR` (the LetBridge induction at the empty stack) `≈ dr.eps μ ρ`
  (the right surface); `es_of_below_letE_of_letBridge` is the `ES` arm it discharges.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the right surface -/

/-- The un-inlined let at the changed declaration, typed at `B[v']`. -/
def letRightSurface {E : ResolvedEnv} {n : Nat} (w : CvWalkHyp E) {Γ : LCtx}
    {A A' v v' b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (D : TyP E n (.letBinding A v :: Γ) b' B) (w₀ : Level)
    (H : TyP E n (.letBinding A v :: Γ) B (.sort w₀)) :
    TyP E n Γ (.letE A' v' b') (instantiate0 v' B) :=
  TyP.letE E n Γ A' u v' B b' w₀ hA.dr (TyP.conv E n Γ v' A A' u hv.dr hA)
    (letCtxConvP_of_cvWalkHyp w hA hv D)
    (letSub (letCtxConvP_of_cvWalkHyp w hA hv H) (TyP.conv E n Γ v' A A' u hv.dr hA) hA.dr)

/-- `U.eps μ ρ = D'.eps μ δR`, definitionally through the let clause and `eps_conv`. -/
theorem eps_letRightSurface {E : ResolvedEnv} {n : Nat} (w : CvWalkHyp E) {Γ : LCtx}
    {A A' v v' b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (D : TyP E n (.letBinding A v :: Γ) b' B) (w₀ : Level)
    (H : TyP E n (.letBinding A v :: Γ) B (.sort w₀)) (μ : Level → Level) (ρ : List Disp) :
    (letRightSurface w hA hv D w₀ H).eps μ ρ =
      (letCtxConvP_of_cvWalkHyp w hA hv D).eps μ (letDisp (hv.dr.eps μ ρ) :: ρ) := by
  unfold letRightSurface
  rw [let_eps_eq, eps_conv]

/-! ## §2 the answers record -/

/-- The smaller answers of Part III at the top level. -/
structure LetBridgeAnswers {E : ResolvedEnv} {n : Nat} (tbl : List CRule) (w : CvWalkHyp E)
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (μ : Level → Level) (ρ : List Disp) : Prop where
  /-- `ES[hv]`. -/
  valueES : ConvMod (EStep tbl) LvlEq (hv.dl.eps μ ρ) (hv.dr.eps μ ρ)
  /-- `PB[hv.dl, hA.dl]`. -/
  valuePBLeft : PBit μ ρ hv.dl hA.dl
  /-- `PB[hv.dr, hA.dl]`. -/
  valuePBRight : PBit μ ρ hv.dr hA.dl
  /-- The body's per-node answers at the root stage (empty stack, slot `0`). -/
  body : BodyAnswers w (iotaPack_of_cvWalkHyp w) (fun hext' h => derivedIotaExt hext' h) tbl μ
    (envExt_refl E) hb.dr
    (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
    (letDisp (hv.dl.eps μ ρ) :: ρ) [] .nil
    (letDisp (hv.dr.eps μ ρ) :: ρ)
  /-- The right-surface MixedCL: `U` against `dr` (same subject, ascriptions `B[v']` / `B[v]`). -/
  rightSurface : ConvMod (EStep tbl) LvlEq
    ((letRightSurface w hA hv hb.dr hb.dr.reg.1 hb.dr.reg.2).eps μ ρ) (dr.eps μ ρ)

/-- The initial value relation from exactly `ES[hv]`, `PB[hv.dl, hA.dl]`, `PB[hv.dr, hA.dl]`. -/
theorem rel_value_of_answers {E : ResolvedEnv} {n : Nat} {tbl : List CRule} {w : CvWalkHyp E}
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb : CvP E n (.letBinding A v :: Γ) b b' B}
    {dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)} {μ : Level → Level} {ρ : List Disp}
    (ans : LetBridgeAnswers tbl w hA hv hb dr μ ρ) :
    Rel tbl (hv.dl.eps μ ρ) (hv.dr.eps μ ρ) :=
  ⟨ans.valueES, ans.valuePBLeft.trans ans.valuePBRight.symm⟩

/-! ## §3 the final composition -/

/-- The `hR` argument of `es_of_below_letE_of_dr`. -/
theorem letE_dr_of_letBridge {E : ResolvedEnv} {n : Nat} {tbl : List CRule}
    (hcl : TableClosed tbl) (w : CvWalkHyp E) {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (μ : Level → Level) (ρ : List Disp)
    (hAP : hb.dr.AssumpPref) (hfit : DisplayFits Γ ρ)
    (ans : LetBridgeAnswers tbl w hA hv hb dr μ ρ) :
    ConvMod (EStep tbl) LvlEq (hb.dr.eps μ (letDisp (hv.dl.eps μ ρ) :: ρ)) (dr.eps μ ρ) := by
  have hdisp : DispRel tbl (letDisp (hv.dl.eps μ ρ) :: ρ) (letDisp (hv.dr.eps μ ρ) :: ρ) :=
    DispRel.letDisp (rel_value_of_answers ans) (DispRel.refl tbl ρ)
  have htr := traceInv_nil (μ' := μ) (E := E) (n := n) (k := 0) (Dom' := A') (Val' := v')
    (Γ := .letBinding A v :: Γ) hcl hdisp
  have hbridge := letBridge hcl w (iotaPack_of_cvWalkHyp w) (fun hext' h => derivedIotaExt hext' h)
    μ (envExt_refl E) hb.dr
    (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
    (letDisp (hv.dl.eps μ ρ) :: ρ) [] .nil
    (letDisp (hv.dr.eps μ ρ) :: ρ) hAP (displayFits_letDisp A v _ hfit) trivial htr ans.body
  have hsurf := eps_letRightSurface w hA hv hb.dr hb.dr.reg.1 hb.dr.reg.2 μ ρ
  have hright := ans.rightSurface
  rw [hsurf] at hright
  exact hbridge.conv.trans hright

/-- The `ES` arm for `CvP.letE` discharged through the LetBridge route. -/
theorem es_of_below_letE_of_letBridge (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {tbl : List CRule} (hcl : TableClosed tbl) (w : CvWalkHyp E) {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)))
    (hAP : hb.dr.AssumpPref) (ans : LetBridgeAnswers tbl w hA hv hb dr σ ρ) :
    ES tbl σ ρ (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) :=
  es_of_below_letE_of_dr Aw tbl hA hv hb dl dr σ ρ hρ Bel
    (by
      have h := letE_dr_of_letBridge hcl w hA hv hb dr σ ρ hAP
        (DisplayFits.of_dispShape (dispShape_of_dispFor hρ)) ans
      cases hve : hv.dl.eps σ ρ
      all_goals
        simp only [letDisp, hve] at h
        exact h)

end Rcic.Syn

#print axioms Rcic.Syn.letRightSurface
#print axioms Rcic.Syn.eps_letRightSurface
#print axioms Rcic.Syn.rel_value_of_answers
#print axioms Rcic.Syn.letE_dr_of_letBridge
#print axioms Rcic.Syn.es_of_below_letE_of_letBridge
