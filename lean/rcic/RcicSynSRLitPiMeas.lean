import rcic.RcicSynSRLitPiIssuesSR
import rcic.RcicSynSRLitPiCLW
import rcic.RcicSynTableOfIFull
import rcic.RcicSynES

/-!
# `RcicSynSRLitPiMeas` — cc 00:40Z: measure lemmas, `ConvModPiCongrW`, W-assemblers

§1 discharges the named row-10 right-surface measure residual
`piDomain_H_wt_le`: the LANDED `TyP.piDomain_wt_lt` (batch 167, #7605,
`RcicSynDomainSource`) already proves it STRICTLY — the census row had it
as "owed, wrapper-spine induction" without measuring the tree
(`[asserted_absence_without_measuring]`, corrected additively). The rank
edge `piSRsurfaceR_before` becomes unconditional. Same for the row-8
"app decode-wt lemma": the LANDED `TyP.appSrc_wt` is exactly it.

§2 proves `ConvModPiCongrW` — named OPEN in `RcicSynSRLitPiCLW` as "not on
the tree under this shape": the ConvMod-level pi congruences
`convMod_piL`/`convMod_piR` ARE on the tree (`RcicSynInst`), and the
`piSlot` lift is the LANDED `convMod_piSlot` at a real `TableClosed`; at
`tableOfI hW` that is `tableWF_tableOfI_full` (#7771). The residual is
DISCHARGED at every closed table, in particular at the canonical one.

§3 the W-assemblers: epsW mirrors of the landed `es_beta_drop`/`es_beta_rel`
finishers and the piSlot assembler `esW_pi_of_congr` (the `es_pi` mirror
whose middle congruence is `ConvModPiCongrW`), plus the epsW erasure
equations of the two Π surfaces the row-10 field consumes.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the measure lemmas -/

/-- The named row-10 residual, discharged by the landed strict bound: the
    decoded domain's `H` is strictly lighter than `dr` itself. -/
theorem piDomain_H_wt_le {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A' B' : Expr Nat} {u v : Level} (Aw : Nat → Nat)
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v))) :
    (dr.piDomain rfl).H.wt Aw ≤ dr.wt Aw :=
  Nat.le_of_lt (TyP.piDomain_wt_lt Aw dr rfl)

/-- Row 8's named "app decode-wt lemma", discharged by the landed pair
    bound: both decoded sources are strictly lighter than `dr`. -/
theorem appSrc_wt_le {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T : Expr Nat} {g b : Expr Nat} (Aw : Nat → Nat)
    (dr : TyP E n Γ (.app g b) T) :
    (TyP.appSrc dr rfl).hf.wt Aw ≤ dr.wt Aw ∧
      (TyP.appSrc dr rfl).ha.wt Aw ≤ dr.wt Aw :=
  ⟨Nat.le_of_lt (TyP.appSrc_wt Aw dr rfl).1,
    Nat.le_of_lt (TyP.appSrc_wt Aw dr rfl).2⟩

/-- Row 10 right: the rank edge, UNCONDITIONAL — the `hHRwt` premise of
    `piSRsurfaceR_before_of` is `piDomain_H_wt_le` above. -/
theorem piSRsurfaceR_before {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl (piRightSurface hA hB dr) dr S σ ρ)
      (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) :=
  piSRsurfaceR_before_of Aw hA hB dl dr (piDomain_H_wt_le Aw dr) S σ ρ

/-! ## §2 `ConvModPiCongrW`, discharged at every closed table -/

/-- The named `RcicSynSRLitPiCLW` residual, PROVED: the raw congruences are
    the LANDED `convMod_piL`/`convMod_piR` (`RcicSynInst`), and the `piSlot`
    lift is the LANDED `convMod_piSlot` at a real `TableClosed`. -/
theorem convModPiCongrW_of_tableClosed {tbl : List CRule} (hcl : TableClosed tbl) :
    ConvModPiCongrW tbl :=
  fun b _x x' y _y' hx hy =>
    (convMod_piL (piSlot b y) hx).trans (convMod_piR x' (convMod_piSlot hcl b hy))

/-- At the canonical table the named pi congruence is unconditional:
    `tableWF_tableOfI_full` (#7771) supplies the closedness. -/
theorem convModPiCongrW_tableOfI {E : ResolvedEnv} (hW : EnvWfT E) :
    ConvModPiCongrW (tableOfI hW) :=
  convModPiCongrW_of_tableClosed (tableWF_tableOfI_full hW).closed

/-! ## §3 the W-assemblers -/

/-- `es_beta_drop` at `epsW`: the two `ConvMod` legs compose to the β `ESW`
    exactly as at `eps` — the erasure functions differ, the judgment shape
    does not. -/
theorem esW_beta_drop {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (hL : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ) (hbody.epsW σ (.drop :: ρ)))
    (hR : ConvMod (EStep tbl) LvlEq (hbody.epsW σ (.drop :: ρ)) (dr.epsW σ ρ)) :
    ESW tbl σ ρ (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) := by
  simpa [ESW, CvP.dl, CvP.dr] using (hL.trans hR)

/-- `es_beta_rel` at `epsW`: the mirror with the β redex step in the middle. -/
theorem esW_beta_rel {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (hL : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ)
      (.app (.lam (hbody.epsW σ (.keep :: ρ))) (harg.epsW σ ρ)))
    (hR : ConvMod (EStep tbl) LvlEq
      (ETm.inst 0 (harg.epsW σ ρ) (hbody.epsW σ (.keep :: ρ))) (dr.epsW σ ρ)) :
    ESW tbl σ ρ (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) := by
  have step : ConvMod (EStep tbl) LvlEq
      (.app (.lam (hbody.epsW σ (.keep :: ρ))) (harg.epsW σ ρ))
      (ETm.inst 0 (harg.epsW σ ρ) (hbody.epsW σ (.keep :: ρ))) :=
    .fwd (.inl (.beta _ _))
  simpa [ESW, CvP.dl, CvP.dr] using (hL.trans (step.trans hR))

/-! ### the piSlot assembler (row 10) -/

/-- `TyP.eps_castS` at `epsW`: subject casts preserve the erasure. -/
theorem TyP.epsW_castS {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T e e' : Expr Nat} (h : e = e') (D : TyP E n Γ e T) (σ : Level → Level)
    (ρ : List Disp) : (h ▸ D).epsW σ ρ = D.epsW σ ρ := by
  cases h
  rfl

/-- `TyP.eps_castT` at `epsW`: type casts preserve the erasure. -/
theorem TyP.epsW_castT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T T' : Expr Nat} (h : T = T') (D : TyP E n Γ e T) (σ : Level → Level)
    (ρ : List Disp) : (h ▸ D).epsW σ ρ = D.epsW σ ρ := by
  cases h
  rfl

/-- `piLeftSurface_eps` at `epsW`: the left surface erases to the Π of the
    left endpoints at the bit-chosen slot. -/
theorem piLeftSurface_epsW {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (σ : Level → Level) (ρ : List Disp) :
    (piLeftSurface hA hB).epsW σ ρ =
      .pi (hA.dl.epsW σ ρ)
        (piSlot (levelIsZero (σ u))
          (hB.dl.epsW σ (binderDisp (levelIsZero (σ u)) :: ρ))) := by
  cases hb : levelIsZero (σ u) <;>
    simp only [piLeftSurface, TyP.epsW, hb, binderDisp, piSlot_true,
      piSlot_false]

/-- `piRightSurfaceSrc_eps` at `epsW`. -/
theorem piRightSurfaceSrc_epsW {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (HR : DomainSource E n Γ A')
    (σ : Level → Level) (ρ : List Disp) :
    (piRightSurfaceSrc hA hB HR).epsW σ ρ =
      .pi (HR.H.epsW σ ρ)
        (piSlot (levelIsZero (σ HR.u))
          (hB.dr.epsW σ (binderDisp (levelIsZero (σ HR.u)) :: ρ))) := by
  cases hb : levelIsZero (σ HR.u) <;>
    simp only [piRightSurfaceSrc, TyP.epsW, hb, binderDisp, piSlot_true,
      piSlot_false, epsW_tyCast, TyP.epsW_castS, TyP.epsW_castT]

theorem piRightSurface_epsW {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (σ : Level → Level) (ρ : List Disp) :
    (piRightSurface hA hB dr).epsW σ ρ =
      .pi ((TyP.piDomain dr rfl).H.epsW σ ρ)
        (piSlot (levelIsZero (σ (TyP.piDomain dr rfl).u))
          (hB.dr.epsW σ
            (binderDisp (levelIsZero (σ (TyP.piDomain dr rfl).u)) :: ρ))) :=
  piRightSurfaceSrc_epsW hA hB (dr.piDomain rfl) σ ρ

/-- The piSlot assembler: `es_pi` at `epsW`, the middle congruence being the
    now-proved `ConvModPiCongrW` (slot-aware, unlike the raw `convMod_pi` the
    eps finisher composes with). The legs are at the bit-chosen slot shape. -/
theorem esW_pi_of_congr {tbl : List CRule} (cong : ConvModPiCongrW tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    {σ : Level → Level} {ρ : List Disp} {eA eA' eB eB' : ETm} {b : Bool}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (hAd : ConvMod (EStep tbl) LvlEq eA eA') (hBd : ConvMod (EStep tbl) LvlEq eB eB')
    (hL : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ) (.pi eA (piSlot b eB)))
    (hR : ConvMod (EStep tbl) LvlEq (.pi eA' (piSlot b eB')) (dr.epsW σ ρ)) :
    ESW tbl σ ρ (CvP.pi E n Γ A A' B B' u v hA hB dl dr) := by
  simpa [ESW, CvP.dl, CvP.dr] using
    (hL.trans ((cong b _ _ _ _ hAd hBd).trans hR))

end Rcic.Syn
