import rcic.RcicSynDeltaBeta
import rcic.RcicERPiSlotConv

/-!
# Syntactic sortRow, build step 3at — `lam` and `pi` right endpoints (`TyP.cctx` at `0`, zero `tyCctxAt`) and Step 4 `sortRow` bridge

`research/rcic/semantic/S3_ES_ARMS.md` §46. Continuing the remaining `ES` arms
and Step 4 bridge after step 3as (`RcicSynDeltaBeta`):

1. **`CvP.lam` right endpoint (`atoms_cctx`, `lam_dr_body_cl`,
   `es_of_below_lam_got_both_drop`, `es_of_below_lam_got_both_keep`,
   `es_of_below_lam_got_both_keep_star`)**:
   - In `CvP.lam E n Γ A A' b b' B u hA hb dl dr`, `hb.dr` types `b'` in
     `.assumption A :: Γ`, while `gR : LamGot Aw (dr.wt Aw) E n Γ A' b'` gives
     `gR.hbody : TyP E n (.assumption A' :: Γ) b' gR.B`.
   - Wrapping `hb.dr` in a single outer `TyP.cctx` at index `0`:
     `TyP.cctx E n Γ b' B A A' u hb.dr hA : TyP E n (.assumption A' :: Γ) b' B`
     gives a typing of `b'` in `.assumption A' :: Γ` whose atoms are
     `hb.dr.atoms Aw ++ hA.atoms Aw` (every atom `< hnode.wt Aw`) and whose
     erasure is `hb.dr.eps σ ρ'` definitionally (`rfl`).
   - Thus `cl_under_atoms` proves `lam_dr_body_cl` in `.assumption A' :: Γ` at
     `binderDisp (levelIsZero (σ u)) :: ρ` (`dispFor_binderDisp hρ hA.dr`) with
     **zero `tyCctxAt` walk**, discharging `es_of_below_lam_got_both_drop`,
     `es_of_below_lam_got_both_keep`, and `es_of_below_lam_got_both_keep_star`.

2. **`CvP.pi` right endpoint (`eps_pi_clause`, `pi_dl_clause`, `PiGot`,
   `PiRead`, `piOfNode`, `piClauseOf`, `pi_dr_dom_bitCoh`, `pi_dr_dom_cl`,
   `pi_dr_cod_cl`, `es_of_below_pi_got_drop`, `es_of_below_pi_got_keep`,
   `es_of_below_pi_got`)**:
   - When `dr` is read into `gR : PiGot Aw (dr.wt Aw) E n Γ A' B'`, `hA.dr` and
     `gR.hA` both type `A'` at a sort in `Γ` with atoms `< hnode.wt Aw`.
   - `bitCoh_under_atoms` proves `pi_dr_dom_bitCoh`
     (`levelIsZero (σ u) = levelIsZero (σ gR.u)`) directly from `Bel`, and
     `cl_under_atoms` proves `pi_dr_dom_cl` (`CL tbl σ ρ hA.dr gR.hA`) with
     **zero `piInv`**.
   - Wrapping `hB.dr` in `TyP.cctx E n Γ B' (.sort v) A A' u hB.dr hA`,
     `cl_under_atoms` against `gR.hB` in `.assumption A' :: Γ` proves
     `pi_dr_cod_cl` with **zero `tyCctxAt` walk**, discharging
     `es_of_below_pi_got`, `es_of_below_pi_got_drop`, and
     `es_of_below_pi_got_keep`.

3. **Step 4 `sortRow` bridge (`eqN_of_cvp_sorts_es_cl`,
   `eqN_of_cvp_sorts_es_cl_id`, `eqN_of_cvp_sorts_below`,
   `eqN_of_cvp_sorts_below_nil`, `not_eqN_zero_succ`,
   `not_cvp_sort_zero_succ_of_below`)**:
   - For any `h : CvP E n Γ (.sort u) (.sort v) T` with `TableWF tbl` and
     `ES tbl σ ρ h`, coherence of `h.dl` and `h.dr` against canonical `TyP.sort`
     nodes (supplied by `cl_under` on `CvP.symm` from `Below`) chains with
     `eqN_of_convE_sort_wf hW` to prove `eqN (σ u) (σ v)` (and `eqN u v` at
     `σ = id`).

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `CvP.lam` right endpoint: `TyP.cctx` at `0` (zero `tyCctxAt`) and full `ES` arms -/

theorem atoms_cctx (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A A' : Expr Nat} {u : Level}
    (D : TyP E n (.assumption A :: Γ) e T) (hA : CvP E n Γ A A' (.sort u)) :
    (TyP.cctx E n Γ e T A A' u D hA).atoms Aw = D.atoms Aw ++ hA.atoms Aw := rfl

/-- In `CvP.lam E n Γ A A' b b' B u hA hb dl dr`, wrapping `hb.dr` in a single
    outer `TyP.cctx` at index `0` along `hA` places `hb.dr` in `.assumption A' :: Γ`
    with atoms `hb.dr.atoms Aw ++ hA.atoms Aw < hnode.wt Aw` and identical
    erasure (`rfl`). Thus `cl_under_atoms` gives `CL` against `gR.hbody` with
    **zero `tyCctxAt` walk**. -/
theorem lam_dr_body_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (gR : LamGot Aw (dr.wt Aw) E n Γ A' b')
    (σ : Level → Level) (ρ' : List Disp)
    (hρ' : DispFor σ E n (.assumption A' :: Γ) ρ')
    (Bel : Below Aw tbl (cvMeas Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr))) :
    CL tbl σ ρ' (TyP.cctx E n Γ b' B A A' u hb.dr hA) gR.hbody := by
  let hnode := CvP.lam E n Γ A A' b b' B u hA hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hdr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwbr : hb.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw hb
    simp only [CvP.wt]; omega
  have hwA : hA.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  refine cl_under_atoms Aw tbl hnode ht Bel
    (TyP.cctx E n Γ b' B A A' u hb.dr hA) gR.hbody σ ρ' hρ' ?_ ?_
  · intro y hy
    rw [atoms_cctx] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact atoms_lt_of_wt_lt Aw hb.dr hwbr y hy
    · exact cvp_atoms_lt_of_wt_lt Aw hA hwA y hy
  · intro y hy
    exact Nat.lt_trans (gR.lt y hy) hdr

/-- Full `ES` for `CvP.lam` on a proof domain (`levelIsZero (σ u) = true`) when
    both `dl` and `dr` erase to `lamClauseOf` with `levelIsZero (σ gL.u) = true`
    and `levelIsZero (σ gR.u) = true`. -/
theorem es_of_below_lam_got_both_drop (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (gL : LamGot Aw (dl.wt Aw) E n Γ A b)
    (gR : LamGot Aw (dr.wt Aw) E n Γ A' b')
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = true)
    (hgL : levelIsZero (σ gL.u) = true) (hgR : levelIsZero (σ gR.u) = true)
    (hWL : dl.eps σ ρ = lamClauseOf gL σ ρ)
    (hWR : dr.eps σ ρ = lamClauseOf gR σ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr))) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  have hR_cl := lam_dr_body_cl Aw tbl hA hb dl dr gR σ (.drop :: ρ)
    (dispFor_assumption_drop hρ hA.dr hu) Bel
  unfold CL at hR_cl
  rw [eps_cctx] at hR_cl
  have hdr_eq : dr.eps σ ρ = gR.hbody.eps σ (.drop :: ρ) := by
    rw [hWR]
    unfold lamClauseOf
    rw [hgR, binderDisp_drop]
    rfl
  rw [← hdr_eq] at hR_cl
  exact es_of_below_lam_got_drop Aw tbl hA hb dl dr gL σ ρ hρ hu hgL hWL hR_cl Bel

/-- Full `ES` for `CvP.lam` on a relevant domain (`levelIsZero (σ u) = false`)
    when both `dl` and `dr` erase to `lamClauseOf` with relevant non-`★` bodies. -/
theorem es_of_below_lam_got_both_keep (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (gL : LamGot Aw (dl.wt Aw) E n Γ A b)
    (gR : LamGot Aw (dr.wt Aw) E n Γ A' b')
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = false)
    (hgL : levelIsZero (σ gL.u) = false) (hgR : levelIsZero (σ gR.u) = false)
    (hWL : dl.eps σ ρ = lamClauseOf gL σ ρ)
    (hWR : dr.eps σ ρ = lamClauseOf gR σ ρ)
    (hgbL_ne : gL.hbody.eps σ (.keep :: ρ) ≠ .star)
    (hgbR_ne : gR.hbody.eps σ (.keep :: ρ) ≠ .star)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr))) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  have hR_cl := lam_dr_body_cl Aw tbl hA hb dl dr gR σ (.keep :: ρ)
    (dispFor_assumption_keep hρ hA.dr hu) Bel
  unfold CL at hR_cl
  rw [eps_cctx] at hR_cl
  have hdr_eq : dr.eps σ ρ = .lam (gR.hbody.eps σ (.keep :: ρ)) := by
    rw [hWR]
    unfold lamClauseOf
    rw [hgR, binderDisp_keep]
    exact lamClause_of_ne hgbR_ne
  have hR : ConvMod (EStep tbl) LvlEq (.lam (hb.dr.eps σ (.keep :: ρ))) (dr.eps σ ρ) := by
    rw [hdr_eq]
    exact convMod_lam hR_cl
  exact es_of_below_lam_got_keep Aw tbl hA hb dl dr gL σ ρ hρ hu hgL hWL hgbL_ne hR Bel

/-- Full `ES` for `CvP.lam` on a relevant domain when both extracted bodies
    erase to `★`: both `dl.eps` and `dr.eps` are `★`. -/
theorem es_of_below_lam_got_both_keep_star (tbl : List CRule)
    {Aw : Nat → Nat} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (gL : LamGot Aw (dl.wt Aw) E n Γ A b)
    (gR : LamGot Aw (dr.wt Aw) E n Γ A' b')
    (σ : Level → Level) (ρ : List Disp)
    (hgL : levelIsZero (σ gL.u) = false) (hgR : levelIsZero (σ gR.u) = false)
    (hWL : dl.eps σ ρ = lamClauseOf gL σ ρ)
    (hWR : dr.eps σ ρ = lamClauseOf gR σ ρ)
    (hgbL_star : gL.hbody.eps σ (.keep :: ρ) = .star)
    (hgbR_star : gR.hbody.eps σ (.keep :: ρ) = .star) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  have hdl_star : dl.eps σ ρ = .star := by
    rw [hWL]
    unfold lamClauseOf
    rw [hgL, binderDisp_keep, hgbL_star]
    rfl
  have hdr_star : dr.eps σ ρ = .star := by
    rw [hWR]
    unfold lamClauseOf
    rw [hgR, binderDisp_keep, hgbR_star]
    rfl
  simp only [ES, CvP.dl, CvP.dr, hdl_star, hdr_star]
  exact .refl _

/-! ## §2 `CvP.pi` right endpoint: `PiGot`, `piClauseOf`, `TyP.cctx` at `0`, and full `ES` arms -/

/-- Unified clause equation for `TyP.pi` using `binderDisp`. -/
theorem eps_pi_clause {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {B : Expr Nat} {v : Level}
    (hA : TyP E n Γ A (.sort u)) (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.pi E n Γ A u B v hA hB).eps σ ρ =
      .pi (hA.eps σ ρ) (piSlot (levelIsZero (σ u))
        (hB.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))) := by
  cases hzu : levelIsZero (σ u) <;> simp only [TyP.eps, hzu, binderDisp, piSlot]

/-- `CvP.pi`'s left endpoint `dl` is `CL` to `.pi (hA.dl.eps σ ρ) (hB.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))`. -/
theorem pi_dl_clause (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (.pi (hA.dl.eps σ ρ) (piSlot (levelIsZero (σ u))
        (hB.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)))) := by
  have hL := pi_dl Aw tbl hA hB dl dr σ ρ hρ Bel
  cases hzu : levelIsZero (σ u) <;> simpa only [hzu, binderDisp, piSlot] using hL

/-- Domain and codomain typings extracted from a typing of `.pi A B`, both
    under an external atom bound `src`. -/
structure PiGot (Aw : Nat → Nat) (src : Nat) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (A B : Expr Nat) : Type where
  u : Level
  v : Level
  hA : TyP E n Γ A (.sort u)
  hB : TyP E n (.assumption A :: Γ) B (.sort v)
  ltA : ∀ y ∈ hA.atoms Aw, y < src
  ltB : ∀ y ∈ hB.atoms Aw, y < src

inductive PiRead (Aw : Nat → Nat) (src : Nat) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (A B : Expr Nat) : Type where
  | yes (g : PiGot Aw src E n Γ A B)
  | no

def PiRead.isYes {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A B : Expr Nat} : PiRead Aw src E n Γ A B → Bool
  | .yes _ => true
  | .no => false

/-- Extract `PiGot` from a pure `TyP.pi` node. -/
def piOfNode {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat) (src : Nat)
    {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hA : TyP Ei n Γ A (.sort u))
    (hB : TyP Ei n (.assumption A :: Γ) B (.sort v))
    (hAt : ∀ y ∈ (TyP.pi Ei n Γ A u B v hA hB).atoms Aw, y < src) :
    PiGot Aw src E n Γ A B :=
  let D := TyP.pi Ei n Γ A u B v hA hB
  let hw : D.wt Aw < src := hAt (D.wt Aw) (by
    simp only [TyP.atoms]
    exact List.mem_singleton.mpr rfl)
  let hAw : hA.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  let hBw : hB.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  { u := u
    v := v
    hA := TyP.ewk Ei E n Γ A (.sort u) hext hA
    hB := TyP.ewk Ei E n (.assumption A :: Γ) B (.sort v) hext hB
    ltA := fun y hy => by
      rw [show (TyP.ewk Ei E n Γ A (.sort u) hext hA).atoms Aw = hA.atoms Aw from rfl] at hy
      exact Nat.lt_trans (atoms_lt_of_wt_lt Aw hA hAw y hy) hw
    ltB := fun y hy => by
      rw [show (TyP.ewk Ei E n (.assumption A :: Γ) B (.sort v) hext hB).atoms Aw = hB.atoms Aw from rfl] at hy
      exact Nat.lt_trans (atoms_lt_of_wt_lt Aw hB hBw y hy) hw }

/-- The erased clause of a `PiGot` reading. -/
def piClauseOf {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A B : Expr Nat} (g : PiGot Aw src E n Γ A B)
    (σ : Level → Level) (ρ : List Disp) : ETm :=
  .pi (g.hA.eps σ ρ) (piSlot (levelIsZero (σ g.u))
    (g.hB.eps σ (binderDisp (levelIsZero (σ g.u)) :: ρ)))

theorem piOfNode_eps {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat) (src : Nat)
    {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hA : TyP Ei n Γ A (.sort u))
    (hB : TyP Ei n (.assumption A :: Γ) B (.sort v))
    (hAt : ∀ y ∈ (TyP.pi Ei n Γ A u B v hA hB).atoms Aw, y < src)
    (σ : Level → Level) (ρ : List Disp) :
    piClauseOf (piOfNode hext Aw src hA hB hAt) σ ρ =
      (TyP.pi Ei n Γ A u B v hA hB).eps σ ρ := by
  rw [eps_pi_clause]
  rfl

/-- Push `wk` under a `PiRead` reading. -/
def pushPiWk {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {n : Nat}
    {Γ₀ : LCtx} {A₀ B₀ : Expr Nat} (d : LocalDecl) (c : Nat)
    (r : PiRead Aw src E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hA : lift c 1 A₀ = A) (hB : lift (c + 1) 1 B₀ = B) :
    PiRead Aw src E n (insertAt d c Γ₀) A B :=
  match r with
  | .no => .no
  | .yes g =>
      .yes {
        u := g.u
        v := g.v
        hA := tyCast hA rfl (TyP.wk E n Γ₀ A₀ (.sort g.u) d c g.hA)
        hB :=
          tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hA)
            (tyCast hB rfl
              (TyP.wk E n (.assumption A₀ :: Γ₀) B₀ (.sort g.v) d (c + 1) g.hB))
        ltA := by
          intro y hy
          rw [atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltA y hy
        ltB := by
          intro y hy
          rw [atoms_tyCastCtx, atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltB y hy }

/-- Push `linst` under a `PiRead` reading. -/
def pushPiLinst {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {a n : Nat}
    {Γ₀ : LCtx} {A₀ B₀ : Expr Nat} (ls : List Level)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (r : PiRead Aw src E a Γ₀ A₀ B₀) {A B : Expr Nat}
    (hA : instantiateLevels ls A₀ = A) (hB : instantiateLevels ls B₀ = B) :
    PiRead Aw src E n (instLvlsCtx ls Γ₀) A B :=
  match r with
  | .no => .no
  | .yes g =>
      .yes {
        u := instLevel ls g.u
        v := instLevel ls g.v
        hA := tyCast hA rfl
          (TyP.linst E a n Γ₀ A₀ (.sort g.u) ls hls hlen g.hA)
        hB :=
          tyCastCtx ((instLvls_assumption ls A₀ Γ₀).trans
              (congrArg (fun X => .assumption X :: instLvlsCtx ls Γ₀) hA))
            (tyCast hB rfl
              (TyP.linst E a n (.assumption A₀ :: Γ₀) B₀ (.sort g.v) ls hls hlen g.hB))
        ltA := by
          intro y hy
          rw [atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltA y hy
        ltB := by
          intro y hy
          rw [atoms_tyCastCtx, atoms_tyCast] at hy
          simp only [TyP.atoms] at hy
          exact g.ltB y hy }

/-- Push `esub` under a `PiRead` reading. -/
def pushPiEsub {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    {src : Nat} {n : Nat} {Γ₀ : LCtx} {A₀ B₀ t repl : Expr Nat}
    {j : Nat} {uE : Level}
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP Ei n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP Ei n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (r : PiRead Aw src E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B)
    (hAtv : ∀ y ∈ hv.atoms Aw, y < src)
    (hAtT : ∀ y ∈ hvT.atoms Aw, y < src) :
    PiRead Aw src E n (substRemove repl j Γ₀) A B :=
  match r with
  | .no => .no
  | .yes g =>
      let hvE := TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv
      let hvTE := TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT
      .yes {
        u := g.u
        v := g.v
        hA := tyCast hAe rfl
          (TyP.esub E n Γ₀ A₀ (.sort g.u) t repl j uE g.hA hget hvE hvTE)
        hB := pushBodyEsub g.hB hget hvE hvTE hAe hBe
        ltA := by
          intro y hy
          rw [atoms_tyCast, atoms_esub] at hy
          have hvA : hvE.atoms Aw = hv.atoms Aw := rfl
          have hvTA : hvTE.atoms Aw = hvT.atoms Aw := rfl
          rw [hvA, hvTA] at hy
          cases List.mem_append.mp hy with
          | inl hy =>
            cases List.mem_append.mp hy with
            | inl hya => exact g.ltA y hya
            | inr hyv => exact hAtv y hyv
          | inr hyT => exact hAtT y hyT
        ltB := by
          intro y hy
          rw [atoms_pushBodyEsub] at hy
          have hvA : hvE.atoms Aw = hv.atoms Aw := rfl
          have hvTA : hvTE.atoms Aw = hvT.atoms Aw := rfl
          rw [hvA, hvTA] at hy
          cases List.mem_append.mp hy with
          | inl hy =>
            cases List.mem_append.mp hy with
            | inl hyb => exact g.ltB y hyb
            | inr hyv => exact hAtv y hyv
          | inr hyT => exact hAtT y hyT }

set_option maxHeartbeats 800000 in
/-- Read a typing of `.pi A B` into `PiRead Aw src E n Γ A B`. -/
def readPi {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat) (src : Nat) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {A B : Expr Nat} → (he : e = .pi A B) →
    (hAt : ∀ y ∈ D.atoms Aw, y < src) →
    PiRead Aw src E n Γ A B
  | _, _, _, _, .sort .., _, _, he, _ => by cases he
  | _, _, _, _, .bvar .., _, _, he, _ => by cases he
  | _, _, _, _, .const .., _, _, he, _ => by cases he
  | _, _, _, _, .pi _ _ _ A₀ u B₀ v hA hB, _, _, he, hAt =>
      match A₀, B₀, he with
      | _, _, rfl => .yes (piOfNode hext Aw src hA hB hAt)
  | _, _, _, _, .lam .., _, _, he, _ => by cases he
  | _, _, _, _, .app .., _, _, he, _ => by cases he
  | _, _, _, _, .letE .., _, _, he, _ => by cases he
  | _, _, _, _, .lit .., _, _, he, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner hc, _, _, he, hAt =>
      readPi hext Aw src inner he (conv_atom_src Aw inner hc hAt)
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he, hAt =>
      match lift_eq_pi he with
      | .mk A₀ B₀ he₀ hAe hBe =>
          pushPiWk d c (readPi hext Aw src inner he₀ (wk_atom_src Aw inner hAt)) hAe hBe
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, _, _, he, hAt =>
      match instantiate_eq_pi he with
      | .under A₀ B₀ he₀ hAe hBe =>
          pushPiEsub hext Aw hget hv hvT
            (readPi hext Aw src inner he₀
              (esub_inner_src Aw inner hget hv hvT hAt))
            hAe hBe
            (esub_val_src Aw inner hget hv hvT hAt)
            (esub_ty_src Aw inner hget hv hvT hAt)
      | .here _ hr =>
          readPi hext Aw src hv hr (esub_val_src Aw inner hget hv hvT hAt)
  | _, _, _, _, .lsub .., _, _, _, _ => .no
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he, hAt =>
      match instantiateLevels_eq_pi he with
      | .mk A₀ B₀ he₀ hAe hBe =>
          pushPiLinst ls hls hlen
            (readPi hext Aw src inner he₀ (linst_atom_src Aw hls hlen inner hAt))
            hAe hBe
  | _, _, _, _, .ewk E₀ _ _ _ _ _ hext' inner, _, _, he, hAt =>
      readPi (envExt_trans hext' hext) Aw src inner he (ewk_atom_src Aw hext' inner hAt)
  | _, _, _, _, .cctx .., _, _, _, _ => .no

theorem readPi_pi_yes (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B : Expr Nat} {u v : Level}
    (hA : TyP E n Γ A (.sort u)) (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
    (readPi (envExt_refl E) Aw ((TyP.pi E n Γ A u B v hA hB).wt Aw + 1)
      (TyP.pi E n Γ A u B v hA hB) rfl
      (fun y hy => atoms_lt_of_wt_lt Aw (TyP.pi E n Γ A u B v hA hB)
        (Nat.lt_succ_self _) y hy)).isYes = true := by
  rfl

/-- `hA.dr` and `gR.hA` both type `A'` at a sort in `Γ` with atoms `< hnode.wt Aw`,
    so `bitCoh_under_atoms` gives `levelIsZero (σ u) = levelIsZero (σ gR.u)`
    directly from `Bel`. -/
theorem pi_dr_dom_bitCoh (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (gR : PiGot Aw (dr.wt Aw) E n Γ A' B')
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    BitCoh σ hA.dr gR.hA := by
  let hnode := CvP.pi E n Γ A A' B B' u v hA hB dl dr
  have ht : hnode.isTransport = false := rfl
  have hdr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwAr : hA.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw hA
    simp only [CvP.wt]; omega
  refine bitCoh_under_atoms Aw tbl hnode ht Bel hA.dr gR.hA σ ρ hρ ?_ ?_
  · intro y hy
    exact atoms_lt_of_wt_lt Aw hA.dr hwAr y hy
  · intro y hy
    exact Nat.lt_trans (gR.ltA y hy) hdr

/-- `hA.dr` and `gR.hA` both type `A'` in `Γ` with atoms `< hnode.wt Aw`,
    so `cl_under_atoms` gives `CL` of `hA.dr` and `gR.hA` with **zero `piInv`**. -/
theorem pi_dr_dom_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (gR : PiGot Aw (dr.wt Aw) E n Γ A' B')
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    CL tbl σ ρ hA.dr gR.hA := by
  let hnode := CvP.pi E n Γ A A' B B' u v hA hB dl dr
  have ht : hnode.isTransport = false := rfl
  have hdr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwAr : hA.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw hA
    simp only [CvP.wt]; omega
  refine cl_under_atoms Aw tbl hnode ht Bel hA.dr gR.hA σ ρ hρ ?_ ?_
  · intro y hy
    exact atoms_lt_of_wt_lt Aw hA.dr hwAr y hy
  · intro y hy
    exact Nat.lt_trans (gR.ltA y hy) hdr

/-- Wrapping `hB.dr` in a single outer `TyP.cctx` at index `0` along `hA`
    places `hB.dr` in `.assumption A' :: Γ` with atoms `< hnode.wt Aw` and
    identical erasure (`rfl`). Thus `cl_under_atoms` gives `CL` against `gR.hB`
    with **zero `tyCctxAt` walk**. -/
theorem pi_dr_cod_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (gR : PiGot Aw (dr.wt Aw) E n Γ A' B')
    (σ : Level → Level) (ρ' : List Disp)
    (hρ' : DispFor σ E n (.assumption A' :: Γ) ρ')
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    CL tbl σ ρ' (TyP.cctx E n Γ B' (.sort v) A A' u hB.dr hA) gR.hB := by
  let hnode := CvP.pi E n Γ A A' B B' u v hA hB dl dr
  have ht : hnode.isTransport = false := rfl
  have hdr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwBr : hB.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw hB
    simp only [CvP.wt]; omega
  have hwA : hA.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  refine cl_under_atoms Aw tbl hnode ht Bel
    (TyP.cctx E n Γ B' (.sort v) A A' u hB.dr hA) gR.hB σ ρ' hρ' ?_ ?_
  · intro y hy
    rw [atoms_cctx] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact atoms_lt_of_wt_lt Aw hB.dr hwBr y hy
    · exact cvp_atoms_lt_of_wt_lt Aw hA hwA y hy
  · intro y hy
    exact Nat.lt_trans (gR.ltB y hy) hdr

/-- Full `ES` for `CvP.pi` when `dr` erases to `piClauseOf gR σ ρ`.
    Because `pi_dr_dom_bitCoh` proves `levelIsZero (σ u) = levelIsZero (σ gR.u)`
    directly from `Bel`, no level-bit hypothesis on `gR.u` is needed. -/
theorem es_of_below_pi_got (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (gR : PiGot Aw (dr.wt Aw) E n Γ A' B')
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hTC : TableClosed tbl)
    (hWR : dr.eps σ ρ = piClauseOf gR σ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    ES tbl σ ρ (CvP.pi E n Γ A A' B B' u v hA hB dl dr) := by
  have hbit : levelIsZero (σ u) = levelIsZero (σ gR.u) :=
    pi_dr_dom_bitCoh Aw tbl hA hB dl dr gR σ ρ hρ Bel
  have hdom_cl := pi_dr_dom_cl Aw tbl hA hB dl dr gR σ ρ hρ Bel
  have hcod_cl := pi_dr_cod_cl Aw tbl hA hB dl dr gR σ
    (binderDisp (levelIsZero (σ u)) :: ρ) (dispFor_binderDisp hρ hA.dr) Bel
  unfold CL at hdom_cl hcod_cl
  rw [eps_cctx] at hcod_cl
  have hdr_eq : dr.eps σ ρ =
      .pi (gR.hA.eps σ ρ) (piSlot (levelIsZero (σ u))
        (gR.hB.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))) := by
    rw [hWR]
    unfold piClauseOf
    rw [← hbit]
  have hR : ConvMod (EStep tbl) LvlEq
      (.pi (hA.dr.eps σ ρ) (piSlot (levelIsZero (σ u))
        (hB.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))))
      (dr.eps σ ρ) := by
    rw [hdr_eq]
    exact convMod_pi hdom_cl (convMod_piSlot hTC _ hcod_cl)
  exact es_of_below_pi_of_dr Aw tbl hA hB dl dr σ ρ hρ hTC Bel hR

/-- Proof-domain corollary of `es_of_below_pi_got`. -/
theorem es_of_below_pi_got_drop (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (gR : PiGot Aw (dr.wt Aw) E n Γ A' B')
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hTC : TableClosed tbl)
    (hWR : dr.eps σ ρ = piClauseOf gR σ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    ES tbl σ ρ (CvP.pi E n Γ A A' B B' u v hA hB dl dr) :=
  es_of_below_pi_got Aw tbl hA hB dl dr gR σ ρ hρ hTC hWR Bel

/-- Relevant-domain corollary of `es_of_below_pi_got`. -/
theorem es_of_below_pi_got_keep (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (gR : PiGot Aw (dr.wt Aw) E n Γ A' B')
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hTC : TableClosed tbl)
    (hWR : dr.eps σ ρ = piClauseOf gR σ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    ES tbl σ ρ (CvP.pi E n Γ A A' B B' u v hA hB dl dr) :=
  es_of_below_pi_got Aw tbl hA hB dl dr gR σ ρ hρ hTC hWR Bel

/-! ## §3 Step 4 `sortRow` bridge: `eqN` from `ES` + `CL` / `Below` -/

/-- Step 4 bridge: for any `h : CvP E n Γ (.sort u) (.sort v) T` with
    `TableWF tbl`, if `ES tbl σ ρ h` holds and `h.dl`, `h.dr` are `CL` to
    canonical `TyP.sort` nodes, then `eqN_of_convE_sort_wf` gives `eqN (σ u) (σ v)`. -/
theorem eqN_of_cvp_sorts_es_cl {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u v : Level} {T : Expr Nat}
    (h : CvP E n Γ (.sort u) (.sort v) T)
    (σ : Level → Level) (ρ : List Disp)
    (hes : ES tbl σ ρ h)
    (hL : CL tbl σ ρ h.dl (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
    (hR : CL tbl σ ρ h.dr (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    eqN (σ u) (σ v) := by
  have hL' : ConvMod (EStep tbl) LvlEq (h.dl.eps σ ρ) (.sort (σ u)) := by
    simpa only [CL, eps_sort] using hL
  have hR' : ConvMod (EStep tbl) LvlEq (h.dr.eps σ ρ) (.sort (σ v)) := by
    simpa only [CL, eps_sort] using hR
  have hconv : ConvMod (EStep tbl) LvlEq (.sort (σ u)) (.sort (σ v)) :=
    (ConvMod.symm' LvlEq.symm' hL').trans (hes.trans hR')
  exact eqN_of_convE_sort_wf hW hconv

/-- At `σ = id`, `eqN_of_cvp_sorts_es_cl` yields `eqN u v`. -/
theorem eqN_of_cvp_sorts_es_cl_id {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u v : Level} {T : Expr Nat}
    (h : CvP E n Γ (.sort u) (.sort v) T)
    (ρ : List Disp)
    (hes : ES tbl id ρ h)
    (hL : CL tbl id ρ h.dl (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
    (hR : CL tbl id ρ h.dr (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    eqN u v :=
  eqN_of_cvp_sorts_es_cl hW h id ρ hes hL hR

/-- Step 4 bridge from `Below`: for any `h : CvP E n Γ (.sort u) (.sort v) T`
    (transport or non-transport), wrapping `h` in `CvP.symm` produces a
    non-transport node whose weight strictly bounds `h.dl`, `h.dr`, and both
    canonical `TyP.sort` nodes (weight `1`). Thus `ES tbl σ ρ h` and `Bel`
    yield `eqN (σ u) (σ v)`. -/
theorem eqN_of_cvp_sorts_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u v : Level} {T : Expr Nat}
    (h : CvP E n Γ (.sort u) (.sort v) T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hes : ES tbl σ ρ h)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.symm E n Γ (.sort u) (.sort v) T h h.dr h.dl))) :
    eqN (σ u) (σ v) := by
  let hsymm := CvP.symm E n Γ (.sort u) (.sort v) T h h.dr h.dl
  have ht : hsymm.isTransport = false := rfl
  let canonL := TyP.sort E n Γ u (.succ u) (eqN_refl _)
  let canonR := TyP.sort E n Γ v (.succ v) (eqN_refl _)
  have hdl : h.dl.wt Aw < hsymm.wt Aw := by simp only [CvP.wt]; omega
  have hdr : h.dr.wt Aw < hsymm.wt Aw := by simp only [CvP.wt]; omega
  have hcL : canonL.wt Aw < hsymm.wt Aw := by
    have hpos := TyP.wt_pos Aw h.dl
    simp only [TyP.wt, CvP.wt]; omega
  have hcR : canonR.wt Aw < hsymm.wt Aw := by
    have hpos := TyP.wt_pos Aw h.dr
    simp only [TyP.wt, CvP.wt]; omega
  have hL := cl_under Aw tbl hsymm ht Bel h.dl canonL σ ρ hρ hdl hcL
  have hR := cl_under Aw tbl hsymm ht Bel h.dr canonR σ ρ hρ hdr hcR
  exact eqN_of_cvp_sorts_es_cl hW h σ ρ hes hL hR

/-- Closed-context corollary of `eqN_of_cvp_sorts_below`: in `Γ = []` at
    `σ = id, ρ = []`, `ES tbl id [] h` and `Bel` yield `eqN u v`. -/
theorem eqN_of_cvp_sorts_below_nil (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {u v : Level} {T : Expr Nat}
    (h : CvP E n [] (.sort u) (.sort v) T)
    (hes : ES tbl id [] h)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.symm E n [] (.sort u) (.sort v) T h h.dr h.dl))) :
    eqN u v :=
  eqN_of_cvp_sorts_below Aw hW h id [] (.nil levelSub_id) hes Bel

/-- `Level.zero` and `Level.succ u` are never `eqN`-equivalent. -/
theorem not_eqN_zero_succ (u : Level) : ¬ eqN .zero (.succ u) := by
  intro h
  have hbit := levelIsZero_congr h
  exact Bool.noConfusion hbit

/-- No `CvP` between `sort 0` and `sort (succ u)` can satisfy `ES` and `Below`
    under any `TableWF` table. -/
theorem not_cvp_sort_zero_succ_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u : Level} {T : Expr Nat}
    (h : CvP E n Γ (.sort .zero) (.sort (.succ u)) T)
    (ρ : List Disp) (hρ : DispFor id E n Γ ρ)
    (hes : ES tbl id ρ h)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.symm E n Γ (.sort .zero) (.sort (.succ u)) T h h.dr h.dl))) :
    False :=
  not_eqN_zero_succ u (eqN_of_cvp_sorts_below Aw hW h id ρ hρ hes Bel)

end Rcic.Syn

#print axioms Rcic.Syn.atoms_cctx
#print axioms Rcic.Syn.lam_dr_body_cl
#print axioms Rcic.Syn.es_of_below_lam_got_both_drop
#print axioms Rcic.Syn.es_of_below_lam_got_both_keep
#print axioms Rcic.Syn.es_of_below_lam_got_both_keep_star
#print axioms Rcic.Syn.eps_pi_clause
#print axioms Rcic.Syn.pi_dl_clause
#print axioms Rcic.Syn.PiRead.isYes
#print axioms Rcic.Syn.piOfNode
#print axioms Rcic.Syn.piClauseOf
#print axioms Rcic.Syn.piOfNode_eps
#print axioms Rcic.Syn.pushPiWk
#print axioms Rcic.Syn.pushPiLinst
#print axioms Rcic.Syn.pushPiEsub
#print axioms Rcic.Syn.readPi
#print axioms Rcic.Syn.readPi_pi_yes
#print axioms Rcic.Syn.pi_dr_dom_bitCoh
#print axioms Rcic.Syn.pi_dr_dom_cl
#print axioms Rcic.Syn.pi_dr_cod_cl
#print axioms Rcic.Syn.es_of_below_pi_got
#print axioms Rcic.Syn.es_of_below_pi_got_drop
#print axioms Rcic.Syn.es_of_below_pi_got_keep
#print axioms Rcic.Syn.eqN_of_cvp_sorts_es_cl
#print axioms Rcic.Syn.eqN_of_cvp_sorts_es_cl_id
#print axioms Rcic.Syn.eqN_of_cvp_sorts_below
#print axioms Rcic.Syn.eqN_of_cvp_sorts_below_nil
#print axioms Rcic.Syn.not_eqN_zero_succ
#print axioms Rcic.Syn.not_cvp_sort_zero_succ_of_below
