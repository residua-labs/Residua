import rcic.RcicSynES
import rcic.RcicSynBelow
import rcic.RcicSynZetaMeasureRefute

/-!
`research/rcic/sortrow/S16_BVAR_CCTX_IOTA_STEPS.md` §3 and §4.2: the two
local `step` cases that compose completely.

§3 — `CvP.cctx` deferred body. The callee reads the child's `ES h` under
the same `σ`/`ρ` while the bridge `c` stays in the live occurrence table:
both sides carry `K ++ at(h) ++ at(c)` (`cctx_deferred_live_atoms`), and
the handled `cctx` wrapper is exactly one unit of weight
(`cctx_deferred_weight`), so the strict edge is `Prod.Lex.right`
(`cctx_deferred_edge`). `cctx_source_request_exact` records that the
body request's goal under the same `σ`,`ρ` is precisely the argument
`es_cctx` consumes — the source route never rebuilds `ρ`.
`es_cctx_deferred` is the composition. §3.4's counting control runs on
main's `cctxWallDomCv`: caller `[1,4,9]` weight 15, deferred `[1,4,9]`
weight 14; the optional fast path's gate is `[1,1]` and the
`dl`-resolved body is `[6,4]` (the source provider is heavier than the
target provider, not a fixed spine).

§4.2 — `CvP.iota` proof result. The two real requests are the PBs
`PBit σ ρ dl hlhs.reg.2` and `PBit σ ρ dr hlhs.reg.2` (`iota_qL_below`,
`iota_qR_below`), each paid by the original node `N` — the `reg.2` atom
bound composes `TyP.wt_reg_le` with `hlhs < N`, never a fresh admission.
`iota_proof_conv_of_pbits` / `es_iota_proof_of_pbits` take the two PBit
answers and `hu` as their only premises and finish by `pL.mpr hu`,
`pR.mpr hu`, `ConvMod.refl`: the whole `ES H` is never a hypothesis.

`closure_claim` stays `0`: this is the local dispatch of two cases; the
retained-result ι slots, the cctx fast-path gate answers, and every
`(b)` supplier remain the open residue.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `cctx` deferred body: identical atoms, weight minus one -/

section CctxDeferred

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T A A' : Expr Nat} {u : Level}

/-- The bridge stays in the live table: the caller's pending atoms over the
    `cctx` node ARE `K ++ at(h) ++ at(c)`, and the deferred callee reads the
    same list — nothing is deleted while descendants still read `c`. -/
theorem cctx_deferred_live_atoms (Aw : Nat → Nat) (K : List Nat)
    (h : CvP E n (.assumption A :: Γ) a b T) (c : CvP E n Γ A A' (.sort u)) :
    K ++ (CvP.cctx E n Γ a b T A A' u h c).atoms Aw =
      K ++ h.atoms Aw ++ c.atoms Aw := by
  simp only [CvP.atoms, List.append_assoc]

/-- The handled `cctx` wrapper costs exactly one unit: stripping it leaves
    `wK + h.wt + c.wt`, one less than the caller's `wK + H.wt`. -/
theorem cctx_deferred_weight (Aw : Nat → Nat) (wK : Nat)
    (h : CvP E n (.assumption A :: Γ) a b T) (c : CvP E n Γ A A' (.sort u)) :
    wK + h.wt Aw + c.wt Aw =
      wK + (CvP.cctx E n Γ a b T A A' u h c).wt Aw - 1 := by
  simp only [CvP.wt]; omega

/-- The strict edge of the deferred call: same occurrence list on both
    sides, the second component drops by the one handled wrapper. -/
theorem cctx_deferred_edge (Aw : Nat → Nat) (K : List Nat) (wK : Nat)
    (h : CvP E n (.assumption A :: Γ) a b T) (c : CvP E n Γ A A' (.sort u)) :
    LexDM (K ++ h.atoms Aw ++ c.atoms Aw, wK + h.wt Aw + c.wt Aw)
      (K ++ (CvP.cctx E n Γ a b T A A' u h c).atoms Aw,
        wK + (CvP.cctx E n Γ a b T A A' u h c).wt Aw) := by
  rw [cctx_deferred_live_atoms]
  refine Prod.Lex.right _ ?_
  simp only [CvP.wt]; omega

/-- The deferred body request keeps the caller's `σ` and `ρ`: its goal is
    literally `ES σ ρ h`, the exact premise `es_cctx` consumes. -/
theorem cctx_source_request_exact (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) (h : CvP E n (.assumption A :: Γ) a b T)
    (c : CvP E n Γ A A' (.sort u)) :
    ES tbl σ ρ (CvP.cctx E n Γ a b T A A' u h c) ↔ ES tbl σ ρ h :=
  ⟨fun x => x, es_cctx h c⟩

/-- §3.1–§3.2 composition: the body's semantic answer under the unchanged
    `σ`,`ρ` discharges `H` through main's `es_cctx` — no extra `ES c`, no
    source `CtxP`. -/
theorem es_cctx_deferred (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    (h : CvP E n (.assumption A :: Γ) a b T) (c : CvP E n Γ A A' (.sort u))
    (hBody : ES tbl σ ρ h) :
    ES tbl σ ρ (CvP.cctx E n Γ a b T A A' u h c) :=
  es_cctx h c hBody

end CctxDeferred

/-! ## §2 the §3.4 counting control on `cctxWallDomCv` -/

section CctxWallControl

variable (E : ResolvedEnv) (n : Nat) (Aw : Nat → Nat)

/-- The target-head provider: a plain `sort 0 : sort 1` typing, weight 1. -/
def s16Prov : TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort E n [] .zero (.succ .zero) (eqN_refl _)

/-- The bridge: main's `cctxWallDomCv`, `refl` with `dl` of weight 6 and
    `dr` of weight 1 — weight `1 + 1 + 6 + 1 = 9`. -/
def s16Bridge : CvP E n [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  cctxWallDomCv E n

/-- The body under the source binder: a direct `refl (sort 0)`, weight
    `1 + 1 + 1 + 1 = 4`. -/
def s16Body :
    CvP E n [.assumption (.sort .zero)] (.sort .zero) (.sort .zero)
      (.sort (.succ .zero)) :=
  let s01 := TyP.sort E n [.assumption (.sort .zero)] .zero (.succ .zero) (eqN_refl _)
  CvP.refl E n _ _ _ s01 s01 s01

/-- The caller's `cctx` node: weight `1 + 4 + 9 = 14`. -/
def s16H :
    CvP E n [.assumption (.sort .zero)] (.sort .zero) (.sort .zero)
      (.sort (.succ .zero)) :=
  CvP.cctx E n [] (.sort .zero) (.sort .zero) (.sort (.succ .zero))
    (.sort .zero) (.sort .zero) (.succ .zero) (s16Body E n) (s16Bridge E n)

theorem s16_prov_atoms : (s16Prov E n).atoms Aw = [1] := rfl

theorem s16_bridge_atoms : (s16Bridge E n).atoms Aw = [9] := rfl

theorem s16_bridge_dl_atoms : (s16Bridge E n).dl.atoms Aw = [6] := rfl

theorem s16_bridge_dr_atoms : (s16Bridge E n).dr.atoms Aw = [1] := rfl

theorem s16_body_atoms : (s16Body E n).atoms Aw = [4] := rfl

/-- Caller: live table `[1] ++ [4] ++ [9]`, weight `1 + 1 + 4 + 9 = 15`. -/
theorem s16_caller_atoms :
    (s16Prov E n).atoms Aw ++ (s16Body E n).atoms Aw ++
      (s16Bridge E n).atoms Aw = [1, 4, 9] := rfl

theorem s16_caller_weight :
    (s16Prov E n).wt Aw + (s16H E n).wt Aw = 15 := rfl

/-- Deferred callee: same atoms `[1,4,9]`, weight `1 + 4 + 9 = 14`. -/
theorem s16_deferred_atoms :
    (s16Prov E n).atoms Aw ++ (s16Body E n).atoms Aw ++
      (s16Bridge E n).atoms Aw = [1, 4, 9] := rfl

theorem s16_deferred_weight :
    (s16Prov E n).wt Aw + (s16Body E n).wt Aw + (s16Bridge E n).wt Aw = 14 := rfl

/-- The §3.4 caller-to-deferred edge instance: `([1,4,9],14) < ([1,4,9],15)`. -/
theorem s16_deferred_edge :
    LexDM ((s16Prov E n).atoms Aw ++ (s16Body E n).atoms Aw ++
        (s16Bridge E n).atoms Aw,
        (s16Prov E n).wt Aw + (s16Body E n).wt Aw + (s16Bridge E n).wt Aw)
      ((s16Prov E n).atoms Aw ++ (s16H E n).atoms Aw,
        (s16Prov E n).wt Aw + (s16H E n).wt Aw) :=
  cctx_deferred_edge Aw _ _ (s16Body E n) (s16Bridge E n)

/-- Fast-path gate `BitCoh σ J c.dr`: `at(J) ++ at(c.dr) = [1,1]`. -/
theorem s16_gate_atoms :
    (s16Prov E n).atoms Aw ++ (s16Bridge E n).dr.atoms Aw = [1, 1] := rfl

/-- Fast-path resolved source body: `at(c.dl) ++ at(h) = [6,4]` — the source
    provider outweighs the target provider, paid by replacing the 9. -/
theorem s16_source_body_atoms :
    (s16Bridge E n).dl.atoms Aw ++ (s16Body E n).atoms Aw = [6, 4] := rfl

end CctxWallControl

/-! ## §3 `iota` proof result: the two PBs -/

section IotaProof

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}

/-- `qL = PB[dl, hlhs.reg.2]` is paid by the original node: `dl` is a field
    and `hlhs.reg.2` is bounded by `hlhs` through `TyP.wt_reg_le`. -/
theorem iota_qL_below (Aw : Nat → Nat)
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T) (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T) :
    LexDM (tyPairMeas Aw dl hlhs.reg.2)
      (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr)) := by
  have hwl : dl.wt Aw < (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr).wt Aw := by
    simp only [CvP.wt]; omega
  have hwlhs : hlhs.wt Aw < (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr).wt Aw := by
    simp only [CvP.wt]; omega
  exact lex_of_dm (dmStep_pair_below Aw
    (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) rfl dl hlhs.reg.2 hwl
    (Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hlhs) hwlhs))

/-- `qR = PB[dr, hlhs.reg.2]` under the same original node and bound. -/
theorem iota_qR_below (Aw : Nat → Nat)
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T) (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T) :
    LexDM (tyPairMeas Aw dr hlhs.reg.2)
      (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr)) := by
  have hwr : dr.wt Aw < (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr).wt Aw := by
    simp only [CvP.wt]; omega
  have hwlhs : hlhs.wt Aw < (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr).wt Aw := by
    simp only [CvP.wt]; omega
  exact lex_of_dm (dmStep_pair_below Aw
    (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) rfl dr hlhs.reg.2 hwr
    (Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hlhs) hwlhs))

/-- The §4.2 composition: with the actual `hu`, the two PBit answers alone
    give `ConvMod` of the stored endpoints' erasures. The whole `ES H` is
    never a premise. -/
theorem iota_proof_conv_of_pbits (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) (hlhs : TyP E n Γ lhs T) (dl : TyP E n Γ lhs T)
    (dr : TyP E n Γ rhs T) (hu : levelIsZero (σ hlhs.reg.1) = true)
    (pL : PBit σ ρ dl hlhs.reg.2) (pR : PBit σ ρ dr hlhs.reg.2) :
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ) := by
  have hL := pL.mpr hu
  have hR := pR.mpr hu
  rw [hL, hR]
  exact .refl _

/-- The same two answers discharge `ES` of the `iota` node, mirroring
    `es_of_below_iota_proof` with `Bel.pb` replaced by the explicit PBits. -/
theorem es_iota_proof_of_pbits (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T) (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (hu : levelIsZero (σ hlhs.reg.1) = true)
    (pL : PBit σ ρ dl hlhs.reg.2) (pR : PBit σ ρ dr hlhs.reg.2) :
    ES tbl σ ρ (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) :=
  iota_proof_conv_of_pbits tbl σ ρ hlhs dl dr hu pL pR

end IotaProof

end Rcic.Syn
