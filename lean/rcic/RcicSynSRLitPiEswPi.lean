import rcic.RcicSynSRLitPiEswLit
import rcic.RcicSynSRLitPiPi

/-!
# `RcicSynSRLitPiEswPi` — row 10 (`es_pi`) under epsW + `LevelHom`

cc 2026-10-20 20:00Z re-measure. Verdict: **OPEN** — the landed cutoff
tooth is dead on-cone; the gated ESW field obligation is restated as ONE
named Prop.

* The landed `pi_leftSurface_cl` refutation's `sr2_σ2` is not a `LevelHom`
  (`sr2_σ2_not_hom`); at every hom the tooth pair co-erases under `epsW`
  (`pi_tooth_pair_clw_hom`) — `levelIsZero_congr_hom` kills the
  `.max 2 0`-vs-`.succ (.succ .zero)` cutoff slack exactly as at row 7.
* The gated field obligation (`piW_field_wall`): the `CaseStepW` statement
  of the `es_pi` row at `tableOfI` — `Demand` supplies the `LevelHom`.
  Supply route: the pi arm's own bit is eqN-dead at homs; the remaining
  content is the domain/codomain legs (`pi_leftSurface_cl`,
  `pi_rightSurface_cl`, `occHA`/`occHR` restated under `CLW`).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the landed tooth is off-cone, and dead at every hom -/

/-- The landed refutation's `sr2_σ2` is not a `LevelHom`: it zeroes
    `.succ (.succ .zero)` while fixing `.succ .zero`, breaking `map_succ`
    at `.succ .zero`. -/
theorem sr2_σ2_not_hom : ¬ LevelHom sr2_σ2 := by
  intro hσ
  have h1 := hσ.map_succ (.succ .zero)
  have e1 : sr2_σ2 (.succ (.succ .zero)) = .zero := by rfl
  have e2 : sr2_σ2 (.succ .zero) = .succ .zero := by rfl
  rw [e1, e2] at h1
  exact Level.noConfusion h1

#print axioms Rcic.Syn.sr2_σ2_not_hom

/-! ## §2 at every hom the landed pi pair co-erases -/

/-- At any `LevelHom σ`, the tooth's stored cutoff `.max 2 0` keeps the
    false bit — `max_bit` + `succ_bit` + `zero_bit`. -/
theorem pi_tooth_bit_hom {σ : Level → Level} (hσ : LevelHom σ) :
    levelIsZero (σ (.max (.succ (.succ .zero)) .zero)) = false := by
  rw [hσ.max_bit, hσ.succ_bit (.succ .zero), hσ.zero_bit]
  rfl

/-- The landed `pi_leftSurface_cl` fixture pair co-erases at every hom
    under `epsW`: both pi arms take the same branch, and the two cutoffs
    keep the same bit by `levelIsZero_congr_hom`'s bit lemmas. -/
theorem pi_tooth_pair_clw_hom {σ : Level → Level} (hσ : LevelHom σ) :
    CLW (tableOfI natEnvUWfT) σ [] sr2_piTooth (piLeftSurface sr2_piA sr2_piB) := by
  have b2 : levelIsZero (σ (.succ (.succ .zero))) = false := hσ.succ_bit (.succ .zero)
  have bmax := pi_tooth_bit_hom hσ
  have b1 : levelIsZero (σ (.succ .zero)) = false := hσ.succ_bit .zero
  unfold CLW
  simp only [sr2_piTooth, piLeftSurface, sr2_piA, sr2_piB, CvP.dl, TyP.epsW,
    sr2_famMaxC, TyP.epsW, bmax, sr2_famTy, TyP.epsW, b2, b1]
  exact ConvMod.refl _

#print axioms Rcic.Syn.pi_tooth_bit_hom
#print axioms Rcic.Syn.pi_tooth_pair_clw_hom

/-! ## §3 the row-10 gated field wall, ONE Prop -/

/-- Row 10 under epsW + `LevelHom`: the gated `CaseStepW` obligation of
    the `es_pi` field at `tableOfI` — `Demand` supplies the hom. The
    pi arm's own bit is eqN-dead at homs; the remaining content is the
    domain/codomain legs (`pi_leftSurface_cl` / `pi_rightSurface_cl` /
    `occHA` / `occHR`, restated under `CLW`). -/
def piW_field_wall : Prop :=
  ∀ {E : ResolvedEnv} (hW : EnvWfT E) (Aw : Nat → Nat) {E₀ : ResolvedEnv}
    {n₀ : Nat} {Γ₀ : LCtx} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat}
    {u v : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx E₀ E n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw (tableOfI hW)
      (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ)

#print axioms Rcic.Syn.piW_field_wall

end Rcic.Syn
