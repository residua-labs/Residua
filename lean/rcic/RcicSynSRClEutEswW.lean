import rcic.RcicSynSRBetaZetaEpsW
import rcic.RcicSynSameRankDep

/-!
# RcicSynSRClEutEswW — rows 14/15/17 under the `epsW` erasure, the frame

cc 2026-10-20 20:00Z brief, lane glm-sr3 (branch glm/sr3-esw, from
origin/glm/sr1-epsw2): re-measure sortRow rows 14 (`cl_case`), 15
(`eut_case`, the lamP gated supply) and 17 (`mixed_case`) under the epsW
erasure, LevelHom-gated exactly as in #7800 — the `LevelHom σ` every
demanded query carries (`Demand.hom`), which is what `step_of_suppliers`
consumes. `closure_claim = 0`.

The gated W-field shapes below are #7800's `GatedClCase`/`GatedEutCase`
Goal halves with `CL`/`EUT` restated at the display-aware erasure
(`CLW` from `RcicSynSRBetaZetaEpsW`; `EUTW` here): the `Demand`/`StepIH`
resources talk about the query tree, not the erasure, so the measurement
isolates exactly the Goal half. The `.mixed` arm is the pair, as landed.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `EUT` restated with the display-aware erasure: the two regularity
    type-erasures are computed by `epsW`. -/
def EUTW (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T T' : Expr Nat}
    (D₁ : TyP E n Γ e T) (D₂ : TyP E n Γ e T') : Prop :=
  ConvMod (EStep tbl) LvlEq (D₁.reg.2.epsW σ ρ) (D₂.reg.2.epsW σ ρ)

/-- The gated `cl_case` W-field: #7800's `GatedClCase` with the `.cl` Goal
    restated at `CLW` (`Demand`/`StepIH` verbatim). -/
def GatedClCaseW (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp), CLW tbl σ ρ D₁ D₂

/-- The gated `eut_case` W-field, same restatement at `EUTW`. -/
def GatedEutCaseW (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp), EUTW tbl σ ρ D₁ D₂

/-- The gated `mixed_case` W-field: the `.mixed` Goal is the pair, as
    landed. -/
def GatedMixedCaseW (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp), CLW tbl σ ρ D₁ D₂ ∧ EUTW tbl σ ρ D₁ D₂

/-- Row 17 under epsW: the `mixed_case` W-field from the `cl_case` and
    `eut_case` W-fields — pointwise the pair (the `.mixed` Goal is the
    conjunction), mirroring `mixedField_of_cl_eut`; no new wall. -/
theorem mixedFieldW_of_clW_eutW (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (hcl : GatedClCaseW Aw tbl Eₐ) (heut : GatedEutCaseW Aw tbl Eₐ) :
    GatedMixedCaseW Aw tbl Eₐ := by
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ hσ ρ
  exact ⟨hcl D₁ D₂ S σ hσ ρ, heut D₁ D₂ S σ hσ ρ⟩

/-- Row 17 under epsW, converse: a full-pair W-`mixed_case` field is
    exactly the two parent W-fields. -/
theorem gatedMixedW_iff (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) :
    GatedMixedCaseW Aw tbl Eₐ ↔
      GatedClCaseW Aw tbl Eₐ ∧ GatedEutCaseW Aw tbl Eₐ := by
  refine ⟨fun hmix => ⟨?_, ?_⟩, fun h => mixedFieldW_of_clW_eutW Aw tbl h.1 h.2⟩
  · intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ hσ ρ
    exact (@hmix E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ hσ ρ).1
  · intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ hσ ρ
    exact (@hmix E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ hσ ρ).2

#print axioms EUTW
#print axioms mixedFieldW_of_clW_eutW
#print axioms gatedMixedW_iff

end Rcic.Syn
