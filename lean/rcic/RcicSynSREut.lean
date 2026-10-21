import rcic.RcicSynTableOfIFull
import rcic.RcicSynClosedCleut

/-!
# RcicSynSREut — sortRow row 15 (`eut_case`) at `tableOfI hW`

Deliverable (lane devin-sr-eut): the row is REFUTED at its raw `piP` supply —
a kernel-checked refutation of `eutPiP_tableOfI` (the `es_eut_field` `piP`
premise at `tbl := tableOfI hW`), every input of the refuted instance a
closed inhabited term; plus the exact restated wall `eutPiP_wall` as ONE
named Prop, and the named residual wall `eutResidualWall` (the census's
`eut_residualTag_caseStep`) with its diagonal non-vacuity witness.

## Why the raw supply is false

`EutPiPorts.cohB` owes `SortCoh σ hB₁ hB₂ = eqN (σ v₁) (σ v₂)` for the
ARBITRARY `σ` the raw port quantifies — the demanded-cell `LevelHom σ`
(`P2Query.hom`) exists only inside a `CaseStep`; the port signature itself
never restricts `σ`. The closed fixture `sreuthB₁`/`sreuthB₂` types one
subject `sreutB = sort (max 0 0)` at `v₁ = succ (max 0 0)` vs `v₂ = succ 0` —
equal under every valuation, syntactically distinct — and the closed
match-map `sreutσ` sends `v₁ ↦ succ 0` and `v₂ ↦ zero`, making `cohB` the
false `eqN 1 0`. (Sibling lane glm-sr3 refuted `lamP` at the same σ-gap in
`RcicSynSRClEutEutCase`.)

## The retained walls

`eutPiP_wall` restricts `piP` by `LevelHom σ` — the constraint every
demanded query actually carries; under it `cohB` reduces to `eqN v₁ v₂`, the
sortRow uniqueness content itself. `eutResidualWall` is `eutOther`'s exact
shape at `tableOfI` (transport-headed non-`.conv` cells): `StepIH` cannot
reach the peeled inners (they live at shifted contexts/`ρ`), so it stays
open; `eutResidualWall_diag_sat` shows the diagonal inhabited.
`eut_appPorts_of_casted` (the `appP` existential, `EutAppPorts`) remains
retained — `PiGen` extraction hits `readPi`'s `lsub`/`cctx` hole and the
`instEnd`/`piL` bridges sit off the payload grid. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv} {Eₐ : ResolvedEnv}

/-- The distinguishing map `1 ↦ 0`, everything else `↦ 1` (closed, no
    homomorphism content — the point of the refutation). -/
def sreutσ : Level → Level := fun l => match l with
  | .succ .zero => .zero
  | _ => .succ .zero

/-- The shared assumption type of the fixture context. -/
def sreutA : Expr Nat := .sort .zero

/-- The shared codomain subject: `sort (max 0 0)` — a Prop, `eqN`-equal to
    `sort 0` but syntactically distinct. -/
def sreutB : Expr Nat := .sort (.max .zero .zero)

/-- `sreutA : sort 1` in the empty context (closed). -/
def sreuthA : TyP emptyEnv 0 [] sreutA (.sort (.succ .zero)) :=
  TyP.sort _ _ _ _ _ (eqN_refl _)

/-- `sreutB : sort (succ (max 0 0))` — `v₁` is `succ (max 0 0)`, sent to `1`
    by `sreutσ`. -/
def sreuthB₁ : TyP emptyEnv 0 [.assumption sreutA] sreutB
    (.sort (.succ (.max .zero .zero))) :=
  TyP.sort _ _ _ _ _ (eqN_refl _)

/-- `sreutB : sort 1` — `v₂` is `succ 0`, sent to `0` by `sreutσ`. -/
def sreuthB₂ : TyP emptyEnv 0 [.assumption sreutA] sreutB (.sort (.succ .zero)) :=
  TyP.sort _ _ _ _ _ (fun _ => rfl)

/-- `sreutσ` splits the two `v`'s: `eqN 1 0` is false. -/
theorem sreutσ_split : ¬ eqN (sreutσ (.succ (.max .zero .zero)))
    (sreutσ (.succ .zero)) := by
  intro h
  have e := h (fun _ => some 0)
  revert e; decide

/-- The refuted instance: `sreuthA`/`sreuthB₁`/`sreuthB₂` are closed terms
    and `sreutσ`/`[]` closed — every input inhabited. -/
theorem eutPiPorts_tableOfI_empty_refuted (hW : EnvWfT emptyEnv) :
    ¬ EutPiPorts (tableOfI hW) sreutσ [] sreuthA sreuthB₁ sreuthA sreuthB₂ :=
  fun p => sreutσ_split p.cohB

/-- The `piP` premise shape of `es_eut_field` at `tbl := tableOfI hW` —
    refuted below at the `emptyEnv` witness. -/
def eutPiP_tableOfI (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    {u₁ u₂ v₁ v₂ : Level}
    (hA₁ : TyP E' n Γ A (.sort u₁))
    (hB₁ : TyP E' n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E' n Γ A (.sort u₂))
    (hB₂ : TyP E' n (.assumption A :: Γ) B (.sort v₂))
    {σ : Level → Level} {ρ : List Disp},
    EutPiPorts (tableOfI hW) σ ρ hA₁ hB₁ hA₂ hB₂

/-- **Row 15 verdict: the `piP` supply is FALSE** at `tableOfI` — `es_eut_field`
    cannot be supplied there, so `EutField` cannot come from this closer. -/
theorem eutPiP_tableOfI_empty_refuted : ¬ eutPiP_tableOfI EnvWfT.empty :=
  fun h => eutPiPorts_tableOfI_empty_refuted EnvWfT.empty
    (h sreuthA sreuthB₁ sreuthA sreuthB₂)

/-- **The restated wall, ONE named Prop**: `piP` at `tableOfI` gated by the
    `LevelHom σ` every demanded `.eut` cell carries. Under `LevelHom`, `cohB`
    is `eqN v₁ v₂`-transported — the sortRow uniqueness content. Retained
    (not claimed); inhabited at identical instances (`eutPiP_wall_ident_sat`). -/
def eutPiP_wall (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    {u₁ u₂ v₁ v₂ : Level}
    (hA₁ : TyP E' n Γ A (.sort u₁))
    (hB₁ : TyP E' n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E' n Γ A (.sort u₂))
    (hB₂ : TyP E' n (.assumption A :: Γ) B (.sort v₂))
    {σ : Level → Level} {ρ : List Disp}, LevelHom σ →
    EutPiPorts (tableOfI hW) σ ρ hA₁ hB₁ hA₂ hB₂

/-- The restated wall is not vacuously false: at an identical cell instance
    its conclusion is inhabited — `hW` from `tableWF_tableOfI_full`, the
    `edgeL`/`edgeR` antecedents false on the sort-headed `sreuthA`, `cohB`
    reflexive. -/
theorem eutPiP_wall_ident_sat (hW : EnvWfT emptyEnv) (σ : Level → Level)
    (ρ : List Disp) :
    EutPiPorts (tableOfI hW) σ ρ sreuthA sreuthB₁ sreuthA sreuthB₁ := by
  refine ⟨tableWF_tableOfI_full hW, fun h => ?_, fun h => ?_, eqN_refl _⟩ <;>
    exact absurd h (by decide)

/-- The residual wall: `eutOther`'s exact shape at `tbl := tableOfI hW` —
    the census's `eut_residualTag_caseStep` (transport-headed non-`.conv`
    cells; `StepIH` cannot reach the peeled cross-context inners). Retained;
    the diagonal is inhabited (`eutResidualWall_diag_sat`). -/
def eutResidualWall (Aw : Nat → Nat) (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ Γ₁ Γ₂ : LCtx} {e e₁ e₂ T₁ T₂ : Expr Nat}
    {E₀' : ResolvedEnv} {n₀' : Nat} {Γ₀' : LCtx}
    (D₁ : TyP E' n Γ₁ e₁ T₁) (D₂ : TyP E' n Γ₂ e₂ T₂)
    (hΓ₁ : Γ₁ = Γ) (he₁ : e₁ = e) (hΓ₂ : Γ₂ = Γ) (he₂ : e₂ = e)
    (S : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ : Level → Level) (ρ : List Disp),
    eutResidualTag D₁.headTag D₂.headTag = true →
    CaseStep Aw (tableOfI hW)
      (.eut (hΓ₁ ▸ he₁ ▸ D₁) (hΓ₂ ▸ he₂ ▸ D₂) S σ ρ)

/-- The residual wall's conclusion is inhabited on the `wk`/`wk` diagonal —
    `eut_residual_cell_sat` at `tbl := tableOfI hW`, with
    `eut_residual_tag_wk` certifying the pair is residual. -/
theorem eutResidualWall_diag_sat (Aw : Nat → Nat) (hW : EnvWfT E)
    {E₀ : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (d : LocalDecl) (c : Nat)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw (tableOfI hW)
      (.eut (TyP.wk _ _ _ _ _ d c D) (TyP.wk _ _ _ _ _ d c D) S σ ρ) :=
  eut_residual_cell_sat Aw (tableOfI hW) D d c S σ ρ

#print axioms sreutσ_split
#print axioms eutPiPorts_tableOfI_empty_refuted
#print axioms eutPiP_tableOfI_empty_refuted
#print axioms eutPiP_wall_ident_sat
#print axioms eutResidualWall_diag_sat

end Rcic.Syn
