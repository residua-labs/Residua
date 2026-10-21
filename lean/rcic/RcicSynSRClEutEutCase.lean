import rcic.RcicSynTableOfIFull
import rcic.RcicSynCensusCorePortRefutations
import rcic.RcicSynDispForPathPins

/-!
# RcicSynSRClEutEutCase — sortRow row 15 (`eut_case`) at `tableOfI hW`

Deliverable (lane glm-sr3): the row is REFUTED at its raw `lamP` supply — a
kernel-checked refutation of the missing lemma `eutLamP_tableOfI` (the
`es_eut_field` `lamP` premise at `tbl := tableOfI hW`), with every input of
the refuted instance a closed inhabited term, plus the exact restated wall
`eut_case_wall` as ONE named Prop.

## Why the raw supply is false

`EutLamPorts`'s two sort-typings quantify over INDEPENDENT subjects `B₁ B₂`
(the raw port never sees the common `body` that the `.eut` lam-lam cell
binds), and its `convB` demands `ConvMod` between their erasures. At the
closed fixtures `hs0s : .sort 0 : sort 1` / `hs1s : .sort 1 : sort 2`
(`RcicSynDispForPathPins`) with `σ := id`, `ρ := []`, `u₁ := two`, `convB`
is `ConvMod (EStep tbl) LvlEq (.sort 0) (.sort 1)` — false at every
`TableWF` table (`eutLamPorts_sort_zero_one_refuted`), and
`tableWF_tableOfI_full` makes `tableOfI hW` a `TableWF` table for every
admitted env. The raw `lamP` premise is therefore uninhabited at
`tableOfI hW`: `es_eut_field` cannot be supplied there, so row 15's
`EutField` cannot come from this closer. The cell-demanded shape (common
body) is restated as `eut_case_wall` and retained — it is inhabited at
identical instances (`eut_case_wall_ident_sat`) and is not claimed beyond
that. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins (two hs0s hs1s)

variable {E : ResolvedEnv}

/-- The row-15 missing lemma, exact: the `es_eut_field` `lamP` premise shape
    at `tbl := tableOfI hW`. Refuted below at the `emptyEnv` witness. -/
def eutLamP_tableOfI (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B₁ B₂ : Expr Nat}
    {u₁ v₁ v₂ : Level}
    (hB₁ : TyP E' n (.assumption A :: Γ) B₁ (.sort v₁))
    (hB₂ : TyP E' n (.assumption A :: Γ) B₂ (.sort v₂))
    {σ : Level → Level} {ρ : List Disp},
    EutLamPorts (tableOfI hW) σ ρ u₁ hB₁ hB₂

/-- The refuted instance: `hs0s`/`hs1s`/`two` are closed terms and
    `id`/`[]` closed — every input inhabited. -/
theorem eutLamPorts_tableOfI_empty_refuted (hW : EnvWfT emptyEnv) :
    ¬ EutLamPorts (tableOfI hW) id [] two hs0s hs1s :=
  CensusCorePortRefutations.eutLamPorts_sort_zero_one_refuted
    (tableWF_tableOfI_full hW)

/-- **Row 15 verdict: the missing lemma `eutLamP_tableOfI` is FALSE** (at the
    inhabited `emptyEnv` witness; all inputs closed terms). -/
theorem eutLamP_tableOfI_empty_refuted : ¬ eutLamP_tableOfI EnvWfT.empty :=
  fun h => eutLamPorts_tableOfI_empty_refuted EnvWfT.empty (h hs0s hs1s)

/-- Row 15's exact restated wall, ONE Prop: `lamP` restricted to the `.eut`
    lam-lam cell's own data — the common-body typings the closer
    `eut_lam_lam_caseStep_of_ports` actually binds. Retained (not claimed,
    not refuted); its conclusion is inhabited at identical instances
    (`eut_case_wall_ident_sat`). -/
def eut_case_wall (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E' n Γ A (.sort u₁))
    (hb₁ : TyP E' n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E' n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E' n Γ A (.sort u₂))
    (hb₂ : TyP E' n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E' n (.assumption A :: Γ) B₂ (.sort v₂))
    {σ : Level → Level} {ρ : List Disp},
    EutLamPorts (tableOfI hW) σ ρ u₁ hB₁ hB₂

/-- The restated wall is not vacuously false: at an identical cell instance
    its conclusion is inhabited — `hTC` from `tableWF_tableOfI_full`,
    `convB` reflexive. -/
theorem eut_case_wall_ident_sat (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body B₁ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E' n Γ A (.sort u₁))
    (hb : TyP E' n (.assumption A :: Γ) body B₁)
    (hB : TyP E' n (.assumption A :: Γ) B₁ (.sort v₁))
    {σ : Level → Level} {ρ : List Disp} :
    EutLamPorts (tableOfI hW) σ ρ u₁ hB hB :=
  ⟨(tableWF_tableOfI_full hW).closed, ConvMod.refl _⟩

#print axioms eutLamPorts_tableOfI_empty_refuted
#print axioms eutLamP_tableOfI_empty_refuted
#print axioms eut_case_wall_ident_sat

end Rcic.Syn
