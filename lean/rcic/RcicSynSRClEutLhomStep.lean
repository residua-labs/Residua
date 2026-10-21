import rcic.RcicSynStepSkeleton

/-!
# RcicSynSRClEutLhomStep — the SIGMA GAP, consumer side (closure_claim = 0)

The census ports of the `cl_case`/`eut_case`/`pb_case` closers quantify over
ARBITRARY `σ : Level → Level`, but the consumer of those fields — the
`step_of_suppliers` dispatch — only ever applies them WITH the demand proof
in hand, and `Demand.hom` certifies `LevelHom σ` for every demanded query
(rows 14/15/16 of `TABLEOFI_SUPPLIER_CENSUS.md`; #7781/#7788/#7789).

This module makes that kernel implication mechanical, per tag: a GATED field
(the landed `StepSuppliers` field conclusion restricted to `LevelHom σ`)
patches a landed `StepSuppliers` record via `{W with …}` at exactly the
application sites (`RcicSynStepSkeleton.lean:915/916/918`, plus the
`.bitCoh`-issued `.eut` at `:923`), because `hq.hom` supplies the gate from
the demand the dispatch already carries. No landed statement is edited; the
gated shapes are new names.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The gated `cl_case` field shape: the landed `StepSuppliers.cl_case`
    conclusion restricted to the `LevelHom σ` every demanded `.cl` query
    carries (`Demand.hom`). -/
def GatedClCase (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp), CaseStep Aw tbl (.cl D₁ D₂ S σ ρ)

/-- The gated `eut_case` field shape, same restriction. -/
def GatedEutCase (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp), CaseStep Aw tbl (.eut D₁ D₂ S σ ρ)

/-- The gated `pb_case` field shape, same restriction. -/
def GatedPbCase (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {s : Level} (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (hσ : LevelHom σ)
    (ρ : List Disp), CaseStep Aw tbl (.pb D DT S σ ρ)

/-- A gated `cl_case` field suffices at the landed consumption site: the
    dispatch applies the field with the demand proof, and `Demand.hom` is the
    gate. `{W with …}` leaves every other field untouched. -/
theorem stepSuppliers_cl_of_gated {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (W : StepSuppliers Aw tbl Eₐ) (gated : GatedClCase Aw tbl Eₐ) :
    StepSuppliers Aw tbl Eₐ := by
  refine { W with cl_case := ?_ }
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ ρ hq ih
  exact gated D₁ D₂ S σ hq.hom ρ hq ih

/-- A gated `eut_case` field suffices at the landed consumption site
    (including the `.bitCoh`-issued `.eut` application, whose constructed
    demand proof also carries `Demand.hom`). -/
theorem stepSuppliers_eut_of_gated {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (W : StepSuppliers Aw tbl Eₐ) (gated : GatedEutCase Aw tbl Eₐ) :
    StepSuppliers Aw tbl Eₐ := by
  refine { W with eut_case := ?_ }
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ ρ hq ih
  exact gated D₁ D₂ S σ hq.hom ρ hq ih

/-- A gated `pb_case` field suffices at the landed consumption site. -/
theorem stepSuppliers_pb_of_gated {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (W : StepSuppliers Aw tbl Eₐ) (gated : GatedPbCase Aw tbl Eₐ) :
    StepSuppliers Aw tbl Eₐ := by
  refine { W with pb_case := ?_ }
  intro E₀ n₀ Γ₀ E n Γ e T s D DT S σ ρ hq ih
  exact gated D DT S σ hq.hom ρ hq ih

/-- Consumer-side kernel implication, composed: a gated `cl` field plus a
    landed `W` for everything else yields the full `Step`. -/
theorem step_of_suppliers_cl_gated {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ) (gated : GatedClCase Aw tbl Eₐ) :
    Step Aw tbl Eₐ :=
  step_of_suppliers Aw tbl hTbl (stepSuppliers_cl_of_gated Aw tbl W gated)

/-- Consumer-side kernel implication, composed, `eut` field. -/
theorem step_of_suppliers_eut_gated {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ) (gated : GatedEutCase Aw tbl Eₐ) :
    Step Aw tbl Eₐ :=
  step_of_suppliers Aw tbl hTbl (stepSuppliers_eut_of_gated Aw tbl W gated)

/-- Consumer-side kernel implication, composed, `pb` field. -/
theorem step_of_suppliers_pb_gated {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ) (gated : GatedPbCase Aw tbl Eₐ) :
    Step Aw tbl Eₐ :=
  step_of_suppliers Aw tbl hTbl (stepSuppliers_pb_of_gated Aw tbl W gated)

#print axioms GatedClCase
#print axioms GatedEutCase
#print axioms GatedPbCase
#print axioms stepSuppliers_cl_of_gated
#print axioms stepSuppliers_eut_of_gated
#print axioms stepSuppliers_pb_of_gated
#print axioms step_of_suppliers_cl_gated
#print axioms step_of_suppliers_eut_gated
#print axioms step_of_suppliers_pb_gated

end Rcic.Syn
