import rcic.RcicSynTableOfIFull

/-!
# RcicSynSRFsub — sortRow closure, row 13 (`es_fsub`)

Row 13's table wall (`tableWFI_build`, i.e. `TableWF (tableOfI hW)` and hence
`TableClosed`) is discharged by `tableWF_tableOfI_full` (#7771, merged here via
`origin/devin/swe-tableicompat` while in flight).

## The restated wall (exactly the closer's need)

The landed closer `es_fsub_field_closed` retains precisely two ports:

    hL : CL tbl σ ρ dl (instEnd hB hab.dl hA)
    hR : CL tbl σ ρ (instEnd hB hab.dr hA) dr

`FsubInstEndCl` restates them as ONE named Prop at the field's own data, and
`es_fsub_tableI_of_fsubInstEndCl` pins the field at `tableOfI hW` under
exactly that wall — `TableClosed` discharged by
`tableWF_tableOfI_full.closed`, nothing else retained.

## Status of the refutation (withdrawn)

An earlier version of this module refuted the ports at an *arbitrary*
`σ : Level → Level`.  That instance is not one the closer feeds: every
`Demand` carries `hσ : LevelHom σ` (root/rootEs/… constructors all take it,
`Demand.hom` preserves it), so `StepSuppliers.es_fsub` owes `hL`/`hR` only at
`LevelHom` σ.  At `LevelHom σ`, `levelIsZero (σ u) = levelIsZero u` (σ
distributes over every `Level` constructor), and `TyP.bvar`'s stored
annotation is `eqN`-pinned to its target's sort level — `eqN`-equal levels
share `levelIsZero`, so the eps branch is semantic, not loose.  The esub
drop-arm (`D.eps σ (insertDisp .drop j ρ)`) is substitution-correct by
construction.  The unconditional-∀ refutation was therefore withdrawn:
the wall stands **open at `LevelHom σ`**, restated exactly as
`FsubInstEndCl`.

`closure_claim = 0`.  No `sorry`, axioms ⊆ `{propext, Quot.sound}`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat)

/-- **The exact restated wall** for `es_fsub`: the two `instEnd` composite
    `CL` ports at the field's own data, as ONE named Prop.  Consumed only at
    `Demand` σ's (always `LevelHom σ`); open, not refuted — see the module
    doc for why the over-general-σ refutation was withdrawn. -/
def FsubInstEndCl (tbl : List CRule) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (σ : Level → Level) (ρ : List Disp) : Prop :=
  CL tbl σ ρ dl (instEnd hB hab.dl hA) ∧ CL tbl σ ρ (instEnd hB hab.dr hA) dr

/-- `es_fsub` at `tableOfI hW` under exactly `FsubInstEndCl`: `TableClosed`
    is discharged by `tableWF_tableOfI_full.closed`; nothing else remains. -/
theorem es_fsub_tableI_of_fsubInstEndCl
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {A B Sx a b : Expr Nat} {u : Level}
    (hW : EnvWfT E)
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hcl : FsubInstEndCl (tableOfI hW) hB hA hab dl dr σ ρ) :
    CaseStep Aw (tableOfI hW)
      (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ) :=
  es_fsub_field_closed Aw (tableOfI hW) hB hA hab dl dr S σ ρ
    (tableWF_tableOfI_full hW) hcl.1 hcl.2

#print axioms Rcic.Syn.FsubInstEndCl
#print axioms Rcic.Syn.es_fsub_tableI_of_fsubInstEndCl
