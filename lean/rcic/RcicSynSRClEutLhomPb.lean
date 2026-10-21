import rcic.RcicSynStepPbCase
import rcic.RcicSynSortPBit
import rcic.RcicSynSRClEutLhomStep
import rcic.RcicSynSRPbDeltaHead

/-!
# RcicSynSRClEutLhomPb — the SIGMA GAP on row 16 (`pb_case`)

The landed closer `pb_case Aw tbl (head : PbHead D DT σ ρ)` and #7789's wall
`sr4PbHeadWall` / goal supply `sr4PbGoalSupply` quantify over ARBITRARY
`σ : Level → Level`; the consumer only instantiates `LevelHom σ`
(`Demand.hom`, patched in `RcicSynSRClEutLhomStep`). Restatements here
(new names; #7789's landed statements are untouched):

* `pb_case_lhom` — the gated closer: a `Nonempty (PbHead D DT σ ρ)` supply
  at `LevelHom σ` yields the gated `pb_case` field (`Nonempty.elim` into
  the `CaseStep` Prop — no choice).
* `pbHeadLhomWall` — row 16's gated wall. NOT refuted at the gate:
  #7789's refuting σ `fun _ => Level.zero` is not a `LevelHom` (it breaks
  `map_succ`). At a `LevelHom` the same mechanism needs the RIGHT side of
  `PBit` true — `levelIsZero (σ s) = true` — which forces a `.sort
  .zero`-bit type level `s`; bottoming that out requires the SortUnique
  conversion chain (`.sort .zero`-typed leaves), i.e. content this row
  cannot assume. That is the open measurement direction at the gate.
* `pbGoalSupplyLhom` — the gated goal-level supply, with an
  identical-instance tooth (`pbGoalSupplyLhom_ident_sat`, both sides of the
  `PBit` iff definitionally false at the #7789 pins).
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv} {Eₐ : ResolvedEnv}

/-- **`pb_case` gated**: the landed closer under a `Nonempty (PbHead …)`
    supply restricted to `LevelHom σ`, concluding the gated field shape
    `GatedPbCase`. -/
theorem pb_case_lhom (Aw : Nat → Nat) (tbl : List CRule)
    (supply : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
      {s : Level} (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
      (σ : Level → Level) (ρ : List Disp),
      LevelHom σ → Nonempty (PbHead D DT σ ρ)) :
    GatedPbCase Aw tbl Eₐ :=
  fun D DT S σ hσ ρ => (supply D DT σ ρ hσ).elim (fun head => pb_case Aw tbl head)

/-- Row 16's gated wall, ONE named Prop: the #7789 `sr4PbHeadWall` premise
    restricted to the `LevelHom σ` every demanded `.pb` cell carries.
    Retained (not claimed, not refuted at the gate). -/
def pbHeadLhomWall : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) (σ : Level → Level)
    (ρ : List Disp), LevelHom σ → Nonempty (PbHead D DT σ ρ)

/-- The gated goal-level supply: what a premise-free gated `pb_case` field
    would yield at `Goal (.pb D DT S σ ρ)` (which IS `PBit σ ρ D DT`), at
    `LevelHom σ` only. Retained; tooth below. -/
def pbGoalSupplyLhom : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) (σ : Level → Level)
    (ρ : List Disp), LevelHom σ → PBit σ ρ D DT

/-- Tooth: the gated goal supply's conclusion is inhabited at the #7789
    pins (`sr4SortZ`/`sr4SortZUp`, `σ := id`, `ρ := []`) — both sides of
    the `PBit` iff are definitionally false there (`eps` is `ETm.sort _`,
    never `.star`; the sort level is succ-headed). -/
theorem pbGoalSupplyLhom_ident_sat :
    PBit id [] (sr4SortZ []) (sr4SortZUp []) :=
  ⟨fun h => ETm.noConfusion h, fun h => Bool.noConfusion h⟩

/-- The gated wall composes with the closer: `pbHeadLhomWall` supplies the
    gated `pb_case` field exactly (`GatedPbCase`, the shape the consumer
    patch in `RcicSynSRClEutLhomStep` consumes). -/
theorem gatedPbCase_of_pbHeadLhomWall (Aw : Nat → Nat) (tbl : List CRule)
    (wall : pbHeadLhomWall) : GatedPbCase Aw tbl Eₐ :=
  pb_case_lhom Aw tbl wall

#print axioms pb_case_lhom
#print axioms pbHeadLhomWall
#print axioms pbGoalSupplyLhom
#print axioms pbGoalSupplyLhom_ident_sat
#print axioms gatedPbCase_of_pbHeadLhomWall

end Rcic.Syn
