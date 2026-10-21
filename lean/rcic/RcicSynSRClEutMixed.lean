import rcic.RcicSynTableOfIFull
import rcic.RcicSynSameRankDep

/-!
# RcicSynSRClEutMixed — sortRow row 17 (`mixed_case`) at `tableOfI hW`

Deliverable (lane glm-sr3): row 17 has NO independent missing lemma —
`mixedField_iff` makes the three pair fields one obligation, so the row is
fully determined by rows 14 (`cl_case`) and 15 (`eut_case`). Both parent
rows are refuted at their RAW supplies at `tableOfI hW` (this lane:
`clConstP_tableOfI_empty_refuted`, `eutLamP_tableOfI_empty_refuted`), so
their restated walls (`cl_case_wall`, `eut_case_wall`) are exactly what row
17 inherits. This module pins the inheritance mechanically at
`tableOfI hW` and states the row's exact restated wall as ONE named Prop.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv}

/-- Row 17's exact restated wall, ONE Prop: the `MixedField` statement at
    `tableOfI hW` — no bundling, no independent wall; rows 14–15's restated
    walls (`cl_case_wall`, `eut_case_wall`) are the inherited blockers. -/
def mixed_case_wall (hW : EnvWfT E) (Aw : Nat → Nat) (Eₐ : ResolvedEnv) : Prop :=
  MixedField Aw (tableOfI hW) Eₐ

/-- Relative-closure pin: rows 14+15 discharged ⇒ row 17 discharged, with
    no new wall (the derivation uses only same-rank `Demand` edges). -/
theorem mixed_case_of_cl_eut_tableI (hW : EnvWfT E) {Aw : Nat → Nat}
    {Eₐ : ResolvedEnv} (hcl : ClField Aw (tableOfI hW) Eₐ)
    (heut : EutField Aw (tableOfI hW) Eₐ) : MixedField Aw (tableOfI hW) Eₐ :=
  mixedField_of_cl_eut Aw (tableOfI hW) hcl heut

/-- The three pair fields are one obligation at `tableOfI hW` too: row 17
    conversely determines rows 14+15 (`mixedField_iff` at the real table). -/
theorem mixedField_iff_tableI (hW : EnvWfT E) (Aw : Nat → Nat) (Eₐ : ResolvedEnv) :
    MixedField Aw (tableOfI hW) Eₐ ↔
      ClField Aw (tableOfI hW) Eₐ ∧ EutField Aw (tableOfI hW) Eₐ :=
  mixedField_iff Aw (tableOfI hW) Eₐ

#print axioms mixed_case_of_cl_eut_tableI
#print axioms mixedField_iff_tableI

end Rcic.Syn
