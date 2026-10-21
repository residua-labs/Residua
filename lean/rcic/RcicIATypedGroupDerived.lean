import rcic.RcicIATypedIota

/-!
# IA-025 on the typed root: the semantic group contains the exact derived objects

05 §15 (`docs/rcic/05_INDUCTIVE_ADMISSION.md:289-301`): the checked-group identity includes
the recursor type and the iota descriptors — the group's derived objects are identity-bearing.
05 §18 row IA-025: "semantic group contains exact derived objects". The scm carrier
`apps/rcic-ind-group-identity` makes the tokens identity-bearing and names the open half
(APP.md DOES NOT DECIDE): nothing binds them to the *actually derived* objects. This module is
the Lean half of that binding, as an environment-level extraction in the `IA023T` pattern.

**No walk of its own.** Per cc's ruling on the S0 plan (#6726, risk 1) this module does NOT
mirror `RcicIATypedIota`'s ~60-line walk; it consumes the BUNDLED walk added there in the same
change: `envWfT_recursorCellMinors` traverses `EnvWfT`/`GroupMembersT` once and returns the
admission cell TOGETHER with the `MinorPremisesMatch` clause (`h12`) that IA-023's bare cell
drops. IA-023's own names are one-line projections of the same walk, so both rows share one
traversal.

**What the extraction says:** every `recursorM` member of an `EnvWfT` environment belongs to
a checked group whose admission carries the exact derived objects — the stored recursor type
IS `policyRecursorType` at the admission's family and minors (`RecursorEliminationAdmitted
.recursorType`, a field), the stored arity IS `policyRecursorArity` (field), every minor IS
the derived minor at its analysis bound (`MinorPremisesMatch`, the judgment's `h12`), and
every ι equation is the computed schema, typed (`IotaDescriptorClause`, the judgment's `h14`,
with the typed equations `IndGroupTypedT` carries).

**The evidence that admission checks is NOT this module** — it is the landed teeth:
GM-IND-001 (`RcicIARecUniquePins.lean`: swapped minors admit no `MinorPremisesMatch` at any
bound) and GM-IND-005 (`tooth_GM_IND_005_listDecoys`: the checker refuses the three decoy
right-hand sides). This module extracts; it does not re-tooth.

`closure_claim` 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Declarative

/-! ## (1) the row shape and its extraction via IA-023's bundled walk -/

/-- IA-025, the row shape at one recursor member: the checked group contains the exact
derived objects — the stored recursor type and arity are the derived `policyRecursorType` /
`policyRecursorArity` at some admission, every minor is the derived minor at its analysis
bound (`MinorPremisesMatch`), and every ι equation is the computed schema at the
descriptor's own bound, typed (`IotaEquationTypedT`). -/
def GroupContainsDerivedAt (E : ResolvedEnv) (r : Nat) (m : CheckedMember) : Prop :=
  ∃ (E0 : ResolvedEnv) (a : RecursorEliminationAdmitted E0 r m)
      (h12 : MinorPremisesMatch a) (h14 : IotaDescriptorClause E0 a),
    m.mtype = policyRecursorType a.family a.minorTypes a.policy ∧
      m.arity = policyRecursorArity a.family.member.arity a.policy ∧
      ∀ i, IotaEquationTypedT a i (h14.fuelAt i) (h14.shapesAt i)

/-- IA-025 on the typed root, AS AN EXTRACTION: every recursor member of an `EnvWfT`
environment belongs to a checked group that contains the exact derived objects — the
stored type/arity equalities are the admission's own fields (`recursorType`,
`recursorArity`), the minors clause is the judgment's `h12` (kept by the bundled walk;
`RecursorCellT` drops it), the ι schemas its `h14` with the typed equations `IndGroupTypedT`
carries. The first two conjuncts are fields of the admission; the walk supplies which
admission. -/
theorem IA025T_group_contains_derived {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (hcls : m.mclass = .recursorM) :
    GroupContainsDerivedAt E r m :=
  let b := envWfT_recursorCellMinors hW hm hcls
  ⟨b.cell.E0, b.cell.adm, b.minors, b.cell.clause, b.cell.adm.recursorType,
    b.cell.adm.recursorArity, b.cell.typed⟩

/-! ## (2) pins at real fixtures (teeth by citation: GM-IND-001, GM-IND-005) -/

/-- PIN (IA-025T): List's recursor (ref 11) in the two-group environment `listEnvUT`. -/
theorem pin_IA025T_listU : GroupContainsDerivedAt listEnvUT 11 listURecMember :=
  IA025T_group_contains_derived listEnvUWfT rfl rfl

end Rcic.Declarative

namespace Rcic.Scm.SrcG

open Rcic.Declarative

/-- PIN (IA-025T): `srcEnvG`'s nine-minor recursor `recValueAt` (slot 143), through the
unconditional `envWfT_srcEnvG` — the same fixture `pin_IA023T_srcVA` types. -/
theorem pin_IA025T_srcVA : GroupContainsDerivedAt srcEnvG 143 recValueAt :=
  IA025T_group_contains_derived envWfT_srcEnvG srcEnvG_slot143 rfl

end Rcic.Scm.SrcG

#print axioms Rcic.Declarative.GroupContainsDerivedAt
#print axioms Rcic.Declarative.IA025T_group_contains_derived
#print axioms Rcic.Declarative.pin_IA025T_listU
#print axioms Rcic.Scm.SrcG.pin_IA025T_srcVA
