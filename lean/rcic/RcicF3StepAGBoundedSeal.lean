import rcic.RcicF3StepAGBounded

/-!
# StepAG bounded-cell boundary seal

Audit the public declarations in `RcicF3StepAGBounded` at compile time.
The literal global cells are refuted; no StepAG apex is claimed.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.StepAGBoundedSeal

open Lean Elab Command

def sealedTheorems : List Name := [
  ``Rcic.F3.StepAGBounded.RecGroupAShape,
  ``Rcic.F3.StepAGBounded.recGroupA_of_facts,
  ``Rcic.F3.StepAGBounded.DomainBounds,
  ``Rcic.F3.StepAGBounded.domainBoundsB,
  ``Rcic.F3.StepAGBounded.domainBoundsB_iff,
  ``Rcic.F3.StepAGBounded.domainBounds_iff_storedType,
  ``Rcic.F3.StepAGBounded.BoundsRefusal,
  ``Rcic.F3.StepAGBounded.boundsRefusalOf,
  ``Rcic.F3.StepAGBounded.boundsRefusalOf_none_iff,
  ``Rcic.F3.StepAGBounded.boundsRefusalOf_sound,
  ``Rcic.F3.StepAGBounded.badDomain,
  ``Rcic.F3.StepAGBounded.badDomainTy,
  ``Rcic.F3.StepAGBounded.badDomainTyT,
  ``Rcic.F3.StepAGBounded.badFamilyMember,
  ``Rcic.F3.StepAGBounded.badPrefix,
  ``Rcic.F3.StepAGBounded.badFamilyView,
  ``Rcic.F3.StepAGBounded.badFamilyTyped,
  ``Rcic.F3.StepAGBounded.badRecMember,
  ``Rcic.F3.StepAGBounded.badAdmission,
  ``Rcic.F3.StepAGBounded.badFamilyAppTyT,
  ``Rcic.F3.StepAGBounded.badRecTypeTyT,
  ``Rcic.F3.StepAGBounded.badCensus,
  ``Rcic.F3.StepAGBounded.badIotaClause,
  ``Rcic.F3.StepAGBounded.badEnv,
  ``Rcic.F3.StepAGBounded.badNode,
  ``Rcic.F3.StepAGBounded.bare_params_refuted,
  ``Rcic.F3.StepAGBounded.bare_indices_refuted,
  ``Rcic.F3.StepAGBounded.badFamily_storedType_refuses,
  ``Rcic.F3.StepAGBounded.badNode_refusal,
  ``Rcic.F3.StepAGBounded.bare_recGroupA_refuted,
  ``Rcic.F3.StepAGBounded.literal_cells_of_groupMembersT,
  ``Rcic.F3.StepAGBounded.boundsRefusalOf_params_iff,
  ``Rcic.F3.StepAGBounded.boundsRefusalOf_indices_iff,
  ``Rcic.F3.StepAGBounded.vec_bounds_nonvacuous,
  ``Rcic.F3.StepAGBounded.badEnv_not_wfT,
  ``Rcic.F3.StepAGBounded.badNode_shape
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_stepag_bounded_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_stepag_bounded_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_stepag_bounded_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.StepAGBoundedSeal
