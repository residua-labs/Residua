import rcic.RcicNativeTypedModel
import rcic.RcicAnnEqLargeFixture

/-!
# Nonbottom membership overlap in the existing two-universe-code model

The compact `pi bot []` is both a proposition code and a type code in
`CTyS`.  It is also an actual approximation of the erased, proposition-typed
parameter of the admitted Eq-with-large-elimination fixture.  Consequently,
neither excluding bottom nor restricting to this observed source image makes
semantic universe membership determine a unique Prop/non-Prop bit.  The same
overlap holds for the whole observation set: every observed compact belongs
to both universe codes.  No ideal-closure laws are asserted for that set.

This is a boundary of `CTyS` and membership-based tag extraction.  There is
no second source typing at a positive sort in the statement.  In particular,
the result is not a counterexample to source zero-sort coherence, and it does
not refute another model or an additional source-image adequacy theorem.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ModelMembershipBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.TypedModelAudit

/-- The empty-row Pi observation already supplied by the landed model. -/
def overlapCompact : CptT := .pi .bot []

theorem overlapCompact_nonbottom : overlapCompact ≠ .bot := by
  intro h
  cases h

theorem universeCodes_distinct : (CptT.prop : CptT) ≠ .sort := by
  intro h
  cases h

theorem overlapCompact_propCode (E : ResolvedEnv) : IsPropCT E overlapCompact := by
  exact .pi .bot (fun s hs => (List.not_mem_nil s hs).elim)

theorem overlapCompact_propMember (E : ResolvedEnv) : CTyS E overlapCompact .prop := by
  rw [CTyS]
  exact Or.inr (overlapCompact_propCode E)

theorem overlapCompact_sortMember (E : ResolvedEnv) : CTyS E overlapCompact .sort := by
  rw [CTyS]
  exact Or.inr (tyCodeCT_of_isPropCT (overlapCompact_propCode E))

/-- The overlap compact is on the erased image of the actual typed fixture. -/
theorem parameter_observed :
    ApproxT eqEnvT EnvT.bot (erase EqLargeFixture.parameter) overlapCompact :=
  approxT_pi_bot_nil eqEnvT EnvT.bot (.sort .zero) (.bvar 0)

/-- Distinct universe codes do not give disjoint nonbottom memberships. -/
theorem no_nonbottom_membership_separation (E : ResolvedEnv) :
    ¬ (∀ c : CptT, c ≠ .bot → CTyS E c .prop → CTyS E c .sort → False) := by
  intro h
  exact h overlapCompact overlapCompact_nonbottom
    (overlapCompact_propMember E) (overlapCompact_sortMember E)

/-- Membership cannot assign an exact universe bit even when restricted to
nonbottom observations of this one proposition-typed source term. -/
theorem no_observed_membership_tag (tag : CptT → Bool) :
    ¬ (∀ c : CptT,
      ApproxT eqEnvT EnvT.bot (erase EqLargeFixture.parameter) c → c ≠ .bot →
      (CTyS eqEnvT c .prop → tag c = true) ∧
      (CTyS eqEnvT c .sort → tag c = false)) := by
  intro h
  have hc := h overlapCompact parameter_observed overlapCompact_nonbottom
  have ht := hc.1 (overlapCompact_propMember eqEnvT)
  have hf := hc.2 (overlapCompact_sortMember eqEnvT)
  exact Bool.noConfusion (ht.symm.trans hf)

/-- Every compact in a term's observation set belongs to one universe code.
This definition does not require or assert ideal laws. -/
def ObservedUniverseMembership (E : ResolvedEnv) (ρ : EnvT)
    (e : Expr Nat) (a : CptT) : Prop :=
  ∀ c : CptT, ApproxT E ρ e c → CTyS E c a

/-- The coarse model includes all proposition codes among its type codes. -/
theorem observedUniverseMembership_prop_sort {E : ResolvedEnv} {ρ : EnvT}
    {e : Expr Nat} (h : ObservedUniverseMembership E ρ e .prop) :
    ObservedUniverseMembership E ρ e .sort := by
  intro c hc
  rw [CTyS]
  rcases ctyS_prop_inv (h c hc) with hbot | hprop
  · exact Or.inl hbot
  · exact Or.inr (tyCodeCT_of_isPropCT hprop)

/-- Every observation of the actual erased parameter is a proposition code,
by the landed impredicative-Pi calculation. -/
theorem parameter_observation_set_prop :
    ObservedUniverseMembership eqEnvT EnvT.bot
      (erase EqLargeFixture.parameter) .prop := by
  intro c hc
  rw [CTyS]
  exact Or.inr (isPropCT_of_approxT_idPiProp hc)

theorem parameter_observation_set_sort :
    ObservedUniverseMembership eqEnvT EnvT.bot
      (erase EqLargeFixture.parameter) .sort :=
  observedUniverseMembership_prop_sort parameter_observation_set_prop

/-- An exact bit extracted solely from membership of the whole observation
set, with `true` required at Prop and `false` at the other universe code. -/
def ObservationSetMembershipTagAt (E : ResolvedEnv) (ρ : EnvT)
    (e : Expr Nat) (tag : (CptT → Prop) → Bool) : Prop :=
  (ObservedUniverseMembership E ρ e .prop → tag (denT E ρ e) = true) ∧
  (ObservedUniverseMembership E ρ e .sort → tag (denT E ρ e) = false)

/-- Moving from one compact to the entire observation set does not repair
this membership-only extraction rule. -/
theorem no_observation_set_membership_tag (tag : (CptT → Prop) → Bool) :
    ¬ ObservationSetMembershipTagAt eqEnvT EnvT.bot
      (erase EqLargeFixture.parameter) tag := by
  intro h
  have ht := h.1 parameter_observation_set_prop
  have hf := h.2 parameter_observation_set_sort
  exact Bool.noConfusion (ht.symm.trans hf)

/-- All source-admission, source-typing, and semantic-membership premises are
supplied.  The positive-sort membership is semantic, not a second typing. -/
theorem inhabited_membership_boundary :
    eraseEnv EqLargeFixture.env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) ∧
    Nonempty (CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 []) ∧
    Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 []
      EqLargeFixture.parameter (.sort .zero)) ∧
    ApproxT eqEnvT EnvT.bot (erase EqLargeFixture.parameter) overlapCompact ∧
    overlapCompact ≠ .bot ∧
    CTyS eqEnvT overlapCompact .prop ∧
    CTyS eqEnvT overlapCompact .sort ∧
    ObservedUniverseMembership eqEnvT EnvT.bot
      (erase EqLargeFixture.parameter) .prop ∧
    ObservedUniverseMembership eqEnvT EnvT.bot
      (erase EqLargeFixture.parameter) .sort ∧
    ¬ (∀ c : CptT, c ≠ .bot →
      CTyS eqEnvT c .prop → CTyS eqEnvT c .sort → False) ∧
    ∀ tag : (CptT → Prop) → Bool,
      ¬ ObservationSetMembershipTagAt eqEnvT EnvT.bot
        (erase EqLargeFixture.parameter) tag :=
  ⟨EqLargeFixture.erase_env, EqLargeFixture.wf, ⟨.nil⟩,
    ⟨EqLargeFixture.parameterTyped⟩, parameter_observed, overlapCompact_nonbottom,
    overlapCompact_propMember eqEnvT, overlapCompact_sortMember eqEnvT,
    parameter_observation_set_prop, parameter_observation_set_sort,
    no_nonbottom_membership_separation eqEnvT, no_observation_set_membership_tag⟩

#print axioms overlapCompact
#print axioms overlapCompact_nonbottom
#print axioms universeCodes_distinct
#print axioms overlapCompact_propCode
#print axioms overlapCompact_propMember
#print axioms overlapCompact_sortMember
#print axioms parameter_observed
#print axioms no_nonbottom_membership_separation
#print axioms no_observed_membership_tag
#print axioms ObservedUniverseMembership
#print axioms observedUniverseMembership_prop_sort
#print axioms parameter_observation_set_prop
#print axioms parameter_observation_set_sort
#print axioms ObservationSetMembershipTagAt
#print axioms no_observation_set_membership_tag
#print axioms inhabited_membership_boundary

end Rcic.Declarative.Ann.LR3.ModelMembershipBoundary
