import rcic.RcicF3PointwiseRemainingPropOnlyPrefixBeta

set_option autoImplicit false

namespace Rcic.F3.PSet.RouteRemaining

/-- Encoding-only binding of the exact original target to a declared
producer edge. This theorem proves no new soundness result. -/
theorem root_binding
    (hRoot : Rcic.Apex.KernelSoundnessTierUncond) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  hRoot


/-- The exact environment-side antecedents of the original tier. This is a
predicate on an admission derivation, not merely on the member lookup table. -/
def Fragment (K : Nat → Nat) (E : Rcic.Declarative.ResolvedEnv)
    (hW : Rcic.Declarative.EnvWfT E) : Prop :=
  BoundG K hW ∧ BoundDG K hW ∧ AxiomFreeEnv' E ∧
    E.members 0 = some Rcic.Declarative.falseFamMember ∧
    E.members 1 = some Rcic.Declarative.falseRecMemberU

/-- Decidability is relative to the explicit decision data already in the
original root. No executable import decider or inhabitant of Premises4 is
constructed here. -/
def fragmentDecision (P : Premises4) (K : Nat → Nat)
    (E : Rcic.Declarative.ResolvedEnv) (hW : Rcic.Declarative.EnvWfT E) :
    Decidable (Fragment K E hW) := P.dec _

/-- The fragment description preserves every original antecedent and the
height/instance restriction on the hypothetical final derivation. -/
theorem tierF3_iff_fragment : Rcic.Apex.TierF3Uncond ↔
    (∀ (P : Premises4) (K : Nat → Nat) (E : Rcic.Declarative.ResolvedEnv)
      (hW : Rcic.Declarative.EnvWfT E), Fragment K E hW →
      ∀ (n : Nat) (e : Rcic.Declarative.Expr Nat)
        (D : Rcic.Declarative.HasTyT E n [] e (.const 0 [])),
        LevelsBelow 4 K D → False) := by
  constructor
  · intro h P K E hW hF
    exact h P K E hW hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 hF.2.2.2.2
  · intro h P K E hW hB hD hAx h0 h1
    exact h P K E hW ⟨hB, hD, hAx, h0, h1⟩

end Rcic.F3.PSet.RouteRemaining

#print axioms Rcic.F3.PSet.RouteRemaining.root_binding

#print axioms Rcic.F3.PSet.RouteRemaining.Fragment
#print axioms Rcic.F3.PSet.RouteRemaining.fragmentDecision
#print axioms Rcic.F3.PSet.RouteRemaining.tierF3_iff_fragment
