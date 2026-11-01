import rcic.RcicF3PointwiseDataNormal
import rcic.RcicF3CheckedCtorWorld

/-!
# Exact local candidate obligation at checked DATA worlds

This internal predicate retains existence of an actual small local closed
candidate. It is not a produced universal theorem or an additional check.
The pointwise frame is globally admissible without it; only constructor
closure at a reached bounded world consumes it. Canonicalization preserves
family universe coordinates and supplies no numeric bound.

The producer from a known global candidate is useful for existing finite
and W fixtures. It does not prove the outstanding bounded-domain/LR step.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataLocal
open Rcic.Declarative RawFamily

noncomputable abbrev frame (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) : Frame :=
  PointwiseData.frame P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity

def LocalCandidates (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (K : Nat → Nat) : Prop :=
  ∀ vs : List Nat, vs.length = p.node.a.family.member.arity →
    (∀ v, v ∈ vs → v ≤ K p.rr) →
    PointwiseData.ExistsAt P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity
      (PiSmallFrame.canonical p.node.a.family.member.arity vs)

theorem admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E') :
    Admissible (EvalPlanNormal.fd p) (frame P μ p) :=
  PointwiseData.frame_admissible P μ _ _
    (EvalPlanNormal.bounded_of_group p fm ctors hE hmem)

theorem closed_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (K : Nat → Nat) (hLocal : LocalCandidates P μ p K)
    (vs : List Nat) (hvl : vs.length = p.node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K p.rr) :
    ∀ i z, CtorAt P μ (EvalPlanNormal.fd p) (frame P μ p) vs i z →
      z ∈ frame P μ p vs i :=
  PointwiseData.frame_closed_at P μ p fm ctors hE hmem vs (hLocal vs hvl hvs)

theorem of_global_candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hex : ∃ C, Admissible (EvalPlanNormal.fd p) C ∧ Closed P μ (EvalPlanNormal.fd p) C)
    (K : Nat → Nat) : LocalCandidates P μ p K := by
  obtain ⟨C, hC, hc⟩ := hex
  intro vs _ _
  exact PointwiseData.exists_of_candidate P μ p fm ctors hE hmem C hC
    (PiSmallFrame.canonical p.node.a.family.member.arity vs)
    (PiSmallFrame.canonical_idem _ vs) (hc _)

end Rcic.F3.PSet.PointwiseDataLocal
