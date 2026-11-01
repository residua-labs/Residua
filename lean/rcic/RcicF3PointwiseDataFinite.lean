import rcic.RcicF3PointwiseDataGroup
import rcic.RcicF3NormFiniteFamily

/-!
# The finite DATA face supplies the new local candidates

Actual NoFunRec admission already produces a small closed candidate for
all ambient tables. Its one-world projection pays LocalCandidates, so the
new checked DATA group producer requires no additional semantic premise
on this face. No old/new family or invariant equality is used.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataFinite
open Rcic.Declarative RawFamily

theorem local_candidates (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hN : NoFunRec p.node) (K : Nat → Nat) :
    PointwiseDataLocal.LocalCandidates P μ p K := by
  have h := NormFiniteFamily.package_of_group P μ p fm ctors hE hmem hN
  exact PointwiseDataLocal.of_global_candidate P μ p fm ctors hE hmem
    ⟨RawFiniteFrame.candidate P μ (EvalPlanNormal.fd p),
      h.candidateAdmissible, h.candidateClosed⟩ K

theorem group_step_of_check (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hN : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hcheck : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none) :
    PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem := by
  apply PointwiseDataGroup.group_step_of_check P K hE hfam hctors hrec hmem hType hcheck
  intro _ _ _ _ _ _ _ _ _ _ μ _
  exact local_candidates P μ (EvalPlan.ofGroup hE hfam hctors hrec hmem)
    fm ctors hE hmem hN K

end Rcic.F3.PSet.PointwiseDataFinite
