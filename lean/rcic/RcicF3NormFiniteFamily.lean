import rcic.RcicF3RawFiniteCompare
import rcic.RcicF3NormDPlanBridge
import rcic.RcicF3EvalPlanNormalLevels
import rcic.RcicF3EvalPlanNormalMono

/-!
# Produced finite-family comparison at the actual normalized no-PendA node

Every premise of the finite-frame construction is obtained from the
admitted group and its actual normalized cache. The result includes the
small closed candidate, admissibility and closure of the intersection,
and its all-instance equality with the existing normalized finite limit.

This is the A-negative branch of the migration. The positive-depth PendA
branch remains a separate universal obligation; no check or admission
domain is strengthened. No predecessor invariant or semantic callback is
needed for this family component. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormFiniteFamily
open Rcic.Declarative PiIndex RawFamily

/-- The finite syntactic facts used by the already defined limit. The
actual producer below obtains every field from admission. -/
structure Syntax (fd : FamData) (ar : Nat) : Prop where
  bounded : FamBounded fd ar
  familyFree : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false
  fields : ∀ c ∈ fd.ctors, ∀ A ∈ c.1,
    occursConst fd.fref A = false ∨ RecApp fd ar A
  resultFree : ∀ c ∈ fd.ctors, ∀ e ∈ c.2, occursConst fd.fref e = false
  indexCount : ∀ c ∈ fd.ctors, c.2.length = fd.indices.length

theorem syntax_of_group (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hN : NoFunRec p.node) :
    Syntax (EvalPlanNormal.fd p) p.node.a.family.member.arity := by
  have hFF := NormDPlanBridge.bodies_of_group hE hmem p.node
  have he := NormDPlanBridge.normalized_descriptor p hFF hN
  obtain ⟨_, _, hfree, _, _, _⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  refine ⟨EvalPlanNormal.bounded_of_group p fm ctors hE hmem, hfree, ?_, ?_, ?_⟩
  · rw [he]
    exact nodeFam_recApp p.node hFF hN
  · intro c hc e hec
    obtain ⟨k, hk, hkC⟩ := List.getElem_of_mem hc
    let j : Fin (EvalPlanNormal.fd p).ctors.length := ⟨k, hk⟩
    have hget : c = (EvalPlanNormal.fields p (EvalPlanNormal.index p j),
        (p.node.a.constructorViews (EvalPlanNormal.index p j)).resultIndices) := by
      rw [← hkC]
      exact EvalPlanNormal.ctor_get p j
    rw [hget] at hec
    exact (p.node.a.constructorViews (EvalPlanNormal.index p j)).noFamilyInIndices e hec
  · intro c hc
    obtain ⟨k, hk, hkC⟩ := List.getElem_of_mem hc
    let j : Fin (EvalPlanNormal.fd p).ctors.length := ⟨k, hk⟩
    have hget : c = (EvalPlanNormal.fields p (EvalPlanNormal.index p j),
        (p.node.a.constructorViews (EvalPlanNormal.index p j)).resultIndices) := by
      rw [← hkC]
      exact EvalPlanNormal.ctor_get p j
    rw [hget]
    exact (p.node.a.constructorViews (EvalPlanNormal.index p j)).indexCount

/-- The family component retains the concrete candidate and intersection,
and its comparison is only with the normalized finite descriptor. -/
structure Package (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) : Prop where
  candidateAdmissible : Admissible fd (RawFiniteFrame.candidate P μ fd)
  candidateClosed : Closed P μ fd (RawFiniteFrame.candidate P μ fd)
  admissible : Admissible fd (frame P μ fd)
  closed : Closed P μ fd (frame P μ fd)
  value : ∀ vs, Equiv (role P μ fd vs) (famLim P μ fd vs)

/-- Actual admission produces the complete normalized finite-family
package at every semantic table and full universe vector. -/
theorem package_of_group (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hN : NoFunRec p.node) : Package P μ (EvalPlanNormal.fd p) := by
  have hS := syntax_of_group p fm ctors hE hmem hN
  have hCand := RawFiniteFrame.candidate_admissible P μ (EvalPlanNormal.fd p)
  have hClose := RawFiniteFrame.candidate_closed P μ (EvalPlanNormal.fd p)
    p.node.a.family.member.arity hS.bounded hS.familyFree hS.fields hS.resultFree hS.indexCount
  refine ⟨hCand, hClose, frame_admissible P μ _ ⟨_, hCand, hClose⟩, ?_, ?_⟩
  · exact frame_closed_of_mono P μ _ ⟨_, hCand, hClose⟩
      (EvalPlanNormal.constructorMono_of_group P μ p fm ctors hE hmem)
  · exact RawFiniteCompare.role_value P μ (EvalPlanNormal.fd p)
      p.node.a.family.member.arity hS.bounded hS.familyFree hS.fields hS.resultFree hS.indexCount

end Rcic.F3.PSet.NormFiniteFamily
