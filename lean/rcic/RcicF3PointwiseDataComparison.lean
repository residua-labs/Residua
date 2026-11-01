import rcic.RcicF3PointwiseRole

/-!
# Conditional comparison where a global candidate is already produced

This comparison retains the literal global small-closed-candidate premise.
It is useful for existing Nat and W witnesses; it does not discharge that
premise universally, identify the two invariants, or remove the semantic
difference at an empty candidate class. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseData
open Rcic.Declarative PiIndex RawFamily

theorem frame_equiv_of_global_candidate (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hex : ∃ C, Admissible (EvalPlanNormal.fd p) C ∧ Closed P μ (EvalPlanNormal.fd p) C)
    (vs : List Nat) (i : Index.{4}) :
    Equiv (frame P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity vs i)
      (RawFamily.frame P μ (EvalPlanNormal.fd p) vs i) := by
  let d := EvalPlanNormal.fd p
  let ar := p.node.a.family.member.arity
  let R := RawFamily.frame P μ d
  let F := frame P μ d ar
  have hB := EvalPlanNormal.bounded_of_group p fm ctors hE hmem
  have hm := EvalPlanNormal.constructorMono_of_group P μ p fm ctors hE hmem
  have hR : Admissible d R := RawFamily.frame_admissible P μ d hex
  have hcR : Closed P μ d R := frame_closed_of_mono P μ d hex hm
  have hF : Admissible d F := frame_admissible P μ d ar hB
  have hcF : Closed P μ d F := by
    intro ws j z hz
    have he := exists_of_candidate P μ p fm ctors hE hmem R hR
      (PiSmallFrame.canonical ar ws) (PiSmallFrame.canonical_idem ar ws)
      (hcR (PiSmallFrame.canonical ar ws))
    exact frame_closed_at P μ p fm ctors hE hmem ws he j z hz
  apply ext
  intro z
  constructor
  · intro hz
    let w := PiSmallFrame.canonical ar vs
    have hw : PiSmallFrame.canonical ar w = w := PiSmallFrame.canonical_idem ar vs
    have hlocal : ClosedAt P μ d ar w (R w) := by
      intro j x hx
      apply hcR w j x
      apply ctorAt_sub_of_plan P μ p fm ctors hE hmem (embed ar w (R w)) R
        (embed_admissible P d ar hB w (R w) (hR w)) hR w hw ?_ j x hx
      intro k y hy
      rw [embed_at ar w hw] at hy
      exact hy
    have hzR := local_least P μ d ar w (R w) (hR w) hlocal i z hz
    have hc := RawFamily.frame_dense P μ d hR hcR hm w i z hzR
    exact hcR vs i z (ctorAt_levels P μ d ar hB R w vs
      (fun k hk => (PiSmallFrame.canonical_agree ar vs k hk).symm) i z hc)
  · exact RawFamily.frame_least P μ d F hF hcF vs i z

theorem role_equiv_of_global_candidate (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hex : ∃ C, Admissible (EvalPlanNormal.fd p) C ∧ Closed P μ (EvalPlanNormal.fd p) C)
    (vs : List Nat) :
    Equiv (role P μ (EvalPlanNormal.fd p) p.node.a.family.member.arity vs)
      (RawFamily.role P μ (EvalPlanNormal.fd p) vs) := by
  let d := EvalPlanNormal.fd p
  change Equiv (piLam (mkM P μ) (σOf vs) _ ρ0 (famType d))
    (piLam (mkM P μ) (σOf vs) _ ρ0 (famType d))
  apply piLam_congr_fits (mkM P μ) (σOf vs) (.sort d.resLevel)
    (fun _ _ h => Expr.noConfusion h) (d.params ++ d.indices) ρ0
  intro xs hx
  exact tyv_congr (frame_equiv_of_global_candidate P μ p fm ctors hE hmem hex vs _)

end Rcic.F3.PSet.PointwiseData

namespace Rcic.F3.PSet.PointwiseRole
open Rcic.Declarative RawFamily

theorem familyValue_equiv_of_global_candidate (α : Arities) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hα : AritiesAgree α p.E')
    (hex : ∃ C, Admissible (EvalPlanNormal.fd p) C ∧ Closed P μ (EvalPlanNormal.fd p) C)
    (vs : List Nat) :
    Equiv (familyValue α P μ (EvalPlanNormal.fd p) vs)
      (RawFamily.role P μ (EvalPlanNormal.fd p) vs) := by
  unfold familyValue
  split
  · exact Equiv.rfl
  · have har : α (EvalPlanNormal.fd p).fref = p.node.a.family.member.arity :=
      arity_at_node hα p.node
    rw [har]
    exact PointwiseData.role_equiv_of_global_candidate P μ p fm ctors hE hmem hex vs

end Rcic.F3.PSet.PointwiseRole
