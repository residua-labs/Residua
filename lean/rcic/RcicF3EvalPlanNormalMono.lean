import rcic.RcicF3EvalPlanNormal
import rcic.RcicF3CandidatePrefixFromGroup

/-!
# Global monotonicity of the actual normalized operator

Actual admission pays the free parameter/index syntax, normalized field
cleanliness and canonical-level readback. The existing normalized tuple
monotonicity theorem then applies at every vector, without normalizing raw
fields or using a bounded semantic invariant. This does not establish
monotonicity of the raw hidden syntax or produce a small closed frame.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormal
open Rcic.Declarative PiValueRule RawFamily

/-- Every syntactic premise of normalized constructor monotonicity is
produced from this actual typed group and its retained plan data. -/
theorem constructorMono_of_group (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E') :
    ConstructorMono P μ (fd p) := by
  obtain ⟨_, _, hfree, _, _, hbounded⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  apply RawFamily.constructorMono_normalized P μ (fd p)
    (canonL p.node.a.family.member.arity)
    (fun j => specs (p.constructors (index p j)).fields)
  · intro A hA
    exact hfree A (List.mem_append_left _ hA)
  · intro j
    rw [ctor_get]
    rfl
  · intro j
    simpa only [fd, famDataOf, List.length_append] using
      specs_clean (p.constructors (index p j)).fields
  · intro j A hA
    rw [ctor_get] at hA
    exact (p.node.a.constructorViews (index p j)).noFamilyInIndices A hA
  · intro vs
    have hag : ∀ u, u < p.node.a.family.member.arity →
        σOf ((canonL p.node.a.family.member.arity).map (evalTotal (σOf vs))) u =
          σOf vs u := by
      intro u hu
      have hlen : u <
          ((canonL p.node.a.family.member.arity).map (evalTotal (σOf vs))).length := by
        simpa only [canonL, List.length_map, List.length_range] using hu
      change ((canonL p.node.a.family.member.arity).map
        (evalTotal (σOf vs))).getD u 0 = σOf vs u
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
      simp only [Option.getD_some, canonL, List.getElem_map,
        List.getElem_range, evalTotal]
    exact evalTotal_agree hag p.node.a.family.resultLevel hbounded.res

end Rcic.F3.PSet.EvalPlanNormal
