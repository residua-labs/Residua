import rcic.RcicF3EvalPlanNormalMono
import rcic.RcicF3RawFamilyProp

/-!
# Produced normalized proof-family closure and raw inclusion

At the actual Prop/anySort selection, admission forces a uniformly Prop
result. The existing proof-top candidate and the produced normalized
constructor monotonicity give a correctly sized, globally closed
normalized frame. The all-universe forward constructor bridge then places
the unchanged raw frame inside that normalized frame. No raw constructor
monotonicity, small-frame callback or changed family role is assumed.

The converse comparison is a separate bounded induction obligation.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormalProp
open Rcic.Declarative PiIndex RawFamily EvalPlanNormal

/-- The admitted large-elimination selection produces the normalized
proof-family frame, including global closure at every universe vector. -/
theorem normalized_closed (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (σ : Nat → Nat)
    (h0 : evalTotal σ p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort) :
    Admissible (fd p) (frame P μ (fd p)) ∧
      Closed P μ (fd p) (frame P μ (fd p)) := by
  have hprop : ∀ vs, evalTotal (σOf vs) (fd p).resLevel = 0 :=
    fun vs => (selection_prop p.node.a σ h0 hpolicy).1 (σOf vs)
  exact ⟨RawFamilyProp.admissible P μ (fd p) hprop,
    RawFamilyProp.closed P μ (fd p) hprop
      (constructorMono_of_group P μ p fm ctors hE hmem)⟩

/-- The normalized closed frame is also closed for the literal original
constructor syntax. Raw leastness gives global inclusion while preserving
the full universe vector and complete parameter/index key. -/
theorem raw_le_normalized (F : RoleModel.FamilyValue) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hctx : ∀ r, Dom p.E' r →
      ctx r = envCtx (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
        hE hfam hctors hrec hmem) r)
    (hF : EvalRole.Faithful F P μ ctx plans p.E')
    (σ : Nat → Nat)
    (h0 : evalTotal σ p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort) :
    FrameSub (frame P μ (famDataOf p.node.a)) (frame P μ (fd p)) := by
  obtain ⟨hN, hclosed⟩ := normalized_closed P μ p fm ctors hE hmem σ h0 hpolicy
  have hNraw : Admissible (famDataOf p.node.a) (frame P μ (fd p)) := hN
  have hrawClosed : Closed P μ (famDataOf p.node.a) (frame P μ (fd p)) := by
    intro vs i z hz
    exact hclosed vs i z (ctorAt_of_group F P μ ctx plans p fm ctors hE hfam
      hctors hrec hmem hctx hF (frame P μ (fd p)) vs i z hz)
  exact frame_least P μ (famDataOf p.node.a) (frame P μ (fd p)) hNraw hrawClosed

end Rcic.F3.PSet.EvalPlanNormalProp
