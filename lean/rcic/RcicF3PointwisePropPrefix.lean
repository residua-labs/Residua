import rcic.RcicF3PointwiseGroupFacts
import rcic.RcicF3NormPropCtorUniform

/-!
# Actual Prop family equations with the pointwise predecessor

Uniformly Prop families retain the existing normalized raw-frame operation
literally. Earlier DATA families are NOT identified with their old values.
All predecessor and arbitrary-candidate prefix soundness comes from the
new pointwise invariant and its read law. Prop admissibility and closure
are produced by the existing policy-independent theorem.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwisePropPrefix
open Rcic.Declarative Rcic.Model.PS RawFamily CandidatePrefixFromGroup

theorem family_equation_of_group (P : Premises4) (α : PointwiseRole.Arities)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
    ∀ vs, Equiv (μ p.node.a.family.ref vs) (role P μ (EvalPlanNormal.fd p) vs) := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  change ∀ vs : List Nat, Equiv (μ p.node.a.family.ref vs)
    (role P μ (EvalPlanNormal.fd p) vs)
  have hf' : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  intro vs
  have h := hFaith f fm hf' vs
  rw [hctx f (dom_of_members hf'), NormRole.envCtx_group, groupRoles_at_f] at h
  change Equiv (μ f vs)
    (PointwiseRole.familyValue α P μ (EvalPlanNormal.fd p) vs) at h
  rw [PointwiseRole.familyValue_prop α P μ _ hProp vs] at h
  simpa only [p.node.fam] using h

theorem canonical_group_facts (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    GroupPrefixFacts P μ K E E' f rr rm fm
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node := by
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hαE : PointwiseRole.AritiesAgree α E := hα.mono (groupMembersT_preserve hmem)
  have hFaithE : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E :=
    fun r m hm => hFaith r m (groupMembersT_preserve hmem r m hm)
  have hFamily := family_equation_of_group P α μ hE hfam hctors hrec hmem
    ctx plans hctx hFaith hProp
  exact PointwiseGroupFacts.group_facts P K μ hE hfam hmem p.node hPred α hαE ctx plans
    hctxE hplansE hFaithE (frame P μ (EvalPlanNormal.fd p))
    (NormPropCtorUniform.normalized_closed P μ p fm ctors hE hmem hProp).1 hFamily

end Rcic.F3.PSet.PointwisePropPrefix
