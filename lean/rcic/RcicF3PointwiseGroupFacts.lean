import rcic.RcicF3PointwisePrefix
import rcic.RcicF3PointwiseRoleEquations

/-!
# Actual family-only facts in the separate faithful DATA table

Actual arity metadata and the DATA branch yield the pointwise family
value equation. Unconditional admissibility supplies family soundness.
The new predecessor supplies stable iota and survives every admissible
fresh-family replacement. No local candidate existence is used here.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseGroupFacts
open Rcic.Declarative Rcic.Model.PS RawFamily CandidatePrefixFromGroup

theorem group_facts (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (N : Frame) (hN : Admissible (famDataOf node.a) N)
    (hFamily : ∀ vs, Equiv (μ node.a.family.ref vs)
      (ofFrame P μ (famDataOf node.a) N vs)) :
    GroupPrefixFacts P μ K E E' f rr rm fm node := by
  have hPrior := hPred α hα ctx hctx plans hplans μ hFaith
  have hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r :=
    hPrior.2 E' (groupMembersT_preserve hmem)
  obtain ⟨hfm, hty, hfree, hTF, hclosed, hbounded⟩ := syntax_facts hE hmem node
  refine ⟨⟨hPrior.1, hI⟩, hbounded, hfree, hclosed,
    NormCandidatePrefix.frame_prefix_envSound P K μ hE hfam hmem node hPrior.1 hI N hN hFamily,
    ?_, hTF, hfm, hty⟩
  intro X hX σ n
  have hf' : E'.members f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hfresh : E.members (famDataOf node.a).fref = none := by
    change E.members node.a.family.ref = none
    rw [node.fam]
    exact groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  have hCand := PointwiseRole.candidate_prefix_envSound P K hE hPred α hα μ ctx plans hctx hplans hFaith
    (famDataOf node.a) X hX hfree fm hty
    (hTF f fm hf').1 (hTF f fm hf').2.1 hbody hfam hfresh σ n
  simpa only [show (famDataOf node.a).fref = f from node.fam] using hCand


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
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
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
  have hFamily := PointwiseRoleEquations.family_equation_of_group P α μ hE hfam
    hctors hrec hmem hα ctx plans hctx hFaith hType
  exact group_facts P K μ hE hfam hmem p.node hPred α hαE ctx plans
    hctxE hplansE hFaithE (PointwiseDataLocal.frame P μ p)
    (PointwiseDataLocal.admissible P μ p fm ctors hE hmem) hFamily

end Rcic.F3.PSet.PointwiseGroupFacts
