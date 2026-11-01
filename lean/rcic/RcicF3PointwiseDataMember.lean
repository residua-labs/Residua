import rcic.RcicF3PointwiseDataRecMem
import rcic.RcicF3PointwiseDataPrefix

/-!
# Complete stored-member soundness from bounded pointwise candidates

The actual original constructor walk supplies ordinary reader soundness
before the recursor. Its invocation vectors reach the shared row bound
using the ORIGINAL selected D check. The new frame is globally admissible;
only local closure at those bounded worlds consumes LocalCandidates.

The stored recursor then uses produced density and the actual typed
motive/minors at the full valuation. Neither a reader callback nor current
recursor membership is an input to this complete producer. Parameter equality
is read from the unchanged check, not supplied independently. The bounded
local-candidate producer remains explicitly unpaid. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataMember
open Rcic.Declarative Rcic.Model.PS RawFamily

theorem sound_of_local_candidates (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hAg : ∀ node : RecNode E E' f rr rm,
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (hcheck : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none)
    (hLocal : PointwiseDataLocal.LocalCandidates P μ
      (EvalPlan.ofGroup hE hfam hctors hrec hmem) K)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    AllSound P μ K E' := by
  have hs := (Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hcheck
  have hPrefix := PointwiseDataPrefix.sound_of_local_candidates P μ K hE hfam hctors hrec hmem
    hAg hBound hPred α hα ctx plans hctx hplans hFaith hcheck hLocal hType
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E :=
    fun r m hm => hFaith r m (groupMembersT_preserve hmem r m hm)
  have hR := PointwiseDataRecMem.member_sound P μ K hE hfam hctors hrec hmem
    hBound hBoundD hs.1 hPred α hα ctx plans hctxE hplansE hFaithE
    ctx plans hctx hplans hFaith hType
    (fun fullvs _ _ => hPrefix.2 (σOf fullvs) _)
  have hrm : E'.members rr = some rm := groupMembersT_installed hmem
    (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  intro r m hm
  by_cases hr : r = rr
  · subst r
    have hm' : m = rm := Option.some.inj (hm.symm.trans hrm)
    subst m
    exact hR
  · exact hPrefix.1 r m hm hr

/-- The original stored recursor member is a consequence of the complete
member producer, with its reader supplied by the preceding actual walk. -/
theorem member_sound_of_local_candidates (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hAg : ∀ node : RecNode E E' f rr rm,
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E')
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E' r → ctx r = NormRole.envCtx
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hplans : ∀ r, Dom E' r → plans r = EvalRole.envPlan
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E')
    (hcheck : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none)
    (hLocal : PointwiseDataLocal.LocalCandidates P μ
      (EvalPlan.ofGroup hE hfam hctors hrec hmem) K)
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel) :
    MemberSound P μ K rr rm :=
  sound_of_local_candidates P μ K hE hfam hctors hrec hmem hAg hBound hBoundD hPred
    α hα ctx plans hctx hplans hFaith hcheck hLocal hType rr rm
    (groupMembersT_installed hmem
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))))

end Rcic.F3.PSet.PointwiseDataMember
