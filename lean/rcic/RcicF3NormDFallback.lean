import rcic.RcicF3NormDFaith
import rcic.RcicF3NormDGroup

/-!
# Produced normalized D group step on the data/propOnly fallback face

The actual admitted plan supplies the finite-family package and installed
value equations. The new predecessor invariant is reapplied to its actual
role and plan prefixes to produce every bounded D stage. The existing
selected-node D conditions then compose these components into the new
group invariant.

This is the A-negative data/propOnly branch. It adds no check and assumes
no family comparison, frame closure, endpoint-typing callback, or legacy
invariant. Prop/anySort and the positive-depth A producer remain separate
branches of the unchanged target. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.NormDFallback
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder RawFamily

/-- The existing D conditions at the selected node suffice for this face.
All semantic component inputs of the at-table kernel are produced here. -/
theorem group_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hN : NoFunRec (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hside : StepDGSide K (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hFallback : ¬ (UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel ∧
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)) :
    NormRole.GroupStepAt P K hE hfam hctors hrec hmem := by
  intro hAg hB hD hPred ctx hctx plans hplans μ hFaith
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hsub : ∀ r m, E.members r = some m → E'.members r = some m :=
    groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful role P μ ctx plans E :=
    fun r m hm => hFaith r m (hsub r m hm)
  have hPrior := hPred ctx hctxE plans hplansE μ hFaithE
  have hfm := NormDFaith.family_member_sound P μ hE hfam hctors hrec hmem
    ctx plans hctx hFaith hN K
  have D := NormDStage.stage_of_invariant hE hfam hctors hrec hmem p.node hN
    hside.1 hB.1 (hD.2 p.node) hPred ctx hctxE plans hplansE μ hFaithE hfm
  have hlim := NormDFaith.family_limit P μ hE hfam hctors hrec hmem
    ctx plans hctx hFaith hN
  have hG := NormDFaith.group_faith P μ K hE hfam hctors hrec hmem
    ctx plans hctx hplans hFaith hN hFallback D
  exact NormDGroup.at_table P K hE hfam hctors hrec hmem p.node hN
    hside.1 hside.2.1 hside.2.2 hAg hB hD μ hPrior hlim hfm D hG

/-- The executable check is exactly the already declared selected-node
condition. The negative A branch and fallback case introduce no new check. -/
theorem group_step_of_check (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hp : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none)
    (hAn : ¬ ∃ node : RecNode E E' f rr rm, PendA node)
    (hFallback : ¬ (UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel ∧
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .anySort)) :
    NormRole.GroupStepAt P K hE hfam hctors hrec hmem :=
  group_step P K hE hfam hctors hrec hmem
    (noFunRec_of_not_pendA (fun h => hAn ⟨_, h⟩))
    ((Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hp)
    hFallback

end Rcic.F3.PSet.NormDFallback
