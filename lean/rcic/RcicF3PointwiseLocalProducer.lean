import rcic.RcicF3PointwiseFieldMasks
import rcic.RcicF3PointwiseADataChecked

/-!
# Actual checked groups produce their bounded local DATA candidates

The selected-node D check supplies the literal own/family parameter
equality. The complete faithful table and its arity, context and plan
metadata are restricted to the actual predecessor; its pointwise invariant
then pays the reader and both original fitting models used by the bounded
field-mask producer. That producer constructs the small candidate before
its closure at the reached world is invoked.

The universal conclusion is exactly LocalCandidatesChecked on its original
selected DATA, existential PendA and executable-check domain. No frame,
mask, reader provenance, normalized typing or invariant-conversion premise
is added. The old unbounded interpretations and targets are unchanged.
This source composition is not a native or RCC verdict. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseLocalProducer
open Rcic.Declarative Rcic.Model.PS Rcic.F3.StepDGOrder

/-- Every faithful-table instance of the original checked group has the
required local candidates at its actual bounded family worlds. -/
theorem local_candidates_at (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hType : UniformType (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hcheck : Rcic.F3.StepWDApex.groupCheck K hE hfam hctors hrec hmem = none) :
    PointwiseDataGroup.LocalCandidatesAt P K hE hfam hctors hrec hmem := by
  intro _hAg hB hD hPred α hα ctx hctx plans hplans μ hFaith
  let p := EvalPlan.ofGroup hE hfam hctors hrec hmem
  have hside : StepDGSide K p.node :=
    (Rcic.F3.StepWDApex.groupCheck_pass_iff K hE hfam hctors hrec hmem).mp hcheck
  have hsub : ∀ r m, E.members r = some m → E'.members r = some m :=
    groupMembersT_preserve hmem
  have hαE : PointwiseRole.AritiesAgree α E := hα.mono hsub
  have hctxE : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r := fun r hr =>
    (hctx r (dom_groupMembersT hmem hr)).trans
      (NormRole.envCtx_group_stable hE hfam hctors hrec hmem r hr)
  have hplansE : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r := fun r hr =>
    (hplans r (dom_groupMembersT hmem hr)).trans
      (EvalRole.envPlan_group_stable hE hfam hctors hrec hmem r hr)
  have hFaithE : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E :=
    fun r m hm => hFaith r m (hsub r m hm)
  exact PointwiseFieldMasks.local_candidates P μ K p fm ctors
    hE hfam hctors hrec hmem hB hD hside.1 hPred
    α hαE ctx plans hctxE hplansE hFaithE hType

/-- The exact original checked positive-depth DATA obligation is produced.
The existential PendA domain is retained literally in the conclusion. -/
theorem localCandidatesChecked (P : Premises4) (K : Nat → Nat) :
    PointwiseADataChecked.LocalCandidatesChecked P K := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem hType _hPend hcheck
  exact local_candidates_at P K hE hfam hctors hrec hmem hType hcheck

/-- Actual stored constructors, recursor membership and stable legacy iota
consume the produced local candidates through the existing checked step. -/
theorem stepADataChecked (P : Premises4) (K : Nat → Nat) :
    PointwiseADataChecked.StepADataChecked P K :=
  PointwiseADataChecked.stepADataChecked_of_localCandidates P K
    (localCandidatesChecked P K)

end Rcic.F3.PSet.PointwiseLocalProducer
