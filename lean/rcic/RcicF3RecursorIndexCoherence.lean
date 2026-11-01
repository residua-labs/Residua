import rcic.RcicF3RecursorFieldArguments
import rcic.RcicF3PropEvalIndexFromBound

/-!
# Supplied-index coherence from the actual original bounded redex

The installed recursor recovers its complete dependent argument spine.
The same-target memberships and its nonempty left application recover the
original constructor fields through the executable selected minor, including
the inserted direct-recursive IH binders. The unchanged BoundG proof-field
typings then compare that tuple with the constructor presentation produced
by the evaluation theorem at the supplied key.

Every semantic field and index premise below is produced. No source CtxWfT,
ScopeCheck, NoFunRec, allplain classification, completed-group EnvSound, or
additional coherence hypothesis is required.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.RecursorFieldArguments
open Rcic.Declarative Rcic.Model.PS PiIndex RawFamily PropEval

/-- Complete argument production and supplied/result-index agreement for
the actual selected legacy redex in the original bounded Prop face. -/
theorem coherent_arguments_of_nonempty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hBound : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hFamily : ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (famDataOf p.node.a)
        (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node))) vs))
    (hRec : ∀ vs, Equiv (μ p.rr vs)
      (EvalPlanValue.memberValue (mkM P μ) (σOf vs) p p.rm))
    {S : ResolvedEnv} (w : IotaWitness S)
    (hwr : w.recRef = p.rr) (hm : w.recMember = p.rm)
    (j : Fin p.node.a.constructors.length) (hj : w.ctorIdx = j.val)
    (hcm : w.ctorMember = p.node.a.constructors[j.val])
    (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (h0 : evalTotal (RecArguments.valuation w σ) p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (hvs : ∀ u, u ∈ w.ls.map (evalTotal σ) → u ≤ K p.rr)
    {X : PSet.{4}}
    (ml : den (mkM P μ) σ ρ (iotaLhsOf w) ∈ Ed (mkM P μ) X)
    (mr : den (mkM P μ) σ ρ (iotaRhsOf w) ∈ Ed (mkM P μ) X)
    (hne : ¬ Equiv (den (mkM P μ) σ ρ (iotaLhsOf w)) pempty) :
    ∃ ps mo ms is, RecArguments.Arguments (mkM P μ) p w σ ρ ps mo ms is ∧
      TelFits (mkM P μ) (RecArguments.valuation w σ)
        (p.node.a.constructorViews j).fields (push ps ρ0)
        (w.fields.map (den (mkM P μ) σ ρ)) ∧
      LEq is ((p.node.a.constructorViews j).resultIndices.map
        (den (mkM P μ) (RecArguments.valuation w σ)
          (push (w.fields.map (den (mkM P μ) σ ρ)) (push ps ρ0)))) := by
  obtain ⟨ps, mo, ms, is, ha, hf⟩ :=
    arguments_with_fields_of_nonempty (mkM P μ) p fm ctors hE hmem hRec
      w hwr hm j hj hcm σ ρ ml mr hne
  refine ⟨ps, mo, ms, is, ha, hf, ?_⟩
  let C := (EvalPlanValue.context p (mkM P μ) (RecArguments.valuation w σ) ρ0).withValues
    ps mo ms ha.minors_length
  exact PointwisePropEval.result_indices_of_boundG P μ K C rfl fm ctors
    hE hfam hctors hrec hmem hBound hPred α hα ctx plans hctx hplans hFaith
    hFamily (w.ls.map (evalTotal σ)) rfl hvs h0 hpolicy
    (policyMotiveLevel p.node.a.family.member.arity p.node.a.policy)
    ha.motive_fit ha.minors_fit is (den (mkM P μ) σ ρ (ctorMajor w))
    ha.parameters_fit ha.indices_fit ha.major_fit j
    (w.fields.map (den (mkM P μ) σ ρ)) hf

end Rcic.F3.PSet.RecursorFieldArguments

#print axioms Rcic.F3.PSet.RecursorFieldArguments.coherent_arguments_of_nonempty
