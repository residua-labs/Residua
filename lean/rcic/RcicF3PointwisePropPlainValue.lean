import rcic.RcicF3PointwisePropEvalValue
import rcic.RcicF3NormPropPlainValue

/-!
# Actual typed plain-Prop endpoint with the new predecessor

Indexed evaluation and the proof-spine equation retain actual stored minors,
full keys and motive levels. All family-prefix soundness is produced from
PointwiseRole.GInv. The checked family-free/no-functional-recursion face is
unchanged; no endpoint law at illtyped environments is asserted.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePropEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

/-- Evaluation existence and the proof-spine equation are both produced
from the actual admitted group; the selected row is retained literally. -/
theorem result_plain (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (C : Context) (hM : C.M = mkM P μ)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hBound : BoundG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (hN : NoFunRec C.node)
    (hfree : ∀ (j : Fin C.node.a.constructors.length) A,
      A ∈ (C.node.a.constructorViews j).fields →
      occursConst C.node.a.family.ref A = false)
    (v : Level)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors)
    (is : List PSet.{4}) (major : PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters)
    (his : TelFits C.M C.σ C.node.a.family.indices (push C.parameters ρ0) is)
    (hmajor : major ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (C.parameters ++ is)))
    (j : Fin C.node.a.constructors.length) :
    Eval C (key (C.parameters ++ is))
      (PropEvalValue.result C v (key (C.parameters ++ is))) ∧
    Equiv (PropEvalValue.result C v (key (C.parameters ++ is)))
      (fapps (C.minors.getD j.val pempty)
        ((C.node.a.constructorViews j).fields.map (fun _ => pempty))) := by
  have hs := result_spec P μ K C hM fm ctors hE hfam hctors hrec hmem hBound hPred α hα
    ctx plans hctx hplans hFaith hFamily fullvs hσfull hvs h0 hpolicy v
    hmo hminors is major hps his hmajor
  have hRaw : Admissible (famDataOf C.node.a) (base P μ C) :=
    (EvalPlanNormalProp.normalized_closed P μ (EvalPlan.ofNode C.node)
      fm ctors hE hmem C.σ h0 hpolicy).1
  have F := PointwiseGroupFacts.group_facts P K μ hE hfam hmem C.node
    hPred α hα ctx plans hctx hplans hFaith (base P μ C) hRaw hFamily
  have hplain := plain_shapes_of_free C (NormDPlanBridge.bodies_of_group hE hmem C.node)
    hN hfree
  exact ⟨hs.2.1, hs.2.1.plain_result_of_boundG C P μ K hE hfam hctors hrec hmem
    hBound hM h0 hpolicy (F.rawEnv C.σ C.node.a.family.member.arity)
    fullvs hσfull hvs hplain j⟩

/-- The production endpoint equation at the actual complete typed argument
tuple. The motive level is admission's level, including its extra slot. -/
theorem endValue_plain (P : Premises4)
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
    (fullvs : List Nat) (hvs : ∀ u, u ∈ fullvs → u ≤ K p.rr)
    (h0 : evalTotal (σOf fullvs) p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (hN : NoFunRec p.node)
    (hfree : ∀ (j : Fin p.node.a.constructors.length) A,
      A ∈ (p.node.a.constructorViews j).fields →
      occursConst p.node.a.family.ref A = false)
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4}) (major : PSet.{4})
    (hms : ms.length = p.node.a.constructors.length)
    (hps : TelFits (mkM P μ) (σOf fullvs) p.node.a.family.parameters ρ0 ps)
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf fullvs) (push ps ρ0)
      (policyMotiveType p.node.a.family p.node.a.policy)))
    (hminors : TelFits (mkM P μ) (σOf fullvs) p.node.a.minorTypes
      (vcons mo (push ps ρ0)) ms)
    (his : TelFits (mkM P μ) (σOf fullvs) p.node.a.family.indices (push ps ρ0) is)
    (hmajor : major ∈ Ed (mkM P μ) (fapps (μ p.node.a.family.ref
      ((canonL p.node.a.family.member.arity).map (evalTotal (σOf fullvs)))) (ps ++ is)))
    (j : Fin p.node.a.constructors.length) :
    Equiv (EvalPlanValue.endValue (mkM P μ) (σOf fullvs) p
      (push (ps ++ mo :: (ms ++ (is ++ [major]))) ρ0))
      (fapps (ms.getD j.val pempty)
        ((p.node.a.constructorViews j).fields.map (fun _ => pempty))) := by
  rw [EvalPlanValue.endValue_input (mkM P μ) (σOf fullvs) p ps mo ms is major ρ0
    h0 hpolicy hps.length hms his.length]
  let C := (EvalPlanValue.context p (mkM P μ) (σOf fullvs) ρ0).withValues ps mo ms hms
  exact (result_plain P μ K C rfl fm ctors hE hfam hctors hrec hmem hBound hPred α hα
    ctx plans hctx hplans hFaith hFamily fullvs rfl hvs h0 hpolicy hN hfree
    (policyMotiveLevel p.node.a.family.member.arity p.node.a.policy)
    hmo hminors is major hps his hmajor j).2

end Rcic.F3.PSet.PointwisePropEval
