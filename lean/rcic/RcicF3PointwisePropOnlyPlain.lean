import rcic.RcicF3PointwisePropOnlyPipeline

/-!
# Original-bound PropOnly groups with plain admitted field shapes

All-plain admission makes the cached normalized field telescope literally
its original field telescope. Family-freedom then transports its actual
fitting tuple between arbitrary family candidates. No parameter-mirror
comparison or bounded mirror conversion is required on this face.

This producer follows that concrete tuple theorem through constructor
closure, evaluation totality, stored recursor membership, the original
stable IotaAt clause, and the pointwise group invariant. Both original
BoundG and BoundDG remain unchanged. Recursive PropOnly rows are outside
this additive producer and retain the existing mirror/reader obligation.
closure_claim = 0.
-/
/- Evaluation, recursor membership and invariant assembly are shared
through PointwisePropOnlyPipeline; this file constructs its field boundary
from the same syntax hypothesis carried by every public endpoint. -/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePropOnlyPlainFields
open Rcic.Declarative RawFamily

/-- The actual cached field list is the original list when every admitted
shape is plain. This conclusion uses the same original node and cache. -/
theorem normalized_fields (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hplain : PropShapeCoverage.AllPlain p.node)
    (j : Fin p.node.a.constructors.length) :
    EvalPlanNormal.fields p j = (p.node.a.constructorViews j).fields := by
  rw [NormDPlanBridge.normalized_fields p
    (NormDPlanBridge.bodies_of_group hE hmem p.node)
    (PropShapeCoverage.all_plain_noFun hplain) j]
  calc
    ((p.node.a.constructorViews j).fields.map
        (normField p.node.E0 (p.node.h14.fuelAt j) p.node.a.family.ref)) =
        (p.node.a.constructorViews j).fields.map id := by
      apply List.map_congr_left
      intro A hA
      exact normField_free (E := p.node.E0) (fuel := p.node.h14.fuelAt j)
        (PropShapeCoverage.all_plain_fields_free hplain j A hA)
    _ = (p.node.a.constructorViews j).fields := List.map_id _

/-- Every actual plain tuple is retained at the same values, local
prefix, valuation and full descriptor. No own-parameter Fits is needed. -/
theorem fields_to_raw (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hplain : PropShapeCoverage.AllPlain p.node)
    (X D : Frame) (j : Fin p.node.a.constructors.length)
    (ρ : Nat → PSet.{4}) (xs : List PSet.{4})
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) X)) σ
      (EvalPlanNormal.fields p j) ρ xs) :
    TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      (p.node.a.constructorViews j).fields ρ xs := by
  rw [normalized_fields p fm ctors hE hmem hplain j] at hxs
  exact (PiIndependent.telFits_free P μ (famDataOf p.node.a).fref
    (ofFrame P μ (famDataOf p.node.a) X)
    (ofFrame P μ (famDataOf p.node.a) D) σ
    (p.node.a.constructorViews j).fields
    (PropShapeCoverage.all_plain_fields_free hplain j) ρ xs).mp hxs


/-- The original plain-field syntax pays the shared internal boundary. -/
theorem field_transport (P : Premises4)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (hplain : PropShapeCoverage.AllPlain node) :
    PointwisePropOnlyPipeline.FieldTransport P node := by
  intro μ σ fm ctors hE hmem α ctx plans hctx hFaith X D hX hD hsub j ps xs hps hxs
  exact fields_to_raw P μ σ (EvalPlan.ofNode node) fm ctors hE hmem hplain
    X D j (push ps ρ0) xs hxs

end Rcic.F3.PSet.PointwisePropOnlyPlainFields


namespace Rcic.F3.PSet.PointwisePropOnlyPlainEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

theorem constructor_step (P : Premises4)
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
    (hBoundD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hplain : PropShapeCoverage.AllPlain C.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvl : fullvs.length = C.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (hProp : UniformProp C.node.a.family.resultLevel)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors) :
    ∀ vs i z, CtorAt P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
      (NormPropEval.candidate P μ C) vs i z → EvalPredicate C vs i z := by
  exact PointwisePropOnlyPipeline.Eval.constructor_step P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyPlainFields.field_transport P _ hplain) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hσfull hvl hvs hProp hmo hminors

end Rcic.F3.PSet.PointwisePropOnlyPlainEval

namespace Rcic.F3.PSet.PointwisePropOnlyPlainEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

/-- Plain-field composition produces candidate admissibility and global
constructor closure for the actual normalized operator. -/
theorem candidate_closed (P : Premises4)
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
    (hBoundD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hplain : PropShapeCoverage.AllPlain C.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvl : fullvs.length = C.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (hProp : UniformProp C.node.a.family.resultLevel)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors) :
    Admissible (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) (NormPropEval.candidate P μ C) ∧
    Closed P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) (NormPropEval.candidate P μ C) := by
  exact PointwisePropOnlyPipeline.Eval.candidate_closed P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyPlainFields.field_transport P _ hplain) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hσfull hvl hvs hProp hmo hminors

/-- Every normalized member produces evaluation at the complete key
once the actual valuation and parameter guard are supplied. -/
theorem normalized_evaluates (P : Premises4)
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
    (hBoundD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hplain : PropShapeCoverage.AllPlain C.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvl : fullvs.length = C.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (hProp : UniformProp C.node.a.family.resultLevel)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors) :
    ∀ vs i z, z ∈ base P μ C vs i → EvalPredicate C vs i z := by
  exact PointwisePropOnlyPipeline.Eval.normalized_evaluates P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyPlainFields.field_transport P _ hplain) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hσfull hvl hvs hProp hmo hminors

end Rcic.F3.PSet.PointwisePropOnlyPlainEval

namespace Rcic.F3.PSet.PointwisePropOnlyPlainEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

/-- Produced totality and typed guarding justify the literal erased value
in the exact requested dependent Prop motive. -/
theorem empty_mem (P : Premises4)
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
    (hBoundD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hplain : PropShapeCoverage.AllPlain C.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a) (base P μ C) vs))
    (fullvs : List Nat) (hσfull : C.σ = σOf fullvs)
    (hvl : fullvs.length = C.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K C.rr)
    (hProp : UniformProp C.node.a.family.resultLevel)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors)
    (is : List PSet.{4}) (major : PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters)
    (his : TelFits C.M C.σ C.node.a.family.indices (push C.parameters ρ0) is)
    (hmajor : major ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (C.parameters ++ is))) :
    pempty ∈ Ed C.M (fapps C.motive (is ++ [major])) := by
  exact PointwisePropOnlyPipeline.Eval.empty_mem P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyPlainFields.field_transport P _ hplain) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hσfull hvl hvs hProp hmo hminors is major hps his hmajor

end Rcic.F3.PSet.PointwisePropOnlyPlainEval

namespace Rcic.F3.PSet.PointwisePropOnlyPlainRecMem
open Rcic.Declarative Rcic.Model.PS RawFamily PropEval

/-- At every bounded full recursor vector, the actual new abstraction is a
member of the actual stored type. Its end obligation is produced inside
this proof from the typed group and the repaired predecessor invariant. -/
theorem memberValue_mem (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hBound : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hplain : PropShapeCoverage.AllPlain p.node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α p.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom p.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hFamily : ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (famDataOf p.node.a)
        (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode p.node))) vs))
    (fullvs : List Nat) (hvl : fullvs.length = p.node.a.family.member.arity)
    (hvs : ∀ u, u ∈ fullvs → u ≤ K p.rr)
    (hProp : UniformProp p.node.a.family.resultLevel)
    (hpolicy : p.node.a.policy = .propOnly) :
    EvalPlanValue.memberValue (mkM P μ) (σOf fullvs) p p.rm ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf fullvs) ρ0 p.rm.mtype) := by
  exact PointwisePropOnlyPipeline.RecMem.memberValue_mem P μ K p fm ctors hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyPlainFields.field_transport P _ hplain) hPred α hα ctx plans hctx hplans hFaith
    hFamily fullvs hvl hvs hProp hpolicy

/-- The canonical new recursor is sound on the uniformly Prop/propOnly
plain-field face. Both equations are read from the actual admitted group
and faithful table; the original bound packages retain their literal types. -/
theorem member_sound (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hplain : PropShapeCoverage.AllPlain (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly) :
    MemberSound P μ K rr rm := by
  exact PointwisePropOnlyPipeline.RecMem.member_sound P μ K hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyPlainFields.field_transport P _ hplain) hPred α hα ctx plans hctx hplans hFaith
    ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy

end Rcic.F3.PSet.PointwisePropOnlyPlainRecMem

namespace Rcic.F3.PSet.PointwisePropOnlyPlainIota
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- The produced plain-field membership composes with the already-general
PropOnly stable IotaAt theorem at the same actual pointwise table. -/
theorem rec_pkg (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hBound : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hplain : PropShapeCoverage.AllPlain (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans E)
    (ctxFull : Nat → Role) (plansFull : EvalRole.Plans)
    (hctxFull : ∀ r, Dom E' r →
      ctxFull r = NormRole.envCtx (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hplansFull : ∀ r, Dom E' r →
      plansFull r = EvalRole.envPlan (EnvWfT.group E f fm ctors rr rm E'
        hE hfam hctors hrec hmem) r)
    (hFaithFull : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctxFull plansFull E')
    (hProp : UniformProp (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly) :
    RecPkg P μ K E' rr rm := by
  exact PointwisePropOnlyPipeline.Iota.rec_pkg P μ K hE hfam hctors hrec hmem
    hBound hBoundD (PointwisePropOnlyPlainFields.field_transport P _ hplain) hPred α hα ctx plans hctx hplans hFaith
    ctxFull plansFull hctxFull hplansFull hFaithFull hProp hpolicy

end Rcic.F3.PSet.PointwisePropOnlyPlainIota

namespace Rcic.F3.PSet.PointwisePropOnlyPlainGroup
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- Complete group composition on the admitted plain-field face, with
arbitrary constructor parameter mirrors and the original bound packages. -/
theorem group_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (hplain : PropShapeCoverage.AllPlain (EvalPlan.ofGroup hE hfam hctors hrec hmem).node) :
    PointwiseDataGroup.GroupStepAt P K hE hfam hctors hrec hmem := by
  exact PointwisePropOnlyPipeline.Group.group_step P K hE hfam hctors hrec hmem hProp hpolicy (PointwisePropOnlyPlainFields.field_transport P _ hplain)

/-- Uniform Prop admission pays the walk premise at every RecNode, so
this invariant step has neither a W check nor a D check. -/
theorem invariant_step (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hProp : UniformProp
      (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.family.resultLevel)
    (hpolicy : (EvalPlan.ofGroup hE hfam hctors hrec hmem).node.a.policy = .propOnly)
    (hplain : PropShapeCoverage.AllPlain (EvalPlan.ofGroup hE hfam hctors hrec hmem).node)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hPred : PointwiseRole.GInv P K hE) :
    PointwiseRole.GInv P K
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) := by
  exact PointwisePropOnlyPipeline.Group.invariant_step P K hE hfam hctors hrec hmem hProp hpolicy (PointwisePropOnlyPlainFields.field_transport P _ hplain)
    hB hD hPred

end Rcic.F3.PSet.PointwisePropOnlyPlainGroup

#print axioms Rcic.F3.PSet.PointwisePropOnlyPlainFields.fields_to_raw
#print axioms Rcic.F3.PSet.PointwisePropOnlyPlainEval.constructor_step
#print axioms Rcic.F3.PSet.PointwisePropOnlyPlainEval.normalized_evaluates
#print axioms Rcic.F3.PSet.PointwisePropOnlyPlainRecMem.member_sound
#print axioms Rcic.F3.PSet.PointwisePropOnlyPlainIota.rec_pkg
#print axioms Rcic.F3.PSet.PointwisePropOnlyPlainGroup.invariant_step
