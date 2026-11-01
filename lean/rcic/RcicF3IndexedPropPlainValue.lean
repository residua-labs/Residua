import rcic.RcicF3IndexedPropEvalValue
import rcic.RcicF3NormPropPlainValue

/-!
# Produced plain endpoint at the actual constructor result key

The result indices below are read from the selected original constructor
view at the actual fitting field tuple. Evaluation existence is produced
from BoundGIndexed and the actual pointwise predecessor. The safe-index
comparison then yields the stored minor applied to those actual fields;
there is no all-fields Prop premise and no erasure of revealed data.

This proves an endpoint at the literal constructor result key. It does not
assert that a legacy redex's freely supplied recursor index arguments have
that key. Their equality must be produced from the typed redex before this
module can supply a general plain IotaAt consumer.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.IndexedPropEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

/-- The actual result-index expressions, read after parameters and fields. -/
noncomputable def fieldResultIndices (M : Interp.{4}) (σ : Nat → Nat)
    (ps xs : List PSet.{4}) (Is : List (Expr Nat)) : List PSet.{4} :=
  Is.map (den M σ (push xs (push ps ρ0)))

/-- Produce evaluation and the actual-field minor equation at the literal
constructor key. No comparison or key-equality callback is assumed. -/
theorem result_plain_at_fields (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (C : Context) (hM : C.M = mkM P μ)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hBound : IndexedFieldBounds.BoundGIndexed K
      (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E' hE hfam hctors hrec hmem))
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
    (j : Fin C.node.a.constructors.length) (xs : List PSet.{4}) (major : PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters)
    (hxs : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs)
    (his : TelFits C.M C.σ C.node.a.family.indices (push C.parameters ρ0)
      (fieldResultIndices C.M C.σ C.parameters xs (C.node.a.constructorViews j).resultIndices))
    (hmajor : major ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (C.parameters ++ fieldResultIndices C.M C.σ C.parameters xs
        (C.node.a.constructorViews j).resultIndices))) :
    Eval C (key (C.parameters ++ fieldResultIndices C.M C.σ C.parameters xs
      (C.node.a.constructorViews j).resultIndices))
      (PropEvalValue.result C v (key (C.parameters ++ fieldResultIndices C.M C.σ
        C.parameters xs (C.node.a.constructorViews j).resultIndices))) ∧
    Equiv (PropEvalValue.result C v (key (C.parameters ++ fieldResultIndices C.M C.σ
      C.parameters xs (C.node.a.constructorViews j).resultIndices)))
      (fapps (C.minors.getD j.val pempty) xs) := by
  let is := fieldResultIndices C.M C.σ C.parameters xs
    (C.node.a.constructorViews j).resultIndices
  have hs := result_spec P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hPred α hα ctx plans hctx hplans hFaith hFamily fullvs hσfull hvs
    h0 hpolicy v hmo hminors is major hps his hmajor
  have hRaw : Admissible (famDataOf C.node.a) (base P μ C) :=
    (EvalPlanNormalProp.normalized_closed P μ (EvalPlan.ofNode C.node)
      fm ctors hE hmem C.σ h0 hpolicy).1
  have F := PointwiseGroupFacts.group_facts P K μ hE hfam hmem C.node
    hPred α hα ctx plans hctx hplans hFaith (base P μ C) hRaw hFamily
  have hplain := plain_shapes_of_free C (NormDPlanBridge.bodies_of_group hE hmem C.node)
    hN hfree
  have hRows : ∀ i : Fin C.node.a.constructors.length,
      PropEvalSafeIndex.UnrevealedBounds (extendEnv C.E C.f fm)
        C.node.a.family.member.arity C.σ K C.node.a.family.parameters
        (C.node.a.constructorViews i).fields (C.node.a.constructorViews i).resultIndices := by
    intro i
    rw [hσfull]
    exact (hBound.2.2.2 C.node (selection_prop C.node.a C.σ h0 hpolicy).1
      hpolicy i fullvs hvs).unrevealed
  exact ⟨hs.2.1, PropEvalSafeIndex.plain_result_at_fields_of_bounds C P μ K
    (extendEnv C.E C.f fm) C.node.a.family.member.arity hM h0 hpolicy
    (F.rawEnv C.σ C.node.a.family.member.arity) hRows hplain j C.parameters xs
    hps hxs hs.2.1 rfl⟩

/-- The actual installed endpoint at the constructor result indices. Its
minor receives the fitting fields unchanged, including revealed data. -/
theorem endValue_plain_at_fields (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hBound : IndexedFieldBounds.BoundGIndexed K
      (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E' hE hfam hctors hrec hmem))
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
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms : List PSet.{4}) (major : PSet.{4})
    (hms : ms.length = p.node.a.constructors.length)
    (hps : TelFits (mkM P μ) (σOf fullvs) p.node.a.family.parameters ρ0 ps)
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf fullvs) (push ps ρ0)
      (policyMotiveType p.node.a.family p.node.a.policy)))
    (hminors : TelFits (mkM P μ) (σOf fullvs) p.node.a.minorTypes
      (vcons mo (push ps ρ0)) ms)
    (j : Fin p.node.a.constructors.length) (xs : List PSet.{4})
    (hxs : TelFits (mkM P μ) (σOf fullvs) (p.node.a.constructorViews j).fields
      (push ps ρ0) xs)
    (his : TelFits (mkM P μ) (σOf fullvs) p.node.a.family.indices (push ps ρ0)
      (fieldResultIndices (mkM P μ) (σOf fullvs) ps xs
        (p.node.a.constructorViews j).resultIndices))
    (hmajor : major ∈ Ed (mkM P μ) (fapps (μ p.node.a.family.ref
      ((canonL p.node.a.family.member.arity).map (evalTotal (σOf fullvs))))
      (ps ++ fieldResultIndices (mkM P μ) (σOf fullvs) ps xs
        (p.node.a.constructorViews j).resultIndices))) :
    Equiv (EvalPlanValue.endValue (mkM P μ) (σOf fullvs) p
      (push (ps ++ mo :: (ms ++
        (fieldResultIndices (mkM P μ) (σOf fullvs) ps xs
          (p.node.a.constructorViews j).resultIndices ++ [major]))) ρ0))
      (fapps (ms.getD j.val pempty) xs) := by
  rw [EvalPlanValue.endValue_input (mkM P μ) (σOf fullvs) p ps mo ms _ major ρ0
    h0 hpolicy hps.length hms his.length]
  let C := (EvalPlanValue.context p (mkM P μ) (σOf fullvs) ρ0).withValues ps mo ms hms
  exact (result_plain_at_fields P μ K C rfl fm ctors hE hfam hctors hrec hmem
    hBound hPred α hα ctx plans hctx hplans hFaith hFamily fullvs rfl hvs h0 hpolicy
    hN hfree (policyMotiveLevel p.node.a.family.member.arity p.node.a.policy)
    hmo hminors j xs major hps hxs his hmajor).2

end Rcic.F3.PSet.IndexedPropEval

#print axioms Rcic.F3.PSet.IndexedPropEval.result_plain_at_fields
#print axioms Rcic.F3.PSet.IndexedPropEval.endValue_plain_at_fields
