import rcic.RcicF3IndexedPropEvalTotal
import rcic.RcicF3NormPropEvalValue

/-!
# Typed evaluation values under the separate indexed bound

Evaluation existence is produced by normalized candidate closure.
Functionality is produced from bare result-index key equality and typed
Prop bounds on unrevealed fields. The scalar specification retains the
actual dependent motive and the recursor's extra universe slot. Only the
family prefix is made sound; completed-group EnvSound is not a premise.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal. The actual same-P
AccR composition witness is in RcicF3IndexedPropEvalAttack. Plain iota and
modern recursive shape-schema iota remain separate consumer obligations.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.IndexedPropEval
open Rcic.Declarative PiIndex RawFamily RawFamilyRec PropEval PropEvalCandidate
open NormPropEval (base major_at_frame frame_inputs)

/-- Existence, guarded typing and functionality are all produced from the
actual admitted group and typed recursor arguments. The output contains
the evaluation and its exact requested dependent motive membership. -/
theorem result_spec (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (C : Context) (hM : C.M = mkM P μ)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hBound : IndexedFieldBounds.BoundGIndexed K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
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
      (C.parameters ++ is))) :
    PropEvalValue.result C v (key (C.parameters ++ is)) ∈
        childCarrier C v (key (C.parameters ++ is)) ∧
    Eval C (key (C.parameters ++ is)) (PropEvalValue.result C v (key (C.parameters ++ is))) ∧
    PropEvalValue.result C v (key (C.parameters ++ is)) ∈
        Ed C.M (fapps C.motive (is ++ [major])) := by
  have hRaw : Admissible (famDataOf C.node.a) (base P μ C) :=
    (EvalPlanNormalProp.normalized_closed P μ (EvalPlan.ofNode C.node)
      fm ctors hE hmem C.σ h0 hpolicy).1
  have F := PointwiseGroupFacts.group_facts P K μ hE hfam hmem C.node
    hPred α hα ctx plans hctx hplans hFaith (base P μ C) hRaw hFamily
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  have hmajorR := major_at_frame P μ C hM F.bounded hFamily hRaw is major hps his hmajor
  have hkey : paramKey C.node.a.family.parameters.length (key (C.parameters ++ is)) =
      key C.parameters := by
    rw [← hps.length]
    exact paramKey_append C.parameters is
  have hex := normalized_evaluates P μ K C hM fm ctors hE hfam hctors hrec hmem hBound hPred α hα ctx plans hctx hplans hFaith hFamily fullvs hσfull hvs h0 hpolicy v hmo hminors vs
    (key (C.parameters ++ is)) major hmajorR (canonical_agreement C) hkey
  obtain ⟨_, _, _, hProp⟩ := frame_inputs P μ C hM F.bounded (base P μ C) hFamily hRaw h0
  have hU : C.M.U = U W4 := by rw [hM]; rfl
  have hguard : ∀ i z, Eval C i z → z ∈ childCarrier C v i := by
    intro i z hz
    exact hz.mem_guarded_of_typed_motive v hU hmo hProp
  have hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z' := by
    intro i z z' hz hz'
    exact IndexedFieldBounds.functional_of_boundIndexed C P μ K hE hfam hctors hrec hmem hBound
      hM h0 hpolicy (F.rawEnv C.σ C.node.a.family.member.arity)
      fullvs hσfull hvs hz hz'
  have hs := PropEvalValue.result_spec C v (key (C.parameters ++ is)) hex
    (hguard _) (hfunctional _)
  have hproof : Equiv major pempty := hProp (C.parameters ++ is)
    (by rw [List.length_append, hps.length, his.length]) major hmajor
  exact ⟨hs.1, hs.2, PropEvalValue.result_mem_motive C v is major hU hps.length
    hmo his hmajor hproof hs.1⟩

end Rcic.F3.PSet.IndexedPropEval
