import rcic.RcicF3NormPropParamEvalTotal
import rcic.RcicF3NormPropEvalValue

/-!
# Literal erased result from produced Prop evaluation

The actual major lies in the selected normalized frame. Produced candidate
leastness supplies its evaluation and typed guarding puts the output in
its exact requested Prop motive. Erasure identifies that output with the
literal production value. The existing parameter-telescope equality is
retained; unchecked arbitrary parameter mirrors remain open.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropParamEval
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
    (hpar : ∀ j : Fin C.node.a.constructors.length,
      (C.node.a.constructorViews j).parameters = C.node.a.family.parameters)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans C.E)
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
  have h0 := hProp C.σ
  have hRaw : Admissible (famDataOf C.node.a) (base P μ C) :=
    (NormPropCtorUniform.normalized_closed P μ (EvalPlan.ofNode C.node)
      fm ctors hE hmem hProp).1
  have F := NormCandidatePrefix.group_facts P K μ hE hfam hmem C.node
    hPred ctx plans hctx hplans hFaith (base P μ C) hRaw hFamily
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  have hmajorR := NormPropEval.major_at_frame P μ C hM F.bounded hFamily hRaw is major hps his hmajor
  have hkey : RawFamilyRec.paramKey C.node.a.family.parameters.length (key (C.parameters ++ is)) =
      key C.parameters := by
    rw [← hps.length]
    exact RawFamilyRec.paramKey_append C.parameters is
  have hex := normalized_evaluates P μ K C hM fm ctors hE hfam hctors hrec hmem hBound hBoundD hpar hPred ctx plans hctx hplans hFaith hFamily fullvs hσfull hvl hvs hProp hmo hminors vs
    (key (C.parameters ++ is)) major hmajorR (canonical_agreement C) hkey
  obtain ⟨_, _, _, hProof⟩ := NormPropEval.frame_inputs P μ C hM F.bounded (base P μ C) hFamily hRaw h0
  have hU : C.M.U = U W4 := by rw [hM]; rfl
  have hguard : ∀ i z, Eval C i z → z ∈ childCarrier C .zero i := by
    intro i z hz
    exact hz.mem_guarded_of_typed_motive .zero hU hmo hProof
  have hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z' := by
    intro i z z' hz hz'
    exact PropEvalProof.functional C hU hmo hProof hz hz'
  have hs := PropEvalValue.result_spec C .zero (key (C.parameters ++ is)) hex
    (hguard _) (hfunctional _)
  have hproof : Equiv major pempty := hProof (C.parameters ++ is)
    (by rw [List.length_append, hps.length, his.length]) major hmajor
  exact mem_congr_left (PropEvalProof.output_prop C hU hmo hProof hs.2)
    (PropEvalValue.result_mem_motive C .zero is major hU hps.length
      hmo his hmajor hproof hs.1)

end Rcic.F3.PSet.NormPropParamEval
