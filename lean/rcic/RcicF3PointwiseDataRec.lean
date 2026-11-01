import rcic.RcicF3PointwiseDataCases
import rcic.RcicF3NormDataRec

/-!
# The existing arbitrary-frame DATA recursor at the new interpretation

Original constructor cases are produced from pointwise density and the
new predecessor. The existing well-founded DATA engine consumes them with
the actual stored motive/minors and typed IH. No closed-frame or local
candidate-existence input is added. The ordinary reader and actual typed
input tuple remain literal component inputs; their bounded constructor
prefix production is a separate obligation. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataRec
open Rcic.Declarative PiIndex RawFamily PropEval

theorem nodeCore_guarded (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (C : Context)
    (hM : C.M = mkM P (RawFamily.table P μ (famDataOf C.node.a)
      (PointwiseDataCases.frame P μ C.node)))
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
    (hPred : PointwiseRole.GInv P K hE)
    (α : PointwiseRole.Arities) (hα : PointwiseRole.AritiesAgree α C.E)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans C.E)
    (hvs : ∀ u, u ∈ (canonL C.node.a.family.member.arity).map (evalTotal C.σ) → u ≤ K C.rr)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0)
    {n : Nat} (hReader : EnvSound C.M C.σ K C.node.E0 n)
    (v : Level) (hps : C.parameters.length = C.node.a.family.parameters.length)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors)
    (hctor : ∀ (j : Fin C.node.a.constructors.length) xs,
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push C.parameters ρ0) xs →
      Equiv (C.constructorAt j C.parameters xs) (dataVal j.val xs)) :
    ∀ i z, RawFamilyRec.paramKey C.node.a.family.parameters.length i = key C.parameters →
      z ∈ PointwiseDataCases.frame P μ C.node
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i →
      RecPlan.nodeCore C.M C.node C.minors z ∈
        PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
          (C.M.μ C.node.a.family.ref
            ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
          C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i z := by
  let p := EvalPlan.ofNode C.node
  let N := PointwiseDataCases.frame P μ C.node
  have hN := PointwiseDataCases.admissible P μ p fm ctors hE hmem
  obtain ⟨hfm, _, hfree, hTF, _, hRawB⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem C.node
  have hPrefix : ∀ r m, (extendEnv C.E C.f fm).members r = some m →
      C.node.E0.members r = some m := by
    intro r m hm
    by_cases hr : r = C.f
    · subst r
      rw [members_extend_eq] at hm
      cases Option.some.inj hm
      have hh := C.node.a.family.present
      rw [C.node.fam, hfm] at hh
      exact hh
    · rw [members_extend_ne C.E C.f fm r hr] at hm
      exact C.node.base r m hm
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  have hσ : ∀ k, k < C.node.a.family.member.arity → C.σ k = σOf vs k :=
    fun k hk => (σOf_canon C.σ C.node.a.family.member.arity k hk).symm
  have hlen : vs.length = C.node.a.family.member.arity := by
    simp only [vs, canonL, List.length_map, List.length_range]
  have hInst : ∀ j : Fin C.node.a.constructors.length,
      ∀ T ∈ (C.node.a.constructorViews j).fields, InstOK C.node.E0 C.σ K T := by
    intro j T hT
    have hI := NormPropParamFields.original_fields_instOK (σOf vs) K hE hfam hctors hrec
      hmem hBoundD C.node vs rfl hlen hvs j T hT
    have hb := hRawB.ctors _ (List.getElem?_mem (famDataOf_ctor C.node.a j))
    exact NormDataRec.instOK_levels hσ T (hb.1 T hT) (hI.mono_env hPrefix)
  have hcases := PointwiseDataCases.original_cases P μ K C hM fm ctors hE hfam hctors hrec
    hmem hBound hBoundD hpar hPred α hα ctx plans hctx hplans hFaith hvs h0
  exact DataRecCases.nodeCore_guarded P μ C N hM K hN hRawB hfree h0
    (typeFacts_sub (node_sub' C.node) hTF) hReader
    (bodiesOK_node hE hmem C.node K hBound.1 C.σ) hInst
    v hps hmo hminors hctor hcases

end Rcic.F3.PSet.PointwiseDataRec
