import rcic.RcicF3PointwisePrefix
import rcic.RcicF3NormDataCases

/-!
# Original DATA constructor cases for the pointwise interpretation

Actual normalized density is produced from major membership itself. The
new predecessor supplies the family-only prefix at the same frame update.
The unchanged checked parameter equality and bounded reverse-field bridge
then recover the original stored fields at the full recursor valuation.

No global Closed, local ExistsAt, small-frame callback or old invariant is
an input. This does not supply constructor soundness or the remaining
bounded local candidate producer. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseDataCases
open Rcic.Declarative PiIndex RawFamily RawFamilyRec PropEval

noncomputable def frame (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Frame :=
  PointwiseData.frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode node))
    node.a.family.member.arity

theorem admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E') :
    Admissible (famDataOf p.node.a) (frame P μ p.node) :=
  PointwiseData.frame_admissible P μ _ _
    (EvalPlanNormal.bounded_of_group (EvalPlan.ofNode p.node) fm ctors hE hmem)

theorem original_cases (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (C : Context)
    (hM : C.M = mkM P (RawFamily.table P μ (famDataOf C.node.a) (frame P μ C.node)))
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hB : BoundG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hBD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
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
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0) :
    ∀ i z, paramKey C.node.a.family.parameters.length i = key C.parameters →
      z ∈ frame P μ C.node ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i →
      ∃ (j : Fin C.node.a.constructors.length) (xs : List PSet.{4}),
        TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters ∧
        TelFits C.M C.σ (C.node.a.constructorViews j).fields (push C.parameters ρ0) xs ∧
        i = key (C.parameters ++ C.indicesAt j C.parameters xs) ∧
        Equiv z (dataVal j.val xs) := by
  let p := EvalPlan.ofNode C.node
  let N := frame P μ C.node
  let M := mkM P (RawFamily.table P μ (famDataOf C.node.a) N)
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  have hNraw : Admissible (famDataOf C.node.a) N := admissible P μ p fm ctors hE hmem
  obtain ⟨hPrior, hIota, hPrefix⟩ := PointwiseRole.target_facts P μ K p fm ctors
    hE hfam hmem hPred α hα ctx plans hctx hplans hFaith N hNraw
  obtain ⟨_, _, _, _, _, hRawB⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem C.node
  have hσ : ∀ k, k < C.node.a.family.member.arity → C.σ k = σOf vs k :=
    fun k hk => (σOf_canon C.σ C.node.a.family.member.arity k hk).symm
  have hlen : vs.length = C.node.a.family.member.arity := by
    simp only [vs, canonL, List.length_map, List.length_range]
  have h0vs : evalTotal (σOf vs) (EvalPlanNormal.fd p).resLevel ≠ 0 := by
    change evalTotal (σOf vs) (famDataOf C.node.a).resLevel ≠ 0
    rw [← evalTotal_agree hσ _ hRawB.res]
    exact h0
  intro i z hkey hz
  have hdense := PointwiseData.frame_dense P μ p fm ctors hE hmem vs i z hz
  obtain ⟨jn, xs, hp, hx, hi, he⟩ :=
    NormDataCases.ctorAt_parameters P μ (EvalPlanNormal.fd p) N vs i z hdense
      C.parameters hkey h0vs
  let j := EvalPlanNormal.index p jn
  have hget := EvalPlanNormal.ctor_get p jn
  rw [hget] at hx hi
  have hpN : TelFits M (σOf vs) C.node.a.family.parameters ρ0 C.parameters := hp
  have hxN : TelFits M (σOf vs) (EvalPlanNormal.fields p j) (push C.parameters ρ0) xs := hx
  have hxRaw := NormPropParamFields.fields_to_raw_of_guarded P μ (σOf vs) K p fm ctors
    hE hfam hctors hrec hmem hB hBD hpar N N hNraw hNraw hPrior hIota
    (hPrefix (σOf vs) C.node.a.family.member.arity) vs rfl hlen hvs
    j C.parameters xs hpN (fun _ _ _ h _ _ => h) hxN
  have hcb := hRawB.ctors _ (List.getElem?_mem (famDataOf_ctor C.node.a j))
  have hpAt : TelFits M C.σ C.node.a.family.parameters ρ0 C.parameters :=
    (TelFits_levels M hσ C.node.a.family.parameters hRawB.params ρ0 C.parameters).mpr hpN
  have hxAt : TelFits M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs :=
    (TelFits_levels M hσ (C.node.a.constructorViews j).fields hcb.1
      (push C.parameters ρ0) xs).mpr hxRaw
  have hiAt : i = key (C.parameters ++ (C.node.a.constructorViews j).resultIndices.map
      (den M C.σ (push xs (push C.parameters ρ0)))) := by
    rw [map_den_levels M hσ _ hcb.2]
    exact hi
  refine ⟨j, xs, ?_, ?_, ?_, he⟩
  · simpa only [hM] using hpAt
  · simpa only [hM] using hxAt
  · simpa only [hM, Context.indicesAt] using hiAt

end Rcic.F3.PSet.PointwiseDataCases
