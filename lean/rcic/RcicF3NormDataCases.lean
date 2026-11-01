import rcic.RcicF3NormPropParamFields
import rcic.RcicF3NormCandidatePrefix
import rcic.RcicF3EvalPlanNormalMono
import rcic.RcicF3EvalPlanNormalLevels
import rcic.RcicF3PropEvalGuarded

/-!
# Original constructor cases of the normalized DATA frame

Normalized intersection density supplies constructor cases at the full
family key. The actual D field bounds and checked parameter-telescope
equality reconstruct the original field tuple at the canonical family
valuation. Family-level scope then transports that same tuple and complete
result key to the unchanged recursor valuation, retaining an extra motive
universe. No raw/normalized frame equality is used.

Normalized frame admissibility and closure remain explicit size-production
inputs. Monotonicity, prefix soundness and the reverse tuple transport are
produced from admission and the repaired predecessor. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataCases
open Rcic.Declarative PiIndex RawFamily RawFamilyRec PropEval

/-- Full-key parameter replacement preserves the actual data constructor. -/
theorem ctorAt_parameters (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (A : Frame) (vs : List Nat) (i : Index.{4}) (z : PSet.{4})
    (hc : CtorAt P μ fd A vs i z) (ps₀ : List PSet.{4})
    (hkey : paramKey fd.params.length i = key ps₀)
    (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0) :
    let M := mkM P (table P μ fd A)
    ∃ (j : Fin fd.ctors.length) (xs : List PSet.{4}),
      TelFits M (σOf vs) fd.params ρ0 ps₀ ∧
      TelFits M (σOf vs) (fd.ctors.get j).1 (push ps₀ ρ0) xs ∧
      i = key (ps₀ ++ (fd.ctors.get j).2.map
        (den M (σOf vs) (push xs (push ps₀ ρ0)))) ∧
      Equiv z (dataVal j.val xs) := by
  dsimp only
  let M := mkM P (table P μ fd A)
  obtain ⟨j, ps, xs, hp, hx, _, hi, hz⟩ := hc
  have hp₀ : LEq ps ps₀ :=
    paramKey_reflect fd.params.length ps ps₀
      ((fd.ctors.get j).2.map (den M (σOf vs) (push xs (push ps ρ0))))
      hp.length (by rw [← hi]; exact hkey)
  have henv : ∀ k, Equiv (push ps ρ0 k) (push ps₀ ρ0 k) :=
    push_congr hp₀ (fun _ => Equiv.rfl)
  have hparams := TelFits_congr M (σOf vs) fd.params (fun _ => Equiv.rfl) hp₀ hp
  have hfields := TelFits_congr M (σOf vs) (fd.ctors.get j).1 henv (LEq.refl xs) hx
  have hr := LEq_map_den M (σOf vs) (push_congr (LEq.refl xs) henv) (fd.ctors.get j).2
  refine ⟨j, xs, hparams, hfields,
    hi.trans ((key_eq_iff _ _).mpr (LEq_append hp₀ hr)), ?_⟩
  simpa only [if_neg h0] using hz

/-- A member of the actual normalized intersection has an original
admitted constructor presentation at the fixed bounded parameter slice. -/
theorem original_cases (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (C : Context)
    (hM : C.M = mkM P (table P μ (famDataOf C.node.a)
      (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node)))))
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
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans C.E)
    (hN : Admissible (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
      (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))))
    (hClosed : Closed P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
      (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))))
    (hvs : ∀ u, u ∈ (canonL C.node.a.family.member.arity).map (evalTotal C.σ) → u ≤ K C.rr)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0) :
    ∀ i z, paramKey C.node.a.family.parameters.length i = key C.parameters →
      z ∈ frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i →
      ∃ (j : Fin C.node.a.constructors.length) (xs : List PSet.{4}),
        TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters ∧
        TelFits C.M C.σ (C.node.a.constructorViews j).fields (push C.parameters ρ0) xs ∧
        i = key (C.parameters ++ C.indicesAt j C.parameters xs) ∧
        Equiv z (dataVal j.val xs) := by
  let p := EvalPlan.ofNode C.node
  let N := frame P μ (EvalPlanNormal.fd p)
  let M := mkM P (table P μ (famDataOf C.node.a) N)
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  have hNraw : Admissible (famDataOf C.node.a) N := hN
  obtain ⟨hPrior, hIota, hPrefix⟩ := NormCandidatePrefix.target_facts P μ K p fm ctors
    hE hfam hmem hPred ctx plans hctx hplans hFaith N hNraw
  obtain ⟨_, _, _, _, _, hRawB⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem C.node
  have hMono := EvalPlanNormal.constructorMono_of_group P μ p fm ctors hE hmem
  have hσ : ∀ k, k < C.node.a.family.member.arity → C.σ k = σOf vs k :=
    fun k hk => (σOf_canon C.σ C.node.a.family.member.arity k hk).symm
  have hlen : vs.length = C.node.a.family.member.arity := by
    simp only [vs, canonL, List.length_map, List.length_range]
  have h0vs : evalTotal (σOf vs) (EvalPlanNormal.fd p).resLevel ≠ 0 := by
    change evalTotal (σOf vs) (famDataOf C.node.a).resLevel ≠ 0
    rw [← evalTotal_agree hσ _ hRawB.res]
    exact h0
  intro i z hkey hz
  have hdense := frame_dense P μ (EvalPlanNormal.fd p) hN hClosed hMono vs i z hz
  obtain ⟨jn, xs, hp, hx, hi, he⟩ :=
    ctorAt_parameters P μ (EvalPlanNormal.fd p) N vs i z hdense C.parameters hkey h0vs
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

end Rcic.F3.PSet.NormDataCases
