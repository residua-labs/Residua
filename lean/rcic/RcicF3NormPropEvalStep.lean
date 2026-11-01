import rcic.RcicF3PropEvalFrameAdmitted
import rcic.RcicF3EvalPlanNormalCompare
import rcic.RcicF3NormCandidatePrefix
import rcic.RcicF3NormPropEvalInputs
import rcic.RcicF3CandidateBoundTuple

/-!
# Constructor evaluation for the normalized canonical family role

The selected family frame is the actual admitted normalized frame.
Candidate restriction supplies recursive evaluations, and original field
reconstruction is run in the candidate and that same normalized frame.
The new predecessor invariant supplies prefix soundness in both tables.
Actual typed fields and stored minors then produce indexed evaluation.
No equivalence with the original raw-role invariant is assumed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropEval
open Rcic.Declarative PiIndex RawFamily PropEval PropEvalCandidate

noncomputable def base (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : Context) : Frame :=
  frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))

noncomputable def candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : Context) : Frame := PropEvalFrame.candidate (base P μ C) C

/-- Constructor production uses the actual bounded typed group and the
repaired predecessor invariant. Every normalized-to-original field
transport and every recursive evaluation is produced internally. -/
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
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans C.E)
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
      (vcons C.motive (push C.parameters ρ0)) C.minors) :
    ∀ vs i z, CtorAt P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))
      (candidate P μ C) vs i z → EvalPredicate C vs i z := by
  let p := EvalPlan.ofNode C.node
  let N := base P μ C
  let X := candidate P μ C
  let R := N
  obtain ⟨hN, _⟩ := EvalPlanNormalProp.normalized_closed P μ p fm ctors hE hmem
    C.σ h0 hpolicy
  have hNraw : Admissible (famDataOf C.node.a) N := hN
  have hX : Admissible (famDataOf C.node.a) X :=
    PropEvalFrame.admissible P C N hNraw
  have hRaw : Admissible (famDataOf C.node.a) R := hNraw
  have F := NormCandidatePrefix.group_facts P K μ hE hfam hmem C.node
    hPred ctx plans hctx hplans hFaith N hNraw hFamily
  obtain ⟨hAX, hIX, hEX⟩ := NormCandidatePrefix.target_facts P μ K p fm ctors
    hE hfam hmem hPred ctx plans hctx hplans hFaith X hX
  obtain ⟨hAR, hIR, hER⟩ := NormCandidatePrefix.target_facts P μ K p fm ctors
    hE hfam hmem hPred ctx plans hctx hplans hFaith R hRaw
  intro vs i z hc hσ hkey
  obtain ⟨jn, xs, hpX, hxX, hi, _⟩ := ctorAt_parameters_at P μ (EvalPlanNormal.fd p) X
    C.node.a.family.member.arity (EvalPlanNormal.bounded_of_group p fm ctors hE hmem)
    vs C.σ hσ i z hc C.parameters hkey h0
  let j := EvalPlanNormal.index p jn
  have hget := EvalPlanNormal.ctor_get p jn
  rw [hget] at hxX hi
  have hpR : TelFits (mkM P (table P μ (famDataOf C.node.a) R)) C.σ
      C.node.a.family.parameters ρ0 C.parameters :=
    (PiIndependent.telFits_free P μ (famDataOf C.node.a).fref
      (ofFrame P μ (famDataOf C.node.a) X) (ofFrame P μ (famDataOf C.node.a) R)
      C.σ C.node.a.family.parameters
      (fun e he => F.free e (List.mem_append_left _ he)) ρ0 C.parameters).mp hpX
  have hxOriginalX := EvalPlanNormal.fields_to_raw_of_guarded P μ C.σ K p fm ctors
    hE hfam hctors hrec hmem hBound X X hX hX hAX hIX
    (hEX C.σ C.node.a.family.member.arity) h0 hpolicy fullvs hσfull hvs
    j C.parameters xs hpX (fun _ _ _ hx _ _ => hx) hxX
  have hsub : EvalPlanNormalSlice.GuardedSub C.node.a.family.member.arity
      C.node.a.family.parameters.length C.σ C.parameters X R := by
    intro vs' i' x hx hlevel hparam
    exact mem_sep_subset hx
  have hxOriginalR := EvalPlanNormal.fields_to_raw_of_guarded P μ C.σ K p fm ctors
    hE hfam hctors hrec hmem hBound X R hX hRaw hAR hIR
    (hER C.σ C.node.a.family.member.arity) h0 hpolicy fullvs hσfull hvs
    j C.parameters xs hpR hsub hxX
  have he := table_equiv P μ (famDataOf C.node.a) R hFamily
  have hpRaw : TelFits (mkM P μ) C.σ C.node.a.family.parameters ρ0 C.parameters :=
    (TelFits_tables_equiv P he _ _ _ _).mpr hpR
  have hxRaw : TelFits (mkM P μ) C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs :=
    (TelFits_tables_equiv P he _ _ _ _).mpr hxOriginalR
  have hERaw := F.rawEnv C.σ C.node.a.family.member.arity
  have hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z' := by
    intro i z z' hz hz'
    exact Eval.functional_of_boundG C P μ K hE hfam hctors hrec hmem hBound
      hM h0 hpolicy hERaw fullvs hσfull hvs hz hz'
  obtain ⟨endVal, hEnd, hF, hProp⟩ := frame_inputs P μ C hM F.bounded N hFamily hNraw h0
  have hb := CandidateBoundFields.family_prefix_bodiesOK C.σ K hE hBound.1 hmem
  have hInst := CandidateBoundFields.original_fields_instOK C.σ K
    hE hfam hctors hrec hmem hBound C.node h0 hpolicy fullvs hσfull hvs j
  have hRawC : EnvSound C.M C.σ K (extendEnv C.E C.f fm) C.node.a.family.member.arity := by
    rw [hM]
    exact hERaw
  have hpC : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters := by
    rw [hM]
    exact hpRaw
  have hxC : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs := by
    rw [hM]
    exact hxRaw
  have heval := eval_of_frame_fields P μ C hM N hNraw F.free fm ctors hmem K
    hRawC (hEX C.σ C.node.a.family.member.arity) hb F.closedReader v (by rw [hM]; rfl)
    endVal hEnd hF hmo hProp hfunctional hpC hminors j xs hInst hxC hxOriginalX
  have hread := PiIndependent.leafArgs_free P μ (famDataOf C.node.a).fref
    (ofFrame P μ (famDataOf C.node.a) X) (μ (famDataOf C.node.a).fref)
    C.σ (C.node.a.constructorViews j).resultIndices
    (C.node.a.constructorViews j).noFamilyInIndices (push xs (push C.parameters ρ0))
  rw [PiIndependent.upd_self] at hread
  change (C.node.a.constructorViews j).resultIndices.map
      (den (mkM P (table P μ (famDataOf C.node.a) X)) C.σ (push xs (push C.parameters ρ0))) =
    (C.node.a.constructorViews j).resultIndices.map
      (den (mkM P μ) C.σ (push xs (push C.parameters ρ0))) at hread
  change i = key (C.parameters ++ (C.node.a.constructorViews j).resultIndices.map
    (den (mkM P (table P μ (famDataOf C.node.a) X)) C.σ (push xs (push C.parameters ρ0)))) at hi
  rw [hread] at hi
  have hiC : i = key (C.parameters ++ (C.node.a.constructorViews j).resultIndices.map
      (den C.M C.σ (push xs (push C.parameters ρ0)))) := by
    rw [hM]
    exact hi
  rw [hiC]
  exact heval

end Rcic.F3.PSet.NormPropEval
