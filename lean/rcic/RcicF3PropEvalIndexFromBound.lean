import rcic.RcicF3PointwisePropEvalValue
import rcic.RcicF3IndexedPropPlainIota

/-!
# Result-index coherence produced on the unchanged BoundG proof-field face

An evaluation has a constructor presentation at its complete requested key.
The actual BoundG proof-field typings identify the presentation's original
fields with any other tuple fitting the selected constructor fields at the
same parameter slice. Extensional reading then identifies the result indices.

The top-level producer below constructs evaluation and family-prefix
soundness from the existing admitted group and pointwise predecessor. It
does not assume key agreement, a field-comparison callback, syntactic
CtxWfT/ScopeCheck, or soundness of the completed group.

The final wrapper obtains the second tuple from the actual typed plain
redex through arguments_of_typed_nonempty. General recursive-redex tuple
fitting is not claimed. Old definitions and final root are unchanged.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet
open Rcic.Declarative

namespace PropEval
open PiIndex

private theorem leq_cancel_same_prefix (ps : List PSet.{4})
    {xs ys : List PSet.{4}} : LEq (ps ++ xs) (ps ++ ys) → LEq xs ys := by
  induction ps with
  | nil => exact fun h => h
  | cons p ps ih => exact fun h => ih h.2

/-- The actual evaluated constructor and actual fitting fields have the
same complete result key when the original fields are proofs. -/
theorem Eval.key_of_fitting_proof_fields (C : Context)
    (hone : C.node.a.constructors.length ≤ 1)
    (hprop : ∀ (j : Fin C.node.a.constructors.length) ps,
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps →
      LEq ps C.parameters →
      PropTel C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0))
    (j : Fin C.node.a.constructors.length) (xs : List PSet.{4})
    (hxs : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs)
    {i : Index.{4}} {z : PSet.{4}} (h : Eval C i z) :
    i = key (C.parameters ++ (C.node.a.constructorViews j).resultIndices.map
      (den C.M C.σ (push xs (push C.parameters ρ0)))) := by
  cases h with
  | root j' ps xs' ys fuel R out z hps hp hf hs hst hd hm hi hr =>
      have hj : j' = j := Fin.ext (by have := j'.isLt; have := j.isLt; omega)
      subst j'
      have hfields : LEq xs' xs :=
        fields_equiv_of_propTel C hprop j ps C.parameters xs' xs
          hps hp hp hf hxs
      exact (key_eq_iff _ _).mpr (LEq_append hp
        (LEq_map_den C.M C.σ
          (push_congr hfields (push_congr hp (fun _ => Equiv.rfl)))
          (C.node.a.constructorViews j).resultIndices))

/-- The original bound supplies every proof-field premise of key coherence.
The sound environment here is only the family prefix. -/
theorem Eval.indices_of_boundG_fields (C : Context)
    (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hB : BoundG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hM : C.M = mkM P μ)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (hES : EnvSound (mkM P μ) C.σ K (extendEnv C.E C.f fm)
      C.node.a.family.member.arity)
    (vs : List Nat) (hσ : C.σ = σOf vs)
    (hvs : ∀ v, v ∈ vs → v ≤ K C.rr)
    (j : Fin C.node.a.constructors.length) (xs is : List PSet.{4})
    (hxs : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs)
    {z : PSet.{4}} (h : Eval C (key (C.parameters ++ is)) z) :
    LEq is ((C.node.a.constructorViews j).resultIndices.map
      (den C.M C.σ (push xs (push C.parameters ρ0)))) := by
  have hprop : ∀ (k : Fin C.node.a.constructors.length) ps,
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps →
      LEq ps C.parameters →
      PropTel C.M C.σ (C.node.a.constructorViews k).fields (push ps ρ0) := by
    intro k ps hps _
    rw [hM] at hps ⊢
    apply propTel_of_typings_at P μ K C.σ C.node.a.family.parameters
      (C.node.a.constructorViews k).fields hES ?_ ps hps
    intro l
    obtain ⟨v, hv, d, hd⟩ :=
      hB.2.2.2 C.node (selection_prop C.node.a C.σ h0 hpolicy).1
        hpolicy k vs hvs l
    exact ⟨v, hv C.σ, d, by rw [hσ]; exact hd⟩
  have hkey := h.key_of_fitting_proof_fields C
    (selection_prop C.node.a C.σ h0 hpolicy).2 hprop j xs hxs
  exact leq_cancel_same_prefix C.parameters ((key_eq_iff _ _).mp hkey)

end PropEval

namespace PointwisePropEval
open PiIndex RawFamily PropEval PropEvalCandidate
open NormPropEval (base)

/-- The supplied indices agree with the selected constructor's original
result read. Evaluation and family-prefix soundness are both produced by
the existing admitted-group theorems. No index coherence is an input. -/
theorem result_indices_of_boundG (P : Premises4)
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
    (j : Fin C.node.a.constructors.length) (xs : List PSet.{4})
    (hxs : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs) :
    LEq is ((C.node.a.constructorViews j).resultIndices.map
      (den C.M C.σ (push xs (push C.parameters ρ0)))) := by
  have hs := result_spec P μ K C hM fm ctors hE hfam hctors hrec hmem
    hBound hPred α hα ctx plans hctx hplans hFaith hFamily fullvs hσfull hvs
    h0 hpolicy v hmo hminors is major hps his hmajor
  have hRaw : Admissible (famDataOf C.node.a) (base P μ C) :=
    (EvalPlanNormalProp.normalized_closed P μ (EvalPlan.ofNode C.node)
      fm ctors hE hmem C.σ h0 hpolicy).1
  have F := PointwiseGroupFacts.group_facts P K μ hE hfam hmem C.node
    hPred α hα ctx plans hctx hplans hFaith (base P μ C) hRaw hFamily
  exact hs.2.1.indices_of_boundG_fields C P μ K hE hfam hctors hrec hmem
    hBound hM h0 hpolicy (F.rawEnv C.σ C.node.a.family.member.arity)
    fullvs hσfull hvs j xs is hxs

end PointwisePropEval

namespace IndexedPropPlainIota
open PiIndex RawFamily PropEval

/-- Actual typed plain-redex arguments and the original BoundG jointly
produce the previously missing supplied-index/result-index equation.
The arbitrary source context is consumed only through its actual Fits.
No source or completed-environment soundness assumption is added. -/
theorem coherent_arguments_of_typed_nonempty (P : Premises4)
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
    (hN : NoFunRec p.node)
    (hfree : ∀ (j : Fin p.node.a.constructors.length) A,
      A ∈ (p.node.a.constructorViews j).fields →
      occursConst p.node.a.family.ref A = false)
    {S : ResolvedEnv} (w : IotaWitness S)
    (hwr : w.recRef = p.rr) (hm : w.recMember = p.rm)
    (j : Fin p.node.a.constructors.length) (hj : w.ctorIdx = j.val)
    (hcm : w.ctorMember = p.node.a.constructors[j.val])
    (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (h0 : evalTotal (valuation w σ) p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (hvs : ∀ u, u ∈ w.ls.map (evalTotal σ) → u ≤ K p.rr)
    {n : Nat} {Γ : LCtx} {T : Expr Nat}
    (hr : HasTyT S n Γ (iotaRhsOf w) T) (hrs : HSoundT (mkM P μ) σ hr)
    (hfit : Fits (mkM P μ) σ Γ ρ)
    {X : PSet.{4}}
    (ml : den (mkM P μ) σ ρ (iotaLhsOf w) ∈ Ed (mkM P μ) X)
    (mr : den (mkM P μ) σ ρ (iotaRhsOf w) ∈ Ed (mkM P μ) X)
    (hne : ¬ Equiv (den (mkM P μ) σ ρ (iotaLhsOf w)) pempty) :
    ∃ ps mo ms is, Arguments (mkM P μ) p w σ ρ j ps mo ms is ∧
      LEq is ((p.node.a.constructorViews j).resultIndices.map
        (den (mkM P μ) (valuation w σ)
          (push (w.fields.map (den (mkM P μ) σ ρ)) (push ps ρ0)))) := by
  obtain ⟨ps, mo, ms, is, ha⟩ :=
    arguments_of_typed_nonempty P μ p fm ctors hE hmem hRec hN hfree
      w hwr hm j hj hcm σ ρ hr hrs hfit ml mr hne
  refine ⟨ps, mo, ms, is, ha, ?_⟩
  let C := (EvalPlanValue.context p (mkM P μ) (valuation w σ) ρ0).withValues
    ps mo ms ha.minors_length
  exact PointwisePropEval.result_indices_of_boundG P μ K C rfl fm ctors
    hE hfam hctors hrec hmem hBound hPred α hα ctx plans hctx hplans hFaith
    hFamily (w.ls.map (evalTotal σ)) rfl hvs h0 hpolicy
    (policyMotiveLevel p.node.a.family.member.arity p.node.a.policy)
    ha.motive_fit ha.minors_fit is (den (mkM P μ) σ ρ (ctorMajor w))
    ha.parameters_fit ha.indices_fit ha.major_fit j
    (w.fields.map (den (mkM P μ) σ ρ)) ha.fields_fit

end IndexedPropPlainIota

end Rcic.F3.PSet

#print axioms Rcic.F3.PSet.PropEval.Eval.key_of_fitting_proof_fields
#print axioms Rcic.F3.PSet.PropEval.Eval.indices_of_boundG_fields
#print axioms Rcic.F3.PSet.PointwisePropEval.result_indices_of_boundG
#print axioms Rcic.F3.PSet.IndexedPropPlainIota.coherent_arguments_of_typed_nonempty
