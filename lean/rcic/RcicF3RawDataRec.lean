import rcic.RcicF3RawDataMinor
import rcic.RcicF3RawFamilyRecAt

/-!
# Data recursion with the stored-minor contract produced

The well-founded recursion engine receives its step from the actual stored
minor tuple and executable IH producer. Parameter witnesses are transported
extensionally to the fixed slice; every dependent result index is retained.
The syntax valuation, including an additional motive universe, is unchanged.

The raw frame's admissibility, closure and monotonicity, the ordinary reader
environment and literal constructor code equations are still explicit here.
This component does not produce a universal small data frame or StepAG.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawDataRec
open Rcic.Declarative PiIndex RawFamily PropEval

/-- Actual typed stored minors discharge the local recursion contract.
No minor-step, evaluation-existence or recursive-totality callback is assumed. -/
theorem nodeCore_guarded (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context)
    (hM : C.M = RawFamilyRec.model P μ (famDataOf C.node.a))
    (K : Nat → Nat)
    (hB : FamBounded (famDataOf C.node.a) C.node.a.family.member.arity)
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0)
    {n : Nat} (htf : TypeFacts C.node.E0)
    (hE : EnvSound C.M C.σ K C.node.E0 n)
    (hb : BodiesOK C.node.E0 C.σ K)
    (hI : ∀ j : Fin C.node.a.constructors.length,
      ∀ T ∈ (C.node.a.constructorViews j).fields, InstOK C.node.E0 C.σ K T)
    (hA : Admissible (famDataOf C.node.a) (frame P μ (famDataOf C.node.a)))
    (hClosed : Closed P μ (famDataOf C.node.a) (frame P μ (famDataOf C.node.a)))
    (hMono : ConstructorMono P μ (famDataOf C.node.a))
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
      z ∈ frame P μ (famDataOf C.node.a)
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i →
      RecPlan.nodeCore C.M C.node C.minors z ∈
        PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
          (C.M.μ C.node.a.family.ref
            ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
          C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i z := by
  let fd := famDataOf C.node.a
  let M := RawFamilyRec.model P μ fd
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  let Q := PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
    (C.M.μ C.node.a.family.ref vs) C.motive C.parameters
    C.node.a.family.indices (push C.parameters ρ0)
  let g := RecPlan.nodeCore C.M C.node C.minors
  have hg : ∀ x y, Equiv x y → Equiv (g x) (g y) := by
    intro x y he
    exact recCore_resp C.M (RecPlan.descriptor C.f
      (RecPlan.nodePlan C.node)) C.minors x y he
  have hσ : ∀ k, k < C.node.a.family.member.arity → C.σ k = σOf vs k :=
    fun k hk => (σOf_canon C.σ C.node.a.family.member.arity k hk).symm
  have hstep : ∀ (j : Fin C.node.a.constructors.length) ps xs,
      TelFits M C.σ C.node.a.family.parameters ρ0 ps → LEq ps C.parameters →
      TelFits M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs →
      (∀ i y, RawFamilyRec.paramKey C.node.a.family.parameters.length i = key C.parameters →
        MemT y (dataVal j.val xs) → y ∈ frame P μ fd vs i →
        RecPlan.nodeCore M C.node C.minors y ∈ Q i y) →
      fapps (C.minors.getD j.val pempty)
        (RecPlan.args (RecPlan.nodeCore M C.node C.minors) (C.node.h14.shapesAt j) xs) ∈
      Q (key (ps ++ (C.node.a.constructorViews j).resultIndices.map
        (den M C.σ (push xs (push ps ρ0))))) (dataVal j.val xs) := by
    intro j ps xs _ hp hx ih
    have hx' : TelFits C.M C.σ (C.node.a.constructorViews j).fields
        (push ps ρ0) xs := by simpa only [hM] using hx
    have henv : ∀ k, Equiv (push ps ρ0 k) (push C.parameters ρ0 k) :=
      push_congr hp (fun _ => Equiv.rfl)
    have hx0 := TelFits_congr C.M C.σ (C.node.a.constructorViews j).fields
      henv (LEq.refl xs) hx'
    have hmap : ∀ i y, RawFamilyRec.paramKey C.parameters.length i = key C.parameters →
        MemT y (dataVal j.val xs) → y ∈ frame P μ fd vs i → g y ∈ Q i y := by
      intro i y hi hy hfib
      rw [hps] at hi
      have hh := ih i y hi hy hfib
      simpa only [g, hM] using hh
    have hm := RawDataMinor.apply_stored_guarded P μ C (frame P μ fd) hM hA K
      hB hf h0 htf hE hb v hps hmo hminors j xs (hI j) hx0 g hg hmap (hctor j xs hx0)
    have hk : key (ps ++ (C.node.a.constructorViews j).resultIndices.map
        (den C.M C.σ (push xs (push ps ρ0)))) =
        key (C.parameters ++ C.indicesAt j C.parameters xs) :=
      (key_eq_iff _ _).mpr (LEq_append hp
        (LEq_map_den C.M C.σ (push_congr (LEq.refl xs) henv)
          (C.node.a.constructorViews j).resultIndices))
    have hm' : fapps (C.minors.getD j.val pempty)
        (RecPlan.args g (C.node.h14.shapesAt j) xs) ∈
        Q (key (ps ++ (C.node.a.constructorViews j).resultIndices.map
          (den C.M C.σ (push xs (push ps ρ0))))) (dataVal j.val xs) := by
      rw [hk]
      exact hm
    simpa only [g, hM] using hm'
  have hh := RawFamilyRec.produce_at_parameters_at P μ K C.node vs C.σ hB hσ
    (by simpa only [hM] using hE) hb hI hA hClosed hMono h0 C.parameters C.minors Q
    (fun _ _ _ he => PiRawMotiveAny.guarded_resp C.M C.σ (evalTotal C.σ v)
      (C.M.μ C.node.a.family.ref vs) C.motive C.parameters C.node.a.family.indices
      (push C.parameters ρ0) _ he) hstep
  intro i z hi hz
  have hz' := hh i z hi hz
  simpa only [Q, vs, hM] using hz'

end Rcic.F3.PSet.RawDataRec
