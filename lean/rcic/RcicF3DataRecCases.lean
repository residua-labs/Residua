import rcic.RcicF3RawDataMinor
import rcic.RcicF3PiRecExtract

/-!
# The stored-minor DATA bridge for an arbitrary admissible frame

Well-founded recursion on the actual data code needs constructor cases at
the reached parameter slice. It does not require that the interpreted frame
be the raw intersection. The next normalized consumer supplies these cases
from its actual normalized intersection and bounded original-field transport.

The stored-minor step and its executable IH are produced here. Constructor
cases, ordinary reader soundness and the literal constructor-code equations
remain explicit in this intermediate theorem. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.DataRecCases
open Rcic.Declarative PiIndex RawFamily PropEval

theorem nodeCore_guarded (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (A : Frame)
    (hM : C.M = mkM P (table P μ (famDataOf C.node.a) A))
    (K : Nat → Nat)
    (hA : Admissible (famDataOf C.node.a) A)
    (hB : FamBounded (famDataOf C.node.a) C.node.a.family.member.arity)
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0)
    {n : Nat} (htf : TypeFacts C.node.E0)
    (hE : EnvSound C.M C.σ K C.node.E0 n)
    (hb : BodiesOK C.node.E0 C.σ K)
    (hI : ∀ j : Fin C.node.a.constructors.length,
      ∀ T ∈ (C.node.a.constructorViews j).fields, InstOK C.node.E0 C.σ K T)
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
      Equiv (C.constructorAt j C.parameters xs) (dataVal j.val xs))
    (hcases : ∀ i z,
      RawFamilyRec.paramKey C.node.a.family.parameters.length i = key C.parameters →
      z ∈ A ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i →
      ∃ (j : Fin C.node.a.constructors.length) (xs : List PSet.{4}),
        TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters ∧
        TelFits C.M C.σ (C.node.a.constructorViews j).fields (push C.parameters ρ0) xs ∧
        i = key (C.parameters ++ C.indicesAt j C.parameters xs) ∧
        Equiv z (dataVal j.val xs)) :
    ∀ i z, RawFamilyRec.paramKey C.node.a.family.parameters.length i = key C.parameters →
      z ∈ A ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i →
      RecPlan.nodeCore C.M C.node C.minors z ∈
        PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
          (C.M.μ C.node.a.family.ref
            ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
          C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i z := by
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  let Q := PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
    (C.M.μ C.node.a.family.ref vs) C.motive C.parameters
    C.node.a.family.indices (push C.parameters ρ0)
  let g := RecPlan.nodeCore C.M C.node C.minors
  have hg : ∀ x y, Equiv x y → Equiv (g x) (g y) := by
    intro x y he
    exact recCore_resp C.M (RecPlan.descriptor C.f (RecPlan.nodePlan C.node))
      C.minors x y he
  have hsound : ∀ z i,
      RawFamilyRec.paramKey C.node.a.family.parameters.length i = key C.parameters →
      z ∈ A vs i → g z ∈ Q i z := by
    intro z
    induction z using memT_wf.induction with
    | h z ih =>
        intro i hkey hz
        obtain ⟨j, xs, _, hx, hi, he⟩ := hcases i z hkey hz
        subst i
        have hmap : ∀ i y, RawFamilyRec.paramKey C.parameters.length i = key C.parameters →
            MemT y (dataVal j.val xs) → y ∈ A vs i → g y ∈ Q i y := by
          intro i y hparam hy hyA
          rw [hps] at hparam
          exact ih y (hy.congr_right he.symm) i hparam hyA
        have hs := RawDataMinor.apply_stored_guarded P μ C A hM hA K hB hf h0
          htf hE hb v hps hmo hminors j xs (hI j) hx g hg hmap (hctor j xs hx)
        have hu : Equiv (g z)
            (fapps (C.minors.getD j.val pempty) (RecPlan.args g (C.node.h14.shapesAt j) xs)) :=
          (hg z (dataVal j.val xs) he).trans
            (RecPlan.node_data_of_fits C.M C.σ K C.node hE hb C.minors j
              (hI j) (push C.parameters ρ0) xs hx)
        have hQ := PiRawMotiveAny.guarded_resp C.M C.σ (evalTotal C.σ v)
          (C.M.μ C.node.a.family.ref vs) C.motive C.parameters C.node.a.family.indices
          (push C.parameters ρ0) (key (C.parameters ++ C.indicesAt j C.parameters xs)) he.symm
        exact mem_congr_right hQ (mem_congr_left hu.symm hs)
  intro i z hkey hz
  exact hsound z i hkey hz

end Rcic.F3.PSet.DataRecCases
