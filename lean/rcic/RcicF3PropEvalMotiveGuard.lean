import rcic.RcicF3Fam
import rcic.RcicF3PropEvalGuarded

/-!
# Typed motive applications recover their own fitting arguments

An inhabited evaluated endpoint is a nonempty application of the actual
typed motive. Typed application outside its domain is empty, so that endpoint
already forces every dependent index to fit and the actual constructor value
to lie in the family. The Prop family face then gives proof erasure. No
separate constructor-soundness or index-fitting producer is assumed here.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet
open Rcic.Declarative
universe u

/-- A nonempty application of any typed telescope value has fitting arguments.
The function need not be a literal telescope abstraction. -/
theorem fits_of_typed_fapps_ne (M : Interp.{u}) (σ : Nat → Nat) (b : Expr Nat) :
    ∀ (Ds : List (Expr Nat)) (ρ : Nat → PSet.{u}) (f : PSet.{u})
      (xs : List PSet.{u}), xs.length = Ds.length →
      f ∈ Ed M (den M σ ρ (policyPi Ds b)) →
      ¬ Equiv (fapps f xs) pempty → TelFits M σ Ds ρ xs := by
  intro Ds
  induction Ds with
  | nil =>
      intro ρ f xs hl _ _
      have hx : xs = [] := List.eq_nil_of_length_eq_zero hl
      subst xs
      trivial
  | cons A Ds ih =>
      intro ρ f xs hl hf hne
      cases xs with
      | nil => exact Nat.noConfusion hl
      | cons x xs =>
          have hl' : xs.length = Ds.length := Nat.succ.inj hl
          have hB := den_resp M σ ρ (policyPi Ds b)
          have hx : x ∈ Ed M (den M σ ρ A) :=
            mem_dom_of_fapp_ne M hB hf
              (fun he => hne (fapps_equiv_pempty he xs))
          exact ⟨hx, ih (vcons x ρ) (fapp f x) xs hl'
            (app_mem M hB hf hx) hne⟩

namespace PropEval
open PiIndex

/-- Actual endpoint typing supplies the index and constructor obligations of
guarded motive membership. Only typed motive membership and the Prop family
face are needed in addition to the evaluation itself. -/
theorem Eval.mem_guarded_of_typed_motive {C : Context} {i : Index.{4}} {z : PSet.{4}}
    (hEval : Eval C i z) (v : Level) (hU : C.M.U = U W4)
    (hMotive : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref (policyFamilyLevels C.node.a.family))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hProp : ∀ ys,
      ys.length = C.node.a.family.parameters.length + C.node.a.family.indices.length →
      ∀ c, c ∈ Ed C.M (fapps
        (C.M.μ C.node.a.family.ref
          ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ))) ys) →
        Equiv c pempty) :
    z ∈ PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
      (C.M.μ C.node.a.family.ref
        ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ)))
      C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i pempty := by
  obtain ⟨j, ps, xs, hkey, hparams, hps, _, hz⟩ := hEval.result_typed
  let is := C.indicesAt j ps xs
  let c := C.constructorAt j ps xs
  let familyAt : Expr Nat :=
    foldApps (.const C.node.a.family.ref (policyFamilyLevels C.node.a.family))
      (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length))
  let endTy : Expr Nat := .pi familyAt (.sort v)
  have hps₀ : C.parameters.length = C.node.a.family.parameters.length :=
    hparams.length.symm.trans hps.length
  have hisLength : is.length = C.node.a.family.indices.length := by
    change ((C.node.a.constructorViews j).resultIndices.map
      (den C.M C.σ (push xs (push ps ρ0)))).length = C.node.a.family.indices.length
    rw [List.length_map]
    exact (C.node.a.constructorViews j).indexCount
  have hmo : C.motive ∈ Ed C.M (den C.M C.σ (push ps ρ0)
      (policyPi C.node.a.family.indices endTy)) :=
    mem_congr_right (ed_congr C.M
      (den_congr C.M C.σ (policyPi C.node.a.family.indices endTy)
        (push_congr hparams.symm (fun _ => Equiv.rfl)))) hMotive
  change z ∈ Ed C.M (fapp (fapps C.motive is) c) at hz
  have hne : ¬ Equiv (fapp (fapps C.motive is) c) pempty := by
    intro he
    exact not_mem_pempty
      (mem_congr_right ((ed_congr C.M he).trans (ed_pempty C.M)) hz)
  have hmoNe : ¬ Equiv (fapps C.motive is) pempty := by
    intro he
    exact hne ((fapp_congr he Equiv.rfl).trans (fapp_pempty c))
  have his : TelFits C.M C.σ C.node.a.family.indices (push ps ρ0) is :=
    fits_of_typed_fapps_ne C.M C.σ endTy C.node.a.family.indices
      (push ps ρ0) C.motive is hisLength hmo hmoNe
  have hmoApplied := mem_fapps C.M C.σ endTy C.node.a.family.indices
    (push ps ρ0) C.motive is hmo his
  have hcDen : c ∈ Ed C.M (den C.M C.σ (push is (push ps ρ0)) familyAt) :=
    mem_dom_of_fapp_ne C.M
      (den_resp C.M C.σ (push is (push ps ρ0)) (.sort v)) hmoApplied hne
  have hF := Fapp_den C.M C.σ C.node.a.family.ref
    (policyFamilyLevels C.node.a.family) ps is ρ0
  rw [hps.length, his.length] at hF
  have hc : c ∈ Ed C.M (fapps
      (C.M.μ C.node.a.family.ref
        ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ))) (ps ++ is)) := by
    rw [← hF]
    exact hcDen
  have hc0 : Equiv c pempty := hProp (ps ++ is)
    (by rw [List.length_append, hps.length, his.length]) c hc
  have hg := endpoint_mem_guarded C.M hU C.σ C.node.a.family.ref
    (policyFamilyLevels C.node.a.family) C.node.a.family.parameters C.node.a.family.indices
    C.parameters hps₀ C.motive v hMotive ps is c z hparams his hc hc0 hz
  rw [hkey]
  exact hg

end PropEval
end Rcic.F3.PSet
