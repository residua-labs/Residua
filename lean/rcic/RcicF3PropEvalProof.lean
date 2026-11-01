import rcic.RcicF3PropEvalMotiveGuard

/-!
# Produced functionality of evaluation at a typed Prop motive

The universe-zero carrier contains only erased proofs. The guarded
carrier inherits this property. Actual typed motive guarding puts every
Eval output in that carrier, so two evaluations at the same complete key
are equivalent. Neither a singleton constructor nor proof-valued ordinary
fields are required.

These four lemmas are used by the checked-parameter PropOnly constructor,
totality and stored recursor producers. Evaluation existence is produced
separately by their actual guarded candidate. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalProof
open Rcic.Declarative PiIndex PropEval

/-- The universe-zero bound itself forces proof erasure, even at a key
which is not reached by the current constructor. -/
theorem carrier_prop (M : Interp.{4}) (hU : M.U = U W4)
    (y : PSet.{4}) (hy : y ∈ PiRawMotiveAny.carrier M 0) : Equiv y pempty := by
  obtain ⟨X, hX, hyX⟩ := mem_sUnion.mp hy
  obtain ⟨j, hXT⟩ := mem_sImage.mp hX
  let T := (M.U 0).Func j
  have hT0 : T ∈ U W4 0 := by rw [← hU]; exact ⟨j, Equiv.rfl⟩
  exact ed_of_mem_U0 M hT0 (mem_congr_right hXT.symm hyX)

theorem guarded_prop (M : Interp.{4}) (hU : M.U = U W4) (σ : Nat → Nat)
    (F mo : PSet.{4}) (ps : List PSet.{4}) (ds : List (Expr Nat))
    (ρ : Nat → PSet.{4}) (i : Index.{4}) (x y : PSet.{4})
    (hy : y ∈ PiRawMotiveAny.guarded M σ 0 F mo ps ds ρ i x) :
    Equiv y pempty := by
  have he : ∀ z, z ∈ PiRawMotiveAny.elements M σ 0 F mo ps ds ρ i x →
      Equiv z pempty := fun z hz => carrier_prop M hU z (mem_sep_subset hz)
  exact he y (mem_congr_right (ed_tyv M (Or.inl he)) hy)

/-- At a Prop motive, all actual evaluations are proofs. This requires
neither one constructor nor erasure of every ordinary constructor field. -/
theorem output_prop (C : Context) (hU : C.M.U = U W4)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref (policyFamilyLevels C.node.a.family))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hProp : ∀ ys,
      ys.length = C.node.a.family.parameters.length + C.node.a.family.indices.length →
      ∀ c, c ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
        ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ))) ys) → Equiv c pempty)
    {i : Index.{4}} {z : PSet.{4}} (hz : Eval C i z) : Equiv z pempty :=
  guarded_prop C.M hU C.σ _ C.motive C.parameters C.node.a.family.indices
    (push C.parameters ρ0) i pempty z
    (hz.mem_guarded_of_typed_motive .zero hU hmo hProp)

theorem functional (C : Context) (hU : C.M.U = U W4)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref (policyFamilyLevels C.node.a.family))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort .zero)))))
    (hProp : ∀ ys,
      ys.length = C.node.a.family.parameters.length + C.node.a.family.indices.length →
      ∀ c, c ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
        ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ))) ys) → Equiv c pempty)
    {i : Index.{4}} {z z' : PSet.{4}} (hz : Eval C i z) (hz' : Eval C i z') :
    Equiv z z' :=
  (output_prop C hU hmo hProp hz).trans (output_prop C hU hmo hProp hz').symm

end Rcic.F3.PSet.PropEvalProof
