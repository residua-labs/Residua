import rcic.RcicF3RawFamilyRec
import rcic.RcicF3Lvl

/-!
# Raw admitted-plan recursion at an independent syntax universe valuation

The family vector and recursor valuation agree only below the family's arity.
In particular, the motive may read an additional universe parameter. These
theorems retain the actual admitted plan, full dependent index key, and the
local minor contract. They do not produce that contract or a small closed frame.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.RawFamilyRec
open Rcic.Declarative RawFamily PiIndex

theorem node_unfold_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (vs : List Nat) (σ : Nat → Nat)
    (hB : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (hσ : ∀ i, i < node.a.family.member.arity → σ i = σOf vs i) {n : Nat}
    (hE : EnvSound (model P μ (famDataOf node.a)) σ K node.E0 n)
    (hb : BodiesOK node.E0 σ K)
    (hI : ∀ j : Fin node.a.constructors.length,
      ∀ A ∈ (node.a.constructorViews j).fields, InstOK node.E0 σ K A)
    (hF : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hc : Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hm : ConstructorMono P μ (famDataOf node.a))
    (h0 : evalTotal σ node.a.family.resultLevel ≠ 0)
    (ms : List PSet.{4}) (i : Index.{4}) (z : PSet.{4})
    (hz : z ∈ frame P μ (famDataOf node.a) vs i) :
    ∃ (j : Fin node.a.constructors.length) (ps xs : List PSet.{4}),
      TelFits (model P μ (famDataOf node.a)) σ node.a.family.parameters ρ0 ps ∧
      TelFits (model P μ (famDataOf node.a)) σ
        (node.a.constructorViews j).fields (push ps ρ0) xs ∧
      i = key (ps ++ (node.a.constructorViews j).resultIndices.map
        (den (model P μ (famDataOf node.a)) σ (push xs (push ps ρ0)))) ∧
      Equiv z (dataVal j.val xs) ∧
      Equiv (RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms z)
        (fapps (ms.getD j.val pempty)
          (RecPlan.args (RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms)
            (node.h14.shapesAt j) xs)) := by
  obtain ⟨j, ps, xs, hp, hx, _, hi, hz⟩ :=
    frame_dense P μ (famDataOf node.a) hF hc hm vs i z hz
  let j' : Fin node.a.constructors.length :=
    ⟨j.val, by rw [← famDataOf_ctors_length node.a]; exact j.isLt⟩
  have hget : (famDataOf node.a).ctors[j.val]? =
      some ((famDataOf node.a).ctors.get j) :=
    List.getElem?_eq_some_iff.mpr ⟨j.isLt, rfl⟩
  have hj : (famDataOf node.a).ctors.get j =
      ((node.a.constructorViews j').fields, (node.a.constructorViews j').resultIndices) :=
    Option.some.inj (hget.symm.trans (famDataOf_ctor node.a j'))
  have hcb := hB.ctors _ (List.getElem?_mem (famDataOf_ctor node.a j'))
  rw [hj] at hx hi
  have ht : evalTotal (σOf vs) (famDataOf node.a).resLevel ≠ 0 := by
    rw [← evalTotal_agree hσ _ hB.res]
    exact h0
  rw [if_neg ht] at hz
  have hp' := (TelFits_levels (model P μ (famDataOf node.a)) hσ
    node.a.family.parameters hB.params ρ0 ps).mpr hp
  have hx' := (TelFits_levels (model P μ (famDataOf node.a)) hσ
    (node.a.constructorViews j').fields hcb.1 (push ps ρ0) xs).mpr hx
  have hi' : i = key (ps ++ (node.a.constructorViews j').resultIndices.map
      (den (model P μ (famDataOf node.a)) σ (push xs (push ps ρ0)))) := by
    rw [map_den_levels (model P μ (famDataOf node.a)) hσ _ hcb.2]
    exact hi
  refine ⟨j', ps, xs, hp', hx', hi', hz, ?_⟩
  exact (recCore_resp _ (RecPlan.descriptor f (RecPlan.nodePlan node)) ms z _ hz).trans
    (RecPlan.node_data_of_fits _ σ K node hE hb ms j' (hI j') (push ps ρ0) xs hx')

/-- On the data-family face, the local minor contract and motive stay at the
syntax valuation, retaining the motive universe above the family arity. -/
theorem produce_local_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (vs : List Nat) (σ : Nat → Nat)
    (hB : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (hσ : ∀ i, i < node.a.family.member.arity → σ i = σOf vs i) {n : Nat}
    (hE : EnvSound (model P μ (famDataOf node.a)) σ K node.E0 n)
    (hb : BodiesOK node.E0 σ K)
    (hI : ∀ j : Fin node.a.constructors.length,
      ∀ A ∈ (node.a.constructorViews j).fields, InstOK node.E0 σ K A)
    (hF : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hc : Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hm : ConstructorMono P μ (famDataOf node.a))
    (h0 : evalTotal σ node.a.family.resultLevel ≠ 0)
    (ms : List PSet.{4})
    (Q : Index.{4} → PSet.{4} → PSet.{4})
    (hQ : ∀ i x y, Equiv x y → Equiv (Q i x) (Q i y))
    (hstep : ∀ (j : Fin node.a.constructors.length) ps xs,
      TelFits (model P μ (famDataOf node.a)) σ node.a.family.parameters ρ0 ps →
      TelFits (model P μ (famDataOf node.a)) σ
        (node.a.constructorViews j).fields (push ps ρ0) xs →
      (∀ i y, MemT y (dataVal j.val xs) →
        y ∈ frame P μ (famDataOf node.a) vs i →
        RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms y ∈ Q i y) →
      fapps (ms.getD j.val pempty)
        (RecPlan.args (RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms)
          (node.h14.shapesAt j) xs) ∈
      Q (key (ps ++ (node.a.constructorViews j).resultIndices.map
        (den (model P μ (famDataOf node.a)) σ (push xs (push ps ρ0)))))
        (dataVal j.val xs)) :
    ∀ i z, z ∈ frame P μ (famDataOf node.a) vs i →
      RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms z ∈ Q i z := by
  have hsound : ∀ z i, z ∈ frame P μ (famDataOf node.a) vs i →
      RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms z ∈ Q i z := by
    intro z
    induction z using memT_wf.induction with
    | h z ih =>
      intro i hz
      obtain ⟨j, ps, xs, hp, hx, hi, he, hunfold⟩ :=
        node_unfold_at P μ K node vs σ hB hσ hE hb hI hF hc hm h0 ms i z hz
      subst i
      have hs := hstep j ps xs hp hx (fun i y hy hf =>
        ih y (hy.congr_right he.symm) i hf)
      exact mem_congr_right (hQ _ _ z he.symm)
        (mem_congr_left hunfold.symm hs)
  intro i z hz
  exact hsound z i hz

/-- Fixed-parameter recursion at an arbitrary syntax valuation. The local IH is
restricted both by the full index key's parameter prefix and by membership
below the current constructor. -/
theorem produce_at_parameters_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (vs : List Nat) (σ : Nat → Nat)
    (hB : FamBounded (famDataOf node.a) node.a.family.member.arity)
    (hσ : ∀ i, i < node.a.family.member.arity → σ i = σOf vs i) {n : Nat}
    (hE : EnvSound (model P μ (famDataOf node.a)) σ K node.E0 n)
    (hb : BodiesOK node.E0 σ K)
    (hI : ∀ j : Fin node.a.constructors.length,
      ∀ A ∈ (node.a.constructorViews j).fields, InstOK node.E0 σ K A)
    (hF : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hc : Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hm : ConstructorMono P μ (famDataOf node.a))
    (h0 : evalTotal σ node.a.family.resultLevel ≠ 0)
    (ps₀ : List PSet.{4}) (ms : List PSet.{4})
    (Q : Index.{4} → PSet.{4} → PSet.{4})
    (hQ : ∀ i x y, Equiv x y → Equiv (Q i x) (Q i y))
    (hstep : ∀ (j : Fin node.a.constructors.length) ps xs,
      TelFits (model P μ (famDataOf node.a)) σ node.a.family.parameters ρ0 ps →
      LEq ps ps₀ →
      TelFits (model P μ (famDataOf node.a)) σ
        (node.a.constructorViews j).fields (push ps ρ0) xs →
      (∀ i y, paramKey node.a.family.parameters.length i = key ps₀ →
        MemT y (dataVal j.val xs) →
        y ∈ frame P μ (famDataOf node.a) vs i →
        RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms y ∈ Q i y) →
      fapps (ms.getD j.val pempty)
        (RecPlan.args (RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms)
          (node.h14.shapesAt j) xs) ∈
      Q (key (ps ++ (node.a.constructorViews j).resultIndices.map
        (den (model P μ (famDataOf node.a)) σ (push xs (push ps ρ0)))))
        (dataVal j.val xs)) :
    ∀ i z, paramKey node.a.family.parameters.length i = key ps₀ →
      z ∈ frame P μ (famDataOf node.a) vs i →
      RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms z ∈ Q i z := by
  have hsound : ∀ z i, paramKey node.a.family.parameters.length i = key ps₀ →
      z ∈ frame P μ (famDataOf node.a) vs i →
      RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms z ∈ Q i z := by
    intro z
    induction z using memT_wf.induction with
    | h z ih =>
      intro i hi₀ hz
      obtain ⟨j, ps, xs, hp, hx, hi, he, hunfold⟩ :=
        node_unfold_at P μ K node vs σ hB hσ hE hb hI hF hc hm h0 ms i z hz
      subst i
      have hp₀ := paramKey_reflect node.a.family.parameters.length ps ps₀ _ hp.length hi₀
      have hs := hstep j ps xs hp hp₀ hx (fun i y hi₀ hy hf =>
        ih y (hy.congr_right he.symm) i hi₀ hf)
      exact mem_congr_right (hQ _ _ z he.symm)
        (mem_congr_left hunfold.symm hs)
  intro i z hi₀ hz
  exact hsound z i hi₀ hz

end Rcic.F3.PSet.RawFamilyRec
