import rcic.RcicF3RawFamilyInduction
import rcic.RcicF3PiRecExtract
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyRec
open Rcic.Declarative RawFamily PiIndex
noncomputable abbrev model (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) : Interp.{4} := mkM P (table P μ fd (frame P μ fd))
theorem node_unfold (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (vs : List Nat) {n : Nat}
    (hE : EnvSound (model P μ (famDataOf node.a)) (σOf vs) K node.E0 n)
    (hb : BodiesOK node.E0 (σOf vs) K)
    (hI : ∀ j : Fin node.a.constructors.length,
      ∀ A ∈ (node.a.constructorViews j).fields, InstOK node.E0 (σOf vs) K A)
    (hF : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hc : Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hm : ConstructorMono P μ (famDataOf node.a))
    (h0 : evalTotal (σOf vs) node.a.family.resultLevel ≠ 0)
    (ms : List PSet.{4}) (i : Index.{4}) (z : PSet.{4})
    (hz : z ∈ frame P μ (famDataOf node.a) vs i) :
    ∃ (j : Fin node.a.constructors.length) (ps xs : List PSet.{4}),
      TelFits (model P μ (famDataOf node.a)) (σOf vs) node.a.family.parameters ρ0 ps ∧
      TelFits (model P μ (famDataOf node.a)) (σOf vs)
        (node.a.constructorViews j).fields (push ps ρ0) xs ∧
      i = key (ps ++ (node.a.constructorViews j).resultIndices.map
        (den (model P μ (famDataOf node.a)) (σOf vs) (push xs (push ps ρ0)))) ∧
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
      some ((famDataOf node.a).ctors.get j) := by
    exact List.getElem?_eq_some_iff.mpr ⟨j.isLt, rfl⟩
  have hj : (famDataOf node.a).ctors.get j =
      ((node.a.constructorViews j').fields, (node.a.constructorViews j').resultIndices) := by
    exact Option.some.inj (hget.symm.trans (famDataOf_ctor node.a j'))
  rw [hj] at hx hi
  have ht : evalTotal (σOf vs) (famDataOf node.a).resLevel ≠ 0 := h0
  rw [if_neg ht] at hz
  refine ⟨j', ps, xs, hp, hx, hi, hz, ?_⟩
  exact (recCore_resp _ (RecPlan.descriptor f (RecPlan.nodePlan node)) ms z _ hz).trans
    (RecPlan.node_data_of_fits _ (σOf vs) K node hE hb ms j' (hI j') (push ps ρ0) xs hx)
/-- Well-founded recursion at the literal admitted raw family. The minor
contract receives mapping soundness only below this constructor. Paying that
local contract from typed minor syntax remains a production obligation. -/
theorem produce_local (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (vs : List Nat) {n : Nat}
    (hE : EnvSound (model P μ (famDataOf node.a)) (σOf vs) K node.E0 n)
    (hb : BodiesOK node.E0 (σOf vs) K)
    (hI : ∀ j : Fin node.a.constructors.length,
      ∀ A ∈ (node.a.constructorViews j).fields, InstOK node.E0 (σOf vs) K A)
    (hF : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hc : Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hm : ConstructorMono P μ (famDataOf node.a))
    (h0 : evalTotal (σOf vs) node.a.family.resultLevel ≠ 0)
    (ms : List PSet.{4})
    (Q : Index.{4} → PSet.{4} → PSet.{4})
    (hQ : ∀ i x y, Equiv x y → Equiv (Q i x) (Q i y))
    (hstep : ∀ (j : Fin node.a.constructors.length) ps xs,
      TelFits (model P μ (famDataOf node.a)) (σOf vs) node.a.family.parameters ρ0 ps →
      TelFits (model P μ (famDataOf node.a)) (σOf vs)
        (node.a.constructorViews j).fields (push ps ρ0) xs →
      (∀ i y, MemT y (dataVal j.val xs) →
        y ∈ frame P μ (famDataOf node.a) vs i →
        RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms y ∈ Q i y) →
      fapps (ms.getD j.val pempty)
        (RecPlan.args (RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms)
          (node.h14.shapesAt j) xs) ∈
      Q (key (ps ++ (node.a.constructorViews j).resultIndices.map
        (den (model P μ (famDataOf node.a)) (σOf vs) (push xs (push ps ρ0)))))
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
        node_unfold P μ K node vs hE hb hI hF hc hm h0 ms i z hz
      subst i
      have hs := hstep j ps xs hp hx (fun i y hy hf =>
        ih y (hy.congr_right he.symm) i hf)
      exact mem_congr_right (hQ _ _ z he.symm)
        (mem_congr_left hunfold.symm hs)
  intro i z hz
  exact hsound z i hz
/-- The parameter prefix descends to extensional full argument keys. -/
def paramKey (np : Nat) : Index.{4} → Index.{4} :=
  Quotient.lift (fun xs => key (xs.take np))
    (fun _ _ h => (key_eq_iff _ _).mpr (LEq.take h np))
theorem paramKey_append (ps is : List PSet.{4}) :
    paramKey ps.length (key (ps ++ is)) = key ps := by
  change key ((ps ++ is).take ps.length) = key ps
  rw [List.take_left]
theorem paramKey_reflect (np : Nat) (ps ps₀ is : List PSet.{4})
    (hl : ps.length = np)
    (he : paramKey np (key (ps ++ is)) = key ps₀) : LEq ps ps₀ := by
  rw [← hl, paramKey_append] at he
  exact (key_eq_iff _ _).mp he

theorem produce_at_parameters (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (vs : List Nat) {n : Nat}
    (hE : EnvSound (model P μ (famDataOf node.a)) (σOf vs) K node.E0 n)
    (hb : BodiesOK node.E0 (σOf vs) K)
    (hI : ∀ j : Fin node.a.constructors.length,
      ∀ A ∈ (node.a.constructorViews j).fields, InstOK node.E0 (σOf vs) K A)
    (hF : Admissible (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hc : Closed P μ (famDataOf node.a) (frame P μ (famDataOf node.a)))
    (hm : ConstructorMono P μ (famDataOf node.a))
    (h0 : evalTotal (σOf vs) node.a.family.resultLevel ≠ 0)
    (ps₀ : List PSet.{4}) (ms : List PSet.{4})
    (Q : Index.{4} → PSet.{4} → PSet.{4})
    (hQ : ∀ i x y, Equiv x y → Equiv (Q i x) (Q i y))
    (hstep : ∀ (j : Fin node.a.constructors.length) ps xs,
      TelFits (model P μ (famDataOf node.a)) (σOf vs) node.a.family.parameters ρ0 ps →
      LEq ps ps₀ →
      TelFits (model P μ (famDataOf node.a)) (σOf vs)
        (node.a.constructorViews j).fields (push ps ρ0) xs →
      (∀ i y, paramKey node.a.family.parameters.length i = key ps₀ →
        MemT y (dataVal j.val xs) →
        y ∈ frame P μ (famDataOf node.a) vs i →
        RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms y ∈ Q i y) →
      fapps (ms.getD j.val pempty)
        (RecPlan.args (RecPlan.nodeCore (model P μ (famDataOf node.a)) node ms)
          (node.h14.shapesAt j) xs) ∈
      Q (key (ps ++ (node.a.constructorViews j).resultIndices.map
        (den (model P μ (famDataOf node.a)) (σOf vs) (push xs (push ps ρ0)))))
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
        node_unfold P μ K node vs hE hb hI hF hc hm h0 ms i z hz
      subst i
      have hp₀ := paramKey_reflect node.a.family.parameters.length ps ps₀ _ hp.length hi₀
      have hs := hstep j ps xs hp hp₀ hx (fun i y hi₀ hy hf =>
        ih y (hy.congr_right he.symm) i hi₀ hf)
      exact mem_congr_right (hQ _ _ z he.symm)
        (mem_congr_left hunfold.symm hs)
  intro i z hi₀ hz
  exact hsound z i hi₀ hz
end Rcic.F3.PSet.RawFamilyRec
