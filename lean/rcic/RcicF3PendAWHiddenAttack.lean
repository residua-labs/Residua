import rcic.RcicF3PendAWHiddenFixture
import rcic.RcicF3PiRecExtractAttack
import rcic.RcicF3PiRecPlanAttack
/-!
# Typed beta-hidden recursor regression

The complete typed PendA fixture is admitted at depth 1; the stored raw
recursor reads depth 0. A well-typed empty function field and a semantic
minor separate their outputs by membership in a singleton data motive.
This is an operational and local minor-typing regression, not a refutation
of the complete GInv/StepAG statement. The arbitrary reference `f` tests
renumbering in the semantic calculation. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PendAWHiddenAttack
open Rcic.Declarative RecPlan

def hidden (f : Nat) : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (Rcic.Declarative.lift 0 1 (PiRawCtorAttack.paramField f))) (.sort .zero)
def fd (f : Nat) : FamData :=
  ⟨f, [.sort (.succ .zero)], [], .succ .zero,
    [([], []), ([hidden f], [])], .anySort⟩
def datum : PSet.{4} := dataVal 0 []
def proofDom : PSet.{4} := tyv (tv True)
def minor (M : Interp.{4}) : PSet.{4} :=
  lamVal M proofDom (fun _ => lamVal M proofDom (fun _ => datum))

theorem empty_tag : Equiv (tagOf (pempty : PSet.{4})) (ord 0) := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨⟨⟨⟨⟨i, _⟩, _⟩, _⟩, _⟩, _⟩ := hz
    exact i.1.1.elim
  · intro hz
    exact (not_mem_pempty hz).elim

theorem core_empty (M : Interp.{4}) (f : Nat) (ms : List PSet.{4}) :
    Equiv (recCore M (fd f) ms pempty) (ms.getD 0 pempty) := by
  rw [recCore_eq]
  unfold recBody
  have hj : 0 < (fd f).ctors.length := Nat.zero_lt_succ 1
  rw [findIdx_eq M _ empty_tag
    (fun i hi => (ord_inj (empty_tag.symm.trans hi)).symm) (fd f).ctors.length hj]
  exact Equiv.rfl

theorem minor_spec (M : Interp.{4}) :
    minor M ∈ Ed M (piVal M proofDom (fun _ =>
      piVal M proofDom (fun _ => tyv (singleton datum)))) ∧
    Equiv (fapps (minor M) [pempty, pempty]) datum ∧
    Equiv (fapps (minor M) [pempty, datum]) pempty := by
  have ep : Equiv (Ed M proofDom) (tv True) := ed_tyv M (dich_tv True)
  have hp : pempty ∈ Ed M proofDom :=
    mem_congr_right ep.symm (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  have hd : Dich (singleton datum) := Or.inr (fun h =>
    dataVal_ne_pempty 0 [] (mem_singleton.mp h).symm)
  have hm : datum ∈ Ed M (tyv (singleton datum)) :=
    mem_congr_right (ed_tyv M hd).symm (mem_singleton.mpr Equiv.rfl)
  have hi : lamVal M proofDom (fun _ => datum) ∈
      Ed M (piVal M proofDom (fun _ => tyv (singleton datum))) :=
    lam_mem M (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl) (fun _ _ => hm)
  refine ⟨lam_mem M (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl)
    (fun _ _ => hi), ?_, ?_⟩
  · exact (fapp_congr (beta_val M (b := fun _ => lamVal M proofDom (fun _ => datum))
      (fun _ _ _ => Equiv.rfl) hp) Equiv.rfl).trans
      (beta_val M (fun _ _ _ => Equiv.rfl) hp)
  · apply (fapp_congr (beta_val M (b := fun _ => lamVal M proofDom (fun _ => datum))
      (fun _ _ _ => Equiv.rfl) hp) Equiv.rfl).trans
    have hn : ¬ datum ∈ Ed M proofDom := fun h =>
      dataVal_ne_pempty 0 [] (mem_tv.mp (mem_congr_right ep h)).2
    cases M.dec (LamProof M proofDom (fun _ => datum)) with
    | isTrue hL =>
      change Equiv (fapp (cond M.dec _ _ _) datum) pempty
      rw [cond_pos hL]
      exact fapp_pempty datum
    | isFalse hL =>
      change Equiv (fapp (cond M.dec _ _ _) datum) pempty
      rw [cond_neg hL]
      exact fapp_mkLam_out hn

theorem empty_product (M : Interp.{4}) (X : PSet.{4}) :
    Equiv (Ed M (piVal M (tyv pempty) (fun _ => tyv X))) (tv True) := by
  have he : Equiv (Ed M (tyv (pempty : PSet.{4}))) pempty :=
    ed_tyv M (Or.inr not_mem_pempty)
  have hp : PiProp M (tyv pempty) (fun _ => tyv X) :=
    fun _ h => (not_mem_pempty (mem_congr_right he h)).elim
  apply (ed_piVal M (tyv pempty) (fun _ => tyv X) (fun _ _ _ => Equiv.rfl)).trans
  rw [cond_pos hp]
  apply tv_congr
  constructor
  · intro _; trivial
  · intro _ x hx
    exact (not_mem_pempty (mem_congr_right he hx)).elim

theorem raw_failure (M : Interp.{4}) (f : Nat) :
    Equiv (recCore M (fd f) [datum, minor M] (dataVal 1 [pempty])) pempty := by
  have ho : occursConst f (hidden f) = true := by
    simp [hidden, PiRawCtorAttack.paramField, occursConst, Rcic.Declarative.lift]
  have hc : ihChildL f (dataVal 1 [pempty]) [hidden f] [pempty] :=
    ihChildL_of_depth0 f _ _ _ (fun A hA _ => by
      have ha := List.mem_singleton.mp hA
      subst A
      rfl)
  have h := recCore_data M (fd f) [datum, minor M]
    (j := 1) (xs := [pempty]) Equiv.rfl (Nat.lt_succ_self 1) rfl hc
  change Equiv (recCore M (fd f) [datum, minor M] (dataVal 1 [pempty]))
    (fapps (minor M) (ihArgs f (recCore M (fd f) [datum, minor M]) [hidden f] [pempty])) at h
  rw [ihArgs, ho, if_pos rfl] at h
  have he : Equiv (recCore M (fd f) [datum, minor M] pempty) datum :=
    core_empty M f [datum, minor M]
  have hl : LEq [pempty, recCore M (fd f) [datum, minor M] pempty] [pempty, datum] :=
    ⟨Equiv.rfl, he, True.intro⟩
  exact h.trans ((fapps_congr_args (minor M) hl).trans
    (minor_spec M).2.2)

theorem normalized_success (M : Interp.{4}) (f : Nat) :
    Equiv (core M f [[], [.recursive 1]] [datum, minor M] (dataVal 1 [pempty])) datum := by
  have hc : Children f (dataVal 1 [pempty]) [.recursive 1] [pempty] := by
    refine ⟨fun _ => ?_, True.intro⟩
    intro y hy
    exact (not_mem_pempty (mem_congr_right sImage_pfst_pempty hy)).elim
  have h := core_data M f [[], [.recursive 1]] [datum, minor M]
    (j := 1) rfl (xs := [pempty]) Equiv.rfl rfl hc
  have he : Equiv (ihAtN (core M f [[], [.recursive 1]] [datum, minor M]) 1 pempty) pempty :=
    ihAtN_empty_succ _ 0 Equiv.rfl
  have hl : LEq [pempty, ihAtN (core M f [[], [.recursive 1]] [datum, minor M]) 1 pempty]
      [pempty, pempty] := ⟨Equiv.rfl, he, True.intro⟩
  exact h.trans ((fapps_congr_args (minor M) hl).trans (minor_spec M).2.1)

theorem minor_typed (M : Interp.{4}) (X : PSet.{4}) :
    minor M ∈ Ed M (piVal M (piVal M (tyv pempty) (fun _ => tyv X))
      (fun _ => piVal M (piVal M (tyv pempty) (fun _ => tyv (singleton datum)))
        (fun _ => tyv (singleton datum)))) := by
  have ep : ∀ Y : PSet.{4}, Equiv (Ed M proofDom)
      (Ed M (piVal M (tyv pempty) (fun _ => tyv Y))) :=
    fun Y => (ed_tyv M (dich_tv True)).trans (empty_product M Y).symm
  have ei : Equiv (piVal M proofDom (fun _ => tyv (singleton datum)))
      (piVal M (piVal M (tyv pempty) (fun _ => tyv (singleton datum)))
        (fun _ => tyv (singleton datum))) :=
    piVal_ed_congr_on M (ep (singleton datum))
      (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl) (fun _ _ => Equiv.rfl)
  have eo : Equiv (piVal M proofDom (fun _ =>
      piVal M proofDom (fun _ => tyv (singleton datum))))
      (piVal M (piVal M (tyv pempty) (fun _ => tyv X)) (fun _ =>
        piVal M (piVal M (tyv pempty) (fun _ => tyv (singleton datum)))
          (fun _ => tyv (singleton datum)))) :=
    piVal_ed_congr_on M (ep X)
      (fun _ _ _ => Equiv.rfl) (fun _ _ _ => Equiv.rfl) (fun _ _ => ed_congr M ei)
  exact mem_congr_right (ed_congr M eo) (minor_spec M).1

theorem counterexample (M : Interp.{4}) (f : Nat) (X : PSet.{4}) :
    pempty ∈ Ed M (piVal M (tyv pempty) (fun _ => tyv X)) ∧
    minor M ∈ Ed M (piVal M (piVal M (tyv pempty) (fun _ => tyv X))
      (fun _ => piVal M (piVal M (tyv pempty) (fun _ => tyv (singleton datum)))
        (fun _ => tyv (singleton datum)))) ∧
    ¬ recCore M (fd f) [datum, minor M] (dataVal 1 [pempty]) ∈
      Ed M (tyv (singleton datum)) ∧
    core M f [[], [.recursive 1]] [datum, minor M] (dataVal 1 [pempty]) ∈
      Ed M (tyv (singleton datum)) ∧
    ¬ Equiv (recCore M (fd f) [datum, minor M] (dataVal 1 [pempty]))
      (core M f [[], [.recursive 1]] [datum, minor M] (dataVal 1 [pempty])) := by
  have hd : Dich (singleton datum) := Or.inr (fun h =>
    dataVal_ne_pempty 0 [] (mem_singleton.mp h).symm)
  have ed := ed_tyv M hd
  refine ⟨mem_congr_right (empty_product M X).symm
    (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩), minor_typed M X, ?_, ?_, ?_⟩
  · intro hr
    have he := mem_singleton.mp (mem_congr_right ed hr)
    exact dataVal_ne_pempty 0 [] (he.symm.trans (raw_failure M f))
  · exact mem_congr_right ed.symm
      (mem_singleton.mpr (normalized_success M f))
  · intro he
    exact dataVal_ne_pempty 0 []
      ((normalized_success M f).symm.trans (he.symm.trans (raw_failure M f)))


kernel_rfl_theorem admitted_descriptor : famDataOf PendAWHidden.pNode.a = fd 4
kernel_rfl_theorem admitted_plan : nodePlan PendAWHidden.pNode = [[], [.recursive 1]]
kernel_rfl_theorem raw_depth : ihDepth PendAWHidden.field = 0
kernel_rfl_theorem raw_plan : rawPlan (famDataOf PendAWHidden.pNode.a) = [[], [.recursive 0]]

/-- A complete typed PendA group exposes the operational mismatch. This is
not yet a refutation of the full GInv/StepAG statement. -/
theorem typed_counterexample (M : Interp.{4}) :
    Nonempty (EnvWfT PendAWHidden.eAll) ∧ PendA PendAWHidden.pNode ∧
    ¬ Equiv (recCore M (famDataOf PendAWHidden.pNode.a)
        [datum, minor M] (dataVal 1 [pempty]))
      (nodeCore M PendAWHidden.pNode [datum, minor M] (dataVal 1 [pempty])) := by
  refine ⟨⟨PendAWHidden.envWfT⟩, PendAWHidden.pendA, ?_⟩
  rw [admitted_descriptor]
  change ¬ Equiv (recCore M (fd 4) [datum, minor M] (dataVal 1 [pempty]))
    (core M 4 (nodePlan PendAWHidden.pNode) [datum, minor M] (dataVal 1 [pempty]))
  rw [admitted_plan]
  exact (counterexample M 4 pempty).2.2.2.2

end Rcic.F3.PSet.PendAWHiddenAttack
