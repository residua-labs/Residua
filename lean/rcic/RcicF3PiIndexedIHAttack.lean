import rcic.RcicF3PiIndexedIH
import rcic.RcicF3PiRecAttack

/-!
# Typed indexed IHs over an identical erased proof field

The domain is inhabited, Pi depth is positive, and an actual application
observes different data results at two indices. This is a semantic telescope
component witness; raw admitted-group production remains open. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.IndexedIHAttack
universe u

def domain : PSet.{u} := singleton (dataVal 7 [])
noncomputable def telescope (i : Nat) : RecTel.{u,0} Nat 1 := .pi domain (fun _ => .ret i)
def family (_ : Nat) : PSet.{u} := tv True
def target (i : Nat) (_ : PSet.{u}) : PSet.{u} := singleton (dataVal i [])
def mapper (i : Nat) (_ : PSet.{u}) : PSet.{u} := dataVal i []

theorem domain_dich : Dich (domain : PSet.{u}) :=
  Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
theorem domains (i : Nat) : (telescope.{u} i).DomainsDich :=
  ⟨domain_dich, fun _ => True.intro⟩
theorem target_dich (i : Nat) (x : PSet.{u}) : Dich (target i x) :=
  Or.inr (fun h => dataVal_ne_pempty i [] (mem_singleton.mp h).symm)

noncomputable def proofField (M : Interp.{u}) (i : Nat) : PSet.{u} :=
  (telescope i).erasedEncode M (fun _ => pempty)

theorem proofField_mem (M : Interp.{u}) (i : Nat) :
    proofField M i ∈ Ed M ((telescope i).erasedType M family) := by
  exact (telescope i).erasedEncode_mem M (domains i) family (fun _ => dich_tv True)
    (fun _ => pempty) (fun _ => mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)

theorem proofField_empty (M : Interp.{u}) (i : Nat) :
    Equiv (proofField M i) pempty := by
  have hL : LamProof M (tyv domain) (classFiber domain (fun _ => pempty)) := by
    intro a ha
    obtain ⟨j, hj⟩ := mem_congr_right (ed_tyv M domain_dich) ha
    exact (classFiber_congr domain _ hj.symm).trans (classFiber_at domain _ j)
  change Equiv (lamVal M (tyv domain) (classFiber domain (fun _ => pempty))) pempty
  unfold lamVal
  rw [cond_pos hL]
  exact Equiv.rfl

theorem erased_field_mem (M : Interp.{u}) (i : Nat) :
    pempty ∈ Ed M ((telescope i).erasedType M family) :=
  mem_congr_left (proofField_empty M i) (proofField_mem M i)

theorem indexed_member (M : Interp.{u}) (i : Nat) :
    (telescope i).indexedIH M mapper pempty ∈
      Ed M ((telescope i).erasedIHType M target pempty) := by
  exact (telescope i).indexedIH_mem M (domains i) family (fun _ => dich_tv True)
    target target_dich mapper (fun _ _ _ => mem_singleton.mpr Equiv.rfl)
    (erased_field_mem M i)

theorem application (M : Interp.{u}) (i : Nat) (x : PSet.{u}) :
    Equiv (fapp ((telescope i).indexedIH M mapper x) (dataVal 7 []))
      (dataVal i []) := by
  have ha : dataVal 7 [] ∈ (domain : PSet.{u}) := mem_singleton.mpr Equiv.rfl
  have ha' : dataVal 7 [] ∈ Ed M (tyv domain) :=
    mem_congr_right (ed_tyv M domain_dich).symm ha
  change Equiv (fapp (lamVal M (tyv domain)
    (classFiber domain (fun _ => dataVal i []))) (dataVal 7 [])) (dataVal i [])
  refine (beta_val M (fun _ _ h => classFiber_congr domain _ h) ha').trans ?_
  obtain ⟨j, hj⟩ := ha
  exact (classFiber_congr domain _ hj.symm).trans (classFiber_at domain _ j)

theorem indices_distinguished (M : Interp.{u}) :
    ¬ Equiv ((telescope 0).indexedIH M mapper pempty)
      ((telescope 1).indexedIH M mapper pempty) := by
  intro h
  have he : Equiv (dataVal 0 [] : PSet.{u}) (dataVal 1 []) :=
    (application M 0 pempty).symm.trans
      ((fapp_congr h Equiv.rfl).trans (application M 1 pempty))
  have htag : 0 = 1 := (dataVal_inj rfl he).1
  cases htag

/-- The premise data supplies an actual model for the semantic component. -/
theorem component_witness (P : Premises4) :
    let M := mkM P (fun _ _ => pempty)
    (∀ i, pempty ∈ Ed M ((telescope i).erasedType M family)) ∧
    (∀ i, (telescope i).indexedIH M mapper pempty ∈
      Ed M ((telescope i).erasedIHType M target pempty)) ∧
    ¬ Equiv ((telescope 0).indexedIH M mapper pempty)
      ((telescope 1).indexedIH M mapper pempty) := by
  exact ⟨erased_field_mem _, indexed_member _, indices_distinguished _⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ ((¬ Equiv ((telescope 0).indexedIH (mkM P (fun _ _ => pempty)) mapper pempty)
      ((telescope 1).indexedIH (mkM P (fun _ _ => pempty)) mapper pempty)) →
      (Premises4 → False)) := fun h => h (component_witness P).2.2 P

end Rcic.F3.PSet.IndexedIHAttack
