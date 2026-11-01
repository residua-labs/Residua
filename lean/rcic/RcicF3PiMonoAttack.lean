import rcic.RcicF3PiIndependentMono
import rcic.RcicF3PiIndependentAttack
import rcic.RcicF3PiEraseFixture
/-!
# Monotonicity attacks for dependent recursive fields

Three dependent binders retain the same encoded value under strict fibre
inclusion, at every numeric offset. Empty inner domains remain valid with
empty source fibres; a value returned at the wrong dependent index is refused.
These are semantic compiler tests, not universal family production.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiMonoAttack
open PiEraseFixture

def wider (i : Nat) : PSet.{0} := pair (dataVal i []) (dataVal (i + 1) [])
def voidTel : RecTel.{0,0} PUnit.{1} 2 :=
  .pi PiErasureAttack.domain (fun _ => .pi pempty (fun _ => .ret .unit))

theorem dependent_transport (M : Interp.{0}) (offset : Nat) :
    ∃ f, f ∈ Ed M ((nestedTel offset).erasedType M nestedFibre) ∧
      f ∈ Ed M ((nestedTel offset).erasedType M wider) ∧
      ∃ z, z ∈ wider offset ∧ z ∉ nestedFibre offset := by
  have hW : ∀ i, Dich (wider i) := by
    intro i
    apply Or.inr
    intro hz
    rcases mem_pair.mp hz with h | h
    · exact dataVal_ne_pempty i [] h.symm
    · exact dataVal_ne_pempty (i + 1) [] h.symm
  have hsub : ∀ i, Sub (nestedFibre i) (wider i) := by
    intro i z hz
    exact mem_pair.mpr (Or.inl (mem_singleton.mp hz))
  obtain ⟨f, hf⟩ := nested_product M offset
  refine ⟨f, hf, (nestedTel offset).erasedType_mono M (nestedDomainsDich offset)
    nestedFibre wider nestedFibre_dich hW hsub f hf, dataVal (offset + 1) [],
    mem_pair.mpr (Or.inr Equiv.rfl), ?_⟩
  intro hz
  have h := (dataVal_inj (by rfl) (mem_singleton.mp hz)).1
  omega
theorem void_transport (M : Interp.{0}) :
    ∃ f, f ∈ Ed M (voidTel.erasedType M (fun _ => pempty)) ∧
      f ∈ Ed M (voidTel.erasedType M (fun _ => PiErasureAttack.domain)) ∧
      ¬ pempty ∈ PiErasureAttack.literal.{0} := by
  have hd : voidTel.DomainsDich :=
    ⟨Or.inr (fun h => tyv_ne_pempty _ (mem_singleton.mp h).symm),
      fun _ => ⟨Or.inr not_mem_pempty, fun _ => trivial⟩⟩
  have hx : ∀ _ : PUnit.{1}, Dich (pempty : PSet.{0}) :=
    fun _ => Or.inr not_mem_pempty
  have hy : ∀ _ : PUnit.{1}, Dich (PiErasureAttack.domain : PSet.{0}) :=
    fun _ => Or.inr (fun h => tyv_ne_pempty _ (mem_singleton.mp h).symm)
  let v : PiTel.Value.{0,1} voidTel.tel (fun _ => PSet.{0}) :=
    fun _ r => Quotient.lift (fun i => PEmpty.elim i)
      (fun i => PEmpty.elim i) r
  have hr : voidTel.Rel (fun _ => pempty) v := by
    intro q r
    exact Quotient.inductionOn r (fun i => PEmpty.elim i)
  let f := voidTel.erasedEncode M v
  have hf := voidTel.erasedEncode_mem M hd _ hx v hr
  exact ⟨f, hf, voidTel.erasedType_mono M hd _ _ hx hy
    (fun _ _ h => (not_mem_pempty h).elim) f hf,
    (PiErasureAttack.nested_empty_domain.{0,0} M).2⟩
theorem wrong_index_refused (M : Interp.{0}) (offset : Nat) :
    (nestedTel offset).erasedEncode M (fun _ _ _ => dataVal offset []) ∉
      Ed M ((nestedTel offset).erasedType M wider) := by
  have hW : ∀ i, Dich (wider i) := by
    intro i
    apply Or.inr
    intro hz
    rcases mem_pair.mp hz with h | h
    · exact dataVal_ne_pempty i [] h.symm
    · exact dataVal_ne_pempty (i + 1) [] h.symm
  intro hf
  have hr := ((nestedTel offset).erasedEncode_mem_iff M (nestedDomainsDich offset)
    wider hW _).mp hf
  have hb := hr (natCls 0) (Quotient.mk _ ⟨Nat.lt_succ_self 0⟩) (natCls 2)
  change dataVal offset [] ∈ wider (offset + 0 + 2) at hb
  rcases mem_pair.mp hb with h | h
  · have hn := (dataVal_inj (by rfl) h).1
    omega
  · have hn := (dataVal_inj (by rfl) h).1
    omega
end Rcic.F3.PSet.PiMonoAttack
