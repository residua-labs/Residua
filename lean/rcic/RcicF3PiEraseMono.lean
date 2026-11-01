import rcic.RcicF3PiEraseField
/-! Monotone transport for actual proof-erasing recursive fields at any
dependent depth. Canonical readback and candidate-independent encoding
retain both empty domains and the original field value. This is a semantic
field component; syntax/group production remains open. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecTel
universe u v
theorem erasedType_mono {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich) (X Y : I → PSet.{u})
    (hX : ∀ i, Dich (X i)) (hY : ∀ i, Dich (Y i))
    (hsub : ∀ i, Sub (X i) (Y i)) :
    Sub (Ed M (t.erasedType M X)) (Ed M (t.erasedType M Y)) := by
  intro f hf
  have hr := t.erasedRead_spec M ht X hX hf
  have hrel : t.Rel Y (t.erasedRead M f) := by
    apply (PiTel.all_iff _ _ _).mpr
    intro p
    exact hsub _ _ ((PiTel.all_iff _ _ _).mp hr.1 p)
  exact mem_congr_left hr.2.symm (t.erasedEncode_mem M ht Y hY _ hrel)
end Rcic.F3.PSet.RecTel
