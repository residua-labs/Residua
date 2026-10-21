import rcic.RcicNativeFamilyObservation
import rcic.RcicNativeFamilyProjection

set_option autoImplicit false

/-!
# Native family-slot composition at explicit left domains

These consumers construct the slot evidence for transitivity and symmetry.
The second leg is full ConvArgsT, so neither a nonzero sorting of the middle
domain nor a middle-slot existence assumption is needed. The only alignment
input is a native TyConvT between the concrete instantiated domains at
relevant slots. This is not a family observation producer: producing those
domain chains, and reflecting semantic slot equality, remain open.
The telescope and its universe instantiation are fixed here.
closure_claim = 0.
-/

namespace Rcic.Declarative.NativeFamilyObservationAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
variable {pre ds xs ys zs : List (Expr Nat)} {U : Expr Nat}

/-- Mixed native composition keeps the final conversion at the LEFT
instantiated domain. Existing ConvArgsT length and slot projections are reused. -/
theorem relevantSlotConv_trans_convArgsT_of_domainConv
    (hxy : RelevantSlotConv E n Γ pre ds xs ys)
    (hyz : ConvArgsT E n Γ (instPrefix pre (policyPi ds U)) ys zs)
    (hdom : ∀ i d u, ds[i]? = some d →
      HasTyT E n Γ (instPrefix (pre ++ xs.take i) d) (.sort u) →
      u ≠ .zero →
      Nonempty (TyConvT E n Γ
        (instPrefix (pre ++ ys.take i) d)
        (instPrefix (pre ++ xs.take i) d))) :
    RelevantSlotConv E n Γ pre ds xs zs := by
  intro i x z d u hx hz hd hdu hu
  have hiZ : i < zs.length := (List.getElem?_eq_some_iff.mp hz).1
  have hlen := NativeFamilyProjection.convArgs_length hyz
  have hiY : i < ys.length := by omega
  let y := ys[i]
  have hy : ys[i]? = some y := List.getElem?_eq_getElem hiY
  obtain ⟨cxy⟩ := hxy i x y d u hx hy hd hdu hu
  obtain ⟨cyz⟩ := convArgsT_slot_of_telescope hyz pre ds U rfl i y z d hy hz hd
  obtain ⟨cdom⟩ := hdom i d u hd hdu hu
  exact ⟨ConvT.trans Γ x y z _ cxy (convT_of_tyConv cyz cdom)⟩

/-- Full original slot evidence can be reversed at the new left domain
without demanding that a relevance bit transport across sorts. -/
theorem relevantSlotConv_symm_convArgsT_of_domainConv
    (hxy : ConvArgsT E n Γ (instPrefix pre (policyPi ds U)) xs ys)
    (hdom : ∀ i d u, ds[i]? = some d →
      HasTyT E n Γ (instPrefix (pre ++ ys.take i) d) (.sort u) →
      u ≠ .zero →
      Nonempty (TyConvT E n Γ
        (instPrefix (pre ++ xs.take i) d)
        (instPrefix (pre ++ ys.take i) d))) :
    RelevantSlotConv E n Γ pre ds ys xs := by
  intro i y x d u hy hx hd hdu hu
  obtain ⟨cxy⟩ := convArgsT_slot_of_telescope hxy pre ds U rfl i x y d hx hy hd
  obtain ⟨cdom⟩ := hdom i d u hd hdu hu
  exact ⟨convT_of_tyConv (ConvT.symm Γ x y _ cxy) cdom⟩

end Rcic.Declarative.NativeFamilyObservationAudit
