import rcic.RcicF3PiRecBridge

/-!
# Indexed IH construction over the actual erased telescope

Each leaf map receives its full semantic index. The actual telescope domains
are used even when the ordinary field is erased to pempty. This component
retains typed field and leaf-map premises; it does not produce universal
raw recursor soundness. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet
universe u v

def RecTel.indexedIH {I : Type v} (M : Interp.{u})
    (g : I → PSet.{u} → PSet.{u}) :
    {m : Nat} → RecTel.{u,v} I m → PSet.{u} → PSet.{u}
  | _, .ret i, x => g i x
  | _, .pi A B, x => lamVal M (tyv A) (classFiber A
      (fun q => (B q).indexedIH M g (fapp x (PiCompile.classValue A q))))

theorem RecTel.indexedIH_const_index {I : Type v} (M : Interp.{u})
    (g : PSet.{u} → PSet.{u}) {m : Nat} (t : RecTel.{u,v} I m) (x : PSet.{u}) :
    t.indexedIH M (fun _ => g) x = t.erasedIH M g x := by
  induction t generalizing x with
  | ret i => rfl
  | @pi m A B ih =>
    exact congrArg (lamVal M (tyv A)) (congrArg (classFiber A)
      (funext fun q => ih q (fapp x (PiCompile.classValue A q))))

/-- Typed indexed leaves compose through the actual semantic Pi telescope.
The original field may be proof-erased and the IH may return data. -/
theorem RecTel.indexedIH_mem_scoped {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich)
    (X : I → PSet.{u}) (hX : ∀ i, Dich (X i))
    (C : I → PSet.{u} → PSet.{u}) (hC : ∀ i x, Dich (C i x))
    (g : I → PSet.{u} → PSet.{u})
    (S : I → Prop) (hs : ∀ p, S (t.result p))
    (hmap : ∀ i x, S i → x ∈ X i → g i x ∈ C i x)
    {x : PSet.{u}} (hx : x ∈ Ed M (t.erasedType M X)) :
    t.indexedIH M g x ∈ Ed M (t.erasedIHType M C x) := by
  induction t generalizing x with
  | ret i =>
    exact mem_congr_right (ed_tyv M (hC i x)).symm
      (hmap i x (hs PUnit.unit) (mem_congr_right (ed_tyv M (hX i)) hx))
  | @pi m A B ih =>
    have hv : ∀ q, fapp x (PiCompile.classValue A q) ∈
        Ed M ((B q).erasedType M X) := by
      intro q
      have ha : PiCompile.classValue A q ∈ Ed M (tyv A) :=
        mem_congr_right (ed_tyv M ht.1).symm (PiCompile.classValue_mem A q)
      exact mem_congr_right (ed_classFiber_classValue M A
        (fun q => Ed M ((B q).erasedType M X)) (fun _ => dich_ed M _) q)
        (app_mem M (fun _ _ h => tyv_congr (classFiber_congr A _ h)) hx ha)
    apply lam_mem M (fun _ _ h => classFiber_congr A _ h)
      (fun _ _ h => tyv_congr (classFiber_congr A _ h))
    intro a ha
    obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M ht.1) ha
    let q := Quotient.mk (FSetoid A) i
    have ev : Equiv (classFiber A (fun q =>
        (B q).indexedIH M g (fapp x (PiCompile.classValue A q))) a)
        ((B q).indexedIH M g (fapp x (PiCompile.classValue A q))) :=
      (classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)
    have et : Equiv (classFiber A (fun q =>
        Ed M ((B q).erasedIHType M C (fapp x (PiCompile.classValue A q)))) a)
        (Ed M ((B q).erasedIHType M C (fapp x (PiCompile.classValue A q)))) :=
      (classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)
    have ed := ed_tyv M ((dich_congr et).mpr (dich_ed M _))
    exact mem_congr_left ev.symm (mem_congr_right (ed.trans et).symm
      (ih q (ht.2 q) (fun p => hs ⟨q, p⟩) (hv q)))

/-- An everywhere-typed map specializes the scoped construction. -/
theorem RecTel.indexedIH_mem {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich)
    (X : I → PSet.{u}) (hX : ∀ i, Dich (X i))
    (C : I → PSet.{u} → PSet.{u}) (hC : ∀ i x, Dich (C i x))
    (g : I → PSet.{u} → PSet.{u})
    (hmap : ∀ i x, x ∈ X i → g i x ∈ C i x)
    {x : PSet.{u}} (hx : x ∈ Ed M (t.erasedType M X)) :
    t.indexedIH M g x ∈ Ed M (t.erasedIHType M C x) :=
  t.indexedIH_mem_scoped M ht X hX C hC g (fun _ => True)
    (fun _ => True.intro) (fun i x _ => hmap i x) hx

/-- Equivalent leaf maps and majors give equivalent indexed IHs. -/
theorem RecTel.indexedIH_congr {I : Type v} (M : Interp.{u})
    (g g' : I → PSet.{u} → PSet.{u})
    (hg : ∀ i x y, Equiv x y → Equiv (g i x) (g' i y))
    {m : Nat} (t : RecTel.{u,v} I m) {x y : PSet.{u}} (hxy : Equiv x y) :
    Equiv (t.indexedIH M g x) (t.indexedIH M g' y) := by
  induction t generalizing x y with
  | ret i => exact hg i x y hxy
  | @pi m A B ih =>
    apply lamVal_congr M Equiv.rfl
    intro a b hab
    exact (classFiber_values (fun q => ih q (fapp_congr hxy Equiv.rfl)) a).trans
      (classFiber_congr A _ hab)

end Rcic.F3.PSet
