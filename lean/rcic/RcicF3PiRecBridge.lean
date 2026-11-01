import rcic.RcicF3PiEraseField
import rcic.RcicF3KTWRecA

/-!
# Recursor bridge for arbitrary dependent semantic telescopes

The IH motive retains each recursive result index and actual major.
Membership, exact depth-based IH agreement and the well-founded shield
are proved for all dependent telescope depths, including empty domains.
The local variant requires mapping soundness only below the current major,
as needed by membership well-founded induction. Leaf erasure compatibility
is explicit: it follows for data-valued fibres
or erased recursors. This is not normalized raw-syntax extraction or a
universal repaired group producer. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.F3.PSet
universe u v
open Rcic.Declarative

/-- Congruence of the existing depth-based IH. -/
theorem ihAtN_congr {g : PSet.{u} → PSet.{u}}
    (hg : ∀ x y, Equiv x y → Equiv (g x) (g y)) (m : Nat)
    {x y : PSet.{u}} (hxy : Equiv x y) : Equiv (ihAtN g m x) (ihAtN g m y) := by
  induction m generalizing x y with
  | zero => exact hg _ _ hxy
  | succ m ih =>
    have hd := sImage_congr (fun a b h => pfst_congr h) hxy
    apply condP_congr
    · constructor
      · intro h a ha
        exact (ih (fapp_congr hxy Equiv.rfl)).symm.trans
          (h a (mem_congr_right hd.symm ha))
      · intro h a ha
        exact (ih (fapp_congr hxy Equiv.rfl)).trans
          (h a (mem_congr_right hd ha))
    · exact Equiv.rfl
    · exact mkLam_congr' hd (fun a b _ _ hab => ih (fapp_congr hxy hab))

/-- Every positive-depth IH of an erased graph is erased. -/
theorem ihAtN_empty_succ (g : PSet.{u} → PSet.{u}) (m : Nat)
    {x : PSet.{u}} (hx : Equiv x pempty) : Equiv (ihAtN g (m + 1) x) pempty := by
  apply condP_equiv_pos
  intro y hy
  have hd := (sImage_congr (fun a b h => pfst_congr h) hx).trans sImage_pfst_pempty
  exact (not_mem_pempty (mem_congr_right hd hy)).elim

/-- At every remaining depth, a functional graph emits the actual lambda. -/
theorem ihAtN_succ_lamVal (M : Interp.{u}) {A : PSet.{u}} {F : PSet.{u} → PSet.{u}}
    (hF : ∀ a b, Equiv a b → Equiv (F a) (F b))
    {x : PSet.{u}} (hx : x ∈ piSet (Ed M A) F) (g : PSet.{u} → PSet.{u})
    (hg : ∀ a b, Equiv a b → Equiv (g a) (g b)) (m : Nat) :
    Equiv (ihAtN g (m + 1) x) (lamVal M A (fun a => ihAtN g m (fapp x a))) := by
  exact ihAt_pi_equiv_lamVal M hF hx (ihAtN g m)
    (fun _ _ h => ihAtN_congr hg m h)
    (D := .sort .zero) (B := .sort .zero) (fun _ _ h => Expr.noConfusion h)

/-- Application stays below the enclosing value even for proof-erased graphs. -/
theorem memT_fapp_of_mem_piVal (M : Interp.{u}) {A x z : PSet.{u}}
    {F : PSet.{u} → PSet.{u}}
    (hF : ∀ a b, Equiv a b → Equiv (F a) (F b))
    (hx : x ∈ Ed M (piVal M A F)) {a : PSet.{u}} (ha : a ∈ Ed M A)
    (hxz : MemT x z) : MemT (fapp x a) z := by
  have hx' := mem_congr_right (ed_piVal M A F hF) hx
  cases M.dec (PiProp M A F) with
  | isTrue hP =>
    rw [cond_pos hP] at hx'
    have he := (mem_tv.mp hx').2
    have ea : Equiv (fapp x a) x :=
      ((fapp_congr he Equiv.rfl).trans (fapp_pempty a)).trans he.symm
    exact MemT.congr_left ea.symm hxz
  | isFalse hP =>
    rw [cond_neg hP] at hx'
    exact (memT_fapp_of_mem_piSet (fun _ _ h => ed_congr M (hF _ _ h)) hx' ha).trans hxz

namespace RecTel

/-- Induction hypotheses using the full dependent semantic telescope. -/
def erasedIH {I : Type v} (M : Interp.{u}) (g : PSet.{u} → PSet.{u}) :
    {m : Nat} → RecTel.{u,v} I m → PSet.{u} → PSet.{u}
  | _, .ret _, x => g x
  | _, .pi A B, x => lamVal M (tyv A) (classFiber A
      (fun q => (B q).erasedIH M g (fapp x (PiCompile.classValue A q))))

/-- The motive keeps both the recursive result index and its actual major. -/
def erasedIHType {I : Type v} (M : Interp.{u}) (C : I → PSet.{u} → PSet.{u}) :
    {m : Nat} → RecTel.{u,v} I m → PSet.{u} → PSet.{u}
  | _, .ret i, x => tyv (C i x)
  | _, .pi A B, x => piVal M (tyv A) (fun a => tyv (classFiber A
      (fun q => Ed M ((B q).erasedIHType M C (fapp x (PiCompile.classValue A q)))) a))

/-- The motive is required only at recursive arguments below the enclosing major. -/
theorem erasedIH_mem_below {I : Type v} (M : Interp.{u}) {m : Nat} (t : RecTel.{u,v} I m)
    (ht : t.DomainsDich) (X : I → PSet.{u}) (hX : ∀ i, Dich (X i))
    (C : I → PSet.{u} → PSet.{u}) (hC : ∀ i y, Dich (C i y))
    (g : PSet.{u} → PSet.{u}) (z : PSet.{u})
    (hmap : ∀ i y, MemT y z → y ∈ X i → g y ∈ C i y)
    {x : PSet.{u}} (hx : x ∈ Ed M (t.erasedType M X)) (hxz : MemT x z) :
    t.erasedIH M g x ∈ Ed M (t.erasedIHType M C x) := by
  induction t generalizing x with
  | ret i =>
    exact mem_congr_right (ed_tyv M (hC i x)).symm
      (hmap i x hxz (mem_congr_right (ed_tyv M (hX i)) hx))
  | pi A B ih =>
    have hv : ∀ q, fapp x (PiCompile.classValue A q) ∈
        Ed M ((B q).erasedType M X) := by
      intro q
      have ha : PiCompile.classValue A q ∈ Ed M (tyv A) :=
        mem_congr_right (ed_tyv M ht.1).symm (PiCompile.classValue_mem A q)
      exact mem_congr_right (ed_classFiber_classValue M A
        (fun q => Ed M ((B q).erasedType M X)) (fun _ => dich_ed M _) q)
        (app_mem M (fun _ _ h => tyv_congr (classFiber_congr A _ h)) hx ha)
    have hb : ∀ q, MemT (fapp x (PiCompile.classValue A q)) z := by
      intro q
      exact memT_fapp_of_mem_piVal M
        (fun _ _ h => tyv_congr (classFiber_congr A _ h)) hx
        (mem_congr_right (ed_tyv M ht.1).symm (PiCompile.classValue_mem A q)) hxz
    apply lam_mem M
      (fun _ _ h => classFiber_congr A _ h)
      (fun _ _ h => tyv_congr (classFiber_congr A _ h))
    intro a ha
    obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M ht.1) ha
    let q := Quotient.mk (FSetoid A) i
    have ev : Equiv (classFiber A (fun q =>
        (B q).erasedIH M g (fapp x (PiCompile.classValue A q))) a)
        ((B q).erasedIH M g (fapp x (PiCompile.classValue A q))) :=
      (classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)
    have et : Equiv (classFiber A (fun q =>
        Ed M ((B q).erasedIHType M C (fapp x (PiCompile.classValue A q)))) a)
        (Ed M ((B q).erasedIHType M C (fapp x (PiCompile.classValue A q)))) :=
      (classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)
    have ed := ed_tyv M ((dich_congr et).mpr (dich_ed M _))
    exact mem_congr_left ev.symm (mem_congr_right (ed.trans et).symm
      (ih q (ht.2 q) (hv q) (hb q)))

/-- The semantic IH inhabits the dependent motive at all binder depths. -/
theorem erasedIH_mem {I : Type v} (M : Interp.{u}) {m : Nat} (t : RecTel.{u,v} I m)
    (ht : t.DomainsDich) (X : I → PSet.{u}) (hX : ∀ i, Dich (X i))
    (C : I → PSet.{u} → PSet.{u}) (hC : ∀ i z, Dich (C i z))
    (g : PSet.{u} → PSet.{u}) (hg : ∀ i z, z ∈ X i → g z ∈ C i z)
    {x : PSet.{u}} (hx : x ∈ Ed M (t.erasedType M X)) :
    t.erasedIH M g x ∈ Ed M (t.erasedIHType M C x) := by
  exact t.erasedIH_mem_below M ht X hX C hC g (dataVal 0 [x])
    (fun i y _ hy => hg i y hy) hx (memT_dataVal (by simp))

/-- Exact agreement with the existing depth-based recursor, provided
leaf erasure is respected. The premise follows from a data-valued family
or an erased recursor; it does not require inhabited binder domains. -/
theorem erasedIH_eq_ihAtN {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich)
    (X : I → PSet.{u}) (hX : ∀ i, Dich (X i))
    (g : PSet.{u} → PSet.{u})
    (hg : ∀ a b, Equiv a b → Equiv (g a) (g b))
    (hp : ∀ i, pempty ∈ X i → Equiv (g pempty) pempty)
    {x : PSet.{u}} (hx : x ∈ Ed M (t.erasedType M X)) :
    Equiv (t.erasedIH M g x) (ihAtN g m x) := by
  induction t generalizing x with
  | ret i => exact Equiv.rfl
  | @pi k A B ih =>
    let F := fun a => tyv (classFiber A (fun q => Ed M ((B q).erasedType M X)) a)
    have hF : ∀ a b, Equiv a b → Equiv (F a) (F b) :=
      fun _ _ h => tyv_congr (classFiber_congr A _ h)
    have hv : ∀ q, fapp x (PiCompile.classValue A q) ∈
        Ed M ((B q).erasedType M X) := by
      intro q
      have ha : PiCompile.classValue A q ∈ Ed M (tyv A) :=
        mem_congr_right (ed_tyv M ht.1).symm (PiCompile.classValue_mem A q)
      exact mem_congr_right (ed_classFiber_classValue M A
        (fun q => Ed M ((B q).erasedType M X)) (fun _ => dich_ed M _) q)
        (app_mem M hF hx ha)
    have hread := fun q => ih q (ht.2 q) (hv q)
    have hx' := mem_congr_right (ed_piVal M (tyv A) F hF) hx
    cases M.dec (PiProp M (tyv A) F) with
    | isTrue hP =>
      rw [cond_pos hP] at hx'
      have he := (mem_tv.mp hx').2
      have hz : ∀ q, Equiv (ihAtN g k (fapp x (PiCompile.classValue A q))) pempty := by
        intro q
        have ec := (fapp_congr he Equiv.rfl).trans (fapp_pempty (PiCompile.classValue A q))
        cases k with
        | zero =>
          cases hb : B q with
          | ret j =>
            have hvq := hv q
            rw [hb] at hvq
            have hm := mem_congr_right (ed_tyv M (hX j)) hvq
            exact (hg _ _ ec).trans (hp j (mem_congr_left ec hm))
        | succ k => exact ihAtN_empty_succ g k ec
      have hL : LamProof M (tyv A) (classFiber A (fun q =>
          (B q).erasedIH M g (fapp x (PiCompile.classValue A q)))) := by
        intro a ha
        obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M ht.1) ha
        exact ((classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)).trans
          ((hread (Quotient.mk (FSetoid A) i)).trans (hz _))
      change Equiv (lamVal M (tyv A) _) _
      exact (show Equiv (lamVal M (tyv A) _) pempty from by
        unfold lamVal; rw [cond_pos hL]; exact Equiv.rfl).trans
        (ihAtN_empty_succ g k he).symm
    | isFalse hP =>
      rw [cond_neg hP] at hx'
      apply Equiv.trans ?_ (ihAtN_succ_lamVal M (fun _ _ h => ed_congr M (hF _ _ h)) hx' g hg k).symm
      apply lamVal_congr_on M Equiv.rfl
        (fun _ _ h => classFiber_congr A _ h)
      intro a ha
      obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M ht.1) ha
      let q := Quotient.mk (FSetoid A) i
      exact ((classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)).trans
        ((hread q).trans (ihAtN_congr hg k
          (fapp_congr Equiv.rfl ((PiCompile.classValue_at A i).trans hi))))

/-- The existing recursor's well-founded shield is transparent at every
semantic binder, including an erased field's empty graph domain. -/
theorem ihChild_of_erased_mem {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich)
    (X : I → PSet.{u})
    {x z : PSet.{u}} (hx : x ∈ Ed M (t.erasedType M X))
    (hxz : MemT x z) (T : Expr Nat) (hdepth : ihDepth T = m) : ihChild z T x := by
  induction t generalizing x T with
  | ret i => exact ihChild_of_depth0 z hdepth x
  | @pi k A B ih =>
    cases T with
    | pi D C =>
      have hc : ihDepth C = k := Nat.succ.inj hdepth
      let F := fun a => tyv (classFiber A (fun q => Ed M ((B q).erasedType M X)) a)
      have hF : ∀ a b, Equiv a b → Equiv (F a) (F b) :=
        fun _ _ h => tyv_congr (classFiber_congr A _ h)
      have hx' := mem_congr_right (ed_piVal M (tyv A) F hF) hx
      intro y hy
      cases M.dec (PiProp M (tyv A) F) with
      | isTrue hP =>
        rw [cond_pos hP] at hx'
        have hd := (sImage_congr (fun a b h => pfst_congr h) (mem_tv.mp hx').2).trans
          sImage_pfst_pempty
        exact (not_mem_pempty (mem_congr_right hd hy)).elim
      | isFalse hP =>
        rw [cond_neg hP] at hx'
        have hdom := sImage_pfst_of_mem_piSet (fun _ _ h => ed_congr M (hF _ _ h)) hx'
        have hy' := mem_congr_right hdom hy
        have hyA := mem_congr_right (ed_tyv M ht.1) hy'
        have hbelow := (memT_fapp_of_mem_piSet
          (fun _ _ h => ed_congr M (hF _ _ h)) hx' hy').trans hxz
        obtain ⟨i, hi⟩ := hyA
        let q := Quotient.mk (FSetoid A) i
        have hm := app_mem M hF hx hy'
        have et : Equiv (Ed M (F y)) (Ed M ((B q).erasedType M X)) :=
          (ed_congr M (tyv_congr ((classFiber_congr A _ hi.symm).trans
            (classFiber_at A _ i)))).trans (ed_tyv M (dich_ed M _))
        exact ⟨hbelow, ih q (ht.2 q) (mem_congr_right et hm) hbelow C hc⟩
    | _ => exact Nat.noConfusion hdepth

/-- Elementary composition of membership and exact recursor agreement. -/
theorem ihAtN_mem {I : Type v} (M : Interp.{u}) {m : Nat} (t : RecTel.{u,v} I m)
    (ht : t.DomainsDich) (X : I → PSet.{u}) (hX : ∀ i, Dich (X i))
    (C : I → PSet.{u} → PSet.{u}) (hC : ∀ i z, Dich (C i z))
    (g : PSet.{u} → PSet.{u})
    (hg : ∀ a b, Equiv a b → Equiv (g a) (g b))
    (hmap : ∀ i z, z ∈ X i → g z ∈ C i z)
    (hp : ∀ i, pempty ∈ X i → Equiv (g pempty) pempty)
    {x : PSet.{u}} (hx : x ∈ Ed M (t.erasedType M X)) :
    ihAtN g m x ∈ Ed M (t.erasedIHType M C x) := by
  exact mem_congr_left (t.erasedIH_eq_ihAtN M ht X hX g hg hp hx)
    (t.erasedIH_mem M ht X hX C hC g hmap hx)

/-- Elementary composition with exact depth-based IH agreement. -/
theorem ihAtN_mem_below {I : Type v} (M : Interp.{u}) {m : Nat} (t : RecTel.{u,v} I m)
    (ht : t.DomainsDich) (X : I → PSet.{u}) (hX : ∀ i, Dich (X i))
    (C : I → PSet.{u} → PSet.{u}) (hC : ∀ i y, Dich (C i y))
    (g : PSet.{u} → PSet.{u})
    (hg : ∀ a b, Equiv a b → Equiv (g a) (g b)) (z : PSet.{u})
    (hmap : ∀ i y, MemT y z → y ∈ X i → g y ∈ C i y)
    (hp : ∀ i, pempty ∈ X i → Equiv (g pempty) pempty)
    {x : PSet.{u}} (hx : x ∈ Ed M (t.erasedType M X)) (hxz : MemT x z) :
    ihAtN g m x ∈ Ed M (t.erasedIHType M C x) := by
  exact mem_congr_left (t.erasedIH_eq_ihAtN M ht X hX g hg hp hx)
    (t.erasedIH_mem_below M ht X hX C hC g z hmap hx hxz)

end RecTel
end Rcic.F3.PSet
