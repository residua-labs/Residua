import rcic.RcicF3PiCompile
import rcic.RcicF3Core

/-!
# Dependent recursive fields with R-CIC proof erasure

Literal graphs remain the interpretation of `RecTel.denote`. This module
adds a separate interpretation using the existing `piVal` and `lamVal`.
It retains empty domains and arbitrary dependent Pi depth. `DomainsDich`
is the element-set invariant supplied by `Ed`, not an inhabitation wall.
No typed-syntax extractor or full A-axis producer is asserted here.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.F3.PSet
universe u v

namespace RecTel

/-- Every domain is an element set of the model. Empty domains qualify. -/
def DomainsDich {I : Type v} : {m : Nat} → RecTel.{u, v} I m → Prop
  | _, .ret _ => True
  | _, .pi A B => Dich A ∧ ∀ q, (B q).DomainsDich

/-- R-CIC type values, including its proof-erasing dependent products. -/
def erasedType {I : Type v} (M : Interp.{u}) :
    {m : Nat} → RecTel.{u, v} I m → (I → PSet.{u}) → PSet.{u}
  | _, .ret i, X => tyv (X i)
  | _, .pi A B, X => piVal M (tyv A) (fun a =>
      tyv (classFiber A (fun q => Ed M ((B q).erasedType M X)) a))

/-- Erasure-aware encoding depends on values, not a candidate family. -/
def erasedEncode {I : Type v} (M : Interp.{u}) : {m : Nat} →
    (t : RecTel.{u, v} I m) → PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u}) → PSet.{u}
  | _, .ret _, f => f
  | _, .pi A B, f => lamVal M (tyv A)
      (classFiber A (fun q => (B q).erasedEncode M (f q)))

/-- Canonical readback uses semantic application, including on erased
proofs; quotient classes are read without representative choice. -/
def erasedRead {I : Type v} (M : Interp.{u}) : {m : Nat} →
    (t : RecTel.{u, v} I m) → PSet.{u} →
      PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u})
  | _, .ret _, f => f
  | _, .pi A B, f => fun q =>
      (B q).erasedRead M (fapp f (PiCompile.classValue A q))

end RecTel

/-- Equivalent values at all quotient addresses give equivalent extended
fibres. This is elementary membership transport. -/
theorem classFiber_values {A : PSet.{u}} {B C : FBr A → PSet.{u}}
    (h : ∀ q, Equiv (B q) (C q)) (a : PSet.{u}) :
    Equiv (classFiber A B a) (classFiber A C a) := by
  exact ext fun z =>
    ⟨classFiber_mono A (fun q _ hz => mem_congr_right (h q) hz) a z,
      classFiber_mono A (fun q _ hz => mem_congr_right (h q).symm hz) a z⟩

/-- At a quotient address the extended family recovers its actual fibre. -/
theorem classFiber_classValue (A : PSet.{u}) (B : FBr A → PSet.{u}) (q : FBr A) :
    Equiv (classFiber A B (PiCompile.classValue A q)) (B q) := by
  refine Quotient.inductionOn q ?_
  intro i
  exact (classFiber_congr A B (PiCompile.classValue_at A i)).trans
    (classFiber_at A B i)

/-- Reading a dichotomous fibre through its type value loses nothing. -/
theorem ed_classFiber_classValue (M : Interp.{u}) (A : PSet.{u})
    (B : FBr A → PSet.{u}) (hB : ∀ q, Dich (B q)) (q : FBr A) :
    Equiv (Ed M (tyv (classFiber A B (PiCompile.classValue A q)))) (B q) := by
  have e := classFiber_classValue A B q
  exact (ed_tyv M ((dich_congr e).mpr (hB q))).trans e

/-- Every related assignment encodes a member of the actual R-CIC
product, even when some binders have empty domains and erase to proofs. -/
theorem RecTel.erasedEncode_mem {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u, v} I m) (ht : t.DomainsDich) (X : I → PSet.{u})
    (hX : ∀ i, Dich (X i))
    (f : PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u})) (hf : t.Rel X f) :
    t.erasedEncode M f ∈ Ed M (t.erasedType M X) := by
  induction t with
  | ret i => exact mem_congr_right (ed_tyv M (hX i)).symm hf
  | pi A B ih =>
    apply lam_mem M
      (fun _ _ h => classFiber_congr A _ h)
      (fun _ _ h => tyv_congr (classFiber_congr A _ h))
    intro a ha
    obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M ht.1) ha
    let q := Quotient.mk (FSetoid A) i
    have ev : Equiv (classFiber A (fun q => (B q).erasedEncode M (f q)) a)
        ((B q).erasedEncode M (f q)) :=
      (classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)
    have et : Equiv (classFiber A (fun q => Ed M ((B q).erasedType M X)) a)
        (Ed M ((B q).erasedType M X)) :=
      (classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)
    have ed := ed_tyv M ((dich_congr et).mpr (dich_ed M _))
    exact mem_congr_left ev.symm (mem_congr_right (ed.trans et).symm
      (ih q (ht.2 q) (f q) (hf q)))

/-- Actual product membership gives all recursive children and exact
readback of the original value, including its proof erasure. -/
theorem RecTel.erasedRead_spec {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u, v} I m) (ht : t.DomainsDich) (X : I → PSet.{u})
    (hX : ∀ i, Dich (X i)) {f : PSet.{u}} (hf : f ∈ Ed M (t.erasedType M X)) :
    t.Rel X (t.erasedRead M f) ∧ Equiv f (t.erasedEncode M (t.erasedRead M f)) := by
  induction t generalizing f with
  | ret i => exact ⟨mem_congr_right (ed_tyv M (hX i)) hf, Equiv.rfl⟩
  | pi A B ih =>
    have hv : ∀ q, fapp f (PiCompile.classValue A q) ∈
        Ed M ((B q).erasedType M X) := by
      intro q
      have ha : PiCompile.classValue A q ∈ Ed M (tyv A) :=
        mem_congr_right (ed_tyv M ht.1).symm (PiCompile.classValue_mem A q)
      have hm := app_mem M
        (fun _ _ h => tyv_congr (classFiber_congr A _ h)) hf ha
      exact mem_congr_right (ed_classFiber_classValue M A
        (fun q => Ed M ((B q).erasedType M X)) (fun _ => dich_ed M _) q) hm
    have hr := fun q => ih q (ht.2 q) (hv q)
    refine ⟨fun q => (hr q).1, ?_⟩
    apply Equiv.symm
    have he : Equiv
        (lamVal M (tyv A) (classFiber A (fun q =>
          (B q).erasedEncode M ((B q).erasedRead M (fapp f (PiCompile.classValue A q))))))
        (lamVal M (tyv A) (fun a => fapp f a)) := by
      apply lamVal_congr_on M Equiv.rfl
        (fun _ _ h => classFiber_congr A _ h)
      intro a ha
      obtain ⟨i, hi⟩ := mem_congr_right (ed_tyv M ht.1) ha
      let q := Quotient.mk (FSetoid A) i
      exact ((classFiber_congr A _ hi.symm).trans (classFiber_at A _ i)).trans
        ((hr q).2.symm.trans (fapp_congr Equiv.rfl
          ((PiCompile.classValue_at A i).trans hi)))
    exact he.trans
      (eta_val M (fun _ _ h => tyv_congr (classFiber_congr A _ h)) hf)

/-- Pointwise equivalent recursive results give equivalent erased
fields. This is the congruence needed by the guarded-W decoder. -/
theorem RecTel.erasedEncode_congr {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u, v} I m)
    (f g : PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u}))
    (h : ∀ p, Equiv (t.tel.flatten f p) (t.tel.flatten g p)) :
    Equiv (t.erasedEncode M f) (t.erasedEncode M g) := by
  induction t with
  | ret i => exact h .unit
  | pi A B ih =>
    apply lamVal_congr M Equiv.rfl
    intro a b hab
    exact (classFiber_values
      (fun q => ih q (f q) (g q) (fun p => h ⟨q, p⟩)) a).trans
      (classFiber_congr A _ hab)

/-- Exact membership: all children plus the actual erased encoding.
The second conjunct excludes junk functions and arbitrary proof values. -/
theorem RecTel.erasedMem_iff {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u, v} I m) (ht : t.DomainsDich) (X : I → PSet.{u})
    (hX : ∀ i, Dich (X i)) (f : PSet.{u}) :
    f ∈ Ed M (t.erasedType M X) ↔
      t.Rel X (t.erasedRead M f) ∧ Equiv f (t.erasedEncode M (t.erasedRead M f)) := by
  exact ⟨t.erasedRead_spec M ht X hX,
    fun h => mem_congr_left h.2.symm (t.erasedEncode_mem M ht X hX _ h.1)⟩

/-- Every interpreted field type is exactly its tagged element set.
This pays the intermediate type-value bridge for nested R-CIC products. -/
theorem RecTel.erasedType_tagged {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u, v} I m) (X : I → PSet.{u}) (hX : ∀ i, Dich (X i)) :
    Equiv (tyv (Ed M (t.erasedType M X))) (t.erasedType M X) := by
  cases t with
  | ret i => exact tyv_congr (ed_tyv M (hX i))
  | pi A B =>
    exact tyv_congr (ed_piVal M (tyv A)
      (fun a => tyv (classFiber A (fun q => Ed M ((B q).erasedType M X)) a))
      (fun _ _ h => tyv_congr (classFiber_congr A _ h)))

/-- Equivalent fields have equivalent readback at every complete path. -/
theorem RecTel.erasedRead_congr {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u, v} I m) (f g : PSet.{u}) (h : Equiv f g) :
    ∀ p, Equiv (t.tel.flatten (t.erasedRead M f) p)
      (t.tel.flatten (t.erasedRead M g) p) := by
  induction t generalizing f g with
  | ret i => exact fun _ => h
  | pi A B ih => exact fun p => ih p.1 _ _ (fapp_congr h Equiv.rfl) p.2

/-- Readback of an encoded assignment retains each dependent child,
including paths through proof domains. No family premise is needed. -/
theorem RecTel.erasedRead_encode {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u, v} I m) (ht : t.DomainsDich)
    (f : PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u})) :
    ∀ p, Equiv (t.tel.flatten (t.erasedRead M (t.erasedEncode M f)) p)
      (t.tel.flatten f p) := by
  induction t with
  | ret i => exact fun _ => Equiv.rfl
  | pi A B ih =>
    intro p
    have ha : PiCompile.classValue A p.1 ∈ Ed M (tyv A) :=
      mem_congr_right (ed_tyv M ht.1).symm (PiCompile.classValue_mem A p.1)
    have he := (beta_val M (fun _ _ h => classFiber_congr A _ h) ha).trans
      (classFiber_classValue A (fun q => (B q).erasedEncode M (f q)) p.1)
    exact ((B p.1).erasedRead_congr M _ _ he p.2).trans
      (ih p.1 (ht.2 p.1) (f p.1) p.2)

/-- An encoded field is accepted exactly when every dependent child is
in its declared result fibre. This gives rejection tests for wrong indices. -/
theorem RecTel.erasedEncode_mem_iff {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u, v} I m) (ht : t.DomainsDich) (X : I → PSet.{u})
    (hX : ∀ i, Dich (X i))
    (f : PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u})) :
    t.erasedEncode M f ∈ Ed M (t.erasedType M X) ↔ t.Rel X f := by
  constructor
  · intro hf
    have hr := (t.erasedRead_spec M ht X hX hf).1
    apply (PiTel.all_iff _ _ _).mpr
    intro p
    exact mem_congr_left (t.erasedRead_encode M ht f p)
      ((PiTel.all_iff _ _ _).mp hr p)
  · exact t.erasedEncode_mem M ht X hX f

end Rcic.F3.PSet
