import rcic.RcicF3PiEraseField
import rcic.RcicF3PiSmallValue
import rcic.RcicF3PiPropField
import rcic.RcicF3StageFacts
/-! Arbitrary-stage bounds for erased dependent recursive fields.
A staged source value with data-faced reachable leaves bounds the target
type. Empty dependent branches are handled by proof erasure; no domain
inhabitation or inclusion-to-smallness assumption is used.
Universal original-syntax group closure remains open; `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecTel
universe u v

def DomainsStage {I : Type v} (W : PSet.{u}) : {m : Nat} → RecTel.{u,v} I m → Prop
  | _, .ret _ => True
  | _, .pi A B => A ∈ W ∧ ∀ q, DomainsStage W (B q)

theorem erasedType_stage {I : Type v} (M : Interp.{u}) (W : PSet.{u}) (hW : Stage W)
    {m : Nat} (t : RecTel.{u,v} I m) (ht : t.DomainsDich) (hD : t.DomainsStage W)
    (X : I → PSet.{u}) (hX : ∀ i, Dich (X i)) (hS : ∀ i, X i ∈ W) :
    Ed M (t.erasedType M X) ∈ W := by
  induction t with
  | ret i => exact mem_congr_left (ed_tyv M (hX i)).symm (hS i)
  | pi A B ih =>
    let C := fun a => tyv (classFiber A (fun q => Ed M ((B q).erasedType M X)) a)
    have hC : ∀ a b, Equiv a b → Equiv (C a) (C b) :=
      fun _ _ h => tyv_congr (classFiber_congr A _ h)
    have he := ed_piVal M (tyv A) C hC
    change Ed M (piVal M (tyv A) C) ∈ W
    cases hd : M.dec (PiProp M (tyv A) C) with
    | isTrue hp =>
      rw [cond_pos hp] at he
      exact mem_congr_left he.symm (hW.prop_mem (fun _ hz => (mem_tv.mp hz).2))
    | isFalse hp =>
      rw [cond_neg hp] at he
      refine mem_congr_left he.symm (hW.pi (fun _ _ h => ed_congr M (hC _ _ h))
        (mem_congr_left (ed_tyv M ht.1).symm hD.1) ?_)
      intro a ha
      obtain ⟨j, hj⟩ := mem_congr_right (ed_tyv M ht.1) ha
      let q := Quotient.mk (FSetoid A) j
      have hf := (classFiber_congr A
        (fun q => Ed M ((B q).erasedType M X)) hj.symm).trans (classFiber_at A _ j)
      have hc : Equiv (Ed M (C a)) (Ed M ((B q).erasedType M X)) :=
        (ed_tyv M ((dich_congr hf).mpr (dich_ed M _))).trans hf
      exact mem_congr_left hc.symm (ih q (ht.2 q) (hD.2 q))
theorem erasedRead_empty {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) {f : PSet.{u}} (hf : Equiv f pempty) :
    ∀ p, Equiv (t.tel.flatten (t.erasedRead M f) p) pempty := by
  induction t generalizing f with
  | ret _ => intro _; exact hf
  | pi A B ih =>
    intro p
    exact ih p.1 ((fapp_congr hf Equiv.rfl).trans (fapp_pempty _)) p.2
theorem no_paths_of_empty {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich) (X : I → PSet.{u})
    (hX : ∀ i, Dich (X i)) (hN : ∀ p, ¬ pempty ∈ X (t.result p)) {f : PSet.{u}}
    (hf : f ∈ Ed M (t.erasedType M X)) (he : Equiv f pempty) :
    ∀ _p : t.tel.Path, False := by
  intro p
  have hr := t.erasedRead_spec M ht X hX hf
  exact hN p (mem_congr_left (t.erasedRead_empty M he p)
    ((PiTel.all_iff _ _ _).mp hr.1 p))
theorem member_empty_of_no_paths {I : Type v} (M : Interp.{u}) {m : Nat}
    (t : RecTel.{u,v} I m) (ht : t.DomainsDich) (X : I → PSet.{u})
    (hX : ∀ i, Dich (X i)) (hn : ∀ _p : t.tel.Path, False) {f : PSet.{u}}
    (hf : f ∈ Ed M (t.erasedType M X)) : Equiv f pempty := by
  have hr := t.erasedRead_spec M ht X hX hf
  exact hr.2.trans (PiPropField.encode_empty M t ht _ (fun p => (hn p).elim))
theorem domain_stage (M : Interp.{u}) {W : PSet.{u}} (hW : Stage W)
    {A g : PSet.{u}} {B : PSet.{u} → PSet.{u}}
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a'))
    (hg : g ∈ W) (hf : g ∈ Ed M (piVal M A B))
    (hne : ¬ Equiv g pempty) : Ed M A ∈ W := by
  have hf' := mem_congr_right (ed_piVal M A B hB) hf
  cases hd : M.dec (PiProp M A B) with
  | isTrue hP =>
    rw [cond_pos hP] at hf'
    exact (hne (mem_tv.mp hf').2).elim
  | isFalse hP =>
    rw [cond_neg hP] at hf'
    have hfun := isFuncOnDep_of_mem_piSet (fun _ _ h => ed_congr M (hB _ _ h)) hf'
    apply hW.subset (hW.sUnion (hW.sUnion hg))
    intro a ha
    obtain ⟨b, _, hab⟩ := hfun.1 a ha
    exact mem_sUnion_sUnion_of_pair_left hab
theorem erasedType_stage_from_value {I : Type v} (M : Interp.{u})
    {W : PSet.{u}} (hW : Stage W) {m : Nat} (t : RecTel.{u,v} I m)
    (ht : t.DomainsDich) (X Y : I → PSet.{u})
    (hX : ∀ i, Dich (X i)) (hY : ∀ i, Dich (Y i))
    (hN : ∀ p, ¬ pempty ∈ X (t.result p)) (hS : ∀ p, Y (t.result p) ∈ W)
    {f : PSet.{u}} (hf : f ∈ Ed M (t.erasedType M X)) (hs : f ∈ W) :
    Ed M (t.erasedType M Y) ∈ W := by
  induction t generalizing f with
  | ret i => exact mem_congr_left (ed_tyv M (hY i)).symm (hS .unit)
  | pi A B ih =>
    let C := fun a => tyv (classFiber A (fun q => Ed M ((B q).erasedType M X)) a)
    let D := fun a => tyv (classFiber A (fun q => Ed M ((B q).erasedType M Y)) a)
    have hC : ∀ a b, Equiv a b → Equiv (C a) (C b) :=
      fun _ _ h => tyv_congr (classFiber_congr A _ h)
    have hD : ∀ a b, Equiv a b → Equiv (D a) (D b) :=
      fun _ _ h => tyv_congr (classFiber_congr A _ h)
    change f ∈ Ed M (piVal M (tyv A) C) at hf
    have he := ed_piVal M (tyv A) D hD
    change Ed M (piVal M (tyv A) D) ∈ W
    cases hd : M.dec (PiProp M (tyv A) D) with
    | isTrue hp =>
      rw [cond_pos hp] at he
      exact mem_congr_left he.symm (hW.prop_mem (fun _ hz => (mem_tv.mp hz).2))
    | isFalse hp =>
      rw [cond_neg hp] at he
      have hn : ¬ Equiv f pempty := by
        intro hfe
        have hnone := (RecTel.pi A B).no_paths_of_empty M ht X hX hN hf hfe
        apply hp
        intro a ha z hz
        obtain ⟨j, hj⟩ := mem_congr_right (ed_tyv M ht.1) ha
        let q := Quotient.mk (FSetoid A) j
        have heq := (classFiber_congr A
          (fun q => Ed M ((B q).erasedType M Y)) hj.symm).trans (classFiber_at A _ j)
        have heD : Equiv (Ed M (D a)) (Ed M ((B q).erasedType M Y)) :=
          (ed_tyv M ((dich_congr heq).mpr (dich_ed M _))).trans heq
        exact (B q).member_empty_of_no_paths M (ht.2 q) Y hY
          (fun p => hnone ⟨q, p⟩) (mem_congr_right heD hz)
      have hA := domain_stage M hW hC hs hf hn
      refine mem_congr_left he.symm (hW.pi
        (fun _ _ h => ed_congr M (hD _ _ h)) hA ?_)
      intro a ha
      obtain ⟨j, hj⟩ := mem_congr_right (ed_tyv M ht.1) ha
      let q := Quotient.mk (FSetoid A) j
      have heq := (classFiber_congr A
        (fun q => Ed M ((B q).erasedType M Y)) hj.symm).trans (classFiber_at A _ j)
      have heD : Equiv (Ed M (D a)) (Ed M ((B q).erasedType M Y)) :=
        (ed_tyv M ((dich_congr heq).mpr (dich_ed M _))).trans heq
      have ha' : PiCompile.classValue A q ∈ Ed M (tyv A) :=
        mem_congr_right (ed_tyv M ht.1).symm (PiCompile.classValue_mem A q)
      have hval := app_mem M hC hf ha'
      have hCX := ed_classFiber_classValue M A
        (fun q => Ed M ((B q).erasedType M X)) (fun _ => dich_ed M _) q
      have hs' : fapp f (PiCompile.classValue A q) ∈ W :=
        hW.sUnion (hW.subset (hW.sUnion (hW.sUnion hs)) (fun _ hz => mem_sep_subset hz))
      exact mem_congr_left heD.symm
        (ih q (ht.2 q) (fun p => hN ⟨q, p⟩) (fun p => hS ⟨q, p⟩)
          (mem_congr_right hCX hval) hs')
end Rcic.F3.PSet.RecTel
