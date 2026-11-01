import rcic.RcicF3PiSmallRecursive
import rcic.RcicF3PiSmallStage

/-!
# Small branch readback at an explicit universe

This is the mixed-universe reader/encoder of PiSmallField with the small
branch universe left explicit. Values live in max(u+1,v); branch addresses
live in u. It reuses PiSmallRecursive.widen and the generic erased-field
laws. Readback, membership, and extensionality require no choice. The size
theorem uses exactly Choice u. No admitted-group signature is assumed or
produced here. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallFieldAt
universe u v w
open PiSmallRecursive (widen)
open Rcic.Declarative

noncomputable def expand {I : Type w} : {m : Nat} → (t : RecTel.{u,w} I m) →
    PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v}) →
    PiTel.Value.{max (u+1) v,max (u+1) v + 1}
      (widen.{u,v,w} t).tel (fun _ => PSet.{max (u+1) v})
  | _, .ret _, f => f
  | _, .pi A B, f => fun q =>
      expand (B (FBrDown.{u,max (u+1) v} A q)) (f (FBrDown.{u,max (u+1) v} A q))

noncomputable def read {I : Type w} (M : Interp.{max (u+1) v}) :
    {m : Nat} → (t : RecTel.{u,w} I m) → PSet.{max (u+1) v} →
    PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v})
  | _, .ret _, f => f
  | _, .pi A B, f => fun q =>
      read M (B q) (fapp f (lift.{u,max (u+1) v} (PiCompile.classValue A q)))

noncomputable def encode {I : Type w} (M : Interp.{max (u+1) v})
    {m : Nat} (t : RecTel.{u,w} I m)
    (f : PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v})) :
    PSet.{max (u+1) v} :=
  (widen.{u,v,w} t).erasedEncode M (expand.{u,v,w} t f)

def Related {I : Type w} {m : Nat} (t : RecTel.{u,w} I m)
    (X : I → PSet.{max (u+1) v})
    (f : PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v})) : Prop :=
  t.tel.All (fun p z => z ∈ X (t.result p)) f

theorem expand_congr {I : Type w} {m : Nat} (t : RecTel.{u,w} I m)
    (f g : PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v}))
    (h : ∀ p, Equiv (t.tel.flatten f p) (t.tel.flatten g p)) :
    ∀ p, Equiv ((widen.{u,v,w} t).tel.flatten (expand.{u,v,w} t f) p)
      ((widen.{u,v,w} t).tel.flatten (expand.{u,v,w} t g) p) := by
  induction t with
  | ret i => exact fun _ => h .unit
  | pi A B ih =>
      exact fun p => ih (FBrDown.{u,max (u+1) v} A p.1)
        (f (FBrDown.{u,max (u+1) v} A p.1))
        (g (FBrDown.{u,max (u+1) v} A p.1))
        (fun r => h ⟨FBrDown.{u,max (u+1) v} A p.1, r⟩) p.2

theorem read_expand {I : Type w} (M : Interp.{max (u+1) v}) {m : Nat}
    (t : RecTel.{u,w} I m) (f : PSet.{max (u+1) v}) :
    ∀ p, Equiv ((widen.{u,v,w} t).tel.flatten
        (expand.{u,v,w} t (read.{u,v,w} M t f)) p)
      ((widen.{u,v,w} t).tel.flatten ((widen.{u,v,w} t).erasedRead M f) p) := by
  induction t generalizing f with
  | ret i => exact fun _ => Equiv.rfl
  | pi A B ih =>
      intro p
      exact (ih (FBrDown.{u,max (u+1) v} A p.1) _ p.2).trans
        ((widen.{u,v,w} (B (FBrDown.{u,max (u+1) v} A p.1))).erasedRead_congr
          M _ _ (fapp_congr Equiv.rfl (PiSmallRecursive.classValue_lift.{u,v} A p.1)) p.2)

theorem dich_lift {A : PSet.{u}} (hA : Dich A) :
    Dich (lift.{u,max (u+1) v} A) := by
  rcases hA with h | h
  · apply Or.inl
    intro z hz
    obtain ⟨a, ha, he⟩ := mem_lift.{u,max (u+1) v}.mp hz
    exact he.trans ((lift_equiv.{u,max (u+1) v} (h a ha)).trans lift_pempty_equiv)
  · apply Or.inr
    intro hz
    obtain ⟨a, ha, he⟩ := mem_lift.{u,max (u+1) v}.mp hz
    have e : Equiv a pempty :=
      equiv_of_lift.{u,max (u+1) v} (he.symm.trans lift_pempty_equiv.symm)
    exact h (mem_congr_left e ha)

theorem widen_dich {I : Type w} {m : Nat} (t : RecTel.{u,w} I m)
    (ht : t.DomainsDich) : (widen.{u,v,w} t).DomainsDich := by
  induction t with
  | ret i => trivial
  | pi A B ih =>
      exact ⟨dich_lift.{u,v} ht.1, fun q => ih (FBrDown.{u,max (u+1) v} A q) (ht.2 _)⟩

theorem related_expand {I : Type w} {m : Nat} (t : RecTel.{u,w} I m)
    (X : I → PSet.{max (u+1) v})
    (f : PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v}))
    (hf : Related.{u,v,w} t X f) :
    (widen.{u,v,w} t).Rel X (expand.{u,v,w} t f) := by
  induction t with
  | ret i => exact hf
  | pi A B ih => exact fun q => ih (FBrDown.{u,max (u+1) v} A q) (f _) (hf _)

theorem encode_mem {I : Type w} (M : Interp.{max (u+1) v})
    {m : Nat} (t : RecTel.{u,w} I m) (ht : t.DomainsDich)
    (X : I → PSet.{max (u+1) v}) (hX : ∀ i, Dich (X i))
    (f : PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v}))
    (hf : Related.{u,v,w} t X f) :
    encode.{u,v,w} M t f ∈ Ed M ((widen.{u,v,w} t).erasedType M X) :=
  (widen.{u,v,w} t).erasedEncode_mem M (widen_dich.{u,v,w} t ht) X hX _
    (related_expand.{u,v,w} t X f hf)

noncomputable def up : (A : PSet.{u}) → FBr A → FBr (lift.{u,max (u+1) v} A)
  | mk α f => Quotient.lift
      (fun i => Quotient.mk (FSetoid (lift.{u,max (u+1) v} (mk α f))) ⟨i⟩)
      (fun _ _ h => Quotient.sound (lift_equiv.{u,max (u+1) v} h))

theorem down_up (A : PSet.{u}) (q : FBr A) :
    FBrDown.{u,max (u+1) v} A (up.{u,v} A q) = q := by
  cases A with
  | mk α f => exact Quotient.inductionOn q (fun _ => rfl)

theorem read_related {I : Type w} (M : Interp.{max (u+1) v})
    {m : Nat} (t : RecTel.{u,w} I m) (ht : t.DomainsDich)
    (X : I → PSet.{max (u+1) v}) (hX : ∀ i, Dich (X i))
    {f : PSet.{max (u+1) v}} (hf : f ∈ Ed M ((widen.{u,v,w} t).erasedType M X)) :
    Related.{u,v,w} t X (read.{u,v,w} M t f) := by
  induction t generalizing f with
  | ret i => exact mem_congr_right (ed_tyv M (hX i)) hf
  | pi A B ih =>
      intro q
      let q' := up.{u,v} A q
      have eq : FBrDown.{u,max (u+1) v} A q' = q := down_up.{u,v} A q
      have ev : Equiv (lift.{u,max (u+1) v} (PiCompile.classValue A q))
          (PiCompile.classValue (lift.{u,max (u+1) v} A) q') := by
        simpa only [eq] using PiSmallRecursive.classValue_lift.{u,v} A q'
      have ha : PiCompile.classValue (lift.{u,max (u+1) v} A) q' ∈
          Ed M (tyv (lift.{u,max (u+1) v} A)) :=
        mem_congr_right (ed_tyv M (dich_lift.{u,v} ht.1)).symm
          (PiCompile.classValue_mem (lift.{u,max (u+1) v} A) q')
      have hm := app_mem M
        (fun _ _ h => tyv_congr (classFiber_congr (lift.{u,max (u+1) v} A) _ h)) hf ha
      have hv := mem_congr_right
        (ed_classFiber_classValue M (lift.{u,max (u+1) v} A)
          (fun r => Ed M ((widen.{u,v,w} (B (FBrDown.{u,max (u+1) v} A r))).erasedType M X))
          (fun _ => dich_ed M _) q') hm
      rw [eq] at hv
      exact ih q (ht.2 q) (mem_congr_left (fapp_congr Equiv.rfl ev.symm) hv)

theorem read_spec {I : Type w} (M : Interp.{max (u+1) v})
    {m : Nat} (t : RecTel.{u,w} I m) (ht : t.DomainsDich)
    (X : I → PSet.{max (u+1) v}) (hX : ∀ i, Dich (X i))
    {f : PSet.{max (u+1) v}} (hf : f ∈ Ed M ((widen.{u,v,w} t).erasedType M X)) :
    Related.{u,v,w} t X (read.{u,v,w} M t f) ∧
      Equiv f (encode.{u,v,w} M t (read.{u,v,w} M t f)) := by
  refine ⟨read_related.{u,v,w} M t ht X hX hf, ?_⟩
  exact ((widen.{u,v,w} t).erasedRead_spec M (widen_dich.{u,v,w} t ht) X hX hf).2.trans
    ((widen.{u,v,w} t).erasedEncode_congr M _ _ (read_expand.{u,v,w} M t f)).symm

theorem encode_congr {I : Type w} (M : Interp.{max (u+1) v})
    {m : Nat} (t : RecTel.{u,w} I m)
    (f g : PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v}))
    (h : ∀ p, Equiv (t.tel.flatten f p) (t.tel.flatten g p)) :
    Equiv (encode.{u,v,w} M t f) (encode.{u,v,w} M t g) :=
  (widen.{u,v,w} t).erasedEncode_congr M _ _ (expand_congr.{u,v,w} t f g h)

theorem read_congr {I : Type w} (M : Interp.{max (u+1) v})
    {m : Nat} (t : RecTel.{u,w} I m) (f g : PSet.{max (u+1) v}) (h : Equiv f g) :
    ∀ p, Equiv (t.tel.flatten (read.{u,v,w} M t f) p)
      (t.tel.flatten (read.{u,v,w} M t g) p) := by
  induction t generalizing f g with
  | ret i => exact fun _ => h
  | pi A B ih => exact fun p => ih p.1 _ _ (fapp_congr h Equiv.rfl) p.2

theorem read_encode {I : Type w} (M : Interp.{max (u+1) v})
    {m : Nat} (t : RecTel.{u,w} I m) (ht : t.DomainsDich)
    (f : PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v})) :
    ∀ p, Equiv (t.tel.flatten (read.{u,v,w} M t (encode.{u,v,w} M t f)) p)
      (t.tel.flatten f p) := by
  induction t with
  | ret i => exact fun _ => Equiv.rfl
  | pi A B ih =>
      intro p
      let q := up.{u,v} A p.1
      have eq : FBrDown.{u,max (u+1) v} A q = p.1 := down_up.{u,v} A p.1
      have ev : Equiv (lift.{u,max (u+1) v} (PiCompile.classValue A p.1))
          (PiCompile.classValue (lift.{u,max (u+1) v} A) q) := by
        simpa only [eq] using PiSmallRecursive.classValue_lift.{u,v} A q
      have ha : lift.{u,max (u+1) v} (PiCompile.classValue A p.1) ∈
          Ed M (tyv (lift.{u,max (u+1) v} A)) :=
        mem_congr_right (ed_tyv M (dich_lift.{u,v} ht.1)).symm
          (lift_mem_lift.{u,max (u+1) v}.mpr (PiCompile.classValue_mem A p.1))
      have he := (beta_val M
        (fun _ _ h => classFiber_congr (lift.{u,max (u+1) v} A) _ h) ha).trans
        ((classFiber_congr (lift.{u,max (u+1) v} A) _ ev).trans
          (classFiber_classValue (lift.{u,max (u+1) v} A)
            (fun r => encode.{u,v,w} M (B (FBrDown.{u,max (u+1) v} A r))
              (f (FBrDown.{u,max (u+1) v} A r))) q))
      rw [eq] at he
      exact (read_congr.{u,v,w} M (B p.1) _ _ he p.2).trans
        (ih p.1 (ht.2 p.1) (f p.1) p.2)

theorem encode_mem_iff {I : Type w} (M : Interp.{max (u+1) v})
    {m : Nat} (t : RecTel.{u,w} I m) (ht : t.DomainsDich)
    (X : I → PSet.{max (u+1) v}) (hX : ∀ i, Dich (X i))
    (f : PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v})) :
    encode.{u,v,w} M t f ∈ Ed M ((widen.{u,v,w} t).erasedType M X) ↔
      Related.{u,v,w} t X f := by
  constructor
  · intro hf
    have hr := read_related.{u,v,w} M t ht X hX hf
    apply (PiTel.all_iff _ _ _).mpr
    intro p
    exact mem_congr_left (read_encode.{u,v,w} M t ht f p)
      ((PiTel.all_iff _ _ _).mp hr p)
  · exact encode_mem.{u,v,w} M t ht X hX f

theorem dich_lower {A : PSet.{u}}
    (hA : Dich (lift.{u,max (u+1) v} A)) : Dich A := by
  rcases hA with h | h
  · apply Or.inl
    intro z hz
    exact equiv_of_lift.{u,max (u+1) v}
      ((h _ (lift_mem_lift.{u,max (u+1) v}.mpr hz)).trans lift_pempty_equiv.symm)
  · apply Or.inr
    intro hz
    exact h (mem_congr_left lift_pempty_equiv
      (lift_mem_lift.{u,max (u+1) v}.mpr hz))

/-- Conditional compilation has dichotomous small domains even when the
fallback is used. No hereditary-typing or domain-smallness premise occurs. -/
theorem compile_domains {I : Type w} (M : Interp.{max (u+1) v})
    (ch : Choice.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{max (u+1) v}) → I) :
    ∀ ds ρ, (PiSmallRecursive.compile.{u,v,w} M ch σ R ds ρ).DomainsDich
  | [], _ => True.intro
  | A :: ds, ρ =>
      ⟨dich_lower.{u,v}
        (PiSmallRecursive.lifted_rep_dich.{u,v} M ch
          (Ed M (den M σ ρ A)) (dich_ed M _)),
        fun _ => compile_domains M ch σ R ds _⟩

theorem encode_small {I : Type w} (ch : Choice.{u}) (M : Interp.{max (u+1) v})
    {m : Nat} (t : RecTel.{u,w} I m) (ht : t.DomainsDich)
    (f : PiTel.Value.{u,max (u+1) v + 1} t.tel (fun _ => PSet.{max (u+1) v}))
    (hf : ∀ p, Small.{u,max (u+1) v} (t.tel.flatten f p)) :
    Small.{u,max (u+1) v} (encode.{u,v,w} M t f) := by
  have hd : PiSmallStage.DomainsSmall.{u,max (u+1) v,w} (widen.{u,v,w} t) := by
    clear ht f hf
    induction t with
    | ret _ => trivial
    | pi A B ih =>
        exact ⟨small_lift A, fun q => ih (FBrDown.{u,max (u+1) v} A q)⟩
  have hs : ∀ p, Small.{u,max (u+1) v}
      ((widen.{u,v,w} t).tel.flatten (expand.{u,v,w} t f) p) := by
    clear hd
    induction t with
    | ret _ => exact fun _ => hf .unit
    | pi A B ih =>
        intro p
        exact ih (FBrDown.{u,max (u+1) v} A p.1) (ht.2 _) (f _)
          (fun r => hf ⟨FBrDown.{u,max (u+1) v} A p.1, r⟩) p.2
  exact PiSmallStage.erasedEncode_small.{u,max (u+1) v,w} ch M
    (widen.{u,v,w} t) (widen_dich.{u,v,w} t ht) hd (expand.{u,v,w} t f) hs

end Rcic.F3.PSet.PiSmallFieldAt
