import rcic.RcicF3PiSmallCompile
/-! Small branch addresses with large erased values. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallField
universe v
open PiSmallCompile

def expand {I : Type v} : {m : Nat} → (t : RecTel.{3,v} I m) →
    PiTel.Value.{3,5} t.tel (fun _ => PSet.{4}) →
    PiTel.Value.{4,5} (widen t).tel (fun _ => PSet.{4})
  | _, .ret _, f => f
  | _, .pi A B, f => fun q => expand (B (FBrDown.{3,4} A q)) (f (FBrDown.{3,4} A q))

def read {I : Type v} (M : Interp.{4}) : {m : Nat} → (t : RecTel.{3,v} I m) → PSet.{4} →
    PiTel.Value.{3,5} t.tel (fun _ => PSet.{4})
  | _, .ret _, f => f
  | _, .pi A B, f => fun q => read M (B q)
      (fapp f (lift.{3,4} (PiCompile.classValue A q)))

def encode {I : Type v} (M : Interp.{4}) {m : Nat} (t : RecTel.{3,v} I m)
    (f : PiTel.Value.{3,5} t.tel (fun _ => PSet.{4})) : PSet.{4} :=
  (widen t).erasedEncode M (expand t f)

def Related {I : Type v} {m : Nat} (t : RecTel.{3,v} I m) (X : I → PSet.{4})
    (f : PiTel.Value.{3,5} t.tel (fun _ => PSet.{4})) : Prop :=
  t.tel.All (fun p z => z ∈ X (t.result p)) f

theorem expand_congr {I : Type v} {m : Nat} (t : RecTel.{3,v} I m)
    (f g : PiTel.Value.{3,5} t.tel (fun _ => PSet.{4}))
    (h : ∀ p, Equiv (t.tel.flatten f p) (t.tel.flatten g p)) :
    ∀ p, Equiv ((widen t).tel.flatten (expand t f) p)
      ((widen t).tel.flatten (expand t g) p) := by
  induction t with
  | ret i => exact fun _ => h .unit
  | pi A B ih =>
    exact fun p => ih (FBrDown.{3,4} A p.1) (f (FBrDown.{3,4} A p.1)) (g (FBrDown.{3,4} A p.1))
      (fun r => h ⟨FBrDown.{3,4} A p.1, r⟩) p.2


theorem read_expand {I : Type v} (M : Interp.{4}) {m : Nat}
    (t : RecTel.{3,v} I m) (f : PSet.{4}) :
    ∀ p, Equiv ((widen t).tel.flatten (expand t (read M t f)) p)
      ((widen t).tel.flatten ((widen t).erasedRead M f) p) := by
  induction t generalizing f with
  | ret i => exact fun _ => Equiv.rfl
  | pi A B ih =>
    intro p
    exact (ih (FBrDown.{3,4} A p.1) _ p.2).trans
      ((widen (B (FBrDown.{3,4} A p.1))).erasedRead_congr M _ _
        (fapp_congr Equiv.rfl (classValue_lift A p.1)) p.2)


theorem dich_lift {A : PSet.{3}} (hA : Dich A) : Dich (lift.{3,4} A) := by
  rcases hA with h | h
  · apply Or.inl
    intro z hz
    obtain ⟨a, ha, he⟩ := mem_lift.mp hz
    exact he.trans ((lift_equiv.{3,4} (h a ha)).trans lift_pempty_equiv)
  · apply Or.inr
    intro hz
    obtain ⟨a, ha, he⟩ := mem_lift.mp hz
    have e : Equiv a pempty := equiv_of_lift (he.symm.trans lift_pempty_equiv.symm)
    exact h (mem_congr_left e ha)


theorem widen_dich {I : Type v} {m : Nat} (t : RecTel.{3,v} I m)
    (ht : t.DomainsDich) : (widen t).DomainsDich := by
  induction t with
  | ret i => trivial
  | pi A B ih => exact ⟨dich_lift ht.1, fun q => ih (FBrDown.{3,4} A q) (ht.2 _)⟩


theorem related_expand {I : Type v} {m : Nat} (t : RecTel.{3,v} I m)
    (X : I → PSet.{4}) (f : PiTel.Value.{3,5} t.tel (fun _ => PSet.{4}))
    (hf : Related t X f) : (widen t).Rel X (expand t f) := by
  induction t with
  | ret i => exact hf
  | pi A B ih => exact fun q => ih (FBrDown.{3,4} A q) (f _) (hf _)


theorem encode_mem {I : Type v} (M : Interp.{4}) {m : Nat} (t : RecTel.{3,v} I m)
    (ht : t.DomainsDich) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (f : PiTel.Value.{3,5} t.tel (fun _ => PSet.{4})) (hf : Related t X f) :
    encode M t f ∈ Ed M ((widen t).erasedType M X) := by
  exact (widen t).erasedEncode_mem M (widen_dich t ht) X hX _
    (related_expand t X f hf)


def up : (A : PSet.{3}) → FBr A → FBr (lift.{3,4} A)
  | mk α f => Quotient.lift (fun i => Quotient.mk (FSetoid (lift.{3,4} (mk α f))) ⟨i⟩)
      (fun _ _ h => Quotient.sound (lift_equiv.{3,4} h))

theorem down_up (A : PSet.{3}) (q : FBr A) : FBrDown.{3,4} A (up A q) = q := by
  cases A with
  | mk α f => exact Quotient.inductionOn q (fun _ => rfl)


theorem read_related {I : Type v} (M : Interp.{4}) {m : Nat} (t : RecTel.{3,v} I m)
    (ht : t.DomainsDich) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    {f : PSet.{4}} (hf : f ∈ Ed M ((widen t).erasedType M X)) :
    Related t X (read M t f) := by
  induction t generalizing f with
  | ret i => exact mem_congr_right (ed_tyv M (hX i)) hf
  | pi A B ih =>
    intro q
    let q' := up A q
    have eq : FBrDown.{3,4} A q' = q := down_up A q
    have ev : Equiv (lift.{3,4} (PiCompile.classValue A q))
        (PiCompile.classValue (lift.{3,4} A) q') := by
      simpa only [eq] using classValue_lift A q'
    have ha : PiCompile.classValue (lift.{3,4} A) q' ∈ Ed M (tyv (lift.{3,4} A)) :=
      mem_congr_right (ed_tyv M (dich_lift ht.1)).symm
        (PiCompile.classValue_mem (lift.{3,4} A) q')
    have hm := app_mem M
      (fun _ _ h => tyv_congr (classFiber_congr (lift.{3,4} A) _ h)) hf ha
    have hv := mem_congr_right (ed_classFiber_classValue M (lift.{3,4} A)
      (fun r => Ed M ((widen (B (FBrDown.{3,4} A r))).erasedType M X))
      (fun _ => dich_ed M _) q') hm
    rw [eq] at hv
    exact ih q (ht.2 q) (mem_congr_left (fapp_congr Equiv.rfl ev.symm) hv)


theorem read_spec {I : Type v} (M : Interp.{4}) {m : Nat} (t : RecTel.{3,v} I m)
    (ht : t.DomainsDich) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    {f : PSet.{4}} (hf : f ∈ Ed M ((widen t).erasedType M X)) :
    Related t X (read M t f) ∧ Equiv f (encode M t (read M t f)) := by
  refine ⟨read_related M t ht X hX hf, ?_⟩
  exact ((widen t).erasedRead_spec M (widen_dich t ht) X hX hf).2.trans
    ((widen t).erasedEncode_congr M _ _ (read_expand M t f)).symm


theorem encode_congr {I : Type v} (M : Interp.{4}) {m : Nat} (t : RecTel.{3,v} I m)
    (f g : PiTel.Value.{3,5} t.tel (fun _ => PSet.{4}))
    (h : ∀ p, Equiv (t.tel.flatten f p) (t.tel.flatten g p)) :
    Equiv (encode M t f) (encode M t g) := by
  exact (widen t).erasedEncode_congr M _ _ (expand_congr t f g h)


theorem read_congr {I : Type v} (M : Interp.{4}) {m : Nat} (t : RecTel.{3,v} I m)
    (f g : PSet.{4}) (h : Equiv f g) :
    ∀ p, Equiv (t.tel.flatten (read M t f) p) (t.tel.flatten (read M t g) p) := by
  induction t generalizing f g with
  | ret i => exact fun _ => h
  | pi A B ih => exact fun p => ih p.1 _ _ (fapp_congr h Equiv.rfl) p.2


theorem read_encode {I : Type v} (M : Interp.{4}) {m : Nat} (t : RecTel.{3,v} I m)
    (ht : t.DomainsDich) (f : PiTel.Value.{3,5} t.tel (fun _ => PSet.{4})) :
    ∀ p, Equiv (t.tel.flatten (read M t (encode M t f)) p) (t.tel.flatten f p) := by
  induction t with
  | ret i => exact fun _ => Equiv.rfl
  | pi A B ih =>
    intro p
    let q := up A p.1
    have eq : FBrDown.{3,4} A q = p.1 := down_up A p.1
    have ev : Equiv (lift.{3,4} (PiCompile.classValue A p.1))
        (PiCompile.classValue (lift.{3,4} A) q) := by
      simpa only [eq] using classValue_lift A q
    have ha : lift.{3,4} (PiCompile.classValue A p.1) ∈ Ed M (tyv (lift.{3,4} A)) :=
      mem_congr_right (ed_tyv M (dich_lift ht.1)).symm
        (lift_mem_lift.{3,4}.mpr (PiCompile.classValue_mem A p.1))
    have he := (beta_val M (fun _ _ h => classFiber_congr (lift.{3,4} A) _ h) ha).trans
      ((classFiber_congr (lift.{3,4} A) _ ev).trans
        (classFiber_classValue (lift.{3,4} A)
          (fun r => encode M (B (FBrDown.{3,4} A r)) (f (FBrDown.{3,4} A r))) q))
    rw [eq] at he
    exact (read_congr M (B p.1) _ _ he p.2).trans
      (ih p.1 (ht.2 p.1) (f p.1) p.2)


theorem encode_mem_iff {I : Type v} (M : Interp.{4}) {m : Nat} (t : RecTel.{3,v} I m)
    (ht : t.DomainsDich) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (f : PiTel.Value.{3,5} t.tel (fun _ => PSet.{4})) :
    encode M t f ∈ Ed M ((widen t).erasedType M X) ↔ Related t X f := by
  constructor
  · intro hf
    have hr := read_related M t ht X hX hf
    apply (PiTel.all_iff _ _ _).mpr
    intro p
    exact mem_congr_left (read_encode M t ht f p) ((PiTel.all_iff _ _ _).mp hr p)
  · exact encode_mem M t ht X hX f


theorem dich_lower {A : PSet.{3}} (hA : Dich (lift.{3,4} A)) : Dich A := by
  rcases hA with h | h
  · apply Or.inl
    intro z hz
    exact equiv_of_lift ((h _ (lift_mem_lift.{3,4}.mpr hz)).trans lift_pempty_equiv.symm)
  · apply Or.inr
    intro hz
    exact h (mem_congr_left lift_pempty_equiv (lift_mem_lift.{3,4}.mpr hz))


/-- Small representatives retain the Ed invariant; no inhabited-domain wall. -/
theorem rep_dich (P : Premises4) (M : Interp.{4}) (x : PSet.{4})
    (hx : Small.{3,4} (Ed M x)) : Dich (rep P (Ed M x)) := by
  exact dich_lower ((dich_congr (rep_spec P (Ed M x) hx)).mp (dich_ed M x))


open Rcic.Declarative in
theorem compile_domains_of_hsound {I : Type v} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (R : (Nat → PSet.{4}) → I) (b : Expr Nat) :
    ∀ (ds : List (Expr Nat)) {Γ : LCtx} {l : Level}
    (d : HasTyT E n Γ (policyPi ds b) (.sort l)), HSoundT (mkM P μ) σ d →
    ∀ ρ, Fits (mkM P μ) σ Γ ρ → (compile P μ σ R ds ρ).DomainsDich := by
  intro ds
  induction ds with
  | nil => intro Γ l d hs ρ hρ; trivial
  | cons A ds ih =>
    intro Γ l d hs ρ hρ
    obtain ⟨a, dA, hA⟩ := pi_dom_sound d hs
    obtain ⟨v, dB, hB⟩ := pi_body_sound d hs
    have hx := ed_small P (mkM P μ) (evalTotal σ a)
      (mem_congr_right (ed_tyv (mkM P μ) (U4_dich _)) (hA.root ρ hρ))
    refine ⟨rep_dich P (mkM P μ) (den (mkM P μ) σ ρ A) hx, fun q => ?_⟩
    exact ih dB hB _ ⟨hρ, mem_congr_right (rep_spec P _ hx).symm
      (lift_mem_lift.{3,4}.mpr (PiCompile.classValue_mem _ q))⟩

end Rcic.F3.PSet.PiSmallField
