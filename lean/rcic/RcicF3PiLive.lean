import rcic.RcicF3PiSmallValue
/-! Live-path smallness and exact small-telescope element sets. The live
condition is derived from an actual small field with data leaves; it is
not asserted for proof-valued families. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiLive
open Rcic.Declarative
universe u

def Reach (M : Interp.{u}) (σ : Nat → Nat) : List (Expr Nat) → (Nat → PSet.{u}) → Prop
  | [], _ => True
  | A :: ds, ρ => ∃ a, a ∈ Ed M (den M σ ρ A) ∧ Reach M σ ds (vcons a ρ)

def LiveSmall (M : Interp.{4}) (σ : Nat → Nat) : List (Expr Nat) → (Nat → PSet.{4}) → Prop
  | [], _ => True
  | A :: ds, ρ =>
    (Reach M σ (A :: ds) ρ → Small.{3,4} (Ed M (den M σ ρ A))) ∧
    ∀ a, a ∈ Ed M (den M σ ρ A) → LiveSmall M σ ds (vcons a ρ)

theorem empty_refused_at_reach (M : Interp.{u}) (σ : Nat → Nat) (b : Expr Nat)
    (hb : ∀ ρ, pempty ∉ Ed M (den M σ ρ b)) :
    ∀ ds ρ, Reach M σ ds ρ → pempty ∉ Ed M (den M σ ρ (policyPi ds b)) := by
  intro ds
  induction ds with
  | nil => intro ρ _; exact hb ρ
  | cons A ds ih =>
    intro ρ hr hf
    obtain ⟨a, ha, hr'⟩ := hr
    have hm := app_mem M
      (fun _ _ h => den_congr M σ _ (vcons_congr (ρ := ρ) (ρ' := ρ) h (fun _ => Equiv.rfl))) hf ha
    exact ih (vcons a ρ) hr' (mem_congr_left (fapp_pempty a) hm)
theorem liveSmall_of_member (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (b : Expr Nat)
    (hb : ∀ ρ, pempty ∉ Ed (mkM P μ) (den (mkM P μ) σ ρ b)) :
    ∀ ds ρ (g : PSet.{4}), Small.{3,4} g →
      g ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ (policyPi ds b)) →
      LiveSmall (mkM P μ) σ ds ρ := by
  intro ds
  induction ds with
  | nil => intro ρ g hg hf; trivial
  | cons A ds ih =>
    intro ρ g hg hf
    have hB : ∀ a a', Equiv a a' →
        Equiv (den (mkM P μ) σ (vcons a ρ) (policyPi ds b))
          (den (mkM P μ) σ (vcons a' ρ) (policyPi ds b)) :=
      fun _ _ h => den_congr _ _ _ (vcons_congr h (fun _ => Equiv.rfl))
    refine ⟨fun hr => ?_, fun a ha => ?_⟩
    · have hne : ¬ Equiv g pempty := fun he =>
        empty_refused_at_reach (mkM P μ) σ b hb (A :: ds) ρ hr (mem_congr_left he hf)
      exact PiSmallValue.domain_small (mkM P μ) hB hg hf hne
    · exact ih (vcons a ρ) (fapp g a) (PiSmallValue.fapp_small hg)
        (app_mem (mkM P μ) hB hf ha)
theorem dead_ed (M : Interp.{u}) (σ : Nat → Nat) (b : Expr Nat) :
    ∀ ds ρ, ¬ Reach M σ ds ρ →
      Equiv (Ed M (den M σ ρ (policyPi ds b))) (singleton pempty) := by
  intro ds
  induction ds with
  | nil => intro ρ hr; exact (hr trivial).elim
  | cons A ds ih =>
    intro ρ hr
    let B := fun a => den M σ (vcons a ρ) (policyPi ds b)
    have he : ∀ a, a ∈ Ed M (den M σ ρ A) →
        Equiv (Ed M (B a)) (singleton pempty) :=
      fun a ha => ih (vcons a ρ) (fun h => hr ⟨a, ha, h⟩)
    have hP : PiProp M (den M σ ρ A) B :=
      fun a ha y hy => mem_singleton.mp (mem_congr_right (he a ha) hy)
    have et := ed_piVal M (den M σ ρ A) B
      (fun _ _ h => den_congr M σ _ (vcons_congr (ρ := ρ) (ρ' := ρ) h (fun _ => Equiv.rfl)))
    rw [cond_pos hP] at et
    refine et.trans (ext fun z => ⟨fun hz => mem_singleton.mpr (mem_tv.mp hz).2, fun hz => ?_⟩)
    exact mem_tv.mpr ⟨fun a ha => mem_congr_right (he a ha).symm
      (mem_singleton.mpr Equiv.rfl), mem_singleton.mp hz⟩
open PiSmallCompile
universe v
/-- Exact element sets under live-path smallness; dead paths stay erased. -/
theorem compile_ed {I : Type v} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (R : (Nat → PSet.{4}) → I) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (b : Expr Nat) (hL : ∀ ρ, Equiv (X (R ρ)) (Ed (mkM P μ) (den (mkM P μ) σ ρ b))) :
    ∀ ds ρ, LiveSmall (mkM P μ) σ ds ρ →
      Equiv (Ed (mkM P μ) ((widen (compile P μ σ R ds ρ)).erasedType (mkM P μ) X))
        (Ed (mkM P μ) (den (mkM P μ) σ ρ (policyPi ds b))) := by
  intro ds
  induction ds with
  | nil => intro ρ _; exact (ed_tyv (mkM P μ) (hX (R ρ))).trans (hL ρ)
  | cons A ds ih =>
    intro ρ hl
    let M := mkM P μ
    let D := Ed M (den M σ ρ A)
    let S := rep P D
    let T := lift.{3,4} S
    let C := fun a => tyv (classFiber T (fun q =>
      Ed M ((widen (compile P μ σ R ds
        (vcons (lift.{3,4} (PiCompile.classValue S (FBrDown.{3,4} S q))) ρ))).erasedType M X)) a)
    change Equiv (Ed M (piVal M (tyv T) C))
      (Ed M (piVal M (den M σ ρ A) (fun a => den M σ (vcons a ρ) (policyPi ds b))))
    haveI := P.dec
    by_cases hSmall : Small.{3,4} D
    · have e : Equiv D T := rep_spec P D hSmall
      have hT : Dich T := (dich_congr e).mp (dich_ed M _)
      apply ed_congr M
      apply piVal_ed_congr_on M ((ed_tyv M hT).trans e.symm)
        (fun _ _ h => ed_congr M (tyv_congr (classFiber_congr T _ h)))
        (fun _ _ h => ed_congr M (den_congr M σ _
          (vcons_congr (ρ := ρ) (ρ' := ρ) h (fun _ => Equiv.rfl))))
      intro z hz
      have hzT : z ∈ T := mem_congr_right (ed_tyv M hT) hz
      obtain ⟨i, hi⟩ := hzT
      let q := Quotient.mk (FSetoid T) i
      let r := FBrDown.{3,4} S q
      let z' := lift.{3,4} (PiCompile.classValue S r)
      have hz'T : z' ∈ T := lift_mem_lift.{3,4}.mpr (PiCompile.classValue_mem S r)
      have hz'D : z' ∈ D := mem_congr_right e.symm hz'T
      have ev : Equiv z' z := (classValue_lift S q).trans
        ((PiCompile.classValue_at T i).trans hi)
      have ef := (classFiber_congr T (fun q => Ed M
        ((widen (compile P μ σ R ds
          (vcons (lift.{3,4} (PiCompile.classValue S (FBrDown.{3,4} S q))) ρ))).erasedType M X))
        hi.symm).trans (classFiber_at T _ i)
      exact ((ed_tyv M ((dich_congr ef).mpr (dich_ed M _))).trans ef).trans
        ((ih (vcons z' ρ) (hl.2 z' hz'D)).trans
          (ed_congr M (den_congr M σ (policyPi ds b)
            (vcons_congr ev (fun _ => Equiv.rfl)))))
    · have eS : S = pempty := by
        unfold S rep
        rw [dif_neg hSmall]
      have eT : Equiv T pempty := by
        change Equiv (lift.{3,4} S) pempty
        rw [eS]
        exact lift_pempty_equiv
      have hT : Dich T := (dich_congr eT).mpr (Or.inl (fun _ h => (not_mem_pempty h).elim))
      have hnone : ∀ a, a ∈ Ed M (tyv T) → False :=
        fun _ ha => not_mem_pempty (mem_congr_right ((ed_tyv M hT).trans eT) ha)
      have hC : ∀ a a', Equiv a a' → Equiv (C a) (C a') :=
        fun _ _ h => tyv_congr (classFiber_congr T _ h)
      have hP : PiProp M (tyv T) C := fun a ha => (hnone a ha).elim
      have et := ed_piVal M (tyv T) C hC
      rw [cond_pos hP] at et
      have ez : Equiv (Ed M (piVal M (tyv T) C)) (singleton pempty) := by
        refine et.trans (ext fun z => ⟨fun hz => mem_singleton.mpr (mem_tv.mp hz).2, fun hz => ?_⟩)
        exact mem_tv.mpr ⟨fun a ha => (hnone a ha).elim, mem_singleton.mp hz⟩
      exact ez.trans (dead_ed M σ b (A :: ds) ρ (fun hr => hSmall (hl.1 hr))).symm
theorem reach_free (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) : ∀ ds ρ,
    (∀ A ∈ ds, occursConst f A = false) →
    (Reach (mkM P (upd μ f X₁)) σ ds ρ ↔ Reach (mkM P (upd μ f X₂)) σ ds ρ) := by
  intro ds
  induction ds with
  | nil => intro ρ _; exact Iff.rfl
  | cons A ds ih =>
    intro ρ hd
    have he := PiIndependent.den_free P μ f X₁ X₂ σ A
      (hd A (List.mem_cons_self _ _)) ρ
    have ht : ∀ e ∈ ds, occursConst f e = false :=
      fun e h => hd e (List.mem_cons_of_mem _ h)
    constructor
    · rintro ⟨a, ha, hr⟩
      refine ⟨a, ?_, (ih (vcons a ρ) ht).mp hr⟩
      rw [← he]; exact ha
    · rintro ⟨a, ha, hr⟩
      refine ⟨a, ?_, (ih (vcons a ρ) ht).mpr hr⟩
      rw [he]; exact ha
theorem liveSmall_free (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) : ∀ ds ρ,
    (∀ A ∈ ds, occursConst f A = false) →
    (LiveSmall (mkM P (upd μ f X₁)) σ ds ρ ↔ LiveSmall (mkM P (upd μ f X₂)) σ ds ρ) := by
  intro ds
  induction ds with
  | nil => intro ρ _; exact Iff.rfl
  | cons A ds ih =>
    intro ρ hd
    have he := PiIndependent.den_free P μ f X₁ X₂ σ A
      (hd A (List.mem_cons_self _ _)) ρ
    have ht : ∀ e ∈ ds, occursConst f e = false :=
      fun e h => hd e (List.mem_cons_of_mem _ h)
    have hr := reach_free P μ f X₁ X₂ σ (A :: ds) ρ hd
    constructor
    · intro hl
      refine ⟨fun h => ?_, fun a ha => ?_⟩
      · rw [← he]; exact hl.1 (hr.mpr h)
      · apply (ih (vcons a ρ) ht).mp
        apply hl.2 a
        rw [he]; exact ha
    · intro hl
      refine ⟨fun h => ?_, fun a ha => ?_⟩
      · rw [he]; exact hl.1 (hr.mp h)
      · apply (ih (vcons a ρ) ht).mpr
        apply hl.2 a
        rw [← he]; exact ha
end Rcic.F3.PSet.PiLive
