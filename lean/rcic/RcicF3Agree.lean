import rcic.RcicF3IotaIdx

/-!
# F3 S5a-10: the group's values read the constant table only at their references

`RefsIn S es`: every reference of the expressions lies in `S`. Two tables
that agree on `S` give the same fitting, the same fibres and `≈`-equal
family values (`famEnd_agree`). This is what lets the environment table be
built member by member.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs)

namespace PSet

/-- Every reference of every expression lies in `S`. -/
def RefsIn (S : Nat → Prop) (es : List (Expr Nat)) : Prop := ∀ e, e ∈ es → ∀ r, r ∈ denRefs e → S r

/-- Two tables agree on `S`. -/
def AgreeOn (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (S : Nat → Prop) : Prop := ∀ r, S r → ∀ ls, μ₁ r ls = μ₂ r ls

/-- The group's data mentions only references in `S`. -/
def FamRefsIn (S : Nat → Prop) (fd : FamData) : Prop := ∀ c, c ∈ fd.ctors → RefsIn S c.1 ∧ RefsIn S c.2

section Agree

variable (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {S : Nat → Prop} (h : AgreeOn μ₁ μ₂ S)
include h

theorem den_agreeOn (σ : Nat → Nat) (e : Expr Nat) (he : ∀ r, r ∈ denRefs e → S r) (ρ : Nat → PSet.{4}) :
    den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e := by
  rw [mkM_eq_withμ, mkM_eq_withμ]
  exact den_agree _ σ e (fun r hr ls => h r (he r hr) ls) ρ

theorem TelFits_agreeOn (σ : Nat → Nat) : (Ds : List (Expr Nat)) → RefsIn S Ds → (ρ : Nat → PSet.{4}) →
    (xs : List PSet.{4}) → (TelFits (mkM P μ₁) σ Ds ρ xs ↔ TelFits (mkM P μ₂) σ Ds ρ xs)
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | A :: Ds, hb, ρ, x :: xs => by
      show (x ∈ Ed (mkM P μ₁) (den (mkM P μ₁) σ ρ A) ∧ _) ↔ (x ∈ Ed (mkM P μ₂) (den (mkM P μ₂) σ ρ A) ∧ _)
      rw [den_agreeOn P h σ A (hb A (List.mem_cons_self _ _)) ρ,
        TelFits_agreeOn σ Ds (fun e he => hb e (List.mem_cons_of_mem _ he)) (vcons x ρ) xs]
      rfl

theorem map_den_agreeOn (σ : Nat → Nat) (es : List (Expr Nat)) (hb : RefsIn S es) (ρ : Nat → PSet.{4}) :
    es.map (den (mkM P μ₁) σ ρ) = es.map (den (mkM P μ₂) σ ρ) :=
  List.map_congr_left fun e he => den_agreeOn P h σ e (hb e he) ρ

theorem CtorFits_agreeOn (σ : Nat → Nat) (fd : FamData) (hB : FamRefsIn S fd) (ρp : Nat → PSet.{4})
    (is : List PSet.{4}) (j : Nat) (xs : List PSet.{4}) :
    CtorFits (mkM P μ₁) σ fd.ctors ρp is j xs ↔ CtorFits (mkM P μ₂) σ fd.ctors ρp is j xs := by
  constructor
  · rintro ⟨c, hc, hf, hi⟩
    have hcm : c ∈ fd.ctors := List.getElem?_mem hc
    refine ⟨c, hc, (TelFits_agreeOn P h σ c.1 (hB c hcm).1 ρp xs).mp hf, ?_⟩
    rw [← map_den_agreeOn P h σ c.2 (hB c hcm).2]; exact hi
  · rintro ⟨c, hc, hf, hi⟩
    have hcm : c ∈ fd.ctors := List.getElem?_mem hc
    refine ⟨c, hc, (TelFits_agreeOn P h σ c.1 (hB c hcm).1 ρp xs).mpr hf, ?_⟩
    rw [map_den_agreeOn P h σ c.2 (hB c hcm).2]; exact hi

theorem FitSetT_agreeOn (σ : Nat → Nat) (k' : Nat) : (Ds : List (Expr Nat)) → RefsIn S Ds →
    (ρ : Nat → PSet.{4}) → FitSetT (mkM P μ₁) W4 k' σ Ds ρ = FitSetT (mkM P μ₂) W4 k' σ Ds ρ
  | [], _, _ => rfl
  | A :: Ds, hb, ρ => by
      show sUnion (sImage _ (truncW (mkM P μ₁) W4 k' (Ed (mkM P μ₁) (den (mkM P μ₁) σ ρ A)))) =
        sUnion (sImage _ (truncW (mkM P μ₂) W4 k' (Ed (mkM P μ₂) (den (mkM P μ₂) σ ρ A))))
      rw [den_agreeOn P h σ A (hb A (List.mem_cons_self _ _)) ρ]
      have : (fun x => sImage (fun t => ordPair x t) (FitSetT (mkM P μ₁) W4 k' σ Ds (vcons x ρ))) =
          (fun x => sImage (fun t => ordPair x t) (FitSetT (mkM P μ₂) W4 k' σ Ds (vcons x ρ))) :=
        funext fun x => by rw [FitSetT_agreeOn σ k' Ds (fun e he => hb e (List.mem_cons_of_mem _ he)) (vcons x ρ)]
      rw [this]
      rfl

theorem BoundT_agreeOn (σ : Nat → Nat) (k' : Nat) (ρp : Nat → PSet.{4}) :
    (j : Nat) → (cs : List (List (Expr Nat) × List (Expr Nat))) →
    (∀ c, c ∈ cs → RefsIn S c.1) →
    BoundT (mkM P μ₁) W4 k' σ ρp j cs = BoundT (mkM P μ₂) W4 k' σ ρp j cs
  | _, [], _ => rfl
  | j, c :: cs, hb => by
      show sUnion (pair (sImage _ (FitSetT (mkM P μ₁) W4 k' σ c.1 ρp)) _) =
        sUnion (pair (sImage _ (FitSetT (mkM P μ₂) W4 k' σ c.1 ρp)) _)
      rw [FitSetT_agreeOn P h σ k' c.1 (hb c (List.mem_cons_self _ _)) ρp,
        BoundT_agreeOn σ k' ρp (j + 1) cs (fun c' hc' => hb c' (List.mem_cons_of_mem _ hc'))]

theorem famEnd_agreeOn (σ : Nat → Nat) (fd : FamData) (hB : FamRefsIn S fd) (ρ : Nat → PSet.{4}) :
    Equiv (famEnd (mkM P μ₁) W4 σ fd ρ) (famEnd (mkM P μ₂) W4 σ fd ρ) := by
  unfold famEnd
  refine cond_congr Iff.rfl (tyv_congr (tv_congr ?_)) (tyv_congr ?_)
  · exact ⟨fun ⟨j, xs, hc⟩ => ⟨j, xs, (CtorFits_agreeOn P h σ fd hB _ _ j xs).mp hc⟩,
      fun ⟨j, xs, hc⟩ => ⟨j, xs, (CtorFits_agreeOn P h σ fd hB _ _ j xs).mpr hc⟩⟩
  · unfold TypeFib
    rw [BoundT_agreeOn P h σ _ _ 0 fd.ctors (fun c hc => (hB c hc).1)]
    exact sep_congr
      (fun _ _ hab ⟨j, xs, hc, he⟩ => ⟨j, xs, (CtorFits_agreeOn P h σ fd hB _ _ j xs).mp hc, hab.symm.trans he⟩)
      (fun _ _ hab ⟨j, xs, hc, he⟩ => ⟨j, xs, (CtorFits_agreeOn P h σ fd hB _ _ j xs).mpr hc, hab.symm.trans he⟩)
      Equiv.rfl

/-- `piLam` with `≈`-equal end values under agreeing tables. -/
theorem piLam_agreeOn (σ : Nat → Nat) {g₁ g₂ : (Nat → PSet.{4}) → PSet.{4}} (hg : EnvResp g₁)
    (hgg : ∀ ρ, Equiv (g₁ ρ) (g₂ ρ)) : (e : Expr Nat) → (∀ r, r ∈ denRefs e → S r) → (ρ : Nat → PSet.{4}) →
    Equiv (piLam (mkM P μ₁) σ g₁ ρ e) (piLam (mkM P μ₂) σ g₂ ρ e)
  | .pi A B, he, ρ => by
      show Equiv (lamVal (mkM P μ₁) (den (mkM P μ₁) σ ρ A) _) (lamVal (mkM P μ₂) (den (mkM P μ₂) σ ρ A) _)
      rw [den_agreeOn P h σ A (fun r hr => he r (by simp [denRefs, hr])) ρ]
      exact lamVal_congr (mkM P μ₂) Equiv.rfl fun x x' hx =>
        (piLam_congr (mkM P μ₁) σ hg B (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl))).trans
          (piLam_agreeOn σ hg hgg B (fun r hr => he r (by simp [denRefs, hr])) (vcons x' ρ))
  | .bvar _, _, ρ => hgg ρ
  | .sort _, _, ρ => hgg ρ
  | .const _ _, _, ρ => hgg ρ
  | .app _ _, _, ρ => hgg ρ
  | .lam _ _, _, ρ => hgg ρ
  | .letE _ _ _, _, ρ => hgg ρ
  | .lit _, _, ρ => hgg ρ

end Agree

end PSet

end Rcic.F3
