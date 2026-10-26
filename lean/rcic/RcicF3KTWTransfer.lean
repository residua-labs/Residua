import rcic.RcicF3KTWFamLfp

/-!
# F3 S7 KT-2d-1: table transfer at the canonical instance.

Two tables that differ only in the family entry, and agree on that entry at
the one level vector the group reads at `σ`, give the same family value at `σ`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

namespace PSet

open Rcic.Declarative

/-- Every occurrence of `f` in `e` is at the canonical universe instance. -/
def CanonOcc (f ar : Nat) : Expr Nat → Prop
  | .const r ls => r = f → ls = canonL ar
  | .app a b => CanonOcc f ar a ∧ CanonOcc f ar b
  | .lam A b => CanonOcc f ar A ∧ CanonOcc f ar b
  | .pi A B => CanonOcc f ar A ∧ CanonOcc f ar B
  | .letE T v b => CanonOcc f ar T ∧ CanonOcc f ar v ∧ CanonOcc f ar b
  | _ => True

/-- A constant-free expression trivially has canonical occurrences. -/
theorem canonOcc_of_free {f ar : Nat} {e : Expr Nat} (h : occursConst f e = false) :
    CanonOcc f ar e := by
  induction e with
  | const r ls =>
      intro hr; subst hr; simp only [occursConst] at h; exact absurd h (by decide)
  | app a b iha ihb =>
      exact ⟨iha (Bool.or_eq_false_iff.mp h).1, ihb (Bool.or_eq_false_iff.mp h).2⟩
  | lam A b ihA ihb =>
      exact ⟨ihA (Bool.or_eq_false_iff.mp h).1, ihb (Bool.or_eq_false_iff.mp h).2⟩
  | pi A B ihA ihB =>
      exact ⟨ihA (Bool.or_eq_false_iff.mp h).1, ihB (Bool.or_eq_false_iff.mp h).2⟩
  | letE T v b ihT ihv ihb =>
      have h' := Bool.or_eq_false_iff.mp h
      have h'' := Bool.or_eq_false_iff.mp h'.1
      exact ⟨ihT h''.1, ihv h''.2, ihb h'.2⟩
  | _ => trivial

/-- A recursive spine has canonical occurrences. -/
theorem canonOcc_foldApps {f ar : Nat} (args : List (Expr Nat))
    (hargs : ∀ e, e ∈ args → CanonOcc f ar e) :
    CanonOcc f ar (foldApps (.const f (canonL ar)) args) := by
  suffices ∀ (h : Expr Nat), CanonOcc f ar h →
      CanonOcc f ar (foldApps h args) from this _ (fun _ => rfl)
  induction args with
  | nil => intro h hh; exact hh
  | cons a rest ih =>
      intro h hh
      exact ih (fun e he => hargs e (List.mem_cons.mpr (Or.inr he)))
        (Expr.app h a) ⟨hh, hargs a (List.mem_cons.mpr (Or.inl rfl))⟩

/-- A direct-recursive field has canonical occurrences. -/
theorem canonOcc_directRec {f ar np nq d : Nat} {A : Expr Nat}
    (h : DirectRec f ar np nq d A) : CanonOcc f ar A := by
  obtain ⟨idx, hA, hidx, hfree⟩ := h
  rw [hA]
  exact canonOcc_foldApps _ (fun e he =>
    (List.mem_append.mp he).elim
      (fun hp => (canonOcc_of_free
        (paramLocals_free f np d e hp) : CanonOcc f ar e))
      (fun hi => canonOcc_of_free (hfree e hi)))

/-- A function-recursive field has canonical occurrences. -/
theorem canonOcc_fnRec {f ar np nq d : Nat} {A : Expr Nat}
    (h : FnRec f ar np nq d A) : CanonOcc f ar A := by
  obtain ⟨D', idx, hA, hidx, hfD, hfree⟩ := h
  rw [hA]
  exact ⟨canonOcc_of_free hfD,
    canonOcc_foldApps _ (fun e he =>
      (List.mem_append.mp he).elim
        (fun hp => (canonOcc_of_free
          (paramLocals_free f np (d + 1) e hp) : CanonOcc f ar e))
        (fun hi => canonOcc_of_free (hfree e hi)))⟩

/-- Every field of a class-A list has canonical occurrences. -/
theorem canonOcc_fieldsClassA {f ar np nq : Nat} :
    ∀ {Fs : List (Expr Nat)} {d : Nat}, FieldsClassA f ar np nq Fs d →
      ∀ A, A ∈ Fs → CanonOcc f ar A
  | [], _, _, _, hA => absurd hA (List.not_mem_nil _)
  | A' :: Fs, d, ⟨h1, h2⟩, A, hA => by
      rcases (List.mem_cons.mp hA) with h | hA'
      · subst h
        rcases h1 with hf | r | r
        · exact canonOcc_of_free hf
        · exact canonOcc_directRec r
        · exact canonOcc_fnRec r
      · exact canonOcc_fieldsClassA h2 A hA' 

/-- `Ed`/`truncW`/`lamVal`/`piVal`/`cond` only read `M.dec` — same `P` ⇒ equal. -/
theorem Ed_dec_eq (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (t : PSet.{4}) :
    Ed (mkM P μ₁) t = Ed (mkM P μ₂) t := rfl

theorem truncW_dec_eq (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (W : Nat → PSet.{4}) (k : Nat) (S : PSet.{4}) :
    truncW (mkM P μ₁) W k S = truncW (mkM P μ₂) W k S := rfl

theorem lamVal_dec_eq (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (t : PSet.{4}) (f : PSet.{4} → PSet.{4}) :
    lamVal (mkM P μ₁) t f = lamVal (mkM P μ₂) t f := rfl

theorem piVal_dec_eq (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (t : PSet.{4}) (f : PSet.{4} → PSet.{4}) :
    piVal (mkM P μ₁) t f = piVal (mkM P μ₂) t f := rfl


/-- `den` at the `upd`-tables agrees on canonically-occurring expressions when
the family entry agrees at the `σ`-evaluation of `canonL ar`. -/
theorem denLit_transfer (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    {X₁ X₂ : List Nat → PSet.{4}} (hf : f ≠ 1 ∧ f ≠ 2) :
    ∀ t, denLit (mkM P (upd μ f X₁)) t = denLit (mkM P (upd μ f X₂)) t
  | 0 => by
      show (upd μ f X₁) 1 [] = (upd μ f X₂) 1 []
      rw [upd_ne μ f X₁ hf.1.symm, upd_ne μ f X₂ hf.1.symm]
  | n + 1 => by
      show fapp ((upd μ f X₁) 2 []) (denLit _ n) = fapp ((upd μ f X₂) 2 []) (denLit _ n)
      rw [upd_ne μ f X₁ hf.2.symm, upd_ne μ f X₂ hf.2.symm,
        denLit_transfer P μ f hf n]

/-- `den` at the `upd`-tables agrees on canonically-occurring expressions when
the family entry agrees at the `σ`-evaluation of `canonL ar`. -/
theorem den_transfer (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f ar : Nat)
    {X₁ X₂ : List Nat → PSet.{4}} (σ : Nat → Nat)
    (hX : X₁ ((canonL ar).map (evalTotal σ)) = X₂ ((canonL ar).map (evalTotal σ)))
    (hf : f ≠ 1 ∧ f ≠ 2) :
    (e : Expr Nat) → CanonOcc f ar e → ∀ ρ,
      den (mkM P (upd μ f X₁)) σ ρ e = den (mkM P (upd μ f X₂)) σ ρ e
  | .bvar i, _, _ => rfl
  | .sort l, _, _ => rfl
  | .const r ls, hco, ρ => by
      show (upd μ f X₁) r (ls.map (evalTotal σ)) = (upd μ f X₂) r (ls.map (evalTotal σ))
      by_cases hr : r = f
      · rw [hr, upd_eq μ f X₁, upd_eq μ f X₂, hco hr]
        exact hX
      · rw [upd_ne μ f X₁ hr, upd_ne μ f X₂ hr]
  | .app a b, ⟨ha, hb⟩, ρ => by
      show fapp (den _ σ ρ a) (den _ σ ρ b) = fapp (den _ σ ρ a) (den _ σ ρ b)
      rw [den_transfer P μ f ar σ hX hf a ha ρ, den_transfer P μ f ar σ hX hf b hb ρ]
  | .lam A b, ⟨hA, hb⟩, ρ => by
      show lamVal (mkM P (upd μ f X₁)) (den _ σ ρ A) _ = lamVal (mkM P (upd μ f X₂)) (den _ σ ρ A) _
      rw [den_transfer P μ f ar σ hX hf A hA ρ]
      exact congrArg (lamVal (mkM P (upd μ f X₂)) _)
        (funext fun x => den_transfer P μ f ar σ hX hf b hb (vcons x ρ))
  | .pi A B, ⟨hA, hB⟩, ρ => by
      show piVal (mkM P (upd μ f X₁)) (den _ σ ρ A) _ = piVal (mkM P (upd μ f X₂)) (den _ σ ρ A) _
      rw [den_transfer P μ f ar σ hX hf A hA ρ]
      exact congrArg (piVal (mkM P (upd μ f X₂)) _)
        (funext fun x => den_transfer P μ f ar σ hX hf B hB (vcons x ρ))
  | .letE T v b, ⟨hT, hv, hb⟩, ρ => by
      show den _ σ (vcons (den _ σ ρ v) ρ) b = den _ σ (vcons (den _ σ ρ v) ρ) b
      rw [den_transfer P μ f ar σ hX hf v hv ρ]
      exact den_transfer P μ f ar σ hX hf b hb (vcons (den (mkM P (upd μ f X₂)) σ ρ v) ρ)
  | .lit t, _, _ => denLit_transfer P μ f hf t

/-- `TelFits` at tables with den-equal domains agrees. -/
theorem TelFits_den_iff (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (Ds : List (Expr Nat))
    (hden : ∀ e, e ∈ Ds → ∀ ρ,
      den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e) :
    ∀ ρ xs, TelFits (mkM P μ₁) σ Ds ρ xs ↔ TelFits (mkM P μ₂) σ Ds ρ xs := by
  induction Ds with
  | nil => intro ρ xs; cases xs <;> exact Iff.rfl
  | cons A rest ih =>
      intro ρ xs
      cases xs with
      | nil => exact Iff.rfl
      | cons x xs' =>
          show (x ∈ Ed _ (den _ σ ρ A) ∧ TelFits _ σ rest (vcons x ρ) xs') ↔
            (x ∈ Ed _ (den _ σ ρ A) ∧ TelFits _ σ rest (vcons x ρ) xs')
          rw [hden A (List.mem_cons.mpr (Or.inl rfl)) ρ]
          exact and_congr Iff.rfl
            (ih (fun e he => hden e (List.mem_cons.mpr (Or.inr he))) (vcons x ρ) xs')

/-- `FitSetT` at tables with den-equal domains agrees. -/
theorem FitSetT_den_eq (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (k : Nat) (Ds : List (Expr Nat))
    (hden : ∀ e, e ∈ Ds → ∀ ρ,
      den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e) :
    ∀ ρ, FitSetT (mkM P μ₁) W4 k σ Ds ρ = FitSetT (mkM P μ₂) W4 k σ Ds ρ := by
  induction Ds with
  | nil => intro ρ; rfl
  | cons A rest ih =>
      intro ρ
      show sUnion (sImage _ (truncW _ W4 k (Ed _ (den _ σ ρ A)))) =
        sUnion (sImage _ (truncW _ W4 k (Ed _ (den _ σ ρ A))))
      rw [hden A (List.mem_cons.mpr (Or.inl rfl)) ρ,
        Ed_dec_eq P μ₁ μ₂, truncW_dec_eq P μ₁ μ₂]
      exact congrArg sUnion
        (congrArg (fun F => sImage F _)
          (funext fun x => congrArg (fun T => sImage (fun t => ordPair x t) T)
            (ih (fun e he => hden e (List.mem_cons.mpr (Or.inr he))) (vcons x ρ))))

/-- `BoundT` at tables with den-equal field domains agrees. -/
theorem BoundT_den_eq (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (k : Nat) (cs : List (List (Expr Nat) × List (Expr Nat)))
    (hden : ∀ c, c ∈ cs → ∀ e, e ∈ c.1 → ∀ ρ,
      den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e) :
    ∀ ρp, BoundT (mkM P μ₁) W4 k σ ρp 0 cs = BoundT (mkM P μ₂) W4 k σ ρp 0 cs := by
  intro ρp
  suffices ∀ j, BoundT (mkM P μ₁) W4 k σ ρp j cs =
    BoundT (mkM P μ₂) W4 k σ ρp j cs from this 0
  induction cs with
  | nil => intro j; rfl
  | cons c rest ih =>
      intro j
      show sUnion (pair (sImage (dataOfTup j) (FitSetT _ W4 k σ c.1 ρp)) _) =
        sUnion (pair (sImage (dataOfTup j) (FitSetT _ W4 k σ c.1 ρp)) _)
      rw [FitSetT_den_eq P μ₁ μ₂ σ k c.1
        (fun e he => hden c (List.mem_cons.mpr (Or.inl rfl)) e he) ρp]
      exact congrArg sUnion
        (congrArg (pair (sImage (dataOfTup j)
            (FitSetT (mkM P μ₂) W4 k σ c.1 ρp)))
          (ih (fun c' hc => hden c' (List.mem_cons.mpr (Or.inr hc))) (j + 1)))

/-- `CtorFits` at tables with den-equal domains agrees. -/
theorem CtorFits_den_iff (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (cs : List (List (Expr Nat) × List (Expr Nat)))
    (hden : ∀ c, c ∈ cs → (∀ e, e ∈ c.1 → ∀ ρ,
        den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e) ∧
      (∀ e, e ∈ c.2 → ∀ ρ, den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e)) :
    ∀ ρp is j xs,
      CtorFits (mkM P μ₁) σ cs ρp is j xs ↔ CtorFits (mkM P μ₂) σ cs ρp is j xs := by
  intro ρp is j xs
  constructor
  · rintro ⟨c, hc, htf, hle⟩
    have hcm := List.getElem?_mem hc
    exact ⟨c, hc,
      (TelFits_den_iff P μ₁ μ₂ σ c.1 (fun e he => (hden c hcm).1 e he) ρp xs).mp htf,
      (List.map_congr_left (fun e he => (hden c hcm).2 e he (push xs ρp))).symm ▸ hle⟩
  · rintro ⟨c, hc, htf, hle⟩
    have hcm := List.getElem?_mem hc
    exact ⟨c, hc,
      (TelFits_den_iff P μ₁ μ₂ σ c.1 (fun e he => (hden c hcm).1 e he) ρp xs).mpr htf,
      (List.map_congr_left (fun e he => (hden c hcm).2 e he (push xs ρp))) ▸ hle⟩

/-- `famEnd` at tables with den-equal field/result domains agrees. -/
theorem famEnd_den_equiv (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (fd : FamData)
    (hden : ∀ c, c ∈ fd.ctors → (∀ e, e ∈ c.1 → ∀ ρ,
        den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e) ∧
      (∀ e, e ∈ c.2 → ∀ ρ, den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e))
    (ρ : Nat → PSet.{4}) :
    Equiv (famEnd (mkM P μ₁) W4 σ fd ρ) (famEnd (mkM P μ₂) W4 σ fd ρ) := by
  unfold famEnd
  refine cond_congr Iff.rfl (tyv_congr ?_) (tyv_congr ?_)
  · have heq : PropFib (mkM P μ₁) σ fd.ctors (shiftρ fd.indices.length ρ)
        (lastVals fd.indices.length ρ) = PropFib (mkM P μ₂) σ fd.ctors
        (shiftρ fd.indices.length ρ) (lastVals fd.indices.length ρ) :=
      congrArg tv (propext
        (⟨fun ⟨j, xs, h⟩ => ⟨j, xs,
            (CtorFits_den_iff P μ₁ μ₂ σ fd.ctors hden _ _ j xs).mp h⟩,
          fun ⟨j, xs, h⟩ => ⟨j, xs,
            (CtorFits_den_iff P μ₁ μ₂ σ fd.ctors hden _ _ j xs).mpr h⟩⟩ :
          (∃ j xs, CtorFits (mkM P μ₁) σ fd.ctors (shiftρ fd.indices.length ρ)
              (lastVals fd.indices.length ρ) j xs) ↔
            ∃ j xs, CtorFits (mkM P μ₂) σ fd.ctors (shiftρ fd.indices.length ρ)
              (lastVals fd.indices.length ρ) j xs))
    rw [heq]
    exact Equiv.rfl
  · exact sep_congr
      (fun a b hab ⟨j, xs, hcf, he⟩ => ⟨j, xs,
        (CtorFits_den_iff P μ₁ μ₂ σ fd.ctors hden _ _ j xs).mp hcf, hab.symm.trans he⟩)
      (fun a b hab ⟨j, xs, hcf, he⟩ => ⟨j, xs,
        (CtorFits_den_iff P μ₁ μ₂ σ fd.ctors hden _ _ j xs).mpr hcf, hab.symm.trans he⟩)
      (by rw [BoundT_den_eq P μ₁ μ₂ σ (evalTotal σ fd.resLevel) fd.ctors
            (fun c hc e he => (hden c hc).1 e he) (shiftρ fd.indices.length ρ)];
          exact Equiv.rfl)

/-- `famVal` at tables with den-equal telescope and field/result domains agrees. -/
theorem famVal_den_equiv (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (fd : FamData)
    (hdenC : ∀ c, c ∈ fd.ctors → (∀ e, e ∈ c.1 → ∀ ρ,
        den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e) ∧
      (∀ e, e ∈ c.2 → ∀ ρ, den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e))
    (hdenT : ∀ e, e ∈ fd.params ++ fd.indices → ∀ ρ,
      den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e) :
    Equiv (famVal (mkM P μ₁) W4 σ fd) (famVal (mkM P μ₂) W4 σ fd) := by
  show Equiv (piLam (mkM P μ₁) σ (famEnd (mkM P μ₁) W4 σ fd) ρ0 (famType fd))
    (piLam (mkM P μ₂) σ (famEnd (mkM P μ₂) W4 σ fd) ρ0 (famType fd))
  exact piLam_congr_fits₂ (mkM P μ₁) (mkM P μ₂) rfl σ
    (famEnd_resp (mkM P μ₁) W4 σ fd) (famEnd_resp (mkM P μ₂) W4 σ fd)
    (.sort fd.resLevel) (fun A B h => Expr.noConfusion h)
    (fd.params ++ fd.indices) ρ0 (fun ρ A hA => hdenT A hA ρ)
    (fun xs _ => famEnd_den_equiv P μ₁ μ₂ σ fd hdenC (push xs ρ0))

/-- The family value is the same at two `upd`-tables that agree on the family
entry at the canonical instance. -/
theorem famVal_transfer (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    {X₁ X₂ : List Nat → PSet.{4}} (σ : Nat → Nat)
    (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2)
    (hX : X₁ ((canonL ar).map (evalTotal σ)) = X₂ ((canonL ar).map (evalTotal σ))) :
    Equiv (famVal (mkM P (upd μ fd.fref X₁)) W4 σ fd)
      (famVal (mkM P (upd μ fd.fref X₂)) W4 σ fd) :=
  famVal_den_equiv P (upd μ fd.fref X₁) (upd μ fd.fref X₂) σ fd
    (fun c hc => ⟨fun e he ρ => den_transfer P μ fd.fref ar σ hX hf e
        (canonOcc_fieldsClassA (hclsA c hc) e he) ρ,
      fun e he ρ => den_transfer P μ fd.fref ar σ hX hf e
        (canonOcc_of_free (hri c hc e he)) ρ⟩)
    (fun e he ρ => den_transfer P μ fd.fref ar σ hX hf e
      (canonOcc_of_free (hpf e he)) ρ)

end PSet

end Rcic.F3
