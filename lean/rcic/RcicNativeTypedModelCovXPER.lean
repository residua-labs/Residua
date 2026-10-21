import rcic.RcicNativeTypedModelCovXCore

/-!
# Fixed-view PER for the extensional Pi experiment

The Pi proof recurses only into actual domain/codomain children. It uses both
codomain conjuncts explicitly: symmetry exchanges them, and transitivity uses
the left argument for the first composite and the right for the second.
No observation of an intermediate term or type is requested.

The inherited universe payload consumes the existing native/PER premises.
Those premises remain visible; this module is not a new supplier for them.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

def CovXFixedPER (C : CovTyping E) {Γ : LCtx} {A : Expr Nat}
    (view : CovXTypeView E R n Γ A) : Prop :=
  ∀ c, (∀ x y, LRSCoreCovXAt C view x y c → LRSCoreCovXAt C view y x c) ∧
    (∀ x y z, LRSCoreCovXAt C view x y c → LRSCoreCovXAt C view y z c →
      LRSCoreCovXAt C view x z c)

private theorem covX_old_sort_per (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat} {l : Level}
    (hA : RedR R Γ A (.sort l)) (c : CptT) :
    (∀ x y, LRSCoreCov C R n Γ x y A c → LRSCoreCov C R n Γ y x A c) ∧
    (∀ x y z, LRSCoreCov C R n Γ x y A c → LRSCoreCov C R n Γ y z A c →
      LRSCoreCov C R n Γ x z A c) := by
  have forward {x y} : LRSCoreCov C R n Γ x y A c →
      LRSCoreCov C R n Γ x y (.sort l) c :=
    lrSCoreCov_sortIdx_irrel C hL hNU ⟨l, hA⟩ ⟨l, .refl _⟩ c
  have back {x y} : LRSCoreCov C R n Γ x y (.sort l) c →
      LRSCoreCov C R n Γ x y A c :=
    lrSCoreCov_sortIdx_irrel C hL hNU ⟨l, .refl _⟩ ⟨l, hA⟩ c
  exact ⟨fun _ _ h => back (lrSCoreCov_symm C hL hNU hW hS hT c hΓ (forward h)),
    fun _ _ _ h₁ h₂ => back
      (lrSCoreCov_trans C hL hNU hW hS hT c hΓ (forward h₁) (forward h₂))⟩

private theorem covX_old_base_per (C : CovTyping E) (hNU : NormalUniqueR R)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A : Expr Nat}
    (hns : ¬ ∃ l, RedR R Γ A (.sort l))
    (hnp : ¬ ∃ D B, RedR R Γ A (.pi D B)) (c : CptT) :
    (∀ x y, LRSCoreCov C R n Γ x y A c → LRSCoreCov C R n Γ y x A c) ∧
    (∀ x y z, LRSCoreCov C R n Γ x y A c → LRSCoreCov C R n Γ y z A c →
      LRSCoreCov C R n Γ x z A c) := by
  cases c with
  | bot => exact ⟨fun _ _ _ => lrSCoreCov_bot C _ _ _ _,
      fun _ _ _ _ _ => lrSCoreCov_bot C _ _ _ _⟩
  | prop | sort | pi a f =>
      constructor
      · intro x y h; rw [LRSCoreCov.eq_def] at h; exact (hns h.1).elim
      · intro x y z h _; rw [LRSCoreCov.eq_def] at h; exact (hns h.1).elim
  | lam f =>
      constructor
      · intro x y h
        rw [LRSCoreCov.eq_def] at h
        obtain ⟨D, B, hr, _⟩ := h
        exact (hnp ⟨D, B, hr⟩).elim
      · intro x y z h _
        rw [LRSCoreCov.eq_def] at h
        obtain ⟨D, B, hr, _⟩ := h
        exact (hnp ⟨D, B, hr⟩).elim
  | spine r args =>
      constructor
      · intro x y h
        rw [LRSCoreCov.eq_def] at h ⊢
        exact spineClauseS_symm hS hΓ (fun hs => (hns hs).elim) h
      · intro x y z h₁ h₂
        rw [LRSCoreCov.eq_def] at h₁ h₂ ⊢
        exact spineClauseS_trans hNU hT hΓ h₁ h₂

/-- The full fixed-view PER, uniformly at every compact. The inherited
sort/base clauses are consumed by composition; every new recursive call is
on a domain or instantiated-codomain constructor child. -/
theorem lrSCoreCovXAt_PER (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {A : Expr Nat} (view : CovXTypeView E R n Γ A)
    (hΓ : CtxWfT E n Γ) : CovXFixedPER C view := by
  revert hΓ
  induction view with
  | sort l read =>
      intro hΓ c
      obtain ⟨hs, ht⟩ := covX_old_sort_per C hL hNU hW hS hT hΓ read c
      exact ⟨fun x y h => ⟨h.1, hs x y h.2⟩,
        fun x y z h₁ h₂ => ⟨h₁.1, ht x y z h₁.2 h₂.2⟩⟩
  | base Z read normal hns hnp =>
      intro hΓ c
      exact covX_old_base_per C hNU hS hT hΓ hns hnp c
  | pi D B read dom body cod ihdom ihbody ihcod =>
      intro hΓ c
      constructor
      · intro x y h
        refine ⟨h.1, ?_⟩
        intro ds out action N N' hN hN' hc hd
        obtain ⟨hc⟩ := hc
        have hdrev : ∀ u ∈ ds, LRSCoreCovXAt C dom N' N u :=
          fun u hu => (ihdom hΓ u).1 N N' (hd u hu)
        obtain ⟨first, second⟩ := h.2 ds out action N' N hN' hN
          ⟨.symm _ _ _ _ hc⟩ hdrev
        exact ⟨(ihcod N hN hΓ out).1 _ _ second,
          (ihcod N' hN' hΓ out).1 _ _ first⟩
      · intro x y z hxy hyz
        refine ⟨hxy.1, ?_⟩
        intro ds out action N N' hN hN' hc hd
        have left : ∀ u ∈ ds, LRSCoreCovXAt C dom N N u := by
          intro u hu
          exact (ihdom hΓ u).2 _ _ _ (hd u hu) ((ihdom hΓ u).1 _ _ (hd u hu))
        have right : ∀ u ∈ ds, LRSCoreCovXAt C dom N' N' u := by
          intro u hu
          exact (ihdom hΓ u).2 _ _ _ ((ihdom hΓ u).1 _ _ (hd u hu)) (hd u hu)
        have hxx := hxy.2 ds out action N N hN hN ⟨.refl _ _ _ hN⟩ left
        have hzz := hyz.2 ds out action N' N' hN' hN' ⟨.refl _ _ _ hN'⟩ right
        have hxy' := hxy.2 ds out action N N' hN hN' hc hd
        have hyz' := hyz.2 ds out action N N' hN hN' hc hd
        exact ⟨(ihcod N hN hΓ out).2 _ _ _ hxx.1 hyz'.1,
          (ihcod N' hN' hΓ out).2 _ _ _ hxy'.2 hzz.2⟩

theorem lrSCoreCovXAt_symm (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {A : Expr Nat} (view : CovXTypeView E R n Γ A)
    (hΓ : CtxWfT E n Γ) {x y : Expr Nat} {c : CptT}
    (h : LRSCoreCovXAt C view x y c) : LRSCoreCovXAt C view y x c :=
  (lrSCoreCovXAt_PER C hL hNU hW hS hT view hΓ c).1 x y h

theorem lrSCoreCovXAt_trans (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {A : Expr Nat} (view : CovXTypeView E R n Γ A)
    (hΓ : CtxWfT E n Γ) {x y z : Expr Nat} {c : CptT}
    (hxy : LRSCoreCovXAt C view x y c) (hyz : LRSCoreCovXAt C view y z c) :
    LRSCoreCovXAt C view x z c :=
  (lrSCoreCovXAt_PER C hL hNU hW hS hT view hΓ c).2 x y z hxy hyz

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_PER_ROOTS
#print axioms CovXFixedPER
#print axioms lrSCoreCovXAt_PER
#print axioms lrSCoreCovXAt_symm
#print axioms lrSCoreCovXAt_trans
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_PER_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXAudit
