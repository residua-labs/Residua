import rcic.RcicNativeTypedModelCovRelCore

/-!
# Readback transport of the type index

The recursive compact relation observes its type index only through sort and
Pi head readbacks. Transport preserves every recursive child and every native
premise; it does not change the compact typing or make a model observation.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormReadbackAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open ReadbackCK2Audit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

private theorem cov_type_heads (C : CovTyping E)
    {Γ : LCtx} {x y A A₀ : Expr Nat} {c : CptT}
    (hSort : (∃ l, RedR R Γ A (.sort l)) → ∃ l, RedR R Γ A₀ (.sort l))
    (hSortBack : (∃ l, RedR R Γ A₀ (.sort l)) → ∃ l, RedR R Γ A (.sort l))
    (hPi : ∀ D F, RedR R Γ A (.pi D F) → RedR R Γ A₀ (.pi D F))
    (h : LRSCoreCov C R n Γ x y A c) : LRSCoreCov C R n Γ x y A₀ c := by
  cases c with
  | bot => exact lrSCoreCov_bot C _ _ _ _
  | prop | sort =>
      rw [LRSCoreCov.eq_def] at h ⊢
      exact ⟨hSort h.1, h.2⟩
  | pi a f =>
      rw [LRSCoreCov.eq_def] at h ⊢
      exact ⟨hSort h.1, h.2⟩
  | lam f =>
      rw [LRSCoreCov.eq_def] at h ⊢
      obtain ⟨D, F, hA, hrest⟩ := h
      exact ⟨D, F, hPi D F hA, hrest⟩
  | spine r args =>
      rw [LRSCoreCov.eq_def] at h ⊢
      exact spineClauseS_idx hSort hSortBack h

/-- Exact head-observation inputs for changing the type index. No native
typing, model realization, compact typing inclusion, or recursive relation
agreement is assumed. -/
theorem lrSCoreCov_type_heads_iff (C : CovTyping E)
    {Γ : LCtx} {x y A A₀ : Expr Nat} (c : CptT)
    (hSort : (∃ l, RedR R Γ A (.sort l)) ↔ ∃ l, RedR R Γ A₀ (.sort l))
    (hPi : ∀ D F, RedR R Γ A (.pi D F) ↔ RedR R Γ A₀ (.pi D F)) :
    LRSCoreCov C R n Γ x y A c ↔ LRSCoreCov C R n Γ x y A₀ c := by
  constructor
  · exact cov_type_heads C hSort.mp hSort.mpr (fun D F => (hPi D F).mp)
  · exact cov_type_heads C hSort.mpr hSort.mp (fun D F => (hPi D F).mpr)

private theorem cov_red_to_normal_after (hD : DetR R)
    {Γ : LCtx} {A A₀ : Expr Nat} (hA : RedR R Γ A A₀) :
    ∀ {Z : Expr Nat}, NormalR R Γ Z → RedR R Γ A Z → RedR R Γ A₀ Z := by
  intro Z hn hz
  have hd : DiamondR R := fun Δ _ _ _ h₁ h₂ => Or.inl (hD Δ h₁ h₂)
  obtain ⟨d, hleft, hright⟩ := redR_confluent hd hA hz
  obtain rfl := redR_of_normal hn hright
  exact hleft

/-- Type-index readback invariance from deterministic one-step reduction
and the imported normality laws for sort/Pi heads. The endpoint `A₀` need
not be normal. No native typing, context admission, model observation, or
compact typing inclusion is required. -/
theorem lrSCoreCov_type_readback_iff (C : CovTyping E)
    (hL : ReadbackLaws E R) (hD : DetR R)
    {Γ : LCtx} {x y A A₀ : Expr Nat} (hA : RedR R Γ A A₀) (c : CptT) :
    LRSCoreCov C R n Γ x y A c ↔ LRSCoreCov C R n Γ x y A₀ c := by
  apply lrSCoreCov_type_heads_iff C c
  · constructor
    · rintro ⟨l, hs⟩
      exact ⟨l, cov_red_to_normal_after hD hA (hL.sort_normal Γ l) hs⟩
    · rintro ⟨l, hs⟩
      exact ⟨l, redR_trans hA hs⟩
  · intro D F
    constructor
    · exact cov_red_to_normal_after hD hA (hL.pi_normal Γ D F)
    · exact redR_trans hA

/-- The actual CK2 invariant on every admitted environment and arbitrary
context, terms, and compact. Environment admission supplies the already
proved full-core determinism; it is not a type-normalization assumption. -/
theorem lrSCoreCov_type_readback_iff_ck2 (C : CovTyping E) (hW : EnvWfT E)
    {Γ : LCtx} {x y A A₀ : Expr Nat}
    (hA : RedR (WhStepCK2 E n) Γ A A₀) (c : CptT) :
    LRSCoreCov C (WhStepCK2 E n) n Γ x y A c ↔
      LRSCoreCov C (WhStepCK2 E n) n Γ x y A₀ c :=
  lrSCoreCov_type_readback_iff C (readbackLaws_whStepCK2 E n)
    (detR_whStepCK2 hW) hA c

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_READBACK_ROOTS
#print axioms lrSCoreCov_type_heads_iff
#print axioms lrSCoreCov_type_readback_iff
#print axioms lrSCoreCov_type_readback_iff_ck2
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_READBACK_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormReadbackAudit
