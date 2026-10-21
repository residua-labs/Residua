import rcic.RcicNativeTypedModelCovRelCore

/-!
# Both-sided readback expansion for the covariant recursive relation

One compact recursion handles both endpoints and arbitrary readback paths.
The unchanged sort and spine leaves use the landed expansion theorem through
their exact clauses. Only the lambda result requires recursive work.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

private theorem sortClause_expand_red_both (hL : ReadbackLaws E R)
    {Γ : LCtx} {x x' y y' A : Expr Nat}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y')
    (h : SortClauseT R Γ x' y' A) : SortClauseT R Γ x y A := by
  have hs : LRSCoreS R E 0 Γ x' y' A .prop :=
    (lrSCoreS_prop_iff _ _ _ _).mpr h
  exact (lrSCoreS_prop_iff _ _ _ _).mp
    (lrSCoreS_expand_red hL hx .prop (lrSCoreS_expand_red_right hL hy .prop hs))

private theorem spineClause_expand_red_both (hL : ReadbackLaws E R)
    {Γ : LCtx} {x x' y y' A : Expr Nat} {r : Nat} {args : List CptT}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y')
    (h : SpineClauseS R E n Γ x' y' A r args) :
    SpineClauseS R E n Γ x y A r args := by
  have hs : LRSCoreS R E n Γ x' y' A (.spine r args) :=
    (lrSCoreS_spine_iff _ _ _ _ _ _).mpr h
  exact (lrSCoreS_spine_iff _ _ _ _ _ _).mp
    (lrSCoreS_expand_red hL hx (.spine r args)
      (lrSCoreS_expand_red_right hL hy (.spine r args) hs))

/-- Both endpoints absorb entire readback paths. The compact decreases only
at a lambda output; its argument demands retain their original relation. -/
theorem lrSCoreCov_expand_red_both (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {x x' y y' A : Expr Nat}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y') :
    (c : CptT) → LRSCoreCov C R n Γ x' y' A c → LRSCoreCov C R n Γ x y A c
  | .bot, _ => lrSCoreCov_bot C _ _ _ _
  | .prop, h => by
      rw [lrSCoreCov_prop_iff] at h ⊢
      exact sortClause_expand_red_both hL hx hy h
  | .sort, h => by
      rw [lrSCoreCov_sort_iff] at h ⊢
      exact sortClause_expand_red_both hL hx hy h
  | .pi a f, h => by
      rw [LRSCoreCov.eq_def] at h ⊢
      obtain ⟨hA, D, F, D', F', hleft, hright, hrest⟩ := h
      exact ⟨hA, D, F, D', F', redR_trans hx hleft, redR_trans hy hright, hrest⟩
  | .lam f, h => by
      rw [LRSCoreCov.eq_def] at h ⊢
      obtain ⟨D, F, hA, hΓ, hbody⟩ := h
      refine ⟨D, F, hA, hΓ, ?_⟩
      intro s hs N N' hN hN' hc hr
      exact lrSCoreCov_expand_red_both C hL (redR_appHead hL hx)
        (redR_appHead hL hy) s.2 (hbody s hs N N' hN hN' hc hr)
  | .spine r args, h => by
      rw [lrSCoreCov_spine_iff] at h ⊢
      exact spineClause_expand_red_both hL hx hy h
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    (have := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
     have := sizeOfT_snd_lt s
     omega)

theorem lrSCoreCov_expand_red (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {x x' y A : Expr Nat} (hx : RedR R Γ x x')
    (c : CptT) (h : LRSCoreCov C R n Γ x' y A c) :
    LRSCoreCov C R n Γ x y A c :=
  lrSCoreCov_expand_red_both C hL hx (.refl _) c h

theorem lrSCoreCov_expand_red_right (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {x y y' A : Expr Nat} (hy : RedR R Γ y y')
    (c : CptT) (h : LRSCoreCov C R n Γ x y' A c) :
    LRSCoreCov C R n Γ x y A c :=
  lrSCoreCov_expand_red_both C hL (.refl _) hy c h

theorem lrSCoreCov_expand (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {x x' y A : Expr Nat} (hx : R Γ x x')
    (c : CptT) (h : LRSCoreCov C R n Γ x' y A c) :
    LRSCoreCov C R n Γ x y A c :=
  lrSCoreCov_expand_red C hL (redR_single hx) c h

theorem lrSCoreCov_expand_right (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {x y y' A : Expr Nat} (hy : R Γ y y')
    (c : CptT) (h : LRSCoreCov C R n Γ x y' A c) :
    LRSCoreCov C R n Γ x y A c :=
  lrSCoreCov_expand_red_right C hL (redR_single hy) c h

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_EXPANSION_ROOTS
#print axioms lrSCoreCov_expand_red_both
#print axioms lrSCoreCov_expand_red
#print axioms lrSCoreCov_expand_red_right
#print axioms lrSCoreCov_expand
#print axioms lrSCoreCov_expand_right
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_EXPANSION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelAudit
