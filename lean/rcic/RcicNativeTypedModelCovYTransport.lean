import rcic.RcicNativeTypedModelCovYCore

/-!
# Readback transport at a fixed semantic type code

Type reindexing preserves the compact code literally. Endpoint expansion
recurses only to selected codomain codes, with the checked strict decrease.
There is no model expansion premise and no global native type view.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovNormReadbackAudit TypedModelCovXAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

theorem lrSCoreCovY_type_heads_iff (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {A A₀ x y : Expr Nat}
    (h : CovXNormalHeadAgreement R Γ A A₀) (c a : CptT) :
    LRSCoreCovY C R n Γ x y A c a ↔ LRSCoreCovY C R n Γ x y A₀ c a := by
  have hs : (∃ l, RedR R Γ A (.sort l)) ↔ ∃ l, RedR R Γ A₀ (.sort l) := by
    constructor
    · rintro ⟨l, hl⟩
      exact ⟨l, (h _ (hL.sort_normal Γ l)).mp hl⟩
    · rintro ⟨l, hl⟩
      exact ⟨l, (h _ (hL.sort_normal Γ l)).mpr hl⟩
  have old := lrSCoreCov_type_heads_iff (n := n) (x := x) (y := y) C c hs
    (fun D B => h _ (hL.pi_normal Γ D B))
  cases a with
  | bot =>
      constructor <;> intro he <;> rw [LRSCoreCovY.eq_def] at he ⊢ <;> exact he
  | pi d g =>
      constructor
      · intro he
        rw [lrSCoreCovY_pi_iff] at he ⊢
        refine ⟨he.1, ?_⟩
        rcases he.2 with hb | ⟨D, B, hr, hc, ha⟩
        · exact Or.inl hb
        · exact Or.inr ⟨D, B, (h _ (hL.pi_normal Γ D B)).mp hr, hc, ha⟩
      · intro he
        rw [lrSCoreCovY_pi_iff] at he ⊢
        refine ⟨he.1, ?_⟩
        rcases he.2 with hb | ⟨D, B, hr, hc, ha⟩
        · exact Or.inl hb
        · exact Or.inr ⟨D, B, (h _ (hL.pi_normal Γ D B)).mpr hr, hc, ha⟩
  | prop | sort | lam _ | spine _ _ =>
      constructor
      · intro he
        rw [LRSCoreCovY.eq_def] at he ⊢
        exact ⟨he.1, old.mp he.2⟩
      · intro he
        rw [LRSCoreCovY.eq_def] at he ⊢
        exact ⟨he.1, old.mpr he.2⟩

theorem lrSCoreCovY_type_readback_iff (C : CovTyping E) (hL : ReadbackLaws E R)
    (hD : DetR R) {Γ : LCtx} {A A₀ x y : Expr Nat}
    (h : RedR R Γ A A₀) (c a : CptT) :
    LRSCoreCovY C R n Γ x y A c a ↔ LRSCoreCovY C R n Γ x y A₀ c a :=
  lrSCoreCovY_type_heads_iff C hL (covXNormalHeadAgreement_of_red hD h) c a

/-- All recursive calls below use the selected type row's codomain code.
The term compact may grow under application without affecting this measure. -/
theorem lrSCoreCovY_expand_red_both (C : CovTyping E) (hL : ReadbackLaws E R)
    (a : CptT) {Γ : LCtx} {x x' y y' A : Expr Nat} {c : CptT}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y')
    (h : LRSCoreCovY C R n Γ x' y' A c a) :
    LRSCoreCovY C R n Γ x y A c a := by
  cases a with
  | bot =>
      rw [LRSCoreCovY.eq_def] at h ⊢
      exact h
  | pi d g =>
      rw [lrSCoreCovY_pi_iff] at h ⊢
      refine ⟨h.1, ?_⟩
      rcases h.2 with hb | ⟨D, B, hr, hc, ha⟩
      · exact Or.inl hb
      · refine Or.inr ⟨D, B, hr, hc, ?_⟩
        intro ds out hact row hrow hsel N N' hN hN' hconv hdem
        obtain ⟨ho, ho'⟩ := ha ds out hact row hrow hsel N N' hN hN' hconv hdem
        exact ⟨lrSCoreCovY_expand_red_both C hL row.2
            (redR_appHead hL hx) (redR_appHead hL hy) ho,
          lrSCoreCovY_expand_red_both C hL row.2
            (redR_appHead hL hx) (redR_appHead hL hy) ho'⟩
  | prop | sort | lam _ | spine _ _ =>
      rw [LRSCoreCovY.eq_def] at h ⊢
      exact ⟨h.1, lrSCoreCov_expand_red_both C hL hx hy c h.2⟩
termination_by sizeOf a
decreasing_by
  all_goals subst a
  all_goals exact covY_sizeOf_selected_codomain_lt hrow

theorem lrSCoreCovY_expand_red (C : CovTyping E) (hL : ReadbackLaws E R)
    (a : CptT) {Γ : LCtx} {x x' y A : Expr Nat} {c : CptT}
    (hx : RedR R Γ x x') (h : LRSCoreCovY C R n Γ x' y A c a) :
    LRSCoreCovY C R n Γ x y A c a :=
  lrSCoreCovY_expand_red_both C hL a hx (.refl _) h

theorem lrSCoreCovY_expand_red_right (C : CovTyping E) (hL : ReadbackLaws E R)
    (a : CptT) {Γ : LCtx} {x y y' A : Expr Nat} {c : CptT}
    (hy : RedR R Γ y y') (h : LRSCoreCovY C R n Γ x y' A c a) :
    LRSCoreCovY C R n Γ x y A c a :=
  lrSCoreCovY_expand_red_both C hL a (.refl _) hy h

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_TRANSPORT_ROOTS
#print axioms lrSCoreCovY_type_heads_iff
#print axioms lrSCoreCovY_type_readback_iff
#print axioms lrSCoreCovY_expand_red_both
#print axioms lrSCoreCovY_expand_red
#print axioms lrSCoreCovY_expand_red_right
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_TRANSPORT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit
