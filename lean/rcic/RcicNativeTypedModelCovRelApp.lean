import rcic.RcicNativeTypedModelCovRelCore

/-!
# Application consumes the new recursive lambda clause

At a syntactic native Pi index, the imported Pi readback law identifies the
domain and codomain stored in the lambda clause. Its actual recursive action
then supplies the application result. No Fundamental or model conclusion is
assumed. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- The genuine lambda action of `LRSCoreCov`, at its declared Pi index. -/
theorem lrSCoreCov_app (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {f f' A B x y : Expr Nat}
    {g : List (List CptT × CptT)} {s : List CptT × CptT}
    (hf : LRSCoreCov C R n Γ f f' (.pi A B) (.lam g)) (hs : s ∈ g)
    (hx : HasTyT E n Γ x A) (hy : HasTyT E n Γ y A)
    (hxy : Nonempty (ConvT E n Γ x y A))
    (hdemand : ∀ u ∈ s.1, LRSCoreCov C R n Γ x y A u) :
    LRSCoreCov C R n Γ (.app f x) (.app f' y) (instantiate0 x B) s.2 := by
  rw [LRSCoreCov.eq_def] at hf
  obtain ⟨D, F, hpi, _, action⟩ := hf
  obtain ⟨rfl, rfl⟩ := Expr.pi.inj (redR_pi_eq hL hpi)
  exact action s hs x y hx hy hxy hdemand

/-- A common argument needs only its native typing and self-related demands. -/
theorem lrSCoreCov_app_diagonal_arg (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {f f' A B x : Expr Nat}
    {g : List (List CptT × CptT)} {s : List CptT × CptT}
    (hf : LRSCoreCov C R n Γ f f' (.pi A B) (.lam g)) (hs : s ∈ g)
    (hx : HasTyT E n Γ x A)
    (hdemand : ∀ u ∈ s.1, LRSCoreCov C R n Γ x x A u) :
    LRSCoreCov C R n Γ (.app f x) (.app f' x) (instantiate0 x B) s.2 :=
  lrSCoreCov_app C hL hf hs hx hx ⟨.refl _ _ _ hx⟩ hdemand

/-- A self-related function acts on a mixed related argument pair. -/
theorem lrSCoreCov_app_diagonal_head (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {f A B x y : Expr Nat}
    {g : List (List CptT × CptT)} {s : List CptT × CptT}
    (hf : LRSCoreCov C R n Γ f f (.pi A B) (.lam g)) (hs : s ∈ g)
    (hx : HasTyT E n Γ x A) (hy : HasTyT E n Γ y A)
    (hxy : Nonempty (ConvT E n Γ x y A))
    (hdemand : ∀ u ∈ s.1, LRSCoreCov C R n Γ x y A u) :
    LRSCoreCov C R n Γ (.app f x) (.app f y) (instantiate0 x B) s.2 :=
  lrSCoreCov_app C hL hf hs hx hy hxy hdemand

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_APP_ROOTS
#print axioms lrSCoreCov_app
#print axioms lrSCoreCov_app_diagonal_arg
#print axioms lrSCoreCov_app_diagonal_head
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_APP_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelAudit
