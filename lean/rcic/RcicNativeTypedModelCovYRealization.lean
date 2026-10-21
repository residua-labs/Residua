import rcic.RcicNativeTypedModelCovYCore
import rcic.RcicNativeTypedModelCovXRealization

/-!
# Hereditary realization indexed by the semantic type code

The relation and environment interface use this same realization target.
Its only recursive measure is the final TYPE-code argument, checked in the
separate measure module before the relation or this definition was written.

At every non-bottom Pi action, realization keeps all demanded arguments,
the binder body at the extended valuation, and BOTH native codomain
instances. Coverage is exactly the relation's typed-demand coverage. At a
leaf, the normalized native type observes the exact supplied type code.
There is no existential replacement code inside a leaf and no raw alias
observation requirement. A bottom value needs no native type view.

This definition does not assert global escape. In particular the binder
body and exact leaf observation remain substantive conclusions.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovRelRealizationAudit TypedModelCovXAudit
open TypedModelKAudit TypedModelKControlAudit ReadbackCK2Audit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- The hereditary escape and environment-entry target, at one fixed
semantic type code. Every recursive call decreases that code strictly. -/
def HereditaryCovRealizationYAt (C : CovTyping E) (Q : LCtx → CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) (A : Expr Nat)
    (c a : CptT) : Prop :=
  C.ty c a ∧
  match a with
  | .bot => True
  | .pi d g =>
      c = .bot ∨ ∃ D B : Expr Nat, RedR R Γ A (.pi D B) ∧
        CovYActionCoverage C c d g ∧
        ∀ (ds : List CptT) (out : CptT), CovXCompactAction E c ds out → out ≠ .bot →
        ∀ (row : List CptT × CptT), row ∈ g → CovYSelectedRow C ds out row →
        ∀ (N N' : Expr Nat), HasTyT E n Γ N D → HasTyT E n Γ N' D →
        Nonempty (ConvT E n Γ N N' D) →
        (∀ u ∈ ds, LRSCoreCovY C R n Γ N N' D u d) →
          (∀ u ∈ ds, HereditaryCovRealizationYAt C Q R n Γ ρ D u d) ∧
          HereditaryCovRealizationYAt C Q R n (.assumption D :: Γ)
            (EnvT.cons (demandT ds) ρ) B out row.2 ∧
          HereditaryCovRealizationYAt C Q R n Γ ρ (instantiate0 N B) out row.2 ∧
          HereditaryCovRealizationYAt C Q R n Γ ρ (instantiate0 N' B) out row.2
  | _ => c = .bot ∨ ∃ A₀ : Expr Nat,
      RedR R Γ A A₀ ∧ NormalR R Γ A₀ ∧ (Q Γ).Ap ρ A₀ a
termination_by sizeOf a
decreasing_by
  all_goals first
    | exact covY_sizeOf_domain_lt _ _
    | exact covY_sizeOf_selected_codomain_lt ‹row ∈ g›

/-- The wrapper stores an actual type-code witness; no code coherence or
PER across two different witnesses is asserted. -/
def HereditaryCovRealizationY (C : CovTyping E) (Q : LCtx → CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c : CptT) : Prop :=
  ∃ a : CptT, HereditaryCovRealizationYAt C Q R n Γ ρ A c a

theorem hereditaryCovRealizationYAt_typing (C : CovTyping E) (Q : LCtx → CtxModelT E)
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c a : CptT}
    (h : HereditaryCovRealizationYAt C Q R n Γ ρ A c a) : C.ty c a := by
  rw [HereditaryCovRealizationYAt.eq_def] at h
  exact h.1

/-- Bottom is realized independently of a global normalization theorem. -/
theorem hereditaryCovRealizationYAt_bot (C : CovTyping E) (Q : LCtx → CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (a : CptT) :
    HereditaryCovRealizationYAt C Q R n Γ ρ A .bot a := by
  rw [HereditaryCovRealizationYAt.eq_def]
  refine ⟨C.bot a, ?_⟩
  cases a with
  | bot => trivial
  | pi d g => exact Or.inl rfl
  | prop => exact Or.inl rfl
  | sort => exact Or.inl rfl
  | lam g => exact Or.inl rfl
  | spine r args => exact Or.inl rfl

theorem hereditaryCovRealizationY_bot (C : CovTyping E) (Q : LCtx → CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) :
    HereditaryCovRealizationY C Q R n Γ ρ A .bot :=
  ⟨.bot, hereditaryCovRealizationYAt_bot C Q R n Γ ρ A .bot⟩

/-- Exact normal-form observation supplies a non-Pi type-code leaf. -/
theorem hereditaryCovRealizationYAt_leaf (C : CovTyping E) (Q : LCtx → CtxModelT E)
    {Γ : LCtx} {ρ : EnvT} {A A₀ : Expr Nat} {c a : CptT}
    (hnot : ∀ d g, a ≠ .pi d g) (ht : C.ty c a)
    (hr : RedR R Γ A A₀) (hn : NormalR R Γ A₀) (ho : (Q Γ).Ap ρ A₀ a) :
    HereditaryCovRealizationYAt C Q R n Γ ρ A c a := by
  rw [HereditaryCovRealizationYAt.eq_def]
  refine ⟨ht, ?_⟩
  cases a with
  | bot => trivial
  | pi d g => exact (hnot d g rfl).elim
  | prop => exact Or.inr ⟨A₀, hr, hn, ho⟩
  | sort => exact Or.inr ⟨A₀, hr, hn, ho⟩
  | lam g => exact Or.inr ⟨A₀, hr, hn, ho⟩
  | spine r args => exact Or.inr ⟨A₀, hr, hn, ho⟩

/-- A normalized sort observes its exact code in the unchanged guarded
model, at every frozen native context and valuation. -/
theorem hereditaryCovRealizationYAt_sort (C : CovTyping E) (n : Nat)
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT} (l : Level)
    (hr : RedR (WhStepCK2 E n) Γ A (.sort l)) (ht : C.ty c (sortCode l)) :
    HereditaryCovRealizationYAt C (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ A c (sortCode l) := by
  apply hereditaryCovRealizationYAt_leaf C (ctxModelT_approxTK E n) ?_ ht hr
    (normalR_sortCK2 Γ l) (approxTK_sort_code E n Γ ρ l)
  intro d g he
  rcases sortCode_prop_or_sort l with hp | hs
  · rw [hp] at he
    cases he
  · rw [hs] at he
    cases he

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_REALIZATION_ROOTS
#print axioms HereditaryCovRealizationYAt
#print axioms HereditaryCovRealizationY
#print axioms hereditaryCovRealizationYAt_typing
#print axioms hereditaryCovRealizationYAt_bot
#print axioms hereditaryCovRealizationY_bot
#print axioms hereditaryCovRealizationYAt_leaf
#print axioms hereditaryCovRealizationYAt_sort
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_REALIZATION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit
