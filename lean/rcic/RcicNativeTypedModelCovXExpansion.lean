import rcic.RcicNativeTypedModelCovXCore
import rcic.RcicNativeTypedModelCovXEta

/-!
# Readback expansion and eta at explicit Pi views

The eta edge is constructed from the actual beta readback after application.
It holds at every compact for which the function relation is supplied. This
is a relation theorem; a Fundamental supplier must additionally provide that
function relation for every compact observed on either conversion endpoint.
In particular no model eta-contraction law is silently assumed.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovXEtaAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- Both endpoint readback paths preserve the finite-view relation. Each Pi
recursive use descends into its actual instantiated-codomain view. -/
theorem lrSCoreCovXAt_expand_red_both (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {A : Expr Nat} (view : CovXTypeView E R n Γ A)
    {x x' y y' : Expr Nat} {c : CptT}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y')
    (h : LRSCoreCovXAt C view x' y' c) : LRSCoreCovXAt C view x y c := by
  induction view generalizing x x' y y' c with
  | sort l read =>
      exact ⟨h.1, lrSCoreCov_expand_red_both C hL hx hy c h.2⟩
  | base Z read normal hns hnp =>
      exact lrSCoreCov_expand_red_both C hL hx hy c h
  | pi D B read dom body cod ihdom ihbody ihcod =>
      refine ⟨h.1, ?_⟩
      intro ds out action N N' hN hN' hc hd
      obtain ⟨first, second⟩ := h.2 ds out action N N' hN hN' hc hd
      exact ⟨ihcod N hN (redR_appHead hL hx) (redR_appHead hL hy) first,
        ihcod N' hN' (redR_appHead hL hx) (redR_appHead hL hy) second⟩

theorem lrSCoreCovXAt_expand_red (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {A : Expr Nat} (view : CovXTypeView E R n Γ A)
    {x x' y : Expr Nat} {c : CptT} (hx : RedR R Γ x x')
    (h : LRSCoreCovXAt C view x' y c) : LRSCoreCovXAt C view x y c :=
  lrSCoreCovXAt_expand_red_both C hL view hx (.refl _) h

theorem lrSCoreCovXAt_expand_red_right (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {A : Expr Nat} (view : CovXTypeView E R n Γ A)
    {x y y' : Expr Nat} {c : CptT} (hy : RedR R Γ y y')
    (h : LRSCoreCovXAt C view x y' c) : LRSCoreCovXAt C view x y c :=
  lrSCoreCovXAt_expand_red_both C hL view (.refl _) hy h

/-- Eta of the left endpoint at any actual Pi view. No endpoint head test,
type-observation transport or PER premise occurs. -/
theorem lrSCoreCovXAt_eta_left (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {A D B : Expr Nat} (read : RedR R Γ A (.pi D B))
    (dom : CovXTypeView E R n Γ D)
    (body : CovXTypeView E R n (.assumption D :: Γ) B)
    (cod : ∀ N, HasTyT E n Γ N D → CovXTypeView E R n Γ (instantiate0 N B))
    {f g : Expr Nat} {c : CptT}
    (h : LRSCoreCovXAt C (.pi D B read dom body cod) f g c) :
    LRSCoreCovXAt C (.pi D B read dom body cod)
      (.lam D (.app (lift 0 1 f) (.bvar 0))) g c := by
  refine ⟨h.1, ?_⟩
  intro ds out action N N' hN hN' hc hd
  obtain ⟨first, second⟩ := h.2 ds out action N N' hN hN' hc hd
  exact ⟨lrSCoreCovXAt_expand_red C hL (cod N hN)
      (covX_eta_app_readback hL Γ D f N) first,
    lrSCoreCovXAt_expand_red C hL (cod N' hN')
      (covX_eta_app_readback hL Γ D f N) second⟩

/-- The right eta edge is independently obtained from beta expansion. -/
theorem lrSCoreCovXAt_eta_right (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {A D B : Expr Nat} (read : RedR R Γ A (.pi D B))
    (dom : CovXTypeView E R n Γ D)
    (body : CovXTypeView E R n (.assumption D :: Γ) B)
    (cod : ∀ N, HasTyT E n Γ N D → CovXTypeView E R n Γ (instantiate0 N B))
    {f g : Expr Nat} {c : CptT}
    (h : LRSCoreCovXAt C (.pi D B read dom body cod) f g c) :
    LRSCoreCovXAt C (.pi D B read dom body cod)
      f (.lam D (.app (lift 0 1 g) (.bvar 0))) c := by
  refine ⟨h.1, ?_⟩
  intro ds out action N N' hN hN' hc hd
  obtain ⟨first, second⟩ := h.2 ds out action N N' hN hN' hc hd
  exact ⟨lrSCoreCovXAt_expand_red_right C hL (cod N hN)
      (covX_eta_app_readback hL Γ D g N') first,
    lrSCoreCovXAt_expand_red_right C hL (cod N' hN')
      (covX_eta_app_readback hL Γ D g N') second⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_EXPANSION_ROOTS
#print axioms lrSCoreCovXAt_expand_red_both
#print axioms lrSCoreCovXAt_expand_red
#print axioms lrSCoreCovXAt_expand_red_right
#print axioms lrSCoreCovXAt_eta_left
#print axioms lrSCoreCovXAt_eta_right
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_EXPANSION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXAudit
