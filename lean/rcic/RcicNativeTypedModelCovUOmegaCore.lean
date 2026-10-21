import rcic.RcicNativeTypedModelCovTStage
import rcic.RcicSubstTTyped
import rcic.RcicTypedWeaken

/-!
# Native self-application and the deterministic self-step obstruction

These are compositional helpers. The typing lemma explicitly consumes a
cyclic native type conversion; it does not supply that conversion or assert
that every type has it. The readback lemma composes a supplied self-step with
landed CK2 determinism. Concrete admitted witnesses must discharge all of
these premises before a boundary is claimed. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit ReadbackCK2Audit

def covUOmegaDelta (X : Expr Nat) : Expr Nat :=
  .lam X (.app (.bvar 0) (.bvar 0))

def covUOmega (X : Expr Nat) : Expr Nat :=
  .app (covUOmegaDelta X) (covUOmegaDelta X)

/-- Closed cyclic proposition types support the usual typed self-application.
The displayed cycle is an input, and is not inferred from a model candidate. -/
def covUOmega_hasTy_of_cycle {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {X P : Expr Nat} (hW : EnvWfT E)
    (hXlift : ∀ k, lift k 1 X = X) (hPlift : ∀ k, lift k 1 P = P)
    (hX : HasTyT E n Γ X (.sort .zero))
    (hc : ConvT E n Γ X (.pi X P) (.sort .zero)) :
    HasTyT E n Γ (covUOmega X) P := by
  have hi (a : Expr Nat) : instantiate0 a P = P :=
    (substT_cons_id a P).symm.trans (substT_closed hPlift _)
  have hv : HasTyT E n (.assumption X :: Γ) (.bvar 0) X := by
    have hh : HasTyT E n (.assumption X :: Γ) (.bvar 0) (lift 0 1 X) :=
      .bvar _ 0 _ rfl
    simpa only [hXlift] using hh
  have hwc : ConvT E n (.assumption X :: Γ) X (.pi X P) (.sort .zero) := by
    have hh := convTWeaken (.assumption X) (envClosed_of_envWfT hW) (c := 0) hc
    simpa only [insertAt_zero, lift, hXlift, hPlift] using hh
  have hvf : HasTyT E n (.assumption X :: Γ) (.bvar 0) (.pi X P) :=
    .conv _ _ _ _ .zero hv hwc
  have hb : HasTyT E n (.assumption X :: Γ) (.app (.bvar 0) (.bvar 0)) P := by
    have hh := HasTyT.app _ _ _ _ _ hvf hv
    simpa only [hi] using hh
  have hd : HasTyT E n Γ (covUOmegaDelta X) (.pi X P) :=
    .lam Γ X .zero _ P hX hb
  have hdx : HasTyT E n Γ (covUOmegaDelta X) X :=
    .conv _ _ _ _ .zero hd (.symm _ _ _ _ hc)
  have hh := HasTyT.app _ _ _ _ _ hd hdx
  simpa only [hi] using hh

theorem covUOmega_self_step (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (X : Expr Nat) :
    WhStepCK2 E n Γ (covUOmega X) (covUOmega X) :=
  .ctx (.beta X (.app (.bvar 0) (.bvar 0)) (covUOmegaDelta X))

/-- In a deterministic readback, every finite reduct of a self-step source
is that source. This proof recurses on the finite reduction derivation. -/
theorem covU_redR_of_self_step {R : Readback} (hdet : DetR R) {Γ : LCtx}
    {a b : Expr Nat} (hr : RedR R Γ a b) : R Γ a a → b = a := by
  induction hr with
  | refl => intro _; rfl
  | @step a b c hab _ ih =>
      intro hs
      have he : a = b := hdet Γ hs hab
      subst b
      exact ih hs

/-- A supplied CK2 self-step in an admitted environment rules out every
native normal readback. It is stronger than a literal-sort mismatch. -/
theorem covU_no_normal_readback_of_self_step {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a : Expr Nat} (hW : EnvWfT E)
    (hs : WhStepCK2 E n Γ a a) :
    ¬ ∃ b, RedR (WhStepCK2 E n) Γ a b ∧ NormalR (WhStepCK2 E n) Γ b := by
  rintro ⟨b, hr, hn⟩
  have he := covU_redR_of_self_step (detR_whStepCK2 hW) hr hs
  subst b
  exact hn a hs

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_U_OMEGA_CORE_ROOTS
#print axioms covUOmegaDelta
#print axioms covUOmega
#print axioms covUOmega_hasTy_of_cycle
#print axioms covUOmega_self_step
#print axioms covU_redR_of_self_step
#print axioms covU_no_normal_readback_of_self_step
-- END RCIC_NATIVE_TYPED_MODEL_COV_U_OMEGA_CORE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit
