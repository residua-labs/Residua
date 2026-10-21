import rcic.RcicNativePiModelBetaObstruction
import rcic.RcicNativeTypedModelCovPIdentity

/-!
# Type readback does not decrease raw syntax size

The landed dependent-beta fixture supplies a closed Pi type X. A new
type-level beta redex duplicates X into the domain and codomain of an
arrow. Both endpoints are natively typed in Sort 1 in the admitted empty
environment and empty context. The actual CK2 head step reaches a normal
Pi whose raw syntax is larger than the source.

This refutes the displayed raw-size descent obligations only. It neither
refutes normalization nor rules out a different well-founded measure.
In particular, the Abel--Coquand pin's prose composition note is not used
as a kernel certificate for a CK2 cycle. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelBetaObstructionAudit ReadbackCK2Audit

/-- Reuse the closed Pi target of the landed beta counterexample. -/
def covRReadbackArgument : Expr Nat := betaTarget

def covRReadbackSource : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) betaBody) covRReadbackArgument

def covRReadbackTarget : Expr Nat :=
  .pi covRReadbackArgument covRReadbackArgument

/-- Only the native universe is normalized; the landed argument typing
itself is reused unchanged. -/
def covRReadbackArgument_hasTy :
    HasTyT emptyEnv 0 [] covRReadbackArgument (.sort (.succ .zero)) :=
  .conv [] covRReadbackArgument (.sort betaResultLevel) (.sort (.succ .zero))
    (.succ betaResultLevel) betaTargetTyping
    (.sorts [] betaResultLevel (.succ .zero) (fun _ => rfl))

/-- The duplicating type expression is typed under its actual Sort 1
binder. Its two occurrences refer to the same native type variable. -/
def covRReadbackBody_hasTy :
    HasTyT emptyEnv 0 [.assumption (.sort (.succ .zero))] betaBody
      (.sort (.succ .zero)) :=
  .conv _ betaBody (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.succ .zero)) (.succ (.imax (.succ .zero) (.succ .zero)))
    (.pi _ (.bvar 0) (.succ .zero) (.bvar 1) (.succ .zero)
      (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl))
    (.sorts _ (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun _ => rfl))

def covRReadbackSource_hasTy :
    HasTyT emptyEnv 0 [] covRReadbackSource (.sort (.succ .zero)) :=
  .app [] (.lam (.sort (.succ .zero)) betaBody) covRReadbackArgument
    (.sort (.succ .zero)) (.sort (.succ .zero))
    (.lam [] (.sort (.succ .zero)) (.succ (.succ .zero)) betaBody
      (.sort (.succ .zero)) (.sort [] (.succ .zero)) covRReadbackBody_hasTy)
    covRReadbackArgument_hasTy

def covRReadbackTarget_hasTy :
    HasTyT emptyEnv 0 [] covRReadbackTarget (.sort (.succ .zero)) := by
  have hw : HasTyT emptyEnv 0 [.assumption covRReadbackArgument]
      covRReadbackArgument (.sort (.succ .zero)) := by
    simpa [covRReadbackArgument, betaTarget, betaArgument,
      NativePiHeadObs.betaPiHead, lift, insertAt] using
      (hasTyTWeaken (.assumption covRReadbackArgument)
        (envClosed_of_envWfT (E := emptyEnv) .empty) (c := 0)
        covRReadbackArgument_hasTy)
  exact .conv [] covRReadbackTarget (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.succ .zero)) (.succ (.imax (.succ .zero) (.succ .zero)))
    (.pi [] covRReadbackArgument (.succ .zero) covRReadbackArgument (.succ .zero)
      covRReadbackArgument_hasTy hw)
    (.sorts [] (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun _ => rfl))

theorem covRReadback_substitution :
    instantiate0 covRReadbackArgument betaBody = covRReadbackTarget := rfl

/-- The original native conversion is one actual beta constructor. -/
def covRReadback_native_beta :
    ConvT emptyEnv 0 [] covRReadbackSource covRReadbackTarget
      (.sort (.succ .zero)) :=
  .beta [] (.sort (.succ .zero)) betaBody covRReadbackArgument
    (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort [] (.succ .zero)) covRReadbackBody_hasTy covRReadbackArgument_hasTy

theorem covRReadback_ck2_step :
    WhStepCK2 emptyEnv 0 [] covRReadbackSource covRReadbackTarget :=
  (readbackLaws_whStepCK2 emptyEnv 0).beta [] (.sort (.succ .zero))
    betaBody covRReadbackArgument

theorem covRReadback_ck2_readback :
    RedR (WhStepCK2 emptyEnv 0) [] covRReadbackSource covRReadbackTarget :=
  redR_single covRReadback_ck2_step

theorem covRReadback_target_normal :
    NormalR (WhStepCK2 emptyEnv 0) [] covRReadbackTarget :=
  normalR_piCK2 [] covRReadbackArgument covRReadbackArgument

theorem covRReadback_size_grows :
    sizeOf covRReadbackSource < sizeOf covRReadbackTarget := by decide

theorem covRReadback_source_ne_target : covRReadbackSource ≠ covRReadbackTarget :=
  fun h => Expr.noConfusion h

/-- Every native and readback premise used by the negative tests below
has an actual inhabitant, including normality of the readback result. -/
theorem covRReadback_control :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv 0 []) ∧
    Nonempty (HasTyT emptyEnv 0 [] covRReadbackSource (.sort (.succ .zero))) ∧
    Nonempty (HasTyT emptyEnv 0 [] covRReadbackTarget (.sort (.succ .zero))) ∧
    Nonempty (ConvT emptyEnv 0 [] covRReadbackSource covRReadbackTarget
      (.sort (.succ .zero))) ∧
    WhStepCK2 emptyEnv 0 [] covRReadbackSource covRReadbackTarget ∧
    RedR (WhStepCK2 emptyEnv 0) [] covRReadbackSource covRReadbackTarget ∧
    NormalR (WhStepCK2 emptyEnv 0) [] covRReadbackTarget ∧
    covRReadbackSource ≠ covRReadbackTarget ∧
    sizeOf covRReadbackSource < sizeOf covRReadbackTarget :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨covRReadbackSource_hasTy⟩, ⟨covRReadbackTarget_hasTy⟩,
    ⟨covRReadback_native_beta⟩, covRReadback_ck2_step, covRReadback_ck2_readback,
    covRReadback_target_normal, covRReadback_source_ne_target, covRReadback_size_grows⟩

/-- A typed CK2 step is not a strict descent in raw type syntax. This
statement is refuted at a proper beta edge, not a reflexive trace. -/
theorem covR_not_raw_type_step_size_descent :
    ¬ (∀ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A A' : Expr Nat) (u : Level),
      EnvWfT E → CtxWfT E n Γ →
      HasTyT E n Γ A (.sort u) → HasTyT E n Γ A' (.sort u) →
      WhStepCK2 E n Γ A A' → sizeOf A' < sizeOf A) := by
  intro h
  have hlt := h emptyEnv 0 [] covRReadbackSource covRReadbackTarget (.succ .zero)
    .empty .nil covRReadbackSource_hasTy covRReadbackTarget_hasTy covRReadback_ck2_step
  have hg := covRReadback_size_grows
  omega

/-- Requiring an actual normal readback does not repair raw-size descent.
Both endpoints are natively sorted and the source differs from the result.
This theorem makes no assertion about existence of normal readbacks. -/
theorem covR_not_normal_type_readback_size_descent :
    ¬ (∀ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A A' : Expr Nat) (u : Level),
      EnvWfT E → CtxWfT E n Γ →
      HasTyT E n Γ A (.sort u) → HasTyT E n Γ A' (.sort u) →
      A ≠ A' → RedR (WhStepCK2 E n) Γ A A' → NormalR (WhStepCK2 E n) Γ A' →
      sizeOf A' < sizeOf A) := by
  intro h
  have hlt := h emptyEnv 0 [] covRReadbackSource covRReadbackTarget (.succ .zero)
    .empty .nil covRReadbackSource_hasTy covRReadbackTarget_hasTy
    covRReadback_source_ne_target covRReadback_ck2_readback covRReadback_target_normal
  have hg := covRReadback_size_grows
  omega

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_READBACK_ROOTS
#print axioms covRReadbackArgument
#print axioms covRReadbackSource
#print axioms covRReadbackTarget
#print axioms covRReadbackArgument_hasTy
#print axioms covRReadbackBody_hasTy
#print axioms covRReadbackSource_hasTy
#print axioms covRReadbackTarget_hasTy
#print axioms covRReadback_substitution
#print axioms covRReadback_native_beta
#print axioms covRReadback_ck2_step
#print axioms covRReadback_ck2_readback
#print axioms covRReadback_target_normal
#print axioms covRReadback_size_grows
#print axioms covRReadback_source_ne_target
#print axioms covRReadback_control
#print axioms covR_not_raw_type_step_size_descent
#print axioms covR_not_normal_type_readback_size_descent
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_READBACK_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
