import rcic.RcicNativeTypedModelCovYRealization
import rcic.RcicNativeTypedModelCovYReadback

/-!
# Hereditary environment entries at their actual native lookup types

This new interface changes the environment-entry target, not observations.
Its entries use exactly the same realization as relation escape. The actual
model let-coherence field remains separate and unchanged. In particular
the alias control proves the guard for the ENTIRE extended environment,
including lookup zero's lifted type and every tail entry.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelEscapeAudit TypedModelCovXEnvBoundaryAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit

variable {E : ResolvedEnv} {n : Nat}

/-- Both variable entries and escape use `HereditaryCovRealizationY`.
The context-dependent model is evaluated in the actual source context. -/
def EnvTypedCovYAt (C : CovTyping E) (Q : LCtx → CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (ρ : EnvT) : Prop :=
  (∀ i A, lookupType Γ i = some A → ∀ c, ρ i c →
    HereditaryCovRealizationY C Q R n Γ ρ A c) ∧ CtxEnvM (Q Γ) Γ ρ

/-- Bottom entries require no native type view. The let-coherence premise
is retained explicitly; arbitrary nonempty lets cannot be assumed coherent. -/
theorem envTypedCovYAt_bot (C : CovTyping E) (Q : LCtx → CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (hc : CtxEnvM (Q Γ) Γ EnvT.bot) :
    EnvTypedCovYAt C Q R n Γ EnvT.bot := by
  refine ⟨?_, hc⟩
  intro i A hA c hc
  change c = .bot at hc
  subst c
  exact hereditaryCovRealizationY_bot C Q R n Γ EnvT.bot A

theorem envTypedCovYAt_nil (C : CovTyping E) (Q : LCtx → CtxModelT E)
    (R : Readback) (n : Nat) (ρ : EnvT) : EnvTypedCovYAt C Q R n [] ρ :=
  ⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩

/-- The original Eq context retains its actual coherence evidence. -/
theorem envTypedCovYAt_eqGap_bot (C : CovTyping eqEnvT) (n : Nat) :
    EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n eqGapCtx EnvT.bot :=
  envTypedCovYAt_bot C _ _ n eqGapCtx (envTypedCovAtP_eqGap_bot C n).2

/-- All entries of the extended fixture are actual assumptions. Thus its
let-coherence is proved from the actual lookup function, not erased. -/
theorem ctxEnvM_alias_cons (M : CtxModelT eqEnvT) (ρ : EnvT) (A B : Expr Nat) :
    CtxEnvM M (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ρ := by
  intro i v hv
  cases i with
  | zero => cases hv
  | succ i =>
      cases i with
      | zero => cases hv
      | succ i =>
          cases i with
          | zero => cases hv
          | succ i =>
              cases i with
              | zero => cases hv
              | succ i => simp [lookupValue, eqGapCtx] at hv

/-- The E fixture's non-bottom head entry is now realized at its CK2
readback, while every old tail entry retains its bottom realization. -/
theorem envTypedCovYAt_alias_cons (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (A B : Expr Nat) :
    EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n) n
      (.assumption (eqGapDirectAlias A B) :: eqGapCtx)
      (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot) := by
  refine ⟨?_, ctxEnvM_alias_cons _ _ A B⟩
  intro i T hT c hc
  cases i with
  | zero =>
      change some (lift 0 1 (eqGapDirectAlias A B)) = some T at hT
      cases Option.some.inj hT
      change c ∈ [CptT.pi .bot []] at hc
      obtain rfl := List.mem_singleton.mp hc
      refine ⟨sortCode .zero, hereditaryCovRealizationYAt_sort C n .zero
        (redR_lift_eqGapDirectAlias_cons n (eqGapDirectAlias A B) A B) ?_⟩
      rw [sortCode_zero]
      apply hS
      rw [CTyS]
      exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))
  | succ i =>
      change c = .bot at hc
      subst c
      exact hereditaryCovRealizationY_bot C _ _ n _ _ T

/-- The old E obstruction and the new positive guard coexist at precisely
the same non-bottom valuation. Every native/observation premise is retained. -/
theorem covY_alias_environment_control (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat, ∃ w : Level,
      Nonempty (HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort w)) ∧
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
      EnvTypedCovYAt C (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n) n
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot) ∧
      (¬ EnvTypedCovAtP C
        (ctxModelT_approxTK eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx))
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)) ∧
      (.pi .bot [] : CptT) ≠ .bot := by
  obtain ⟨hW, hΓ, _, A, B, w, hD, hΓ', hN, hm, _, _, hraw, hnb⟩ :=
    covX_alias_raw_extension_counterexample C hS n
  exact ⟨hW, hΓ, envTypedCovYAt_eqGap_bot C n, A, B, w, hD, hΓ', hN, hm,
    envTypedCovYAt_alias_cons C hS n A B, hraw, hnb⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_ENVIRONMENT_ROOTS
#print axioms EnvTypedCovYAt
#print axioms envTypedCovYAt_bot
#print axioms envTypedCovYAt_nil
#print axioms envTypedCovYAt_eqGap_bot
#print axioms ctxEnvM_alias_cons
#print axioms envTypedCovYAt_alias_cons
#print axioms covY_alias_environment_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_ENVIRONMENT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit
