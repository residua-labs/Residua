import rcic.RcicNativeTypedModelCovWConvHo

/-!
# A closed, typed candidate for the remaining completeness question

The two calls below have the same W recursor, motive, and constructor major.
Their constant minors return `Sort 0` and `Pi (Sort 0) (Sort 0)`, respectively.
Both calls are supplied with native typing at `Sort 1`, and their full public
observations agree: every observation is bottom.

This module does not prove native nonconversion. The final named proposition
records that remaining obligation; no refutation of completeness follows from
the supplied observation equality alone.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWAudit
open TypedModelCovWIrrelAudit TypedModelCovWMatrixAudit
open TypedModelCovWNativeAudit ReadbackCKAudit ReadbackCK2Audit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWConvBohmBody : Expr Nat := .pi (.sort .zero) (.sort .zero)

def covWConvBohmMinor : Expr Nat :=
  .lam covUHoField (.lam covUHoIhTy covWConvBohmBody)

def covWConvBohmPrefix : Expr Nat :=
  foldApps (.const 65 [.succ (.succ .zero)]) [covUHoMotive, covWConvBohmMinor]

def covWConvBohmCall : Expr Nat :=
  .app covWConvBohmPrefix covWMatrixIotaMajor

/-- The replacement body has exactly the old body's native universe. -/
def covWConv_bohm_body_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWConvBohmBody (.sort (.succ .zero)) :=
  .conv _ _ _ _ _
    (.pi Γ (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
      (.sort _ .zero) (.sort _ .zero))
    (.sorts _ (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun _ => rfl))

/-- Extract the actual binder and type-transport evidence from the public
prefix typing, then replace only the innermost constant body. -/
def covWConv_bohm_minor_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWConvBohmMinor
      (instantiate0 covUHoMotive covUHoMinTy) := by
  let hp := hasTyTInv_app (covWNativeHo_prefix_ty n Γ)
    (show covWNativeHoPrefix =
      .app (.app (.const 65 [.succ (.succ .zero)]) covUHoMotive) covUHoMinor from rfl)
  let ho := hasTyTInv_lam hp.2.2.2.1
    (show covUHoMinor = .lam covUHoField (.lam covUHoIhTy (.sort .zero)) from rfl)
  let hi := hasTyTInv_lam ho.2.2.2.1
    (show Expr.lam covUHoIhTy (.sort .zero) =
      .lam covUHoIhTy (.sort .zero) from rfl)
  let hbody := hasTyT_of_tyConvT (covWConv_bohm_body_ty n _)
    (hasTyTInv_sortT hi.2.2.2.1 rfl)
  let hinner := hasTyT_of_tyConvT
    (.lam _ _ _ _ _ hi.2.2.1 hbody) hi.2.2.2.2
  exact hasTyT_of_tyConvT
    (.lam _ _ _ _ _ ho.2.2.1 hinner) ho.2.2.2.2

/-- The recursor's result after the minor does not depend on that minor. -/
def covWConv_bohm_prefix_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWConvBohmPrefix
      (.pi (.const 63 []) (.app covUHoMotive (.bvar 0))) := by
  let hp := hasTyTInv_app (covWNativeHo_prefix_ty n Γ)
    (show covWNativeHoPrefix =
      .app (.app (.const 65 [.succ (.succ .zero)]) covUHoMotive) covUHoMinor from rfl)
  exact .app _ _ _ _ _ hp.2.2.1 (covWConv_bohm_minor_ty n Γ)

/-- Reuse the old call's actual motive beta transport by application inversion. -/
def covWConv_bohm_call_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWConvBohmCall (.sort (.succ .zero)) := by
  let hp := hasTyTInv_app (covWMatrixIotaSource_ty n Γ)
    (show covWMatrixIotaSource = .app covWNativeHoPrefix covWMatrixIotaMajor from rfl)
  exact hasTyT_of_tyConvT
    (.app _ _ _ _ _ (covWConv_bohm_prefix_ty n Γ) (covWMatrixIotaMajor_ty n Γ))
    hp.2.2.2.2

/-- This is the whole guarded grammar, including eta and the admitted K rule. -/
theorem covWConv_bohm_call_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {c : CptWConvR}
    (h : ApproxTKWConv covUHoEnv n Γ ρ covWConvBohmCall c) : c = .bot :=
  covWConv_Ho_head_only_bot h (.app (.app (.app .head)))

theorem covWConv_bohm_call_observation_iff
    (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) (c : CptWConv) :
    CovWConvObservation covUHoEnv n Γ ρ covWConvBohmCall c ↔ c = .bot :=
  covWConv_observation_bot_iff (fun _ => covWConv_bohm_call_only_bot) c

/-- Equality at every public finite code, with no code-typing restriction. -/
theorem covWConv_bohm_all_observations
    (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) (c : CptWConv) :
    CovWConvObservation covUHoEnv n Γ ρ covWMatrixIotaSource c ↔
    CovWConvObservation covUHoEnv n Γ ρ covWConvBohmCall c :=
  covWConv_bottom_observations_equal (fun _ => covWConv_Ho_ctor_only_bot)
    (fun _ => covWConv_bohm_call_only_bot) c

/-- All admission, closed typing, and full-observation premises are supplied.
The statement deliberately contains no native nonconversion premise. -/
theorem covWConv_bohm_candidate_inhabited (n : Nat) :
    Nonempty (EnvWfT covUHoEnv) ∧ Nonempty (CtxWfT covUHoEnv n []) ∧
    Nonempty (HasTyT covUHoEnv n [] covWMatrixIotaSource (.sort (.succ .zero))) ∧
    Nonempty (HasTyT covUHoEnv n [] covWConvBohmCall (.sort (.succ .zero))) ∧
    Nonempty (HasTyT covUHoEnv n [] (.sort (.succ .zero))
      (.sort (.succ (.succ .zero)))) ∧
    (∀ ρ c, CovWConvObservation covUHoEnv n [] ρ covWMatrixIotaSource c ↔
      CovWConvObservation covUHoEnv n [] ρ covWConvBohmCall c) :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, ⟨covWMatrixIotaSource_ty n []⟩,
    ⟨covWConv_bohm_call_ty n []⟩, ⟨.sort [] (.succ .zero)⟩,
    fun ρ c => covWConv_bohm_all_observations n [] ρ c⟩

/-- Open obligation. This is a definition of the proposition to be proved,
not evidence for it. Absence of a legacy iota witness does not settle it. -/
def CovWConvBohmNonconversionRemaining : Prop :=
  ¬ Nonempty (ConvT covUHoEnv 0 [] covWMatrixIotaSource covWConvBohmCall
    (.sort (.succ .zero)))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_BOHM_ROOTS
#print axioms covWConvBohmBody
#print axioms covWConvBohmMinor
#print axioms covWConvBohmPrefix
#print axioms covWConvBohmCall
#print axioms covWConv_bohm_body_ty
#print axioms covWConv_bohm_minor_ty
#print axioms covWConv_bohm_prefix_ty
#print axioms covWConv_bohm_call_ty
#print axioms covWConv_bohm_call_only_bot
#print axioms covWConv_bohm_call_observation_iff
#print axioms covWConv_bohm_all_observations
#print axioms covWConv_bohm_candidate_inhabited
#print axioms CovWConvBohmNonconversionRemaining
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_BOHM_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
