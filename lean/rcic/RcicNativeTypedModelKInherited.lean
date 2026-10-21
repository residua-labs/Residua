import rcic.RcicNativeTypedModelKIndexFree
import rcic.RcicNativeTypedModelKTypedBeta
import rcic.RcicNativeTypedModelFundSymmCex

/-!
# The obstruction inherited by exact K-free reuse

The landed closed-lambda counterexample has no constants, hence no recursor.
Its non-bottom observation cannot be typed at any observation of its native
type.  Agreement at just those two expressions therefore rules out the old
global `TypingLemmaEnvT` input.  This applies to ApproxTK in every environment
and at every frozen native context, independently of the K guard.

The closed typed beta counterexample is inherited for the same reason.  On
Nat, where the complete carrier is unchanged, the landed `FundCases`
refutation also transports.  These are three distinct failed interfaces;
none of the results below asserts a refutation of `FundamentalSAtT`.

Consequently, changing only the K clause while retaining exact agreement on
the whole K-free fragment cannot supply all the original model inputs.  A
future model must change that fragment, its compact typing, or the precise
global typing obligation.  The statement is about these named interfaces,
not an impossibility theorem for a neutral or provenance model.

All native typing and old-model counterexample proofs are imported unchanged.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit
open Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit

variable {E : ResolvedEnv} {M : CtxModelT E}

theorem kFreeT_cexTerm (E : ResolvedEnv) : KFreeT E cexTerm :=
  kFreeT_lam (kFreeT_sort E U1)
    (kFreeT_lam (kFreeT_bvar E 0) (kFreeT_sort E .zero))

theorem kFreeT_cexType (E : ResolvedEnv) : KFreeT E cexType :=
  kFreeT_pi (kFreeT_sort E U1)
    (kFreeT_pi (kFreeT_bvar E 0) (kFreeT_sort E U1))

theorem kFreeT_closed_beta_cex (E : ResolvedEnv) :
    KFreeT E (.app (.lam cexType (.bvar 0)) cexTerm) :=
  kFreeT_app (kFreeT_lam (kFreeT_cexType E) (kFreeT_bvar E 0)) (kFreeT_cexTerm E)

/-- The empty source context is typed for every model and valuation. -/
theorem envTypedAtT_nil (M : CtxModelT E) (ρ : EnvT) : EnvTypedAtT M [] ρ := by
  intro i A hi
  simp [lookupType] at hi

/-- Agreement at the term and its type alone is enough; no K law is assumed. -/
theorem not_typingLemmaEnvT_of_cex_agreement (n : Nat)
    (he : ModelAgreementAtT M (ctxModelT_approxT E) cexTerm)
    (hA : ModelAgreementAtT M (ctxModelT_approxT E) cexType) :
    ¬ TypingLemmaEnvT M n := by
  intro hTL
  obtain ⟨a, ha, hca⟩ := hTL (hasTyT_cexTerm E n) (envTypedAtT_nil M EnvT.bot)
    cexCpt ((he EnvT.bot cexCpt).mpr (approxT_cexTerm E))
  exact not_ctyS_cexCpt_cexType E ⟨a, (hA EnvT.bot a).mp ha, hca⟩

/-- Exact reuse of the K-free fragment cannot restore the old global typing input. -/
theorem not_typingLemmaEnvT_of_kFree_agreement (n : Nat)
    (h : ∀ e, KFreeT E e → ModelAgreementAtT M (ctxModelT_approxT E) e) :
    ¬ TypingLemmaEnvT M n :=
  not_typingLemmaEnvT_of_cex_agreement n
    (h cexTerm (kFreeT_cexTerm E)) (h cexType (kFreeT_cexType E))

theorem approxTK_cexTerm (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ApproxTK E n Γ EnvT.bot cexTerm cexCpt :=
  .free (kFreeT_cexTerm E) (approxT_cexTerm E)

/-- This failure holds even when the frozen model context is the native empty context. -/
theorem not_typingLemmaEnvT_approxTK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ¬ TypingLemmaEnvT (ctxModelT_approxTK E n Γ) n :=
  not_typingLemmaEnvT_of_kFree_agreement n (fun _ h => modelAgreementAtT_kFree h)

/-- The inherited observation is non-bottom and comes from an actual closed native derivation. -/
theorem closed_cex_control_approxTK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Nonempty (HasTyT E n [] cexTerm cexType) ∧
      EnvTypedAtT (ctxModelT_approxTK E n Γ) [] EnvT.bot ∧
      ApproxTK E n Γ EnvT.bot cexTerm cexCpt ∧ cexCpt ≠ .bot :=
  ⟨⟨hasTyT_cexTerm E n⟩, envTypedAtT_nil _ _, approxTK_cexTerm E n Γ,
    fun h => CptT.noConfusion h⟩

/-- The model-equality beta port already fails on two K-free endpoints. -/
theorem not_modelConvSoundAt_of_closed_beta_agreement
    (ha : ModelAgreementAtT M (ctxModelT_approxT E)
      (.app (.lam cexType (.bvar 0)) cexTerm))
    (hb : ModelAgreementAtT M (ctxModelT_approxT E) cexTerm) :
    ¬ ModelConvSoundAt M EnvT.bot (.app (.lam cexType (.bvar 0)) cexTerm) cexTerm := by
  intro hMS
  exact not_approxT_beta_redex_cex E ((ha EnvT.bot cexCpt).mp
    ((hMS cexCpt).mpr ((hb EnvT.bot cexCpt).mpr (approxT_cexTerm E))))

theorem not_modelConvSoundAt_approxTK_closed_beta (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) :
    Nonempty (ConvT E n [] (.app (.lam cexType (.bvar 0)) cexTerm) cexTerm cexType) ∧
      CtxEnvT E [] EnvT.bot ∧
      EnvTypedAtT (ctxModelT_approxTK E n Γ) [] EnvT.bot ∧
      ¬ ModelConvSoundAt (ctxModelT_approxTK E n Γ) EnvT.bot
        (.app (.lam cexType (.bvar 0)) cexTerm) cexTerm :=
  ⟨⟨convT_beta_cex E n⟩, (fun i v h => by simp [lookupValue] at h),
    envTypedAtT_nil _ _, not_modelConvSoundAt_of_closed_beta_agreement
      (modelAgreementAtT_kFree (kFreeT_closed_beta_cex E))
      (modelAgreementAtT_kFree (kFreeT_cexTerm E))⟩

/-- A separate inherited failure: the original record's symmTyping port is impossible. -/
theorem not_fundCases_approxTK_natEnvU (R : Readback) (n : Nat) (Γ : LCtx) :
    ¬ FundCases (ctxModelT_approxTK natEnvU n Γ) R n := by
  intro h
  exact not_fundCases_approxT natEnvU R n
    ((fundCases_approxTK_iff_of_no_indexed not_indexedPropRecT_natEnvU).mp h)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_INHERITED_ROOTS
#print axioms kFreeT_cexTerm
#print axioms kFreeT_cexType
#print axioms kFreeT_closed_beta_cex
#print axioms envTypedAtT_nil
#print axioms not_typingLemmaEnvT_of_cex_agreement
#print axioms not_typingLemmaEnvT_of_kFree_agreement
#print axioms approxTK_cexTerm
#print axioms not_typingLemmaEnvT_approxTK
#print axioms closed_cex_control_approxTK
#print axioms not_modelConvSoundAt_of_closed_beta_agreement
#print axioms not_modelConvSoundAt_approxTK_closed_beta
#print axioms not_fundCases_approxTK_natEnvU
-- END RCIC_NATIVE_TYPED_MODEL_K_INHERITED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit
