import rcic.RcicNativeTypedModelCovRelEscape
import rcic.RcicNativeTypedModelCovRelWitness
import rcic.RcicNativeTypedModelCovRelAgreement

/-!
# Realization at a readback-normal type: a measured alternative target

This module does not change the raw type used by the imported envelope. It
names a different target, realization at a readback-normal reduct, and proves
that the actual alias-type counterexample inhabits that target. The witness
uses `Sort 0`, its `.prop` observation, and the proposition code `pi bot []`.

This alternative is not a global escape theorem. At any already normal type
it is exactly ordinary model realization. Consequently the current `CTyCov`
rigid-successor gap refutes global normalized escape as well. That second
obstruction is the known rigid-spine Pi typing gap; unlike the raw alias
obstruction, it is not asserted to survive a future `CTyCov2` extension.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovKAudit TypedModelCovRelBoundaryAudit TypedModelCovRelAudit
open TypedModelCovRelEscapeAudit TypedModelCovRelWitnessAudit

variable {E : ResolvedEnv} {R : Readback}

/-- An explicit candidate target: a type reduct, its normality, its model
observation, and compact typing at that observed code. -/
def NormalizedCovRealization (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (c : CptT) : Prop :=
  ∃ A₀ a, RedR R Γ A A₀ ∧ NormalR R Γ A₀ ∧ M.Ap ρ A₀ a ∧ C.ty c a

/-- Normalizing the type changes nothing when the index is already normal. -/
theorem normalizedCovRealization_iff_at_normal (C : CovTyping E) (M : CtxModelT E)
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT} (hA : NormalR R Γ A) :
    NormalizedCovRealization C M R Γ ρ A c ↔ ElTCovP C M ρ A c := by
  constructor
  · rintro ⟨A₀, a, hr, _, ha, hty⟩
    have he := redR_of_normal hA hr
    subst A₀
    exact ⟨a, ha, hty⟩
  · rintro ⟨a, ha, hty⟩
    exact ⟨A, a, .refl _, hA, ha, hty⟩

/-- The alias fixture has a concrete normalized realization for every typing
implementation that includes the old introduction judgment. -/
theorem normalizedCovRealization_eqGapAlias (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    NormalizedCovRealization C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) eqGapCtx ρ (eqGapDirectAlias A B) (.pi .bot []) := by
  refine ⟨.sort .zero, .prop, eqGapAlias_type_read n A B,
    normalR_sortCK2 eqGapCtx .zero, ?_, ?_⟩
  · change ApproxTK eqEnvT n eqGapCtx ρ (.sort .zero) .prop
    rw [← sortCode_zero]
    exact approxTK_sort_code eqEnvT n eqGapCtx ρ .zero
  · apply hS .prop (.pi .bot [])
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))

/-- The current `CTyCov` instance discharges the inclusion condition. -/
theorem normalizedCovRealization_eqGapAlias_ctyCov (n : Nat) (ρ : EnvT)
    (A B : Expr Nat) :
    NormalizedCovRealization (covTypingCTyCov eqEnvT)
      (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
      eqGapCtx ρ (eqGapDirectAlias A B) (.pi .bot []) :=
  normalizedCovRealization_eqGapAlias (covTypingCTyCov eqEnvT)
    (covTypingCTyCov_includesS eqEnvT) n ρ A B

/-- At the very same alias and compact, raw realization fails while normalized
realization succeeds. No model equality or backward observation law is used. -/
theorem alias_raw_and_normalized_realization (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    (¬ ElTCovP C (ctxModelT_approxTK eqEnvT n eqGapCtx) ρ
      (eqGapDirectAlias A B) (.pi .bot [])) ∧
    NormalizedCovRealization C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) eqGapCtx ρ (eqGapDirectAlias A B) (.pi .bot []) :=
  ⟨not_elTCovP_at_eqGapAlias C n eqGapCtx ρ A B (fun h => CptT.noConfusion h),
    normalizedCovRealization_eqGapAlias C hS n ρ A B⟩

/-- The actual fixture also reaches the imported envelope at its normalized
type. The type expression is displayed in the conclusion and is not silently
substituted for the raw alias in the refuted escape statement. -/
theorem eqGapAlias_normalized_envelope (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    ∃ A₀, RedR (WhStepCK2 eqEnvT n) eqGapCtx (eqGapDirectAlias A B) A₀ ∧
      NormalR (WhStepCK2 eqEnvT n) eqGapCtx A₀ ∧
      CovTypedEnvelopeT (ctxModelT_approxTK eqEnvT n eqGapCtx)
        (WhStepCK2 eqEnvT n) n eqGapCtx ρ idPiProp idPiProp A₀ (.pi .bot []) := by
  obtain ⟨A₀, a, hr, hn, ha, ht⟩ := normalizedCovRealization_eqGapAlias_ctyCov n ρ A B
  have he := normalUniqueR_whStepCK2 pinEqGroupWfT eqGapCtx hr hn
    (eqGapAlias_type_read n A B) (normalR_sortCK2 eqGapCtx .zero)
  subst A₀
  have hcore := lrSCoreCov_sortIdx_irrel (covTypingCTyCov eqEnvT)
    (readbackLaws_whStepCK2 eqEnvT n) (normalUniqueR_whStepCK2 pinEqGroupWfT)
    ⟨.zero, eqGapAlias_type_read n A B⟩ ⟨.zero, .refl _⟩ (.pi .bot [])
    (idPiProp_covRel_at_alias (covTypingCTyCov eqEnvT) n A B)
  exact ⟨.sort .zero, eqGapAlias_type_read n A B, normalR_sortCK2 eqGapCtx .zero,
    ⟨a, ha, ht⟩, (lrSCoreCov_iff_coreS (covTypingCTyCov eqEnvT) (.pi .bot [])
      (covGateAgreement_pi_bot_nil (covTypingCTyCov eqEnvT)) eqGapCtx
      idPiProp idPiProp (.sort .zero)).mp hcore⟩

/-- The successor's native Pi type is already readback-normal, so the known
current-typing gap also excludes every normalized realization. -/
theorem not_normalizedCovRealization_natSucc (n : Nat) (ρ : EnvT) :
    ¬ NormalizedCovRealization (covTypingCTyCov natEnvU)
      (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n) [] ρ
      (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) := by
  intro h
  have hraw := (normalizedCovRealization_iff_at_normal (covTypingCTyCov natEnvU)
    (ctxModelT_approxTK natEnvU n [])
    (normalR_piCK2 [] (.const 0 []) (.const 0 []))).mp h
  obtain ⟨a, ha, hty⟩ := hraw
  exact not_elTCov_natSucc_spine ρ ⟨a, approxTK_forget ha, hty⟩

/-- A possible global normalized escape statement, with both native typings,
both term observations, coherent environment typing, and the new core. -/
def NormalizedCovEscape (C : CovTyping E) (n : Nat) : Prop :=
  EnvWfT E →
    ∀ {Γ : LCtx} {ρ : EnvT} {x y A : Expr Nat} {c : CptT},
      CtxWfT E n Γ → HasTyT E n Γ x A → HasTyT E n Γ y A →
      EnvTypedCovAtP C (ctxModelT_approxTK E n Γ) Γ ρ →
      ApproxTK E n Γ ρ x c → ApproxTK E n Γ ρ y c →
      LRSCoreCov C (WhStepCK2 E n) n Γ x y A c →
      NormalizedCovRealization C (ctxModelT_approxTK E n Γ)
        (WhStepCK2 E n) Γ ρ A c

/-- Global normalized escape fails for the unchanged `CTyCov`. This theorem
does not claim the same failure for a repaired rigid-spine typing. -/
theorem not_normalizedCovEscape_ctyCov_nat (n : Nat) :
    ¬ NormalizedCovEscape (covTypingCTyCov natEnvU) n := by
  intro h
  obtain ⟨⟨hW⟩, ⟨hΓ⟩, ⟨ht⟩, hρ, hm, hr, _, _⟩ :=
    natSucc_covRel_nonEscape_control n EnvT.bot
  exact not_normalizedCovRealization_natSucc n EnvT.bot
    (h hW hΓ ht ht hρ hm hm hr)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_REALIZATION_ROOTS
#print axioms NormalizedCovRealization
#print axioms normalizedCovRealization_iff_at_normal
#print axioms normalizedCovRealization_eqGapAlias
#print axioms normalizedCovRealization_eqGapAlias_ctyCov
#print axioms alias_raw_and_normalized_realization
#print axioms eqGapAlias_normalized_envelope
#print axioms not_normalizedCovRealization_natSucc
#print axioms NormalizedCovEscape
#print axioms not_normalizedCovEscape_ctyCov_nat
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_REALIZATION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelRealizationAudit
