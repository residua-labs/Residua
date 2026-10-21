import rcic.RcicNativeTypedModelCov2
import rcic.RcicNativeTypedModelCovRelRealization

/-!
# The imported `CTyCov2` at the landed covariant relation interface

The compact typing is the imported judgment without alteration. Its three-way
Pi inversion supplies both alternatives required by `CovTyping`, and the
imported proposition-collapse theorem supplies `prop_bot`. This module also
measures the previously excluded rigid successor at the actual `ApproxTK`
model: both raw and normalized realization now have concrete witnesses.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormCov2Audit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelCovKAudit
open TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelBoundaryAudit TypedModelCovPropagationAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit
open TypedModelCovRelEscapeAudit TypedModelCovRelRealizationAudit

/-- Every landed interface law is supplied by the imported `CTyCov2`.
The rigid Pi alternative is retained explicitly. -/
def covTypingCTyCov2 (E : ResolvedEnv) : CovTyping E where
  ty := CTyCov2 E
  bot := ctyCov2_bot
  bot_inv := ctyCov2_bot_inv
  prop_inv := ctyCov2_prop_inv
  sort_inv := ctyCov2_sort_inv
  lam_inv := ctyCov2_lam_inv
  spine_inv := by
    intro u r args h
    rcases ctyCov2_spine_inv h with hb | ⟨hsp, _⟩
    · exact Or.inl hb
    · exact Or.inr hsp
  pi_inv := by
    intro u a g h
    rcases ctyCov2_pi_inv h with hb | ⟨f, huf, _, hd, hc⟩ | ⟨r, args, hu, _⟩
    · exact Or.inl hb
    · refine Or.inr (Or.inl ⟨f, huf, hd, ?_⟩)
      intro s hs
      rcases hc s hs with hb | ⟨t, ht, hsub, hout⟩
      · exact Or.inl hb
      · exact Or.inr ⟨t, ht, hsub, hout⟩
    · exact Or.inr (Or.inr ⟨r, args, hu⟩)
  prop_bot := ctyCov2_prop_bot

/-- The introduction judgment used by the model is included unchanged. -/
theorem covTypingCTyCov2_includesS (E : ResolvedEnv) :
    CovTypingIncludesS (covTypingCTyCov2 E) := by
  intro a u h
  exact ctyCov2_of_ctyS h

/-- The concrete typing parameter used by the normalized-realization audit. -/
abbrev C2 (E : ResolvedEnv) : CovTyping E := covTypingCTyCov2 E

theorem C2_includesS (E : ResolvedEnv) : CovTypingIncludesS (C2 E) :=
  covTypingCTyCov2_includesS E

/-- The model realization interface specializes definitionally to the
imported `ElTCov2M`; there is no recursive-relation identification here. -/
theorem elTCovP_C2_iff {E : ResolvedEnv} (M : CtxModelT E) (ρ : EnvT)
    (A : Expr Nat) (c : CptT) :
    ElTCovP (C2 E) M ρ A c ↔ ElTCov2M M ρ A c := Iff.rfl

/-- Both the compact typing and the actual let-value coherence coincide
definitionally with the imported `CTyCov2` environment guard. -/
theorem envTypedCovAtP_C2_iff {E : ResolvedEnv} (M : CtxModelT E)
    (Γ : LCtx) (ρ : EnvT) :
    EnvTypedCovAtP (C2 E) M Γ ρ ↔ EnvTypedCov2M M Γ ρ := Iff.rfl

/-- The imported non-proposition Pi code is an actual observation in the
fixed-context model used by normalized escape. -/
theorem approxTK_natNat_covCode (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) natNatCovCode :=
  ApproxTK.free (kFreeT_natEnvU _) (approxT_natNat_covCode ρ)

/-- The previously excluded rigid successor now has raw realization at the
same native Pi type and the same compact observation. -/
theorem elTCovP_C2_natSucc (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ElTCovP (C2 natEnvU) (ctxModelT_approxTK natEnvU n Γ) ρ
      (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) :=
  ⟨natNatCovCode, approxTK_natNat_covCode n Γ ρ,
    ctyCov2_natSucc_spine (approxT_natNat_covCode ρ) not_isPropCT_natNatCovCode⟩

/-- The successor type is already weak-head normal. Its normalized
realization follows at the actual model, with an explicit type code. -/
theorem normalizedCovRealization_C2_natSucc (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    NormalizedCovRealization (C2 natEnvU) (ctxModelT_approxTK natEnvU n Γ)
      (WhStepCK2 natEnvU n) Γ ρ (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) :=
  (normalizedCovRealization_iff_at_normal (C2 natEnvU)
    (ctxModelT_approxTK natEnvU n Γ)
    (normalR_piCK2 Γ (.const 0 []) (.const 0 []))).mpr
      (elTCovP_C2_natSucc n Γ ρ)

/-- All native, environment, observation, relation and realization controls
coexist for the successor in the admitted Nat environment. -/
theorem natSucc_C2_normalized_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    EnvTypedCovAtP (C2 natEnvU) (ctxModelT_approxTK natEnvU n []) [] ρ ∧
    ApproxTK natEnvU n [] ρ (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] ρ (.pi (.const 0 []) (.const 0 [])) natNatCovCode ∧
    (C2 natEnvU).ty (.spine 2 []) natNatCovCode ∧
    LRSCoreCov (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) ∧
    NormalizedCovRealization (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) [] ρ (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) ∧
    (.spine 2 [] : CptT) ≠ .bot ∧ natNatCovCode ≠ .bot := by
  exact ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, ⟨hasTyT_natEnvU_succ n []⟩,
    envTypedCovAtP_nil (C2 natEnvU) _ ρ,
    ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine ρ),
    approxTK_natNat_covCode n [] ρ,
    ctyCov2_natSucc_spine (approxT_natNat_covCode ρ) not_isPropCT_natNatCovCode,
    lrSCoreCov_natSucc_spine (C2 natEnvU) n [],
    normalizedCovRealization_C2_natSucc n [] ρ,
    (fun h => CptT.noConfusion h), (fun h => CptT.noConfusion h)⟩

/-- At the actual Eq alias, the exact `C2` instance retains raw failure and
the existing normalized realization simultaneously. -/
theorem alias_raw_and_normalized_realization_C2 (n : Nat) (ρ : EnvT)
    (A B : Expr Nat) :
    (¬ ElTCovP (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n eqGapCtx) ρ
      (eqGapDirectAlias A B) (.pi .bot [])) ∧
    NormalizedCovRealization (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) eqGapCtx ρ (eqGapDirectAlias A B) (.pi .bot []) :=
  alias_raw_and_normalized_realization (C2 eqEnvT) (C2_includesS eqEnvT) n ρ A B

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_COV2_ROOTS
#print axioms covTypingCTyCov2
#print axioms covTypingCTyCov2_includesS
#print axioms C2
#print axioms C2_includesS
#print axioms elTCovP_C2_iff
#print axioms envTypedCovAtP_C2_iff
#print axioms approxTK_natNat_covCode
#print axioms elTCovP_C2_natSucc
#print axioms normalizedCovRealization_C2_natSucc
#print axioms natSucc_C2_normalized_control
#print axioms alias_raw_and_normalized_realization_C2
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_COV2_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormCov2Audit
