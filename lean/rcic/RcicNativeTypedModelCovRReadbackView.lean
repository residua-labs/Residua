import rcic.RcicNativeTypedModelCovRSyntax
import rcic.RcicNativeTypedModelCovRReadback

/-!
# Interpreting an actually supplied CK2 type readback

The growing beta example has a concrete finite normal template and a
candidate interpretation. Its certificate is supplied directly; computing
normal readbacks for arbitrary native types is not assumed. This separates
interpretation of a known normal form from a well-founded total normalizer.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit ReadbackCK2Audit PiModelBetaObstructionAudit

def covRReadbackSmallSyntax : CovRSyntax emptyEnv := .allProp .prop

def covRReadbackArgumentSyntax : CovRSyntax emptyEnv :=
  .arrow covRReadbackSmallSyntax covRReadbackSmallSyntax

def covRReadbackSyntax : CovRSyntax emptyEnv :=
  .arrow covRReadbackArgumentSyntax covRReadbackArgumentSyntax

theorem covRReadbackSyntax_native (σ : Nat → Expr Nat) :
    covRNative covRReadbackSyntax σ = covRReadbackTarget := rfl

theorem covRReadbackSyntax_wellFormed :
    CovRTemplateWellFormed covRReadbackSyntax :=
  ⟨True.intro, ⟨True.intro, True.intro, True.intro⟩,
    ⟨True.intro, True.intro, True.intro⟩⟩

theorem covRReadback_actual_view :
    CovRNativeView emptyEnv 0 [] covRReadbackSource covRReadbackSyntax (covRBaseVal emptyEnv) :=
  ⟨covRReadbackSyntax_wellFormed, covRReadback_ck2_readback, covRReadback_target_normal⟩

theorem covRReadback_candidate :
    CandidateCov emptyEnv (WhStepCK2 emptyEnv 0) [] false
      (covRInterpret emptyEnv 0 [] covRReadbackSyntax (fun _ => false) (covRBaseVal emptyEnv)) :=
  covRInterpret_isCandidate emptyEnv 0 [] covRReadbackSyntax (fun _ => false)
    (covRBaseVal emptyEnv) (covRBaseVal_valid emptyEnv 0 [])

/-- The finite template interpretation is available even though the actual
native readback increases size. It supplies no total readback function. -/
theorem covRReadback_candidate_control :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv 0 []) ∧
    Nonempty (HasTyT emptyEnv 0 [] covRReadbackSource (.sort (.succ .zero))) ∧
    Nonempty (HasTyT emptyEnv 0 [] covRReadbackTarget (.sort (.succ .zero))) ∧
    CovRNativeView emptyEnv 0 [] covRReadbackSource covRReadbackSyntax (covRBaseVal emptyEnv) ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv 0) [] false
      (covRInterpret emptyEnv 0 [] covRReadbackSyntax (fun _ => false) (covRBaseVal emptyEnv)) ∧
    sizeOf covRReadbackSource < sizeOf covRReadbackTarget :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨covRReadbackSource_hasTy⟩, ⟨covRReadbackTarget_hasTy⟩,
    covRReadback_actual_view, covRReadback_candidate, covRReadback_size_grows⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_READBACK_VIEW_ROOTS
#print axioms covRReadbackSmallSyntax
#print axioms covRReadbackArgumentSyntax
#print axioms covRReadbackSyntax
#print axioms covRReadbackSyntax_native
#print axioms covRReadbackSyntax_wellFormed
#print axioms covRReadback_actual_view
#print axioms covRReadback_candidate
#print axioms covRReadback_candidate_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_READBACK_VIEW_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
