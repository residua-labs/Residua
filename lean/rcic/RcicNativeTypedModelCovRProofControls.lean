import rcic.RcicNativeTypedModelCovRForall
import rcic.RcicNativeTypedModelCovPProofCollapse
import rcic.RcicNativePiProbeModelBoundary

/-!
# Fresh candidate results for actual collapsing proofs

True.intro, the positive polymorphic lambda identity, and the distinct
Abel--Coquand delta/identity proofs have actual native certificates. Their
landed bottom-only observation theorems supply membership in the new
candidates at every observation. No old CoreY relation is a result field.

The positive lambda uses the new sort-binder operator and its strict positive
arrow body; its observations are bottom independently of that interpretation.
The Abel--Coquand control uses a native positive proposition and the exact
positive candidate, without inventing a positive finite code in the empty
environment. The admitted body-free proof of True remains a counterexample
to unrestricted native observation adequacy. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelKAudit
open ReadbackCK2Audit PiProbeModelBoundaryAudit TypedModelCovPAudit TypedModelCovQAudit

theorem covRTrueIntro_isCandidate (n : Nat) (Γ : LCtx) :
    CandidateCov trueEnvU (WhStepCK2 trueEnvU n) Γ true
      (covRCodeRel trueEnvU (.spine 0 [])) :=
  covRPositiveCode_isCandidate trueEnvU _ Γ _ covP_true_positive

/-- Every actual observation, from either endpoint valuation, belongs to
the new positive-code candidate and is bottom. -/
theorem covR_trueIntro_all_observations (n : Nat) (Γ : LCtx)
    (ρ ρ' : EnvT) (c : CptT)
    (ho : ApproxTK trueEnvU n Γ ρ (.const 1 []) c ∨
      ApproxTK trueEnvU n Γ ρ' (.const 1 []) c) :
    covRCodeRel trueEnvU (.spine 0 []) (.const 1 []) (.const 1 []) c ∧ c = .bot := by
  have hb := covP_trueIntro_collapse n Γ ρ ρ' c ho
  subst c
  exact ⟨(covRTrueIntro_isCandidate n Γ).bot _ _, rfl⟩

theorem covR_trueIntro_control (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n []) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT trueEnvU n [] (.const 1 []) (.const 1 []) (.const 0 [])) ∧
    IsPropCTP trueEnvU (.spine 0 []) ∧
    ApproxTK trueEnvU n [] EnvT.bot (.const 1 []) .bot ∧
    CandidateCov trueEnvU (WhStepCK2 trueEnvU n) [] true
      (covRCodeRel trueEnvU (.spine 0 [])) ∧
    covRCodeRel trueEnvU (.spine 0 []) (.const 1 []) (.const 1 []) .bot ∧
    ∀ ρ ρ' c, (ApproxTK trueEnvU n [] ρ (.const 1 []) c ∨
      ApproxTK trueEnvU n [] ρ' (.const 1 []) c) →
        covRCodeRel trueEnvU (.spine 0 []) (.const 1 []) (.const 1 []) c ∧ c = .bot := by
  obtain ⟨hW, hΓ, hT, hp, hc, hpos, _, ho, _⟩ := covP_trueIntro_control true n
  exact ⟨hW, hΓ, hT, hp, hc, hpos, ho, covRTrueIntro_isCandidate n [],
    (covRTrueIntro_isCandidate n []).bot _ _, covR_trueIntro_all_observations n []⟩

/-- Positive source `forall P : Prop, P -> P`: both the supplied type
candidate and the codomain remain positive at the sort binder. -/
def covRPolyIdProofRelation (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : CovRRel :=
  covRForall E n Γ .zero true true (fun T S => covRArrow E n Γ true T S S)

theorem covRPolyIdProof_isCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CandidateCov E (WhStepCK2 E n) Γ true (covRPolyIdProofRelation E n Γ) := by
  apply covRForall_isCandidate
  intro T S hS
  exact covRArrow_isCandidate hS hS

theorem covR_polyIdProof_all_observations (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ ρ' : EnvT) (c : CptT)
    (ho : ApproxTK E n Γ ρ polyIdProof c ∨ ApproxTK E n Γ ρ' polyIdProof c) :
    covRPolyIdProofRelation E n Γ polyIdProof polyIdProof c ∧ c = .bot := by
  have hb : c = .bot := ho.elim
    (fun h => approxT_polyIdProof_bot E ρ (approxTK_forget h))
    (fun h => approxT_polyIdProof_bot E ρ' (approxTK_forget h))
  subst c
  exact ⟨(covRPolyIdProof_isCandidate E n Γ).bot _ _, rfl⟩

/-- The native positivity tag has an actual Sort-0 derivation here. -/
theorem covR_polyIdProof_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] polyIdProp (.sort .zero)) ∧
    Nonempty (HasTyT emptyEnv n [] polyIdProof polyIdProp) ∧
    Nonempty (ConvT emptyEnv n [] polyIdProof polyIdProof polyIdProp) ∧
    ApproxTK emptyEnv n [] EnvT.bot polyIdProof .bot ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] true
      (covRPolyIdProofRelation emptyEnv n []) ∧
    covRPolyIdProofRelation emptyEnv n [] polyIdProof polyIdProof .bot ∧
    ∀ ρ ρ' c, (ApproxTK emptyEnv n [] ρ polyIdProof c ∨
      ApproxTK emptyEnv n [] ρ' polyIdProof c) →
        covRPolyIdProofRelation emptyEnv n [] polyIdProof polyIdProof c ∧ c = .bot :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨polyIdPropAtZero emptyEnv n⟩,
    ⟨hasTyT_polyIdProof emptyEnv n⟩, ⟨polyIdIrrConversion emptyEnv n⟩,
    .bot _ _ _, covRPolyIdProof_isCandidate emptyEnv n [],
    (covRPolyIdProof_isCandidate emptyEnv n []).bot _ _,
    covR_polyIdProof_all_observations emptyEnv n []⟩

theorem covR_abelCoquand_all_observations (n : Nat) (Γ : LCtx)
    (ρ ρ' : EnvT) (c : CptT)
    (ho : ApproxTK emptyEnv n Γ ρ AbelCoquand.delta c ∨
      ApproxTK emptyEnv n Γ ρ' covPAbelCoquandId c) :
    covRPositiveRel AbelCoquand.delta covPAbelCoquandId c ∧ c = .bot := by
  have hb : c = .bot := ho.elim
    (fun h => covP_abelCoquand_delta_bot (approxTK_forget h))
    (fun h => covP_abelCoquand_id_bot (approxTK_forget h))
  exact ⟨hb, hb⟩

/-- Distinct actual proofs, native irrelevance, and a new candidate result
for every observation. No positive finite code is asserted for AC.top. -/
theorem covR_abelCoquand_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.top (.sort .zero)) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.delta AbelCoquand.top) ∧
    Nonempty (HasTyT emptyEnv n [] covPAbelCoquandId AbelCoquand.top) ∧
    Nonempty (ConvT emptyEnv n [] AbelCoquand.delta covPAbelCoquandId AbelCoquand.top) ∧
    ApproxTK emptyEnv n [] EnvT.bot AbelCoquand.delta .bot ∧
    ApproxTK emptyEnv n [] EnvT.bot covPAbelCoquandId .bot ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] true covRPositiveRel ∧
    covRPositiveRel AbelCoquand.delta covPAbelCoquandId .bot ∧
    ∀ ρ ρ' c, (ApproxTK emptyEnv n [] ρ AbelCoquand.delta c ∨
      ApproxTK emptyEnv n [] ρ' covPAbelCoquandId c) →
        covRPositiveRel AbelCoquand.delta covPAbelCoquandId c ∧ c = .bot := by
  obtain ⟨hW, hΓ, hT, hp, hq, hc, hop, hoq, _⟩ :=
    covP_abelCoquand_distinct_proofs_control n
  exact ⟨hW, hΓ, hT, hp, hq, hc, hop, hoq,
    covRPositive_isCandidate emptyEnv (WhStepCK2 emptyEnv n) [], rfl,
    covR_abelCoquand_all_observations n []⟩

/-- Every genuinely positive candidate rejects the admitted non-bottom
body-free proof observation. Candidate closure alone cannot supply native
observation adequacy for this proof. -/
theorem covRProof_head_no_positive_candidate (n : Nat) (Γ : LCtx) (S : CovRRel)
    (hS : CandidateCov covPProofEnv (WhStepCK2 covPProofEnv n) Γ true S) :
    ¬ S (.const 3 []) (.const 1 []) (.spine 3 []) :=
  fun h => CptT.noConfusion (hS.collapse rfl h)

/-- The candidate class in the negative test has an actual inhabitant,
alongside native irrelevance and the offending model observation. -/
theorem covRProof_positive_boundary_control (n : Nat) :
    Nonempty (EnvWfT covPProofEnv) ∧ Nonempty (CtxWfT covPProofEnv n []) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covPProofEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    ApproxTK covPProofEnv n [] EnvT.bot (.const 3 []) (.spine 3 []) ∧
    ApproxTK covPProofEnv n [] EnvT.bot (.const 1 []) .bot ∧
    (CptT.spine 3 []) ≠ .bot ∧
    CandidateCov covPProofEnv (WhStepCK2 covPProofEnv n) [] true
      (covRCodeRel covPProofEnv (.spine 0 [])) ∧
    ∀ S, CandidateCov covPProofEnv (WhStepCK2 covPProofEnv n) [] true S →
      ¬ S (.const 3 []) (.const 1 []) (.spine 3 []) := by
  obtain ⟨hE, hΓ, hT, hp, hq, hc, hpos, _, hop, hoq, hnb, _⟩ :=
    covPProof_native_irr_counterexample true n
  exact ⟨hE, hΓ, hT, hp, hq, hc, hop, hoq, hnb,
    covRPositiveCode_isCandidate _ _ _ _ hpos,
    covRProof_head_no_positive_candidate n []⟩

/-- Changing the recursive measure cannot by itself repair this unchanged
model-side proof observation. No positive candidate supplies all its values. -/
theorem covRProof_no_positive_observation_supply (n : Nat) :
    ¬ ∃ S, CandidateCov covPProofEnv (WhStepCK2 covPProofEnv n) [] true S ∧
      ∀ c, ApproxTK covPProofEnv n [] EnvT.bot (.const 3 []) c →
        S (.const 3 []) (.const 1 []) c := by
  rintro ⟨S, hS, hs⟩
  exact covRProof_head_no_positive_candidate n [] S hS
    (hs _ (covPProof_head_observed n [] EnvT.bot))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_PROOF_CONTROLS_ROOTS
#print axioms covRTrueIntro_isCandidate
#print axioms covR_trueIntro_all_observations
#print axioms covR_trueIntro_control
#print axioms covRPolyIdProofRelation
#print axioms covRPolyIdProof_isCandidate
#print axioms covR_polyIdProof_all_observations
#print axioms covR_polyIdProof_control
#print axioms covR_abelCoquand_all_observations
#print axioms covR_abelCoquand_control
#print axioms covRProof_head_no_positive_candidate
#print axioms covRProof_positive_boundary_control
#print axioms covRProof_no_positive_observation_supply
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_PROOF_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
