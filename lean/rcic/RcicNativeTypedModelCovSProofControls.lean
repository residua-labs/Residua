import rcic.RcicNativeTypedModelCovSCandidate
import rcic.RcicNativeTypedModelCovPProofCollapse
import rcic.RcicNativePiProbeModelBoundary

/-!
# Total positive candidates at actual proof observations

The body-free proof of True now belongs to every positive S candidate at
its actual nonbottom observation. Native proof irrelevance is retained.
The old bottom-only observation and old compact-typing ports remain false
on that same inhabited control; totality does not supply either port.

The unchanged model still observes True.intro, the positive polymorphic
lambda, and the Abel--Coquand delta/identity proofs only at bottom. Those
are independent properties of ApproxTK and its CTyS binder demands, not
laws inferred from the new total candidate. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelKAudit
open ReadbackCK2Audit PiProbeModelBoundaryAudit TypedModelCovPAudit
open TypedModelCovNormConvCasesAudit

theorem covSProof_head_total (n : Nat) (Γ : LCtx) (S : CovSRel)
    (hS : CandidateCovS covPProofEnv (WhStepCK2 covPProofEnv n) Γ true S) :
    S (.const 3 []) (.const 1 []) (.spine 3 []) :=
  hS.positive_total rfl _ _ _

/-- The exact old positive-code typing implication is incompatible with
totality at the existing nonbottom proof observation. The actual positive
code is the observed True family spine, not an unknown bottom code. -/
theorem covSProof_total_no_old_typing (reflect : Bool) (n : Nat) (Γ : LCtx)
    (S : CovSRel)
    (hS : CandidateCovS covPProofEnv (WhStepCK2 covPProofEnv n) Γ true S) :
    ¬ (∀ c, S (.const 3 []) (.const 1 []) c →
      CTyCovP2 reflect covPProofEnv c (.spine 0 [])) := by
  intro ht
  exact CptT.noConfusion (ctyCovP2_prop_bot covPProof_true_positive
    (ht _ (covSProof_head_total n Γ S hS)))

/-- All premises of the former positive-candidate obstruction are inhabited.
Its fresh relation result is now positive, while the frozen old `prop_bot`,
collapse, and model-observation-transport ports still cannot be supplied. -/
theorem covSProof_total_control (n : Nat) :
    Nonempty (EnvWfT covPProofEnv) ∧ Nonempty (CtxWfT covPProofEnv n []) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 3 []) (.const 0 [])) ∧
    Nonempty (HasTyT covPProofEnv n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT covPProofEnv n [] (.const 3 []) (.const 1 []) (.const 0 [])) ∧
    IsPropCTP covPProofEnv (.spine 0 []) ∧
    ApproxTK covPProofEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    ApproxTK covPProofEnv n [] EnvT.bot (.const 3 []) (.spine 3 []) ∧
    ApproxTK covPProofEnv n [] EnvT.bot (.const 1 []) .bot ∧
    (CptT.spine 3 []) ≠ .bot ∧
    CandidateCovS covPProofEnv (WhStepCK2 covPProofEnv n) [] true covSTotalRel ∧
    covSTotalRel (.const 3 []) (.const 1 []) (.spine 3 []) ∧
    (∀ S, CandidateCovS covPProofEnv (WhStepCK2 covPProofEnv n) [] true S →
      ∀ ρ ρ' c, (ApproxTK covPProofEnv n [] ρ (.const 3 []) c ∨
        ApproxTK covPProofEnv n [] ρ' (.const 1 []) c) →
          S (.const 3 []) (.const 1 []) c) ∧
    (∀ reflect, ¬ (∀ c, covSTotalRel (.const 3 []) (.const 1 []) c →
      CTyCovP2 reflect covPProofEnv c (.spine 0 []))) ∧
    (¬ CovProofCollapseFor (ctxModelT_approxTK covPProofEnv n [])
      (.const 3 []) (.const 1 [])) ∧
    ¬ CovModelContractAt (ctxModelT_approxTK covPProofEnv n [])
      (.const 3 []) (.const 1 []) := by
  obtain ⟨hW, hΓ, hT, hp, hq, hc, hpos, hType, hop, hoq, hnb, _, hcollapse, hcontract⟩ :=
    covPProof_native_irr_counterexample true n
  have htotal := covSTotal_isCandidate covPProofEnv (WhStepCK2 covPProofEnv n) [] true
  exact ⟨hW, hΓ, hT, hp, hq, hc, hpos, hType, hop, hoq, hnb, htotal,
    trivial, fun S hS _ _ c _ => hS.positive_total rfl _ _ c,
    fun reflect => covSProof_total_no_old_typing reflect n [] covSTotalRel htotal,
    hcollapse, hcontract⟩

theorem covS_trueIntro_all_observations (n : Nat) (Γ : LCtx)
    (ρ ρ' : EnvT) (c : CptT)
    (ho : ApproxTK trueEnvU n Γ ρ (.const 1 []) c ∨
      ApproxTK trueEnvU n Γ ρ' (.const 1 []) c) :
    covSTotalRel (.const 1 []) (.const 1 []) c ∧ c = .bot :=
  ⟨trivial, covP_trueIntro_collapse n Γ ρ ρ' c ho⟩

theorem covS_trueIntro_control (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n []) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 0 []) (.sort .zero)) ∧
    Nonempty (HasTyT trueEnvU n [] (.const 1 []) (.const 0 [])) ∧
    Nonempty (ConvT trueEnvU n [] (.const 1 []) (.const 1 []) (.const 0 [])) ∧
    IsPropCTP trueEnvU (.spine 0 []) ∧
    ApproxTK trueEnvU n [] EnvT.bot (.const 1 []) .bot ∧
    CandidateCovS trueEnvU (WhStepCK2 trueEnvU n) [] true covSTotalRel ∧
    covSTotalRel (.const 1 []) (.const 1 []) .bot ∧
    ∀ ρ ρ' c, (ApproxTK trueEnvU n [] ρ (.const 1 []) c ∨
      ApproxTK trueEnvU n [] ρ' (.const 1 []) c) →
        covSTotalRel (.const 1 []) (.const 1 []) c ∧ c = .bot := by
  obtain ⟨hW, hΓ, hT, hp, hc, hpos, _, ho, _⟩ := covP_trueIntro_control true n
  exact ⟨hW, hΓ, hT, hp, hc, hpos, ho,
    covSTotal_isCandidate trueEnvU (WhStepCK2 trueEnvU n) [] true,
    trivial, covS_trueIntro_all_observations n []⟩

theorem covS_polyIdProof_all_observations (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ ρ' : EnvT) (c : CptT)
    (ho : ApproxTK E n Γ ρ polyIdProof c ∨ ApproxTK E n Γ ρ' polyIdProof c) :
    covSTotalRel polyIdProof polyIdProof c ∧ c = .bot :=
  ⟨trivial, ho.elim
    (fun h => approxT_polyIdProof_bot E ρ (approxTK_forget h))
    (fun h => approxT_polyIdProof_bot E ρ' (approxTK_forget h))⟩

/-- Native Sort-0 typing supplies the positivity fact for this control.
Bottom-only observation remains an independent inherited model theorem. -/
theorem covS_polyIdProof_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] polyIdProp (.sort .zero)) ∧
    Nonempty (HasTyT emptyEnv n [] polyIdProof polyIdProp) ∧
    Nonempty (ConvT emptyEnv n [] polyIdProof polyIdProof polyIdProp) ∧
    ApproxTK emptyEnv n [] EnvT.bot polyIdProof .bot ∧
    CandidateCovS emptyEnv (WhStepCK2 emptyEnv n) [] true covSTotalRel ∧
    covSTotalRel polyIdProof polyIdProof .bot ∧
    ∀ ρ ρ' c, (ApproxTK emptyEnv n [] ρ polyIdProof c ∨
      ApproxTK emptyEnv n [] ρ' polyIdProof c) →
        covSTotalRel polyIdProof polyIdProof c ∧ c = .bot :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨polyIdPropAtZero emptyEnv n⟩,
    ⟨hasTyT_polyIdProof emptyEnv n⟩, ⟨polyIdIrrConversion emptyEnv n⟩,
    .bot _ _ _, covSTotal_isCandidate emptyEnv (WhStepCK2 emptyEnv n) [] true,
    trivial, covS_polyIdProof_all_observations emptyEnv n []⟩

theorem covS_abelCoquand_all_observations (n : Nat) (Γ : LCtx)
    (ρ ρ' : EnvT) (c : CptT)
    (ho : ApproxTK emptyEnv n Γ ρ AbelCoquand.delta c ∨
      ApproxTK emptyEnv n Γ ρ' covPAbelCoquandId c) :
    covSTotalRel AbelCoquand.delta covPAbelCoquandId c ∧ c = .bot :=
  ⟨trivial, ho.elim
    (fun h => covP_abelCoquand_delta_bot (approxTK_forget h))
    (fun h => covP_abelCoquand_id_bot (approxTK_forget h))⟩

/-- The actual distinct AC proofs remain related, and their unchanged
observations remain bottom. No positive finite code is invented in emptyEnv. -/
theorem covS_abelCoquand_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.top (.sort .zero)) ∧
    Nonempty (HasTyT emptyEnv n [] AbelCoquand.delta AbelCoquand.top) ∧
    Nonempty (HasTyT emptyEnv n [] covPAbelCoquandId AbelCoquand.top) ∧
    Nonempty (ConvT emptyEnv n [] AbelCoquand.delta covPAbelCoquandId AbelCoquand.top) ∧
    ApproxTK emptyEnv n [] EnvT.bot AbelCoquand.top (.pi .bot []) ∧
    ApproxTK emptyEnv n [] EnvT.bot AbelCoquand.delta .bot ∧
    ApproxTK emptyEnv n [] EnvT.bot covPAbelCoquandId .bot ∧
    CandidateCovS emptyEnv (WhStepCK2 emptyEnv n) [] true covSTotalRel ∧
    covSTotalRel AbelCoquand.delta covPAbelCoquandId .bot ∧
    CovProofCollapseFor (ctxModelT_approxTK emptyEnv n [])
      AbelCoquand.delta covPAbelCoquandId ∧
    ∀ ρ ρ' c, (ApproxTK emptyEnv n [] ρ AbelCoquand.delta c ∨
      ApproxTK emptyEnv n [] ρ' covPAbelCoquandId c) →
        covSTotalRel AbelCoquand.delta covPAbelCoquandId c ∧ c = .bot := by
  obtain ⟨hW, hΓ, hT, hp, hq, hc, hop, hoq, hcollapse⟩ :=
    covP_abelCoquand_distinct_proofs_control n
  exact ⟨hW, hΓ, hT, hp, hq, hc,
    approxTK_pi_bot_nil emptyEnv n [] EnvT.bot _ _, hop, hoq,
    covSTotal_isCandidate emptyEnv (WhStepCK2 emptyEnv n) [] true,
    trivial, hcollapse, covS_abelCoquand_all_observations n []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_PROOF_CONTROLS_ROOTS
#print axioms covSProof_head_total
#print axioms covSProof_total_no_old_typing
#print axioms covSProof_total_control
#print axioms covS_trueIntro_all_observations
#print axioms covS_trueIntro_control
#print axioms covS_polyIdProof_all_observations
#print axioms covS_polyIdProof_control
#print axioms covS_abelCoquand_all_observations
#print axioms covS_abelCoquand_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_PROOF_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
