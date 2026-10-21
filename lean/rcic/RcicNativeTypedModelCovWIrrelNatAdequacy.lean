import rcic.RcicNativeTypedModelCovWIrrelNat
import rcic.RcicNativeTypedModelCovWEtaNatAdequacy

/-!
# Retained local extensional actions for the repaired Nat observations

The new guarded observations are the fresh derivations in `CovWIrrelNat`.
Their structurally erased compacts are exactly the compacts of the landed
Nat action witnesses. The action relation is retained unchanged, including
its native argument typing and its raw observation tests.

This file pairs these two independently supplied facts for successor, its
eta expansion, and the concrete beta and let sources. It also retains the
actual native-zero test of the successor graph. No old observation is
embedded into the new grammar, and no general guarded action supplier is
claimed. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovWTypedAudit TypedModelCovWEtaAudit

/-- The retained graph test uses actual native zero and the same erased
singleton-bottom demand. This is the fixed Nat application action. -/
theorem covWIrrelNat_graph_zero_action (n : Nat) :
    CovWEtaRawAction natEnvU n [] (covWIrrelErase covWIrrelNatResult)
      covWTypedBetaNatTarget (.const 0 []) :=
  covWEtaNat_graph_zero_action n

/-- Every displayed repaired observation is paired with its actual landed
extensional action at the exact structurally erased compact. -/
theorem covWIrrelNat_local_guarded_actions (n : Nat) :
    (ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot covWEtaNatFn covWIrrelNatGraph ∧
      CovWEtaRawAction natEnvU n [] (covWIrrelErase covWIrrelNatGraph)
        covWEtaNatFn covWEtaNatArrow) ∧
    (ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot covWEtaNatExpand covWIrrelNatGraph ∧
      CovWEtaRawAction natEnvU n [] (covWIrrelErase covWIrrelNatGraph)
        covWEtaNatExpand covWEtaNatArrow) ∧
    (ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot covWTypedBetaNatSource covWIrrelNatResult ∧
      CovWEtaRawAction natEnvU n [] (covWIrrelErase covWIrrelNatResult)
        covWTypedBetaNatSource (.const 0 [])) ∧
    (ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot covWTypedBetaNatLet covWIrrelNatResult ∧
      CovWEtaRawAction natEnvU n [] (covWIrrelErase covWIrrelNatResult)
        covWTypedBetaNatLet (.const 0 [])) :=
  ⟨⟨covWIrrelNat_fn_graph n [] EnvWIrrel.bot, covWEtaNat_fn_graph_action n []⟩,
    ⟨covWIrrelNat_expand_graph n [] EnvWIrrel.bot, covWEtaNat_expand_graph_action n []⟩,
    ⟨covWIrrelNat_beta_source n [] EnvWIrrel.bot, covWEtaNat_beta_source_action n⟩,
    ⟨covWIrrelNat_let_source n [] EnvWIrrel.bot, covWEtaNat_let_source_action n⟩⟩

/-- The same four supplies are exposed in the original compact codomain.
Universe provenance does not strengthen the externally tested observation. -/
theorem covWIrrelNat_erased_guarded_actions (n : Nat) :
    (CovWIrrelObservation natEnvU n [] EnvWIrrel.bot covWEtaNatFn covWEtaNatGraph ∧
      CovWEtaRawAction natEnvU n [] covWEtaNatGraph covWEtaNatFn covWEtaNatArrow) ∧
    (CovWIrrelObservation natEnvU n [] EnvWIrrel.bot covWEtaNatExpand covWEtaNatGraph ∧
      CovWEtaRawAction natEnvU n [] covWEtaNatGraph covWEtaNatExpand covWEtaNatArrow) ∧
    (CovWIrrelObservation natEnvU n [] EnvWIrrel.bot
        covWTypedBetaNatSource covWTypedBetaNatCpt ∧
      CovWEtaRawAction natEnvU n [] covWTypedBetaNatCpt
        covWTypedBetaNatSource (.const 0 [])) ∧
    (CovWIrrelObservation natEnvU n [] EnvWIrrel.bot
        covWTypedBetaNatLet covWTypedBetaNatCpt ∧
      CovWEtaRawAction natEnvU n [] covWTypedBetaNatCpt
        covWTypedBetaNatLet (.const 0 [])) := by
  obtain ⟨hfn, hexpand, hbeta, hlet⟩ := covWIrrelNat_local_guarded_actions n
  exact ⟨⟨covWIrrel_observation_of hfn.1, hfn.2⟩,
    ⟨covWIrrel_observation_of hexpand.1, hexpand.2⟩,
    ⟨covWIrrel_observation_of hbeta.1, hbeta.2⟩,
    ⟨covWIrrel_observation_of hlet.1, hlet.2⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_NAT_ADEQUACY_ROOTS
#print axioms covWIrrelNat_graph_zero_action
#print axioms covWIrrelNat_local_guarded_actions
#print axioms covWIrrelNat_erased_guarded_actions
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_NAT_ADEQUACY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
