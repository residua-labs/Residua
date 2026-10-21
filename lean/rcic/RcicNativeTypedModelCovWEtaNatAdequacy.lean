import rcic.RcicNativeTypedModelCovWEtaNat
import rcic.RcicNativeTypedModelCovWEtaActions

/-!
# Concrete extensional adequacy for the Nat eta repairs

The new successor graph has the raw extensional action: its row sends an
actual argument to the matching successor spine, with that same argument as
the spine's field. This construction does not read successor back as a
lambda. The old eta-expansion observation is covered by the proved general
raw supplier. Applying the graph test to native zero supplies the action of
the actual `succ zero` target.

The beta and let source actions are supplied separately by transporting the
target's landed operational action backward along their actual native
steps, then applying the finite extensional adapter. Their old raw
observation failures remain unchanged. Here `Raw` describes the arguments
admitted by an action test; an action can also be proved for these additional
guarded source observations by a concrete operational argument.

The final theorem pairs the displayed new guarded observations with their
actual extensional actions. It is a local supply for these fixtures, not a
general guarded eta-adequacy or conversion-preservation theorem.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit
open TypedModelCovVAudit TypedModelCovWAudit TypedModelCovWTypedAudit
open TypedModelCovXAudit

/-- Successor's graph acts through its rigid spine. The internal old
operational action needs only a native head, which is this same spine. -/
theorem covWEtaNat_fn_graph_action (n : Nat) (Γ : LCtx) :
    CovWEtaRawAction natEnvU n Γ covWEtaNatGraph covWEtaNatFn covWEtaNatArrow := by
  have hrigid : CovWValueAction natEnvU n Γ (.spine 2 []) covWEtaNatFn :=
    covW_raw_closed_actions (Δ := Γ) natEnvUWfT
      (covWEtaNatFn_ty n Γ) (covWEtaNat_fn_raw EnvT.bot)
  apply covWEtaRaw_action_of_value natEnvUWfT (covWEtaNatFn_ty n Γ)
  change CovWValueAction natEnvU n Γ (.lam [([.bot], .spine 2 [.bot])]) covWEtaNatFn
  rw [CovWValueAction]
  refine ⟨covW_value_action_head hrigid (fun he => CptT.noConfusion he), ?_⟩
  intro s hs x ha
  obtain rfl := List.mem_singleton.mp hs
  exact covW_value_action_app_spine hrigid
    (ha .bot (List.mem_singleton.mpr rfl))

/-- The old raw lambda observation has a direct supplied action. -/
theorem covWEtaNat_expand_graph_action (n : Nat) (Γ : LCtx) :
    CovWEtaRawAction natEnvU n Γ covWEtaNatGraph covWEtaNatExpand covWEtaNatArrow :=
  covWEtaRaw_closed natEnvUWfT (covWEtaNatExpand_ty n Γ)
    (covWEtaNat_expand_raw EnvT.bot)

/-- Test the successor graph at native zero, using the actual Nat domain
observation and the exact singleton bottom demand. -/
theorem covWEtaNat_graph_zero_action (n : Nat) :
    CovWEtaRawAction natEnvU n [] covWTypedBetaNatCpt
      covWTypedBetaNatTarget (.const 0 []) := by
  refine covWEtaRaw_action_app
    (D := .const 0 []) (B := .const 0 [])
    (rows := [([.bot], .spine 2 [.bot])])
    (s := ([.bot], .spine 2 [.bot])) (d := .spine 0 [])
    (covWEtaNat_fn_graph_action n [])
    (covWTypedBetaNat_type_raw EnvT.bot) (List.mem_singleton.mpr rfl)
    ?_ (hasTyT_natEnvU_zero n []) ?_
  · intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact .bot _ _

/-- The beta source action uses its literal native step and the raw
target supplier. It does not assume a raw observation of the source. -/
theorem covWEtaNat_beta_source_action (n : Nat) :
    CovWEtaRawAction natEnvU n [] covWTypedBetaNatCpt
      covWTypedBetaNatSource (.const 0 []) := by
  have htarget : CovWValueAction natEnvU n [] covWTypedBetaNatCpt covWTypedBetaNatTarget :=
    covW_raw_closed_actions natEnvUWfT (covWTypedBetaNatTarget_ty n)
      (covWTypedBetaNat_target_raw EnvT.bot)
  exact covWEtaRaw_action_of_value natEnvUWfT (covWTypedBetaNatSource_ty n)
    (covW_value_action_backward covWTypedBetaNatCpt (covWTypedBetaNat_readback n) htarget)

/-- The same concrete construction applies to the actual native let step. -/
theorem covWEtaNat_let_source_action (n : Nat) :
    CovWEtaRawAction natEnvU n [] covWTypedBetaNatCpt
      covWTypedBetaNatLet (.const 0 []) := by
  have htarget : CovWValueAction natEnvU n [] covWTypedBetaNatCpt covWTypedBetaNatTarget :=
    covW_raw_closed_actions natEnvUWfT (covWTypedBetaNatTarget_ty n)
      (covWTypedBetaNat_target_raw EnvT.bot)
  exact covWEtaRaw_action_of_value natEnvUWfT (covWTypedBetaNatLet_ty n)
    (covW_value_action_backward covWTypedBetaNatCpt (covWTypedBetaNat_let_readback n) htarget)

/-- Every displayed repaired observation is paired with a supplied typed
extensional action; the eta expansion supplies the old raw comparison. -/
theorem covWEtaNat_local_guarded_actions (n : Nat) :
    (ApproxTKWEta natEnvU n [] EnvT.bot covWEtaNatFn covWEtaNatGraph ∧
      CovWEtaRawAction natEnvU n [] covWEtaNatGraph covWEtaNatFn covWEtaNatArrow) ∧
    (ApproxTKWEta natEnvU n [] EnvT.bot covWEtaNatExpand covWEtaNatGraph ∧
      CovWEtaRawAction natEnvU n [] covWEtaNatGraph covWEtaNatExpand covWEtaNatArrow) ∧
    (ApproxTKWEta natEnvU n [] EnvT.bot covWTypedBetaNatSource covWTypedBetaNatCpt ∧
      CovWEtaRawAction natEnvU n [] covWTypedBetaNatCpt covWTypedBetaNatSource (.const 0 [])) ∧
    (ApproxTKWEta natEnvU n [] EnvT.bot covWTypedBetaNatLet covWTypedBetaNatCpt ∧
      CovWEtaRawAction natEnvU n [] covWTypedBetaNatCpt covWTypedBetaNatLet (.const 0 [])) :=
  ⟨⟨covWEtaNat_fn_graph n [] EnvT.bot, covWEtaNat_fn_graph_action n []⟩,
    ⟨covWEtaNat_expand_graph n [] EnvT.bot, covWEtaNat_expand_graph_action n []⟩,
    ⟨covWEtaNat_beta_source n [] EnvT.bot, covWEtaNat_beta_source_action n⟩,
    ⟨covWEtaNat_let_source n [] EnvT.bot, covWEtaNat_let_source_action n⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_NAT_ADEQUACY_ROOTS
#print axioms covWEtaNat_fn_graph_action
#print axioms covWEtaNat_expand_graph_action
#print axioms covWEtaNat_graph_zero_action
#print axioms covWEtaNat_beta_source_action
#print axioms covWEtaNat_let_source_action
#print axioms covWEtaNat_local_guarded_actions
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_NAT_ADEQUACY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
