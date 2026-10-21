import rcic.RcicNativeTypedModelCovWEtaAligned
import rcic.RcicNativeTypedModelCovWEtaBoundary

/-!
# The concrete Nat eta, beta and let repairs

The rigid successor and its native eta expansion now share the exact same
strictly typed graph.  That graph is the finite demand used at the function
binder of the landed beta and let counterexamples.  All native evidence,
domain-code observations and demand typing are actual supplies.
The raw relation is unchanged; these are new guarded observations.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKFragmentAudit TypedModelCovWAudit TypedModelCovWTypedAudit
open TypedModelCovTAudit TypedModelCovXAudit ReadbackCKAudit ReadbackCK2Audit
open TypedModelAudit.TypingFin

/-- The eta introduction is used at successor's actual native Nat domain. -/
theorem covWEtaNat_fn_graph (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta natEnvU n Γ ρ covWEtaNatFn covWEtaNatGraph := by
  apply ApproxTKWEta.eta (covWEtaNatFn_ty n Γ)
    (covWEta_of_old (covWTypedBetaNat_type_observed n Γ ρ))
  · intro s hs u hu
    have hs' : s = ([.bot], .spine 2 [.bot]) := List.mem_singleton.mp hs
    subst s
    have hu' : u = .bot := List.mem_singleton.mp hu
    subst u
    exact ctyS_bot _
  · exact ⟨([.bot], .spine 2 [.bot]), by simp, CptT.noConfusion⟩
  · intro s hs
    have hs' : s = ([.bot], .spine 2 [.bot]) := List.mem_singleton.mp hs
    subst s
    exact .free (kFreeT_natEnvU _)
      (.appSpine (.const _ 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ)
        (.bot _ _))

theorem covWEtaNat_expand_graph (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta natEnvU n Γ ρ covWEtaNatExpand covWEtaNatGraph :=
  covWEta_of_old (covWEtaNat_expand_guarded n Γ ρ)

/-- Both terms use one actual observed arrow code and one strictly typed graph. -/
theorem covWEtaNat_shared_graph (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    Nonempty (HasTyT natEnvU n Γ covWEtaNatFn covWEtaNatArrow) ∧
    Nonempty (HasTyT natEnvU n Γ covWEtaNatExpand covWEtaNatArrow) ∧
    Nonempty (ConvT natEnvU n Γ covWEtaNatExpand covWEtaNatFn covWEtaNatArrow) ∧
    ApproxTKWEta natEnvU n Γ ρ covWEtaNatArrow covWEtaNatArrowCode ∧
    CTyS natEnvU covWEtaNatGraph covWEtaNatArrowCode ∧
    ApproxTKWEta natEnvU n Γ ρ covWEtaNatFn covWEtaNatGraph ∧
    ApproxTKWEta natEnvU n Γ ρ covWEtaNatExpand covWEtaNatGraph :=
  ⟨⟨covWEtaNatFn_ty n Γ⟩, ⟨covWEtaNatExpand_ty n Γ⟩,
    ⟨covWEtaNat_contract n Γ⟩, covWEta_of_old (covWEtaNat_arrow_guarded n Γ ρ),
    covWEtaNat_graph_typed, covWEtaNat_fn_graph n Γ ρ, covWEtaNat_expand_graph n Γ ρ⟩

/-- The previously unavailable graph is the single finite demand of f. -/
theorem covWEtaNat_beta_source (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta natEnvU n Γ ρ covWTypedBetaNatSource covWTypedBetaNatCpt := by
  apply ApproxTKWEta.app (g := [([covWEtaNatGraph], covWTypedBetaNatCpt)])
    (s := ([covWEtaNatGraph], covWTypedBetaNatCpt))
  · apply ApproxTKWEta.lam (a := covWEtaNatArrowCode)
      (covWEta_of_old (covWEtaNat_arrow_guarded n Γ ρ))
    · intro s hs u hu
      have hs' : s = ([covWEtaNatGraph], covWTypedBetaNatCpt) :=
        List.mem_singleton.mp hs
      subst s
      have hu' : u = covWEtaNatGraph := List.mem_singleton.mp hu
      subst u
      exact covWEtaNat_graph_typed
    · exact ⟨([covWEtaNatGraph], covWTypedBetaNatCpt), by simp,
        covWTypedBetaNat_nonbottom⟩
    · intro s hs
      have hs' : s = ([covWEtaNatGraph], covWTypedBetaNatCpt) :=
        List.mem_singleton.mp hs
      subst s
      apply ApproxTKWEta.app (g := [([.bot], .spine 2 [.bot])])
        (s := ([.bot], .spine 2 [.bot]))
      · exact .free (kFreeT_natEnvU _) (.bvar (by
          change covWEtaNatGraph ∈ [covWEtaNatGraph]
          simp))
      · simp
      · intro u hu
        have hu' : u = .bot := List.mem_singleton.mp hu
        subst u
        exact .bot _ _ _
  · simp
  · intro u hu
    have hu' : u = covWEtaNatGraph := List.mem_singleton.mp hu
    subst u
    exact covWEtaNat_fn_graph n Γ ρ

theorem covWEtaNat_let_source (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKWEta natEnvU n Γ ρ covWTypedBetaNatLet covWTypedBetaNatCpt :=
  .letE (covWEtaNat_beta_source n Γ ρ)

/-- Both actual native steps now preserve the displayed typed observation
backwards. This is a local supply, not a general expansion theorem. -/
theorem covWEtaNat_beta_let_repaired (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    CovWEtaRealized natEnvU n 3 [] EnvT.bot SubstT.id ∧
    Nonempty (HasTyT natEnvU n [] covWTypedBetaNatSource (.const 0 [])) ∧
    Nonempty (HasTyT natEnvU n [] covWTypedBetaNatLet (.const 0 [])) ∧
    Nonempty (HasTyT natEnvU n [] covWTypedBetaNatTarget (.const 0 [])) ∧
    WhStepCK2 natEnvU n [] covWTypedBetaNatSource covWTypedBetaNatTarget ∧
    WhStepCK2 natEnvU n [] covWTypedBetaNatLet covWTypedBetaNatTarget ∧
    CTyS natEnvU covWTypedBetaNatCpt (.spine 0 []) ∧
    ApproxTKWEta natEnvU n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    ApproxTKWEta natEnvU n [] EnvT.bot covWTypedBetaNatSource covWTypedBetaNatCpt ∧
    ApproxTKWEta natEnvU n [] EnvT.bot covWTypedBetaNatLet covWTypedBetaNatCpt ∧
    ApproxTKWEta natEnvU n [] EnvT.bot covWTypedBetaNatTarget covWTypedBetaNatCpt :=
  ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, covWEta_realized_nil natEnvU n 3,
    ⟨covWTypedBetaNatSource_ty n⟩, ⟨covWTypedBetaNatLet_ty n⟩,
    ⟨covWTypedBetaNatTarget_ty n⟩, covWTypedBetaNat_step n,
    covWTypedBetaNat_let_step n, covWTypedBetaNat_compact_typed,
    covWEta_of_old (covWTypedBetaNat_type_observed n [] EnvT.bot),
    covWEtaNat_beta_source n [] EnvT.bot, covWEtaNat_let_source n [] EnvT.bot,
    covWEta_of_old (covWTypedBetaNat_target_observed n [] EnvT.bot)⟩

theorem covWEtaNat_same_stage_repaired (n : Nat) :
    ApproxTKWEtaStage natEnvU n 3 [] EnvT.bot covWEtaNatFn covWEtaNatGraph ∧
    ApproxTKWEtaStage natEnvU n 3 [] EnvT.bot covWEtaNatExpand covWEtaNatGraph ∧
    ApproxTKWEtaStage natEnvU n 3 [] EnvT.bot covWEtaNatArrow covWEtaNatArrowCode ∧
    ApproxTKWEtaStage natEnvU n 3 [] EnvT.bot covWTypedBetaNatSource covWTypedBetaNatCpt ∧
    ApproxTKWEtaStage natEnvU n 3 [] EnvT.bot covWTypedBetaNatLet covWTypedBetaNatCpt := by
  refine ⟨⟨covWEtaNat_fn_graph n [] EnvT.bot, ?_⟩,
    ⟨covWEtaNat_expand_graph n [] EnvT.bot, ?_⟩,
    ⟨covWEta_of_old (covWEtaNat_arrow_guarded n [] EnvT.bot), ?_⟩,
    ⟨covWEtaNat_beta_source n [] EnvT.bot, ?_⟩,
    ⟨covWEtaNat_let_source n [] EnvT.bot, ?_⟩⟩
  all_goals simp [covTObservationBudget, covWEtaNatGraph, covWEtaNatArrowCode,
    covWTypedBetaNatCpt]

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_NAT_ROOTS
#print axioms covWEtaNat_fn_graph
#print axioms covWEtaNat_expand_graph
#print axioms covWEtaNat_shared_graph
#print axioms covWEtaNat_beta_source
#print axioms covWEtaNat_let_source
#print axioms covWEtaNat_beta_let_repaired
#print axioms covWEtaNat_same_stage_repaired
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_NAT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
