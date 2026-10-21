import rcic.RcicNativeTypedModelCovWIrrelFixtures
import rcic.RcicNativeTypedModelCovWEtaNat

/-! # The Nat eta, beta and let controls with proof-field erasure
All observations are supplied directly. Raw remains strict; the shared
successor graph uses typed eta in the guarded grammar. closure_claim = 0. -/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKFragmentAudit TypedModelCovWTypedAudit TypedModelCovWEtaAudit
open TypedModelCovTAudit ReadbackCKAudit ReadbackCK2Audit

def covWIrrelNatGraph : CptWIrrel := .lam [([.bot], .spine 2 [] [.bot])]
def covWIrrelNatGraphType : CptWIrrel := .pi (.spine 0 [] []) [([.bot], .spine 0 [] [])]
def covWIrrelNatResult : CptWIrrel := .spine 2 [] [.bot]

theorem covWIrrelNat_type_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel natEnvU n Γ ρ covWEtaNatArrow covWIrrelNatGraphType := by
  refine .pi (covWIrrel_nat_observed n Γ ρ) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWIrrel_nat_observed n _ _

theorem covWIrrelNat_fn_graph (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel natEnvU n Γ ρ covWEtaNatFn covWIrrelNatGraph := by
  refine .eta (covWEtaNatFn_ty n Γ) (covWIrrel_nat_observed n Γ ρ) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWIrrel_guarded_appSpine_bot (covWIrrel_succ_observed n _ _)

theorem covWIrrelNat_expand_graph (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel natEnvU n Γ ρ covWEtaNatExpand covWIrrelNatGraph := by
  refine .lam (covWIrrel_nat_observed n Γ ρ) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWIrrel_guarded_appSpine_bot (covWIrrel_succ_observed n _ _)

theorem covWIrrelNat_graph_typed :
    CTyS natEnvU (covWIrrelErase covWIrrelNatGraph) (covWIrrelErase covWIrrelNatGraphType) :=
  covWEtaNat_graph_typed

theorem covWIrrelNat_shared_graph (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    Nonempty (HasTyT natEnvU n Γ covWEtaNatFn covWEtaNatArrow) ∧
    Nonempty (HasTyT natEnvU n Γ covWEtaNatExpand covWEtaNatArrow) ∧
    Nonempty (ConvT natEnvU n Γ covWEtaNatExpand covWEtaNatFn covWEtaNatArrow) ∧
    ApproxTKWIrrel natEnvU n Γ ρ covWEtaNatArrow covWIrrelNatGraphType ∧
    CTyS natEnvU (covWIrrelErase covWIrrelNatGraph) (covWIrrelErase covWIrrelNatGraphType) ∧
    ApproxTKWIrrel natEnvU n Γ ρ covWEtaNatFn covWIrrelNatGraph ∧
    ApproxTKWIrrel natEnvU n Γ ρ covWEtaNatExpand covWIrrelNatGraph :=
  ⟨⟨covWEtaNatFn_ty n Γ⟩, ⟨covWEtaNatExpand_ty n Γ⟩, ⟨covWEtaNat_contract n Γ⟩,
    covWIrrelNat_type_observed n Γ ρ, covWIrrelNat_graph_typed,
    covWIrrelNat_fn_graph n Γ ρ, covWIrrelNat_expand_graph n Γ ρ⟩

theorem covWIrrelNat_beta_source (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel natEnvU n Γ ρ covWTypedBetaNatSource covWIrrelNatResult := by
  refine .app (g := [([covWIrrelNatGraph], covWIrrelNatResult)])
    (s := ([covWIrrelNatGraph], covWIrrelNatResult)) ?_ (List.mem_singleton.mpr rfl) ?_
  · refine .lam (covWIrrelNat_type_observed n Γ ρ) ?_ ?_ ?_
    · intro s hs u hu
      obtain rfl := List.mem_singleton.mp hs
      obtain rfl := List.mem_singleton.mp hu
      exact covWIrrelNat_graph_typed
    · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      refine .app (g := [([.bot], .spine 2 [] [.bot])])
        (s := ([.bot], .spine 2 [] [.bot]))
        (.free (kFreeT_natEnvU _) (.bvar (List.mem_singleton.mpr rfl)))
        (List.mem_singleton.mpr rfl) ?_
      intro u hu
      obtain rfl := List.mem_singleton.mp hu
      exact .bot _ _ _
  · intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact covWIrrelNat_fn_graph n Γ ρ

theorem covWIrrelNat_let_source (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel natEnvU n Γ ρ covWTypedBetaNatLet covWIrrelNatResult :=
  .letE (covWIrrelNat_beta_source n Γ ρ)

theorem covWIrrelNat_beta_let_repaired (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    CovWIrrelRealized natEnvU n 3 [] EnvWIrrel.bot SubstT.id ∧
    Nonempty (HasTyT natEnvU n [] covWTypedBetaNatSource (.const 0 [])) ∧
    Nonempty (HasTyT natEnvU n [] covWTypedBetaNatLet (.const 0 [])) ∧
    Nonempty (HasTyT natEnvU n [] covWTypedBetaNatTarget (.const 0 [])) ∧
    WhStepCK2 natEnvU n [] covWTypedBetaNatSource covWTypedBetaNatTarget ∧
    WhStepCK2 natEnvU n [] covWTypedBetaNatLet covWTypedBetaNatTarget ∧
    CTyS natEnvU (covWIrrelErase covWIrrelNatResult) (.spine 0 []) ∧
    ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot (.const 0 []) (.spine 0 [] []) ∧
    ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot covWTypedBetaNatSource covWIrrelNatResult ∧
    ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot covWTypedBetaNatLet covWIrrelNatResult ∧
    ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot covWTypedBetaNatTarget covWIrrelNatResult :=
  ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, covWIrrel_realized_nil natEnvU n 3,
    ⟨covWTypedBetaNatSource_ty n⟩, ⟨covWTypedBetaNatLet_ty n⟩,
    ⟨covWTypedBetaNatTarget_ty n⟩, covWTypedBetaNat_step n,
    covWTypedBetaNat_let_step n, covWTypedBetaNat_compact_typed,
    covWIrrel_nat_observed n _ _, covWIrrelNat_beta_source n _ _,
    covWIrrelNat_let_source n _ _,
    covWIrrel_guarded_appSpine_bot (covWIrrel_succ_observed n _ _)⟩

theorem covWIrrelNat_same_stage (n : Nat) :
    ApproxTKWIrrelStage natEnvU n 3 [] EnvWIrrel.bot covWEtaNatFn covWIrrelNatGraph ∧
    ApproxTKWIrrelStage natEnvU n 3 [] EnvWIrrel.bot covWEtaNatExpand covWIrrelNatGraph ∧
    ApproxTKWIrrelStage natEnvU n 3 [] EnvWIrrel.bot covWEtaNatArrow covWIrrelNatGraphType ∧
    ApproxTKWIrrelStage natEnvU n 3 [] EnvWIrrel.bot covWTypedBetaNatSource covWIrrelNatResult ∧
    ApproxTKWIrrelStage natEnvU n 3 [] EnvWIrrel.bot covWTypedBetaNatLet covWIrrelNatResult := by
  refine ⟨⟨covWIrrelNat_fn_graph n _ _, ?_⟩, ⟨covWIrrelNat_expand_graph n _ _, ?_⟩,
    ⟨covWIrrelNat_type_observed n _ _, ?_⟩, ⟨covWIrrelNat_beta_source n _ _, ?_⟩,
    ⟨covWIrrelNat_let_source n _ _, ?_⟩⟩
  all_goals simp [covTObservationBudget, covWIrrelErase, covWIrrelEraseRows,
    covWIrrelEraseArgs, covWIrrelNatGraph, covWIrrelNatGraphType, covWIrrelNatResult]

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_NAT_ROOTS
#print axioms covWIrrelNatGraph
#print axioms covWIrrelNatGraphType
#print axioms covWIrrelNatResult
#print axioms covWIrrelNat_type_observed
#print axioms covWIrrelNat_fn_graph
#print axioms covWIrrelNat_expand_graph
#print axioms covWIrrelNat_graph_typed
#print axioms covWIrrelNat_shared_graph
#print axioms covWIrrelNat_beta_source
#print axioms covWIrrelNat_let_source
#print axioms covWIrrelNat_beta_let_repaired
#print axioms covWIrrelNat_same_stage
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_NAT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
