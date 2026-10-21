import rcic.RcicNativeTypedModelCovWNativeFixtures
import rcic.RcicNativeTypedModelCovWIrrelNat
import rcic.RcicNativeTypedModelCovWEtaNat

/-! # The Nat eta, beta and let controls with proof-field erasure
All observations are supplied directly. Raw remains strict; the shared
successor graph uses typed eta in the guarded grammar. closure_claim = 0. -/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelCovWIrrelAudit
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKFragmentAudit TypedModelCovWTypedAudit TypedModelCovWEtaAudit
open TypedModelCovTAudit ReadbackCKAudit ReadbackCK2Audit

def covWNativeNatGraph : CptWIrrel := .lam [([.bot], .spine 2 [] [.bot])]
def covWNativeNatGraphType : CptWIrrel := .pi (.spine 0 [] []) [([.bot], .spine 0 [] [])]
def covWNativeNatResult : CptWIrrel := .spine 2 [] [.bot]

theorem covWNativeNat_type_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ covWEtaNatArrow covWNativeNatGraphType := by
  refine .pi (covWNative_nat_observed n Γ ρ) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWNative_nat_observed n _ _

theorem covWNativeNat_fn_graph (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ covWEtaNatFn covWNativeNatGraph := by
  refine .eta (covWEtaNatFn_ty n Γ) (covWNative_nat_observed n Γ ρ) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWNative_guarded_appSpine_bot
      (covWEtaNatFn_ty n (.assumption (.const 0 []) :: Γ)) (.bvar _ 0 _ rfl) (covWNative_succ_observed n _ _)

theorem covWNativeNat_expand_graph (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ covWEtaNatExpand covWNativeNatGraph := by
  refine .lam (covWNative_nat_observed n Γ ρ) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWNative_guarded_appSpine_bot
      (covWEtaNatFn_ty n (.assumption (.const 0 []) :: Γ)) (.bvar _ 0 _ rfl) (covWNative_succ_observed n _ _)

theorem covWNativeNat_graph_typed :
    CTyS natEnvU (covWIrrelErase covWNativeNatGraph) (covWIrrelErase covWNativeNatGraphType) :=
  covWEtaNat_graph_typed

theorem covWNativeNat_shared_graph (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    Nonempty (HasTyT natEnvU n Γ covWEtaNatFn covWEtaNatArrow) ∧
    Nonempty (HasTyT natEnvU n Γ covWEtaNatExpand covWEtaNatArrow) ∧
    Nonempty (ConvT natEnvU n Γ covWEtaNatExpand covWEtaNatFn covWEtaNatArrow) ∧
    ApproxTKWNative natEnvU n Γ ρ covWEtaNatArrow covWNativeNatGraphType ∧
    CTyS natEnvU (covWIrrelErase covWNativeNatGraph) (covWIrrelErase covWNativeNatGraphType) ∧
    ApproxTKWNative natEnvU n Γ ρ covWEtaNatFn covWNativeNatGraph ∧
    ApproxTKWNative natEnvU n Γ ρ covWEtaNatExpand covWNativeNatGraph :=
  ⟨⟨covWEtaNatFn_ty n Γ⟩, ⟨covWEtaNatExpand_ty n Γ⟩, ⟨covWEtaNat_contract n Γ⟩,
    covWNativeNat_type_observed n Γ ρ, covWNativeNat_graph_typed,
    covWNativeNat_fn_graph n Γ ρ, covWNativeNat_expand_graph n Γ ρ⟩

theorem covWNativeNat_beta_source (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ covWTypedBetaNatSource covWNativeNatResult := by
  refine .app (g := [([covWNativeNatGraph], covWNativeNatResult)])
    (s := ([covWNativeNatGraph], covWNativeNatResult)) ?_ (List.mem_singleton.mpr rfl) ?_
  · refine .lam (covWNativeNat_type_observed n Γ ρ) ?_ ?_ ?_
    · intro s hs u hu
      obtain rfl := List.mem_singleton.mp hs
      obtain rfl := List.mem_singleton.mp hu
      exact covWNativeNat_graph_typed
    · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptWIrrel.noConfusion h⟩
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      refine .app (g := [([.bot], .spine 2 [] [.bot])])
        (s := ([.bot], .spine 2 [] [.bot]))
        (.bvar (List.mem_singleton.mpr rfl))
        (List.mem_singleton.mpr rfl) ?_
      intro u hu
      obtain rfl := List.mem_singleton.mp hu
      exact .bot _ _ _
  · intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact covWNativeNat_fn_graph n Γ ρ

theorem covWNativeNat_let_source (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative natEnvU n Γ ρ covWTypedBetaNatLet covWNativeNatResult :=
  .letE (covWNativeNat_beta_source n Γ ρ)

theorem covWNativeNat_beta_let_repaired (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    CovWNativeRealized natEnvU n 3 [] EnvWIrrel.bot SubstT.id ∧
    Nonempty (HasTyT natEnvU n [] covWTypedBetaNatSource (.const 0 [])) ∧
    Nonempty (HasTyT natEnvU n [] covWTypedBetaNatLet (.const 0 [])) ∧
    Nonempty (HasTyT natEnvU n [] covWTypedBetaNatTarget (.const 0 [])) ∧
    WhStepCK2 natEnvU n [] covWTypedBetaNatSource covWTypedBetaNatTarget ∧
    WhStepCK2 natEnvU n [] covWTypedBetaNatLet covWTypedBetaNatTarget ∧
    CTyS natEnvU (covWIrrelErase covWNativeNatResult) (.spine 0 []) ∧
    ApproxTKWNative natEnvU n [] EnvWIrrel.bot (.const 0 []) (.spine 0 [] []) ∧
    ApproxTKWNative natEnvU n [] EnvWIrrel.bot covWTypedBetaNatSource covWNativeNatResult ∧
    ApproxTKWNative natEnvU n [] EnvWIrrel.bot covWTypedBetaNatLet covWNativeNatResult ∧
    ApproxTKWNative natEnvU n [] EnvWIrrel.bot covWTypedBetaNatTarget covWNativeNatResult :=
  ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, covWNative_realized_nil natEnvU n 3,
    ⟨covWTypedBetaNatSource_ty n⟩, ⟨covWTypedBetaNatLet_ty n⟩,
    ⟨covWTypedBetaNatTarget_ty n⟩, covWTypedBetaNat_step n,
    covWTypedBetaNat_let_step n, covWTypedBetaNat_compact_typed,
    covWNative_nat_observed n _ _, covWNativeNat_beta_source n _ _,
    covWNativeNat_let_source n _ _,
    covWNative_guarded_appSpine_bot (covWEtaNatFn_ty n _)
      (hasTyT_natEnvU_zero n _) (covWNative_succ_observed n _ _)⟩

theorem covWNativeNat_same_stage (n : Nat) :
    ApproxTKWNativeStage natEnvU n 3 [] EnvWIrrel.bot covWEtaNatFn covWNativeNatGraph ∧
    ApproxTKWNativeStage natEnvU n 3 [] EnvWIrrel.bot covWEtaNatExpand covWNativeNatGraph ∧
    ApproxTKWNativeStage natEnvU n 3 [] EnvWIrrel.bot covWEtaNatArrow covWNativeNatGraphType ∧
    ApproxTKWNativeStage natEnvU n 3 [] EnvWIrrel.bot covWTypedBetaNatSource covWNativeNatResult ∧
    ApproxTKWNativeStage natEnvU n 3 [] EnvWIrrel.bot covWTypedBetaNatLet covWNativeNatResult := by
  refine ⟨⟨covWNativeNat_fn_graph n _ _, ?_⟩, ⟨covWNativeNat_expand_graph n _ _, ?_⟩,
    ⟨covWNativeNat_type_observed n _ _, ?_⟩, ⟨covWNativeNat_beta_source n _ _, ?_⟩,
    ⟨covWNativeNat_let_source n _ _, ?_⟩⟩
  all_goals simp [covTObservationBudget, covWIrrelErase, covWIrrelEraseRows,
    covWIrrelEraseArgs, covWNativeNatGraph, covWNativeNatGraphType, covWNativeNatResult]

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_NAT_ROOTS
#print axioms covWNativeNatGraph
#print axioms covWNativeNatGraphType
#print axioms covWNativeNatResult
#print axioms covWNativeNat_type_observed
#print axioms covWNativeNat_fn_graph
#print axioms covWNativeNat_expand_graph
#print axioms covWNativeNat_graph_typed
#print axioms covWNativeNat_shared_graph
#print axioms covWNativeNat_beta_source
#print axioms covWNativeNat_let_source
#print axioms covWNativeNat_beta_let_repaired
#print axioms covWNativeNat_same_stage
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_NAT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
