import rcic.RcicNativeTypedModelCovPropagation
import rcic.RcicNativeTypedModelKIndexFree
import rcic.RcicNativePiProbeRelApp

/-! A joint nonbottom inhabitant of the beta adapter's complete input package.
The target is a closed sort, whose full `FundTyAt` transfers through the
imported K-free equivalence.  No Eq context-model laws or global Fundamental
case are supplied.  The Eq-gap target diagonal remains open. `closure_claim = 0`. -/

namespace Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelKIndexFreeAudit TypedModelKFailureAudit ReadbackCKAudit ReadbackCK2Audit
open PiProbeRelAppAudit TypedModelCovPropagationAudit

def sortBetaSrc : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)

theorem approxTK_sortBeta_contract {E : ResolvedEnv} {n : Nat} {ρ : EnvT} {c : CptT}
    (h : ApproxTK E n [] ρ sortBetaSrc c) : ApproxTK E n [] ρ (.sort .zero) c := by
  rcases approxTK_app_inv h with hbot | ⟨g, s, hec, hf, hs, _⟩ |
    ⟨r, args, u, _, hf, _⟩ | hsat
  · rw [hbot]; exact .bot _ _ _
  · rcases approxTK_lam_inv hf with hbot | ⟨a, g', he, _, _, hb⟩
    · exact CptT.noConfusion hbot
    · injection he with hg
      subst g'
      rcases approxTK_sort_inv (hb s hs).2 with hbot | hsort
      · rw [hec, hbot]; exact .bot _ _ _
      · rw [hec, hsort]; exact approxTK_sort_code E n [] ρ .zero
  · rcases approxTK_lam_inv hf with hbot | ⟨a, g, he, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion he
  · exact (not_saturatedComputationTK_of_nonconst_head
      (fun _ _ he => Expr.noConfusion he) hsat).elim

def SortBetaAdapterWitnessT (E : ResolvedEnv) (n : Nat) : Prop :=
  Nonempty (EnvWfT E) ∧ Nonempty (CtxWfT E n []) ∧
  Nonempty (HasTyT E n [] sortBetaSrc (.sort (.succ .zero))) ∧
  Nonempty (ConvT E n [] sortBetaSrc (.sort .zero) (.sort (.succ .zero))) ∧
  ReadbackLaws E (WhStepCK2 E n) ∧
  (∀ ρ c, ApproxTK E n [] ρ sortBetaSrc c → ApproxTK E n [] ρ (.sort .zero) c) ∧
  FundTyAt (ctxModelT_approxTK E n []) (WhStepCK2 E n) n []
    (.sort .zero) (.sort (.succ .zero)) ∧
  FundConvAt (ctxModelT_approxTK E n []) (WhStepCK2 E n) n []
    sortBetaSrc (.sort .zero) (.sort (.succ .zero)) ∧
  (∀ ρ, ApproxTK E n [] ρ sortBetaSrc .prop ∧
    ApproxTK E n [] ρ (.sort .zero) .prop) ∧
  LRSCoreS (WhStepCK2 E n) E n [] sortBetaSrc (.sort .zero)
    (.sort (.succ .zero)) .prop ∧ (.prop : CptT) ≠ .bot

theorem sortBetaAdapterWitnessT (E : ResolvedEnv) (n : Nat) (hW : EnvWfT E) :
    SortBetaAdapterWitnessT E n := by
  have hL := readbackLaws_whStepCK2 E n
  have htarget : FundTyAt (ctxModelT_approxTK E n []) (WhStepCK2 E n) n []
      (.sort .zero) (.sort (.succ .zero)) :=
    (fundTyAt_approxTK_iff_of_kFree (Ξ := []) (Γ := [])
      (fun i v h => by simp [lookupValue] at h) (kFreeT_sort E .zero)).mpr
      (fundT_sort (ctxModelTLaws_approxT E) .zero)
  have hpres := fun ρ c => @approxTK_sortBeta_contract E n ρ c
  have hconv : FundConvAt (ctxModelT_approxTK E n []) (WhStepCK2 E n) n []
      sortBetaSrc (.sort .zero) (.sort (.succ .zero)) :=
    fundConvAt_beta_of_model_contractT hL (D := .sort (.succ .zero))
      (body := .sort .zero) (arg := .sort .zero) hpres htarget
  have hbeta : ConvT E n [] sortBetaSrc (.sort .zero) (.sort (.succ .zero)) :=
    .beta [] (.sort (.succ .zero)) (.sort .zero) (.sort .zero)
      (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort _ _) (.sort _ _) (.sort _ _)
  have hfree : KFreeT E sortBetaSrc :=
    kFreeT_app (kFreeT_lam (kFreeT_sort E _) (kFreeT_sort E _)) (kFreeT_sort E _)
  have hprop : ∀ ρ, ApproxTK E n [] ρ sortBetaSrc .prop := fun ρ =>
    .free hfree (approxT_app_empty_demand (fun h => CptT.noConfusion h)
      (approxT_sort_code E _ .zero))
  refine ⟨⟨hW⟩, ⟨.nil⟩, ⟨(convEnds hW .nil hbeta).1⟩, ⟨hbeta⟩,
    hL, hpres, htarget, hconv, fun ρ => ⟨hprop ρ, approxTK_sort_code E n [] ρ .zero⟩,
    ?_, fun h => CptT.noConfusion h⟩
  have h := hconv .nil (relSubstIdT_nil_probe _ EnvT.bot) .prop (Or.inl (hprop EnvT.bot))
  simpa only [substT_id] using h

theorem eq_nat_sortBetaAdapterWitnessT (n : Nat) :
    SortBetaAdapterWitnessT eqEnvT n ∧ SortBetaAdapterWitnessT natEnvU n :=
  ⟨sortBetaAdapterWitnessT eqEnvT n pinEqGroupWfT,
    sortBetaAdapterWitnessT natEnvU n natEnvUWfT⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_ADAPTER_WITNESS_ROOTS
#print axioms sortBetaSrc
#print axioms approxTK_sortBeta_contract
#print axioms SortBetaAdapterWitnessT
#print axioms sortBetaAdapterWitnessT
#print axioms eq_nat_sortBetaAdapterWitnessT
-- END RCIC_NATIVE_TYPED_MODEL_COV_ADAPTER_WITNESS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovAdapterWitnessAudit
