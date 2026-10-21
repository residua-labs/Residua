import rcic.RcicNativeTypedModelCovNormApp

/-!
# An inhabited saturated application premise at the typed Nat.rec pin

The existing source observation is used only for the source certificate in
`SaturatedComputationTK`. The required right-hand-side observation is built
separately, and the resulting source observation is then obtained through
`approxTK_of_saturated`. Native source and target typings are imported from
the admitted Nat pin. The actual iota step and the core relation at its
reduct are both exhibited. No global saturated-arm supplier is assumed.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormSaturatedControlAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open ReadbackCKAudit ReadbackCK2Audit
open TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit
open TypedModelCovRelBoundaryAudit TypedModelCovNormCov2Audit
open TypedModelCovNormAppAudit

/-- Both arguments of the concrete step minor have empty demand. The
imported bottom-demand lambda characterization supplies its actual code. -/
theorem approxTK_natRec_good_rhs (ρ : EnvT) :
    ApproxTK natEnvU 1 [] ρ (iotaRhsOf wSuccU1) (.spine 1 []) := by
  apply ApproxTK.free (kFreeT_natEnvU _)
  have hminor : ApproxT natEnvU ρ natMinorS covGoodHsCpt := by
    apply (approxT_lam_botDemand_iff (g := [([], .lam [([], .spine 1 [])])])
      (by simp [BotDemandT])).mpr
    refine ⟨⟨([], .lam [([], .spine 1 [])]), List.mem_singleton.mpr rfl,
      fun h => CptT.noConfusion h⟩, ?_⟩
    intro s hs
    obtain rfl := List.mem_singleton.mp hs
    apply (approxT_lam_botDemand_iff (g := [([], .spine 1 [])])
      (by simp [BotDemandT])).mpr
    refine ⟨⟨([], .spine 1 []), List.mem_singleton.mpr rfl,
      fun h => CptT.noConfusion h⟩, ?_⟩
    intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .const _ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero
  have hfirst : ApproxT natEnvU ρ (.app natMinorS natField)
      (.lam [([], .spine 1 [])]) :=
    .app hminor (List.mem_singleton.mpr rfl)
      (fun _ h => (List.not_mem_nil _ h).elim)
  exact .app hfirst (List.mem_singleton.mpr rfl)
    (fun _ h => (List.not_mem_nil _ h).elim)

/-- The structured witness is the imported upgrade of the typed pin, so
both syntax equalities use its landed adapters. -/
theorem saturatedComputationTK_natRec_good_call (ρ : EnvT) :
    SaturatedComputationTK natEnvU 1 [] ρ (iotaLhsOf wSuccU1) (.spine 1 []) := by
  have hleft : iotaLhsOfS wSuccU1S = iotaLhsOf wSuccU1 :=
    iotaLhsOfS_iotaWitnessSOf wSuccU1 64 pin_iotaWitnessSB_wSuccU1
  have hright : iotaRhsOfS wSuccU1S = iotaRhsOf wSuccU1 :=
    iotaRhsOfS_iotaWitnessSOf wSuccU1 64 pin_iotaWitnessSB_wSuccU1
  refine Or.inl ⟨wSuccU1S, hleft.symm, ?_, ?_⟩
  · rw [hleft]
    exact approxTK_forget (approxTK_natRec_good_call ρ)
  · rw [hright]
    exact approxTK_natRec_good_rhs ρ

/-- This source observation is derived through the saturated computation
constructor using the independently established right-hand side. -/
theorem approxTK_natRec_good_call_saturated (ρ : EnvT) :
    ApproxTK natEnvU 1 [] ρ (iotaLhsOf wSuccU1) (.spine 1 []) :=
  approxTK_of_saturated (saturatedComputationTK_natRec_good_call ρ)

/-- Cancel the actual first iota step from the imported reduction to zero
using the landed strip theorem and CK2 determinism. -/
theorem redR_natRec_good_rhs :
    RedR (WhStepCK2 natEnvU 1) [] (iotaRhsOf wSuccU1) (.const 1 []) := by
  have hd : DiamondR (WhStepCK2 natEnvU 1) :=
    fun Δ _ _ _ h₁ h₂ => Or.inl (detR_whStepCK2 natEnvUWfT Δ h₁ h₂)
  obtain ⟨d, hrhs, hzero⟩ := redR_strip hd
    (WhStepCK2.ctx (WhStepCtx.iota (DerivedIotaU.ofU wSuccU1)))
    redR_natRec_good_call
  have hn := normalR_ctorSpineCK2 (n := 1) natEnvUWfT
    (rfl : natEnvU.members 1 = some natZeroMember) rfl [] [] []
  obtain rfl := redR_of_normal hn hzero
  exact hrhs

/-- The demanded right-hand-side core relation is proved at the actual
non-bottom result, with no motive for a generated derivation assumed. -/
theorem lrSCoreCov_natRec_good_rhs (C : CovTyping natEnvU) :
    LRSCoreCov C (WhStepCK2 natEnvU 1) 1 []
      (iotaRhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 []) (.spine 1 []) :=
  lrSCoreCov_expand_red_both C (readbackLaws_whStepCK2 natEnvU 1)
    redR_natRec_good_rhs redR_natRec_good_rhs (.spine 1 [])
    (lrSCoreCov_natZero_spine C 1 [])

/-- The same compact relates the native iota endpoints, each expanded from
the existing zero constructor leaf. -/
theorem lrSCoreCov_natRec_good_iota (C : CovTyping natEnvU) :
    LRSCoreCov C (WhStepCK2 natEnvU 1) 1 []
      (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 []) (.spine 1 []) :=
  lrSCoreCov_expand_red_both C (readbackLaws_whStepCK2 natEnvU 1)
    redR_natRec_good_call redR_natRec_good_rhs (.spine 1 [])
    (lrSCoreCov_natZero_spine C 1 [])

/-- Both premises of the native conversion constructor are the actual
imported source and preserved target typing derivations. -/
theorem convT_natRec_good_iota :
    Nonempty (ConvT natEnvU 1 [] (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 [])) := by
  obtain ⟨hrhs⟩ := pin_iotaPreserveT
  exact ⟨.iota [] _ _ _ (.of wSuccU1) pinIotaLhsTy hrhs⟩

/-- The saturated antecedent, actual single-step reduct, non-bottom RHS
relation, native endpoints and all model guards coexist in `natEnvU`. -/
theorem natRec_good_saturated_C2_control (ρ : EnvT) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU 1 []) ∧
    Nonempty (HasTyT natEnvU 1 [] (iotaLhsOf wSuccU1) (.const 0 [])) ∧
    Nonempty (HasTyT natEnvU 1 [] (iotaRhsOf wSuccU1) (.const 0 [])) ∧
    Nonempty (ConvT natEnvU 1 [] (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 [])) ∧
    EnvTypedCovAtP (C2 natEnvU) (ctxModelT_approxTK natEnvU 1 []) [] ρ ∧
    SaturatedComputationTK natEnvU 1 [] ρ (iotaLhsOf wSuccU1) (.spine 1 []) ∧
    ApproxTK natEnvU 1 [] ρ (iotaLhsOf wSuccU1) (.spine 1 []) ∧
    ApproxTK natEnvU 1 [] ρ (iotaRhsOf wSuccU1) (.spine 1 []) ∧
    ApproxTK natEnvU 1 [] ρ (.const 0 []) (.spine 0 []) ∧
    (C2 natEnvU).ty (.spine 1 []) (.spine 0 []) ∧
    WhStepCK2 natEnvU 1 [] (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) ∧
    LRSCoreCov (C2 natEnvU) (WhStepCK2 natEnvU 1) 1 []
      (iotaRhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 []) (.spine 1 []) ∧
    LRSCoreCov (C2 natEnvU) (WhStepCK2 natEnvU 1) 1 []
      (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 []) (.spine 1 []) ∧
    (.spine 1 [] : CptT) ≠ .bot ∧ (.spine 0 [] : CptT) ≠ .bot := by
  obtain ⟨_, _, _, _, _, hNat, hty, _, hne, hneNat⟩ := natRec_covRel_control_approxTK ρ
  exact ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, ⟨pinIotaLhsTy⟩, pin_iotaPreserveT,
    convT_natRec_good_iota, envTypedCovAtP_nil (C2 natEnvU) _ ρ,
    saturatedComputationTK_natRec_good_call ρ, approxTK_natRec_good_call_saturated ρ,
    approxTK_natRec_good_rhs ρ, hNat, ctyCov2_of_ctyCov _ _ hty,
    .ctx (.iota (.ofU wSuccU1)), lrSCoreCov_natRec_good_rhs (C2 natEnvU),
    lrSCoreCov_natRec_good_iota (C2 natEnvU), hne, hneNat⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_SATURATED_CONTROL_ROOTS
#print axioms approxTK_natRec_good_rhs
#print axioms saturatedComputationTK_natRec_good_call
#print axioms approxTK_natRec_good_call_saturated
#print axioms redR_natRec_good_rhs
#print axioms lrSCoreCov_natRec_good_rhs
#print axioms lrSCoreCov_natRec_good_iota
#print axioms convT_natRec_good_iota
#print axioms natRec_good_saturated_C2_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_SATURATED_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormSaturatedControlAudit
