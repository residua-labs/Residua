import rcic.RcicNativeTypedModelCovYMeasure
import rcic.RcicNativeTypedModelCovXEtaObserved

/-!
# A common finite type code for every observed successor eta compact

The declared Nat arrow observes the empty-demand row `[] -> Nat`.
Unlike the earlier `[Nat] -> Nat` code, this row is available at every
application demand. It types both the rigid successor compact and every
lambda table observed only at its eta expansion. This is an actual observed
type code; no compact typing or coverage assumption is supplied by a caller.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKTransportAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovXEtaAudit

/-- One actual empty-demand Nat codomain row, with the actual Nat domain. -/
def covYNatArrowCode : CptT := .pi (.spine 0 []) [([], .spine 0 [])]

/-- The singleton codomain is a non-proposition Nat code. -/
theorem covYNatArrowCode_not_prop : ¬ IsPropCT natEnvU covYNatArrowCode := by
  simpa only [covYNatArrowCode, covXNatRows, List.map_cons, List.map_nil] using
    (covXNatRows_not_prop (g := [([], .spine 0 [])])
      ⟨([], .spine 0 []), List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩)

/-- The complete code is observed at the declared arrow in every actual
frozen native context and every valuation. -/
theorem approxTK_covYNatArrowCode (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) covYNatArrowCode := by
  refine ApproxTK.pi
    (ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil _ hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)

theorem approxT_covYNatArrowCode (ρ : EnvT) :
    ApproxT natEnvU ρ (.pi (.const 0 []) (.const 0 [])) covYNatArrowCode :=
  approxTK_forget (approxTK_covYNatArrowCode 0 [] ρ)

/-- The rigid C2 branch obtains its gate from the actual declared-type
observation. No new rigid-member typing rule is introduced. -/
theorem covY_natSucc_code_typed :
    (C2 natEnvU).ty (.spine 2 []) covYNatArrowCode :=
  ctyCov2_natSucc_spine (approxT_covYNatArrowCode EnvT.bot) covYNatArrowCode_not_prop

/-- Every actual eta-left table is typed by this same code. Its annotation
demands and output shapes come from the imported full observation inversion. -/
theorem covY_natSucc_eta_code_typed {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTK natEnvU n Γ ρ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c) :
    (C2 natEnvU).ty c covYNatArrowCode := by
  rcases covX_natSucc_eta_observation h with rfl |
    ⟨a, g, rfl, hA, _, hdemands, houtputs⟩
  · exact (C2 natEnvU).bot _
  · change CTyCov2 natEnvU (.lam g) covYNatArrowCode
    rw [covYNatArrowCode, CTyCov2]
    refine ⟨covYNatArrowCode_not_prop, ?_, ?_⟩
    · intro s hs u hu
      exact ctyCov2_of_ctyS (covX_nat_annotation_demands hA (hdemands s hs u hu))
    · intro s hs
      rcases houtputs s hs with hb | ⟨u, he⟩
      · exact Or.inl hb
      · refine Or.inr ⟨([], .spine 0 []), List.mem_singleton.mpr rfl,
          fun v hv => (List.not_mem_nil _ hv).elim, ?_⟩
        rw [he, CTyCov2]
        exact Or.inr ⟨⟨2, [u], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

/-- A single actual code types every compact observed at either native eta
endpoint, including lambda tables absent from the rigid endpoint's model. -/
theorem covY_natSucc_eta_or_code_typed (n : Nat) (Γ : LCtx) (ρ ρ' : EnvT)
    (c : CptT)
    (h : ApproxTK natEnvU n Γ ρ
        (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c ∨
      ApproxTK natEnvU n Γ ρ' (.const 2 []) c) :
    (C2 natEnvU).ty c covYNatArrowCode := by
  rcases h with h | h
  · exact covY_natSucc_eta_code_typed h
  · rcases approxT_rigid_const_inv rigidConst_natEnvU_succ
        (approxTK_forget h) with rfl | rfl
    · exact (C2 natEnvU).bot _
    · exact covY_natSucc_code_typed

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_ETA_CODE_ROOTS
#print axioms covYNatArrowCode
#print axioms covYNatArrowCode_not_prop
#print axioms approxTK_covYNatArrowCode
#print axioms approxT_covYNatArrowCode
#print axioms covY_natSucc_code_typed
#print axioms covY_natSucc_eta_code_typed
#print axioms covY_natSucc_eta_or_code_typed
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_ETA_CODE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYEtaAudit
