import rcic.RcicNativeTypedModelCovPFixtures
import rcic.RcicNativeTypedModelCovZWall4Control

/-!
# Repaired hereditary typing for the relevant-function alias pattern

The actual outer lambda action supplies its displayed row. The demanded
function's hereditary witness is composed from the landed relation at its
fixed inner code. No reverse typing law for arbitrary reflected neutral
functions is assumed. The unlanded #7776 fixture is imported only by the
separate exact replay. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKControlAudit ReadbackCK2Audit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovYAudit TypedModelCovZAudit

variable {E : ResolvedEnv}

theorem covP_transport_propArrow (reflect : Bool) :
    CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) covZPropArrowCode := by
  apply covP_transport_pi reflect
  · intro c h
    exact ctyCovP2_prop_iff.mp h
  · intro row hr c h
    obtain rfl := List.mem_singleton.mp hr
    exact ctyCovP2_prop_iff.mp h
  · exact covP_transport_prop reflect
  · intro row hr
    obtain rfl := List.mem_singleton.mp hr
    exact covP_transport_prop reflect

theorem covP_hereditary_sort_zero (reflect : Bool) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) {c : CptT} (ht : CTyCovP2 reflect E c .prop) :
    HereditaryCovRealizationPAt (CTyCovP2 reflect E)
      (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
      (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ (.sort .zero) c .prop := by
  apply hereditaryCovRealizationPAt_from_Y (C2 E) (CTyCovP2 reflect E)
    _ _ n Γ ρ (.sort .zero) c .prop (covP_transport_prop reflect)
  simpa only [sortCode_zero] using hereditaryCovRealizationYAt_sort (C2 E) n .zero
    (Γ := Γ) (ρ := ρ) (.refl _)
    (by simpa only [sortCode_zero] using ctyCovP2_prop_iff.mp ht)

theorem covP_relevant_app_coverage (reflect : Bool) :
    CovPActionCoverage E (CTyCovP2 reflect E)
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])])
      covZPropArrowCode [([.lam [([.bot], .pi .bot [])]], .prop)] := by
  intro ds out ha _
  cases ha with
  | bot => exact Or.inl rfl
  | app hs hx =>
      obtain rfl := List.mem_singleton.mp hs
      refine Or.inr ⟨([.lam [([.bot], .pi .bot [])]], .prop),
        List.mem_singleton_self _, ?_, ?_⟩
      · intro u hu
        obtain rfl := List.mem_singleton.mp hu
        exact approxT_bvar_inv (hx _ (List.mem_singleton_self _))
      · exact CTyCovP2.univProp (.pi .bot (by simp))

theorem covP_relevant_app_hereditary (reflect : Bool) (n : Nat)
    {Γ : LCtx} (ρ : EnvT) {D x y : Expr Nat}
    (hr : RedR (WhStepCK2 E n) Γ D (.pi (.sort .zero) (.sort .zero)))
    (hc : LRSCoreCovY (C2 E) (WhStepCK2 E n) n Γ x y (.pi D (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) covZRelevantAppCode) :
    HereditaryCovRealizationPAt (CTyCovP2 reflect E)
      (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
      (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ (.pi D (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) covZRelevantAppCode := by
  rw [HereditaryCovRealizationPAt.eq_def]
  refine ⟨ctyCovP2_of_ctyCov2 reflect _ _ (lrSCoreCovY_typing (C2 E) hc),
    Or.inr ⟨D, .sort .zero, .refl _, covP_relevant_app_coverage reflect, ?_⟩⟩
  intro ds out ha hnb row hrow hsel N N' hN hN' hconv hd
  obtain rfl := List.mem_singleton.mp hrow
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu
    exact hereditaryCovRealizationPAt_from_Y (C2 E) (CTyCovP2 reflect E) _ _ n
      Γ ρ D u covZPropArrowCode (covP_transport_propArrow reflect)
      (hereditaryCovRealizationYAt_relevant_domain (C2 E) n ρ hr (hd u hu))
  · exact covP_hereditary_sort_zero reflect n (.assumption D :: Γ)
      (EnvT.cons (demandT ds) ρ) hsel.2
  · exact covP_hereditary_sort_zero reflect n Γ ρ hsel.2
  · exact covP_hereditary_sort_zero reflect n Γ ρ hsel.2

theorem covP_relevant_app_joint (reflect : Bool) (hW : EnvWfT E) (n : Nat)
    {Γ : LCtx} (ρ ρ' : EnvT) {D Q : Expr Nat}
    (hr : RedR (WhStepCK2 E n) Γ D (.pi (.sort .zero) (.sort .zero)))
    (hQ : HasTyT E n Γ Q (.sort .zero)) :
    CovPJointAt reflect E n Γ ρ ρ'
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi D (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) covZRelevantAppCode := by
  have hc := lrSCoreCovY_relevant_app (C2 E) (C2_includesS E) hW n hr hQ
  exact ⟨hc, covP_relevant_app_hereditary reflect n ρ hr hc,
    covP_relevant_app_hereditary reflect n ρ' hr hc⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_WALL4_ROOTS
#print axioms covP_transport_propArrow
#print axioms covP_hereditary_sort_zero
#print axioms covP_relevant_app_coverage
#print axioms covP_relevant_app_hereditary
#print axioms covP_relevant_app_joint
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_WALL4_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
