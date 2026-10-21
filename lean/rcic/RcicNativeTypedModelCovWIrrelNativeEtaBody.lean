import rcic.RcicNativeTypedModelCovWIrrelShape
import rcic.RcicNativeTypedModelCovWIrrelScope

/-!
# Native typing of the proof family's eta body

The environment scope is actually supplied. The declared constant-type
chain and the landed Pi row identify the domain of any native Pi typing
of the family. Native context conversion transports its fresh-variable
application to that domain. No normalization or confluence is used.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open PiModelDeltaIotaAudit

theorem covWIrrel_family_eta_body {n : Nat} {Γ : LCtx} {D B : Expr Nat}
    (hΓ : CtxWfT covWIrrelEnv n Γ)
    (hF : HasTyT covWIrrelEnv n Γ covWIrrelFamily (.pi D B)) :
    Nonempty (CtxWfT covWIrrelEnv n (.assumption D :: Γ)) ∧
      Nonempty (HasTyT covWIrrelEnv n (.assumption D :: Γ)
        (.app covWIrrelFamily (.bvar 0)) (.sort .zero)) := by
  have hsort := tySort covWIrrelEnv_wf hΓ hF
  obtain ⟨u, v, hD, _, _⟩ := covWIrrel_pi_type_chain hsort.2
  have hchain : TyConvT covWIrrelEnv n Γ
      (.pi covWIrrelProp (.sort .zero)) (.pi D B) :=
    covWIrrel_const_type_chain (m := covWIrrelFamilyMember) rfl hF
  obtain ⟨⟨hdom⟩, _⟩ :=
    (Ann.typedRowsWf_of_envWfT_semPrefix covWIrrelEnv_wf
      covWIrrelEnv_inScope n).piRow hΓ hchain
  have hbody : HasTyT covWIrrelEnv n (.assumption covWIrrelProp :: Γ)
      (.app covWIrrelFamily (.bvar 0)) (.sort .zero) :=
    .app _ covWIrrelFamily (.bvar 0) covWIrrelProp (.sort .zero)
      (covWIrrel_family_ty n _) (.bvar _ 0 _ rfl)
  exact ⟨⟨.assumption Γ D u hΓ hD⟩,
    ⟨hasTyT_tyConvT_head covWIrrelEnv_wf hΓ hdom hbody⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_NATIVE_ETA_BODY_ROOTS
#print axioms covWIrrel_family_eta_body
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_NATIVE_ETA_BODY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
