import rcic.RcicNativeTypedModelCovWIrrelPositionPins
import rcic.RcicAnnSemPrefixRows

/-!
# Native non-proof positions in admitted environments

The landed semantic-prefix bridge supplies native sort separation under
the existing environment admission and scope hypotheses.  Consequently
the primitive Nat and Nat-arrow certificates have no additional sorting
or typing-uniqueness assumption. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys

theorem covWIrrel_native_sort_separation {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hScope : hW.InScope)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level}
    (hc : TyConvT E n Γ (.sort u) (.sort v)) : eqN u v :=
  (Ann.typedRowsWf_of_envWfT_semPrefix hW hScope n).sortRow hΓ hc

theorem covWIrrel_nat_notProp {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hScope : hW.InScope)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hNat : E.members 0 = some natFamMember) :
    ¬ Nonempty (HasTyT E n Γ (.const 0 []) (.sort .zero)) :=
  covWIrrel_nat_notProp_of_sortSeparation hNat
    (fun hc => covWIrrel_native_sort_separation hW hScope hΓ hc)

theorem covWIrrel_natArrow_notProp {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hScope : hW.InScope)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (hNat : E.members 0 = some natFamMember) :
    ¬ Nonempty (HasTyT E n Γ (.pi (.const 0 []) (.const 0 [])) (.sort .zero)) := by
  have hΓ' : CtxWfT E n (.assumption (.const 0 []) :: Γ) :=
    .assumption Γ (.const 0 []) (.succ .zero) hΓ
      (.const Γ 0 [] natFamMember hNat rfl rfl)
  exact covWIrrel_natArrow_notProp_of_sortSeparation hNat
    (fun hc => covWIrrel_native_sort_separation hW hScope hΓ hc)
    (fun hc => covWIrrel_native_sort_separation hW hScope hΓ' hc)

/-- The actual admitted Nat successor's sole binder is not a proof position. -/
theorem covWIrrel_natSucc_nonproof (n : Nat) :
    ¬ CovWIrrelProofPosition natEnvU n 2 [] 0 :=
  covWIrrel_position_nonproof_of_notProp (covWIrrel_natSucc_position n rfl)
    (covWIrrel_nat_notProp natEnvUWfT natEnvUWfT_inScope .nil rfl)

/-- This applies directly to a first Nat-arrow binder in any admitted
extension of the Nat environment whose existing scope certificate is supplied. -/
theorem covWIrrel_natArrowPosition_nonproof {E : ResolvedEnv} {n r : Nat}
    {ls : List Level} {B : Expr Nat}
    (hW : EnvWfT E) (hScope : hW.InScope)
    (hNat : E.members 0 = some natFamMember)
    (hp : CovWIrrelPosition E n r ls 0 []
      (.pi (.const 0 []) (.const 0 [])) B) :
    ¬ CovWIrrelProofPosition E n r ls 0 :=
  covWIrrel_position_nonproof_of_notProp hp
    (covWIrrel_natArrow_notProp hW hScope .nil hNat)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_NATIVE_POSITIONS_ROOTS
#print axioms covWIrrel_native_sort_separation
#print axioms covWIrrel_nat_notProp
#print axioms covWIrrel_natArrow_notProp
#print axioms covWIrrel_natSucc_nonproof
#print axioms covWIrrel_natArrowPosition_nonproof
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_NATIVE_POSITIONS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
