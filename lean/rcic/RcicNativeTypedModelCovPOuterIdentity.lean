import rcic.RcicNativeTypedModelCovPTyping
import rcic.RcicNativeTypedModelCovPRealization
import rcic.RcicNativeTypedModelCovZRigidId

/-!
# Positive collapse alone repairs the outer rigid identity gate and coverage

The concrete code has domain `sort` and the single empty-demand row with
output `pi bot []`. The output carries no positive proposition evidence.
Its exact telescope gate works for every typed argument observation, so the
new neutral-reflection clause is not needed for this outer coverage result.
This is not hereditary realization; the retained recursive obligation is
measured separately. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelAudit.TypingFin TypedModelCovXAudit
open TypedModelCovZMeasureAudit

def covPIdentityOuterCode : CptT := .pi .sort [([], .pi .bot [])]

theorem covPIdentityOuterCode_not_positive :
    ¬ IsPropCTP covZRigidIdEnv covPIdentityOuterCode := by
  intro h
  cases h with
  | pi _ _ hout =>
      exact not_isPropCTP_pi_nil covZRigidIdEnv .bot
        (hout _ (List.mem_singleton.mpr rfl))

theorem approxT_covPIdentityOuterCode (ρ : EnvT) :
    ApproxT covZRigidIdEnv ρ cexPolyIdTy covPIdentityOuterCode := by
  refine .pi (.sort ρ (.succ .zero)) ?_ ?_
  · intro row hr v hv
    rcases List.mem_singleton.mp hr with rfl
    exact (List.not_mem_nil v hv).elim
  · intro row hr
    rcases List.mem_singleton.mp hr with rfl
    exact approxT_pi_bot_nil _ _ _ _

theorem covPIdentity_outer_gate (reflect : Bool) :
    CTyCovP2 reflect covZRigidIdEnv (.spine 0 []) covPIdentityOuterCode := by
  apply CTyCovP2.rigidPi covPIdentityOuterCode_not_positive
  refine ⟨covZRigidIdMember, [], rfl, covZRigidIdHead_rigid, rfl,
    ?_, cexPolyIdTy, rfl, approxT_covPIdentityOuterCode EnvT.bot⟩
  intro i hi
  exact (Nat.not_lt_zero i hi).elim

theorem covPIdentity_outer_output_gate (reflect : Bool) {v : CptT}
    (hv : CTyCovP2 reflect covZRigidIdEnv v .sort) :
    CTyCovP2 reflect covZRigidIdEnv (.spine 0 [v]) (.pi .bot []) := by
  apply CTyCovP2.rigidPi (not_isPropCTP_pi_nil _ _)
  refine ⟨covZRigidIdMember, [], rfl, covZRigidIdHead_rigid, rfl,
    ?_, .pi (.bvar 0) (.bvar 1), rfl, approxT_pi_bot_nil _ _ _ _⟩
  intro i hi D B hpi
  have hi0 : i = 0 := by
    simp only [List.length_singleton] at hi
    omega
  subst i
  change some (.pi (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1)) : Expr Nat) =
    some (.pi D B) at hpi
  obtain ⟨hD, hB⟩ := Expr.pi.inj (Option.some.inj hpi)
  subst D
  exact ⟨.sort, .sort _ (.succ .zero), hv⟩

theorem covPIdentity_outer_coverage (reflect : Bool) :
    CovPActionCoverage covZRigidIdEnv (CTyCovP2 reflect covZRigidIdEnv)
      (.spine 0 []) .sort [([], .pi .bot [])] := by
  intro ds out hact htyped
  cases hact with
  | bot => exact Or.inl rfl
  | @appSpine r args x v hx =>
      have hv : CTyCovP2 reflect covZRigidIdEnv v .sort := by
        rcases approxT_bvar_inv hx with rfl | hv
        · exact .bot _
        · exact htyped v hv
      exact Or.inr ⟨([], .pi .bot []), List.mem_singleton.mpr rfl,
        (by intro u hu; exact (List.not_mem_nil u hu).elim),
        covPIdentity_outer_output_gate reflect hv⟩

theorem covPIdentity_b_only_repairs_outer :
    CTyCovP2 false covZRigidIdEnv (.spine 0 []) covPIdentityOuterCode ∧
    CovPActionCoverage covZRigidIdEnv (CTyCovP2 false covZRigidIdEnv)
      (.spine 0 []) .sort [([], .pi .bot [])] :=
  ⟨covPIdentity_outer_gate false, covPIdentity_outer_coverage false⟩

/-- A non-strict rigid action cannot be covered by an empty row table,
independently of the choice of compact typing or domain code. -/
theorem covP_rigid_empty_rows_no_coverage (E : ResolvedEnv)
    (T : CptT → CptT → Prop) (r : Nat) (us : List CptT) (d : CptT) :
    ¬ CovPActionCoverage E T (.spine r us) d [] := by
  intro h
  have ha : CovXCompactAction E (.spine r us) [] (.spine r (us ++ [.bot])) :=
    AppCptT.appSpine (.bot _ _)
  rcases h [] _ ha (by intro u hu; cases hu) with hb | ⟨row, hr, _⟩
  · exact CptT.noConfusion hb
  · exact List.not_mem_nil row hr

/-- The next premise fails at the code constructed above: the bottom-demand
output is now typed, but its empty Pi table has no covering row. -/
theorem covPIdentity_output_typed_not_covered (reflect : Bool) :
    CTyCovP2 reflect covZRigidIdEnv (.spine 0 [.bot]) (.pi .bot []) ∧
    ¬ CovPActionCoverage covZRigidIdEnv (CTyCovP2 reflect covZRigidIdEnv)
      (.spine 0 [.bot]) .bot [] :=
  ⟨covPIdentity_outer_output_gate reflect (.bot _),
    covP_rigid_empty_rows_no_coverage _ _ _ _ _⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_OUTER_IDENTITY_ROOTS
#print axioms covPIdentityOuterCode
#print axioms covPIdentityOuterCode_not_positive
#print axioms approxT_covPIdentityOuterCode
#print axioms covPIdentity_outer_gate
#print axioms covPIdentity_outer_output_gate
#print axioms covPIdentity_outer_coverage
#print axioms covPIdentity_b_only_repairs_outer
#print axioms covP_rigid_empty_rows_no_coverage
#print axioms covPIdentity_output_typed_not_covered
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_OUTER_IDENTITY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
