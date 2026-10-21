import rcic.RcicNativeTypedModelCovYEtaCoverage

/-!
# Value-compact descent, checked before synthesis

Lambda demand members and outputs are genuine children of the observed
compact. A rigid application's output is not. These facts compose the
landed size lemmas and carry an admitted, typed successor control.
They restrict an implementation; they do not by themselves refute synthesis.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelCovXAudit TypedModelCovYEtaAudit
open TypedModelKAudit TypedModelCovNormCov2Audit

theorem covZ_sizeOf_lam_demand_lt {rows : List (List CptT × CptT)}
    {row : List CptT × CptT} (hr : row ∈ rows) {u : CptT} (hu : u ∈ row.1) :
    sizeOf u < sizeOf (CptT.lam rows) := sizeOf_dem_lt_lam hr hu

theorem covZ_sizeOf_lam_output_lt {rows : List (List CptT × CptT)}
    {row : List CptT × CptT} (hr : row ∈ rows) :
    sizeOf row.2 < sizeOf (CptT.lam rows) := sizeOf_out_lt_lam hr

/-- Existing rigid arguments may be visited structurally. -/
theorem covZ_sizeOf_spine_argument_lt {r : Nat} {us : List CptT} {u : CptT}
    (hu : u ∈ us) : sizeOf u < sizeOf (CptT.spine r us) := by
  have h := List.sizeOf_lt_of_mem hu
  simp
  omega

/-- Applying a rigid compact cannot be used as a recursive child. -/
theorem covZ_not_spine_application_decreases (r : Nat) (us : List CptT) (u : CptT) :
    ¬ sizeOf (CptT.spine r (us ++ [u])) < sizeOf (CptT.spine r us) :=
  Nat.not_lt_of_ge (Nat.le_of_lt (covX_spine_application_grows r us u))

/-- This failed decrease is an actual typed native action in an admitted
environment, rather than an arbitrary pair of compacts. -/
theorem covZ_natSucc_action_measure_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 [])
      (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 1 []) (.const 0 [])) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    (C2 natEnvU).ty .bot (.spine 0 []) ∧
    CovXCompactAction natEnvU (.spine 2 []) [.bot] (.spine 2 [.bot]) ∧
    ¬ sizeOf (CptT.spine 2 [.bot]) < sizeOf (CptT.spine 2 []) := by
  obtain ⟨hW, hΓ, hf, ha, ho, _, _, _, hd, hact, _⟩ :=
    covY_natSucc_standard_code_control n
  exact ⟨hW, hΓ, hf, ha, ho, hd, hact,
    covZ_not_spine_application_decreases 2 [] .bot⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_MEASURE_ROOTS
#print axioms covZ_sizeOf_lam_demand_lt
#print axioms covZ_sizeOf_lam_output_lt
#print axioms covZ_sizeOf_spine_argument_lt
#print axioms covZ_not_spine_application_decreases
#print axioms covZ_natSucc_action_measure_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_MEASURE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit
