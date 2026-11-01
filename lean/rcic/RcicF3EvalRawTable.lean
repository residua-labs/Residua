import rcic.RcicF3RawFamilyReads
import rcic.RcicF3EvalRoleReads

/-!
# Produced faithful tables for the raw family and indexed evaluation plans

The unconditional read law from #8474 and the produced normalized-plan support pay every installation
input to EvalRole. The table exists for every admitted environment; neither
family smallness nor AllSound is asserted by table faithfulness.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalRole
open Rcic.Declarative

noncomputable def rawTable (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    Nat → List Nat → PSet.{4} :=
  envTable RawFamily.role P (envCtx hW) (envPlan hW) hW

/-- Both inputs to the generic table installer are produced from the actual
admitted environment and the universal raw-family read law. -/
theorem rawTable_spec (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    Faithful RawFamily.role P (rawTable P hW) (envCtx hW) (envPlan hW) E ∧
      ReadsClosed (envCtx hW) (envPlan hW) E := by
  exact faithful_envTable RawFamily.role P (envCtx hW) (envPlan hW)
    (RawFamily.familyReadsCtx P _) hW
    (readsOKAlong_envCtxT hW)

/-- A concrete inhabitant of the planned table equations, with no read-law
or family/recursor compatibility premise left for the caller. -/
theorem rawTable_exists (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    ∃ μ, Faithful RawFamily.role P μ (envCtx hW) (envPlan hW) E :=
  ⟨rawTable P hW, (rawTable_spec P hW).1⟩

/-- Non-refutability of this produced installation component only. It is
not non-refutability of universal StepAG or of the soundness tier. -/
theorem rawTable_nonrefutable (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    ¬ ((∃ μ, Faithful RawFamily.role P μ (envCtx hW) (envPlan hW) E) →
      (Premises4 → False)) := by
  intro h
  exact h (rawTable_exists P hW) P

end Rcic.F3.PSet.EvalRole
