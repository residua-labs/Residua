import rcic.RcicF3NormRoleReads
import rcic.RcicF3RawFamilyReads

/-!
# Produced faithful installation of the normalized canonical roles

Both stored normalized-family reads and the unchanged original plan reads
are produced from the admitted environment. The generic indexed-endpoint
installer supplies a table satisfying these new role equations. This is
installation and read closure, not soundness or equivalence to a raw table.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormRole
open Rcic.Declarative

noncomputable def table (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    Nat → List Nat → PSet.{4} :=
  EvalRole.envTable RawFamily.role P (envCtx hW) (EvalRole.envPlan hW) hW

/-- Every input of the installer is produced for the normalized context. -/
theorem table_spec (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    EvalRole.Faithful RawFamily.role P (table P hW) (envCtx hW)
      (EvalRole.envPlan hW) E ∧
    EvalRole.ReadsClosed (envCtx hW) (EvalRole.envPlan hW) E :=
  EvalRole.faithful_envTable RawFamily.role P (envCtx hW) (EvalRole.envPlan hW)
    (RawFamily.familyReadsCtx P _) hW
    (planReadsOKAlong hW _ _ (fun _ _ => rfl) (fun _ _ => rfl))

theorem table_exists (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    ∃ μ, EvalRole.Faithful RawFamily.role P μ (envCtx hW) (EvalRole.envPlan hW) E :=
  ⟨table P hW, (table_spec P hW).1⟩

/-- Non-refutability of the composed installation component. This does not
assert non-refutability or production of the universal StepAG target. -/
theorem table_nonrefutable (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) :
    ¬ ((∃ μ, EvalRole.Faithful RawFamily.role P μ (envCtx hW)
        (EvalRole.envPlan hW) E) → (Premises4 → False)) := by
  intro h
  exact h (table_exists P hW) P

end Rcic.F3.PSet.NormRole
