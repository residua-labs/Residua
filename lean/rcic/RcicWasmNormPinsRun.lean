/-
WX-012 pins — the machine row over the normative embedding (08 §14:
"`WasmStep` is deterministic and the runner is sound, complete, and
resumable"). The L1 host `RcicWasmNormStep` already carries
`normStep_deterministic`, `normRun_suspended_resumable`,
`normSteps_stuck_absorbing`; this module adds the run-level corollaries the
row is read as: `NormSteps` functional, resumption in outcome form, and
split-persistence of a finished run.

Statement shapes per `research/rcic/wx/S0_LEANFACE.md` (#6601).
`closure_claim = 0`.
-/
import rcic.RcicWasmNormStep

namespace Rcic.WasmNorm.Pins.Run

open Rcic.WasmNorm

/-- WX-012 determinism, run level: `NormSteps` is a function — same fuel,
same state, one result. (Step-level is `normStep_deterministic`.) -/
theorem wx012_normSteps_deterministic (fuel : Nat) (st : NormState)
    (r₁ r₂ : NormRunResult)
    (h₁ : NormSteps fuel st = r₁) (h₂ : NormSteps fuel st = r₂) : r₁ = r₂ := by
  rw [← h₁, ← h₂]

/-- WX-012 resumption, outcome form: a run suspended at `st'` after `k`
units of fuel, resumed for `n` to a final `f`, is exactly the `(k+n)`-fuel
run — run composition via `normRun_suspended_resumable`. -/
theorem wx012_resume_done (k n : Nat) (st st' : NormState) (f : NormFinal)
    (h : NormSteps k st = .suspended st') (hd : NormSteps n st' = .done f) :
    NormSteps (k + n) st = .done f := by
  rw [normRun_suspended_resumable k n st st' h, hd]

/-- WX-012 split-persistence: once the run reaches `.done f`, any extra
fuel keeps the same final — the machine has no post-final transitions. -/
theorem wx012_done_absorbing (k n : Nat) (st : NormState) (f : NormFinal)
    (h : NormSteps k st = .done f) : NormSteps (k + n) st = .done f := by
  induction k generalizing st with
  | zero => exact NormRunResult.noConfusion h
  | succ k ih =>
      rw [Nat.add_assoc, Nat.add_comm 1 n, ← Nat.add_assoc, normSteps_succ]
      rw [normSteps_succ] at h
      cases hs : NormStep st with
      | step s =>
          simp only [hs] at h ⊢
          exact ih s h
      | trap r s =>
          simp only [hs] at h ⊢
          exact h
      | ret v m =>
          simp only [hs] at h ⊢
          exact h
      | stuck =>
          simp only [hs] at h ⊢
          exact NormRunResult.noConfusion h

end Rcic.WasmNorm.Pins.Run
