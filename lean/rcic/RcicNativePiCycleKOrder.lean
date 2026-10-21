import rcic.RcicNativePiCycleProbe

/-!
# Pi-cycle audit: K-valued large elimination at the exact typed Pi probe

The proposed order change cannot make the Pi observation blind to proposition-major
conversion.  The landed mixed-And example already has a large-elimination Pi result, a native
`ConvT` derivation (proof irrelevance, application congruence, ordinary iota and beta),
and no `WhStepCtx` reduction.  This file composes those results with `PiProbeLinkT`.

`piProbeLinkT_requires_pi_readback` isolates the necessary consequence of that input:
every native conversion from a typed syntactic Pi must expose a Pi at its other end.
Consequently `PiProbeLinkT (WhStepCtx andEnvU) andEnvU 0` is false.  The same concrete
typed relation is inhabited for `WhStepK`, by composition with the landed positive
control.  No subject-reduction theorem for arbitrary K steps is used here.

Scope: this refutes the K-blind instance of the proposed consumer, not Pi injectivity,
not every possible readback, and not a direct proof of the remaining single-link
input.  K-aware observation and generic K-step soundness are distinct obligations.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiCycleAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit

/-- An exact necessary consequence of the single-link input.  The hypotheses contain
no readback soundness, normal-form uniqueness, or declared-domain alignment. -/
theorem piProbeLinkT_requires_pi_readback {R : Readback} {E : ResolvedEnv} {n : Nat}
    (hlink : PiProbeLinkT R E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B M : Expr Nat} {u : Level}
    (hPi : HasTyT E n Γ (.pi A B) (.sort u))
    (hc : ConvT E n Γ (.pi A B) M (.sort u)) :
    ∃ A' B', RedR R Γ M (.pi A' B') := by
  have h := hlink hΓ hc (piProbe_diagT_of_typing hΓ hPi)
  rw [LRSCoreT.eq_def] at h
  obtain ⟨_, _, _, A', B', _, hM, _⟩ := h
  exact ⟨A', B', hM⟩

/-- The landed mixed-And conversion is a mandatory Pi-readback test for every
candidate readback satisfying the exact single-link input. -/
theorem piProbeLinkT_requires_mixAnd_readback {R : Readback}
    (hlink : PiProbeLinkT R andEnvU 0) :
    ∃ A B, RedR R mixAndCtx mixAndRedex (.pi A B) := by
  obtain ⟨hc⟩ := mixAnd_conv
  exact piProbeLinkT_requires_pi_readback hlink
    Rcic.Domain.Model.PiInversion.mixAndCtx_wf
    (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))
    (.symm _ _ _ _ hc)

/-- No context, type index, left endpoint, or compact typing can repair the missing
Pi readback of the mixed-And redex under `WhStepCtx`. -/
theorem not_piProbe_whStepCtx_mixAnd {n : Nat} {Γ : LCtx} {M A : Expr Nat} :
    ¬ LRSCoreT (WhStepCtx andEnvU) andEnvU n Γ M mixAndRedex A (.pi .bot []) := by
  intro h
  rw [LRSCoreT.eq_def] at h
  obtain ⟨_, _, _, _, _, _, hr, _⟩ := h
  exact Expr.noConfusion (whRedCtx_mixAndRedex_eq (whRedCtx_of_redR hr))

/-- Candidate (b) fails for the K-blind readback at the exact new minimal input,
even though only the Pi row is requested and no family row is read off. -/
theorem not_piProbeLinkT_whStepCtx_andEnvU :
    ¬ PiProbeLinkT (WhStepCtx andEnvU) andEnvU 0 := by
  intro hlink
  obtain ⟨_, _, hr⟩ := piProbeLinkT_requires_mixAnd_readback hlink
  exact Expr.noConfusion (whRedCtx_mixAndRedex_eq (whRedCtx_of_redR hr))

/-- Positive control: the same typed Pi observation is inhabited for the landed
proposition-major readback.  This uses its concrete reduction, with no generic K-step
subject-reduction or `NodeDeclAlign` assumption. -/
theorem piProbe_whStepK_mixAnd :
    LRSCoreT (WhStepK andEnvU 0) andEnvU 0 mixAndCtx mixPi mixAndRedex
      (.sort (.imax (.succ .zero) (.succ .zero))) (.pi .bot []) :=
  piProbe_typed_iff.mpr
    (lrSCore_whStepK_mixAnd (.pi .bot []) (approxI_pi_bot_nil _ _ _))

-- BEGIN RCIC_PI_CYCLE_K_ORDER_ROOTS
#print axioms piProbeLinkT_requires_pi_readback
#print axioms piProbeLinkT_requires_mixAnd_readback
#print axioms not_piProbe_whStepCtx_mixAnd
#print axioms not_piProbeLinkT_whStepCtx_andEnvU
#print axioms piProbe_whStepK_mixAnd
-- END RCIC_PI_CYCLE_K_ORDER_ROOTS

end Rcic.Declarative.NativeValleys.PiCycleAudit
