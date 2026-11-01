import rcic.RcicF3PointwiseLocalProducer

/-!
# The literal checked kernel tier from the actual local-frame producer

The complete pointwise admission fold now receives the produced checked
DATA step. Both Prop policies, finite DATA, ordinary declarations, stable
legacy iota and the distinguished False finalizer retain their existing
produced consumers. The original whole-environment W/D checks, BoundG,
BoundDG and axiom-free condition remain exactly the kernel tier's own
antecedents; there is no additional universal semantic binder here.

The semantic table in the environment corollaries is the actual pointwise
table throughout. This result does not assert an equality with earlier
raw or normalized invariants, or produce their unchecked StepAG targets.
Native elaboration, strict inventory and RCC are separate verification
steps owned by the publication lane. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PointwiseCheckedApex
open Rcic.Declarative

/-- The new invariant is produced at the actual admitted environment from
the original checks and bounds, with no local-candidate hypothesis. -/
theorem invariant_of_checks (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E) :
    PointwiseRole.GInv P K hW :=
  PointwiseADataChecked.invariant_of_checks P K
    (PointwiseLocalProducer.stepADataChecked P K) hW pw pd hB hD hAx

/-- Ordinary semantic soundness uses the same installed pointwise table. -/
theorem envSound_of_checks (P : Premises4) (K : Nat → Nat)
    {E : ResolvedEnv} (hW : EnvWfT E)
    (pw : Rcic.F3.StepWApex.envCheck hW = true)
    (pd : Rcic.F3.StepWDApex.envCheck K hW = true)
    (hB : BoundG K hW) (hD : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P hW)) σ K E n :=
  PointwiseRole.envSound_of_gInv P K hW
    (invariant_of_checks P K hW pw pd hB hD hAx) σ n

/-- The existing F1 ∧ checked-F3 statement, with no named universal
semantic premise left in this producer's type. -/
theorem kernelSoundnessTierWDChecked :
    Rcic.F3.StepWDApex.KernelSoundnessTierWDChecked :=
  PointwiseADataChecked.kernelSoundnessTierWDChecked_of_localCandidates
    PointwiseLocalProducer.localCandidatesChecked

end Rcic.F3.PSet.PointwiseCheckedApex
