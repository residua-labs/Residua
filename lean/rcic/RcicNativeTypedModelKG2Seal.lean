import Lean
import rcic.RcicNativeTypedModelKG2

/-!
# Bounded finite-chain index-agreement seal

The public declarations of the new leaf are queried below.  The leaf is
compiled from its current source; #7761's measurements, #7757's guards and
the landed `KG.KIdxAgree` are imported, never redefined.  Neither aggregate
Foundation target is built.

Summary of what is sealed:

* The step system `KIdxStep` (readback weak-head step, transparent head-δ,
  typed η collapse), its chain closure `KIdxChain`, and the joinability
  relation `KIdxAgree2`, with the landed one-layer relation lifting into it
  (`kIdxAgree2_of_kIdxAgree`).
* (a) All six #7761 controls (`kg2_six_controls`), the δ-under-a-binder
  entry now positive through the explicit η-then-δ chain.
* (b) The composition port discharged (`kg2DeltaEtaCompositionAt`,
  `kg2_deltaEta_premises`, `KG2DeltaEtaCompositionAt`).
* (c) The apart fixture stays refuted (`not_kIdxAgree2_apart`) by distinct
  rigid weak-head normal forms (`kIdxStep_idPiProp_false`,
  `kIdxStep_apartRight_false`, `kIdxChain_stuck`).
* (d) Soundness against native conversion: chains of natively realized
  steps compose into one `ConvT` (`kIdxChain_convT`, `kIdxAgree2_convT`);
  at the δ∘η composition the two step rules alone build the certificate
  (`kg2_deltaBinder_convT`) and pay `KIndexConvAt` at the exact #7761
  witness (`kIndexConvAt_deltaBinder_stepDerived`); the native conjunction
  of all six controls is positive at the former gap
  (`kg2_six_native_conjunction`).

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2

/-- The exact project registration list, checked in this bounded module. -/
private def kIdx2SealedRoots : List Lean.Name := [
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxStep,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxStep.red,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxStep.delta,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxStep.eta,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxChain,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxChain.nil,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxChain.cons,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxAgree2,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxChain_of_redR,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxChain_trans,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_refl,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_of_kIdxAgree,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxChain_stuck,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_eqGap,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_binder,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_deltaHead,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_etaIndex,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_deltaConst_eta,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_deltaBinder,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxStep_idPiProp_false,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxStep_apartRight_false,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.not_kIdxAgree2_apart,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_six_controls,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KG2DeltaEtaCompositionAt,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_deltaEta_premises,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2DeltaEtaCompositionAt,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxChain_convT,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_convT,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_deltaBinder_convT,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIndexConvAt_deltaBinder_stepDerived,
  ``Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_six_native_conjunction
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Quot.sound]
  for root in kIdx2SealedRoots do
    let (_, state) := ((CollectAxioms.collect root).run env).run {}
    for ax in state.axioms do
      unless allowed.contains ax do
        throwError "[rcic_kidx2_seal] {root} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_kidx2_seal] {kIdx2SealedRoots.length} public roots sealed; axioms ⊆ {allowed}"

end Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2
