import Lean
import rcic.RcicF3RouteRemainingRoot

/-!
Exact inventory of the fresh route and fragment module, literal checks of
the original root and the landed two-input adapter type, and strict axiom
audits of the named conditional support theorems. The support checks do
not produce either universal residual. Existing source-module seals and
the claims-graph checker are unchanged.

closure_claim = 0; scope_closure_claim = 0.
-/
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.F3.RouteRemainingRootSeal
open Lean Elab Command

def sealedTheoremsRaw : String := " ".intercalate [
  "Rcic.F3.PSet.RouteRemaining.root_binding",
  "Rcic.F3.PSet.RouteRemaining.Fragment",
  "Rcic.F3.PSet.RouteRemaining.fragmentDecision._cstage1",
  "Rcic.F3.PSet.RouteRemaining.fragmentDecision._cstage2",
  "Rcic.F3.PSet.RouteRemaining.fragmentDecision",
  "Rcic.F3.PSet.RouteRemaining.tierF3_iff_fragment"
]

def sealedTheorems : List Name :=
  (sealedTheoremsRaw.split (· == ' ') |>.map String.toName)

def supportingTheorems : List Name := [
  ``Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta.kernelSoundnessTierUncond_of_remaining,
  ``Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta.stepPropOnly_of_remaining,
  ``Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta.covered_step,
  ``Rcic.F3.PSet.PointwiseRemainingDataSeparated.kernelSoundnessTierUncond_of_remaining,
  ``Rcic.F3.PSet.PointwiseRemainingDataSeparated.stepData_of_remaining,
  ``Rcic.F3.PSet.PointwiseRemainingDataSeparated.data_covered_step,
  ``Rcic.F3.PSet.PointwiseDataFiniteSeparated.invariant_step,
  ``Rcic.F3.PSet.PointwiseRemainingPropOnlyFamilyBeta.stepPropOnly_of_remaining,
  ``Rcic.F3.PSet.PointwiseRemainingPropOnlyFamilyBeta.covered_step,
  ``Rcic.F3.PSet.PointwisePropOnlyFamilyBetaGroup.invariant_step
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `rcic.RcicF3RouteRemainingRoot
    | throwError "[route_remaining_root_seal] fresh root module is not imported"
  let actual := env.header.moduleData[idx.toNat]!.constNames
  unless actual.size == sealedTheorems.length do
    throwError "[route_remaining_root_seal] inventory size {sealedTheorems.length} differs from {actual.size}"
  for n in actual do
    unless sealedTheorems.contains n do
      throwError "[route_remaining_root_seal] uncovered declaration {n}"
  for n in sealedTheorems do
    unless actual.contains n && env.contains n do
      throwError "[route_remaining_root_seal] stale or foreign declaration {n}"

  let rootName := ``Rcic.F3.PSet.RouteRemaining.root_binding
  let originalRoot := mkConst ``Rcic.Apex.KernelSoundnessTierUncond
  let some (.thmInfo rootInfo) := env.find? rootName
    | throwError "[route_remaining_root_seal] root binding is not a theorem"
  unless rootInfo.levelParams.isEmpty do
    throwError "[route_remaining_root_seal] root binding has unexpected universe parameters"
  match rootInfo.type with
  | .forallE binder domain result info =>
      unless binder == `hRoot && info == .default &&
          domain == originalRoot && result == originalRoot do
        throwError "[route_remaining_root_seal] root binding differs from the literal original-root identity"
  | _ =>
      throwError "[route_remaining_root_seal] root binding has no literal hRoot premise"

  let universalResidual (stepName : Name) : Expr :=
    mkForall `P .default (mkConst ``Rcic.F3.PSet.Premises4)
      (mkForall `K .default (mkForall Name.anonymous .default (mkConst ``Nat) (mkConst ``Nat))
        (mkApp2 (mkConst stepName) (mkBVar 1) (mkBVar 0)))
  let expectedAdapterType :=
    mkForall `hData .default
      (universalResidual ``Rcic.F3.PSet.PointwiseRemainingDataSeparated.StepData)
      (mkForall `hPropOnly .default
        (universalResidual ``Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta.StepPropOnly)
        originalRoot)
  let adapterName :=
    ``Rcic.F3.PSet.PointwiseRemainingPropOnlyPrefixBeta.kernelSoundnessTierUncond_of_remaining
  let some (.thmInfo adapterInfo) := env.find? adapterName
    | throwError "[route_remaining_root_seal] landed adapter is not a theorem"
  unless adapterInfo.levelParams.isEmpty && adapterInfo.type == expectedAdapterType do
    throwError "[route_remaining_root_seal] adapter differs from the landed two-universal-input original-root type"

  for n in supportingTheorems do
    let some (.thmInfo _) := env.find? n
      | throwError "[route_remaining_root_seal] support {n} is absent or not a theorem"
  for n in sealedTheorems ++ supportingTheorems do
    let (_, st) := ((CollectAxioms.collect n).run env).run {}
    for ax in st.axioms do
      unless allowedAxioms.contains ax do
        throwError "[route_remaining_root_seal] {n} depends on {ax}"

  logInfo m!"[route_remaining_root_seal] {sealedTheorems.length} exact fresh-module entries; literal original root and landed adapter type checked; {supportingTheorems.length} conditional support theorems audited; axioms ⊆ {allowedAxioms}; closure_claim = 0"

end Rcic.F3.RouteRemainingRootSeal
