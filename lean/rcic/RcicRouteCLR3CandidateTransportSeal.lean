import Lean
import rcic.RcicAnnLR3CandidatePi
import rcic.RcicAnnLR3CandidatePiSourceControls
import rcic.RcicAnnLR3StratifiedCandidates
import rcic.RcicAnnLR3TypedNeutralProducer
import rcic.RcicAnnLR3TypedNeutralAttachment
import rcic.RcicAnnLR3TypedNeutralPiControls
import rcic.RcicAnnLR3FiniteFamilyLabels
import rcic.RcicAnnLR3FiniteFamilyLabelAdapters
import rcic.RcicAnnLR3FunctionalLabelPositions

/-!
Bounded continuation of cc issuecomment-6336496715 after the requested
main merge. Audits every public declaration of the new candidate product,
retained-code universe tower, typed neutral constructions and finite
family-label/functional-position producers. Source Pi closure, compositional
typed members and generic recursors remain open. No public API is introduced
by the seal. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_CANDIDATE_TRANSPORT_ROOTS
private def routeCLR3CandidateTransportModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3CandidatePi,
  `rcic.RcicAnnLR3CandidatePiSourceControls,
  `rcic.RcicAnnLR3StratifiedCandidates,
  `rcic.RcicAnnLR3TypedNeutralProducer,
  `rcic.RcicAnnLR3TypedNeutralAttachment,
  `rcic.RcicAnnLR3TypedNeutralPiControls,
  `rcic.RcicAnnLR3FiniteFamilyLabels,
  `rcic.RcicAnnLR3FiniteFamilyLabelAdapters,
  `rcic.RcicAnnLR3FunctionalLabelPositions
]
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3CandidateTransportModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3CandidateTransport: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3CandidateTransport: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3CandidateTransport: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3CandidateTransport: {total} public declarations checked"
-- END RCIC_LR3_CANDIDATE_TRANSPORT_ROOTS
