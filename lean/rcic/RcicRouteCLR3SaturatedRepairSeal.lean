import Lean
import rcic.RcicAnnLR3SaturatedFamilyCode
import rcic.RcicAnnLR3SaturatedFamilyControl
import rcic.RcicAnnLR3SaturatedFamilyNative
import rcic.RcicAnnLR3SaturatedTower
import rcic.RcicAnnLR3SaturatedAliasControl
import rcic.RcicAnnLR3SemanticMemberEval
import rcic.RcicAnnLR3SemanticMemberReadback
import rcic.RcicAnnLR3SemanticMemberControl
import rcic.RcicAnnLR3SaturatedCandidateControl
import rcic.RcicAnnLR3SaturatedPiTransport
import rcic.RcicAnnLR3SaturatedPiReindex
import rcic.RcicAnnLR3SaturatedProducts
import rcic.RcicAnnLR3SaturatedPiElements
import rcic.RcicAnnLR3SaturatedPiElementsControl
import rcic.RcicAnnLR3SaturatedCandidatePiBoundary

/-!
Bounded continuation of cc issuecomment-6339242327 from 3f43fbcfc7.
Audits every public declaration of the positive alias, restricted tower,
proof products, retained element actions, family interface and the
inhabited level-only saturation boundary. The common enriched model and
the transfer of eleven source suppliers remain open. This seal introduces
no public API. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_SATURATED_REPAIR_ROOTS
private def routeCLR3SaturatedRepairModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3SaturatedFamilyCode,
  `rcic.RcicAnnLR3SaturatedFamilyControl,
  `rcic.RcicAnnLR3SaturatedFamilyNative,
  `rcic.RcicAnnLR3SaturatedTower,
  `rcic.RcicAnnLR3SaturatedAliasControl,
  `rcic.RcicAnnLR3SemanticMemberEval,
  `rcic.RcicAnnLR3SemanticMemberReadback,
  `rcic.RcicAnnLR3SemanticMemberControl,
  `rcic.RcicAnnLR3SaturatedCandidateControl,
  `rcic.RcicAnnLR3SaturatedPiTransport,
  `rcic.RcicAnnLR3SaturatedPiReindex,
  `rcic.RcicAnnLR3SaturatedProducts,
  `rcic.RcicAnnLR3SaturatedPiElements,
  `rcic.RcicAnnLR3SaturatedPiElementsControl,
  `rcic.RcicAnnLR3SaturatedCandidatePiBoundary
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3SaturatedRepairModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3SaturatedRepair: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3SaturatedRepair: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3SaturatedRepair: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3SaturatedRepair: {total} public declarations checked"
-- END RCIC_LR3_SATURATED_REPAIR_ROOTS
