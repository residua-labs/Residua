import Lean
import rcic.RcicAnnLR3TaggedCodeKernel
import rcic.RcicAnnLR3TaggedCarrier
import rcic.RcicAnnLR3TaggedSaturatedTower
import rcic.RcicAnnLR3TaggedPiControls
import rcic.RcicAnnLR3TaggedPiReindex
import rcic.RcicAnnLR3TaggedFamilyInterface
import rcic.RcicAnnLR3SemanticMemberAdmissionReadback
import rcic.RcicAnnLR3SemanticMemberAdmissionDelta
import rcic.RcicAnnLR3SemanticMemberAdmissionControls
import rcic.RcicAnnLR3SemanticMemberAdmissionFixture
import rcic.RcicAnnLR3AdmissionTaggedMember

/-!
Bounded audit of every public declaration in the eleven new proof
modules, including generated public declarations. collectAxioms traverses
all proof dependencies, including private ones. Only propext and
Quot.sound are permitted. No full Foundation build is required.
General source arms and complete model closure remain open.
closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_TAGGED_TOWER_ROOTS
private def routeCLR3TaggedTowerModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3TaggedCodeKernel,
  `rcic.RcicAnnLR3TaggedCarrier,
  `rcic.RcicAnnLR3TaggedSaturatedTower,
  `rcic.RcicAnnLR3TaggedPiControls,
  `rcic.RcicAnnLR3TaggedPiReindex,
  `rcic.RcicAnnLR3TaggedFamilyInterface,
  `rcic.RcicAnnLR3SemanticMemberAdmissionReadback,
  `rcic.RcicAnnLR3SemanticMemberAdmissionDelta,
  `rcic.RcicAnnLR3SemanticMemberAdmissionControls,
  `rcic.RcicAnnLR3SemanticMemberAdmissionFixture,
  `rcic.RcicAnnLR3AdmissionTaggedMember
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3TaggedTowerModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3TaggedTower: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3TaggedTower: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3TaggedTower: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3TaggedTower: {total} public declarations checked"
-- END RCIC_LR3_TAGGED_TOWER_ROOTS
