import Lean
import rcic.RcicAnnLR3GuardedCodeRead
import rcic.RcicAnnLR3GuardDecision
import rcic.RcicAnnLR3SourceFamilyReading
import rcic.RcicAnnLR3GuardedReaderSource
import rcic.RcicAnnLR3GuardedReaderControl
import rcic.RcicAnnLR3GuardedEqFamily
import rcic.RcicAnnLR3GuardedOpenEqCall

/-!
Bounded audit of every public declaration in the seven new proof modules,
including generated public declarations and transitive private dependencies.
Only propext and Quot.sound are permitted. No full Foundation build or
completed semantic model is asserted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_GUARDED_READER_ROOTS
private def routeCLR3GuardedReaderModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3GuardedCodeRead,
  `rcic.RcicAnnLR3GuardDecision,
  `rcic.RcicAnnLR3SourceFamilyReading,
  `rcic.RcicAnnLR3GuardedReaderSource,
  `rcic.RcicAnnLR3GuardedReaderControl,
  `rcic.RcicAnnLR3GuardedEqFamily,
  `rcic.RcicAnnLR3GuardedOpenEqCall
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3GuardedReaderModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3GuardedReader: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3GuardedReader: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3GuardedReader: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3GuardedReader: {total} public declarations checked"
-- END RCIC_LR3_GUARDED_READER_ROOTS
