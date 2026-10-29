import Lean
import rcic.RcicAnnLR3RCodeProofReadback
import rcic.RcicAnnLR3RCodeInterface
import rcic.RcicAnnLR3RCodeZeroInstances
import rcic.RcicAnnLR3RCodeDependentPi
import rcic.RcicAnnLR3RCodeGuardedReadback
import rcic.RcicAnnLR3RCodeUniverseReadback
import rcic.RcicAnnLR3OptionLevelKernel
import rcic.RcicAnnLR3OptionAdmittedLevels
/-!
Bounded audit of every public declaration in the eight new proof modules,
including generated public declarations and transitive private dependencies.
Only propext and Quot.sound are permitted. No full Foundation build or
completed semantic model is asserted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_RCODE_ROOTS
private def routeCLR3RCodeModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3RCodeProofReadback,
  `rcic.RcicAnnLR3RCodeInterface,
  `rcic.RcicAnnLR3RCodeZeroInstances,
  `rcic.RcicAnnLR3RCodeDependentPi,
  `rcic.RcicAnnLR3RCodeGuardedReadback,
  `rcic.RcicAnnLR3RCodeUniverseReadback,
  `rcic.RcicAnnLR3OptionLevelKernel,
  `rcic.RcicAnnLR3OptionAdmittedLevels
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3RCodeModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3RCode: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3RCode: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3RCode: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3RCode: {total} public declarations checked"
-- END RCIC_LR3_RCODE_ROOTS
