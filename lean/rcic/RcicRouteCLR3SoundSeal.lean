import Lean
import rcic.RcicAnnLR3RCodeSoundInterface
import rcic.RcicAnnLR3RCodeSoundZeroInstances
import rcic.RcicAnnLR3RCodeSoundPi
import rcic.RcicAnnLR3RCodeSoundPiControl
import rcic.RcicAnnLR3RCodeSoundCoreSubstitution
import rcic.RcicAnnLR3RCodeDecideReflected
import rcic.RcicAnnLR3NoneSelfUniverse
import rcic.RcicAnnLR3NoneSortSupply
/-!
Bounded audit of every public declaration in the eight new proof modules,
including generated public declarations and transitive private dependencies.
Only propext and Quot.sound are permitted. No full Foundation build or
completed semantic model is asserted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_SOUND_ROOTS
private def routeCLR3SoundModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3RCodeSoundInterface,
  `rcic.RcicAnnLR3RCodeSoundZeroInstances,
  `rcic.RcicAnnLR3RCodeSoundPi,
  `rcic.RcicAnnLR3RCodeSoundPiControl,
  `rcic.RcicAnnLR3RCodeSoundCoreSubstitution,
  `rcic.RcicAnnLR3RCodeDecideReflected,
  `rcic.RcicAnnLR3NoneSelfUniverse,
  `rcic.RcicAnnLR3NoneSortSupply
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3SoundModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3Sound: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3Sound: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3Sound: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3Sound: {total} public declarations checked"
-- END RCIC_LR3_SOUND_ROOTS
