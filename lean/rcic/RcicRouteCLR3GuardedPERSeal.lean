import Lean
import rcic.RcicAnnLR3GuardedDisjunction
import rcic.RcicAnnLR3GuardedKernel
import rcic.RcicAnnLR3GuardedKernelTransport
import rcic.RcicAnnLR3GuardedTypeImage
import rcic.RcicAnnLR3GuardedImageBoundary
import rcic.RcicAnnLR3GuardedMinorTransport
import rcic.RcicAnnLR3GuardedNeutralBoundary
import rcic.RcicAnnLR3GuardedTaggedCode
import rcic.RcicAnnLR3GuardedConversionUniverse
import rcic.RcicAnnLR3GuardedSuspendedRead
import rcic.RcicAnnLR3GuardedPropControl

/-!
Bounded audit of every public declaration in the eleven new proof modules,
including generated public declarations and transitive private dependencies.
Only propext and Quot.sound are permitted. No full Foundation build or
completed semantic model is asserted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_GUARDED_PER_ROOTS
private def routeCLR3GuardedPERModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3GuardedDisjunction,
  `rcic.RcicAnnLR3GuardedKernel,
  `rcic.RcicAnnLR3GuardedKernelTransport,
  `rcic.RcicAnnLR3GuardedTypeImage,
  `rcic.RcicAnnLR3GuardedImageBoundary,
  `rcic.RcicAnnLR3GuardedMinorTransport,
  `rcic.RcicAnnLR3GuardedNeutralBoundary,
  `rcic.RcicAnnLR3GuardedTaggedCode,
  `rcic.RcicAnnLR3GuardedConversionUniverse,
  `rcic.RcicAnnLR3GuardedSuspendedRead,
  `rcic.RcicAnnLR3GuardedPropControl
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3GuardedPERModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3GuardedPER: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3GuardedPER: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3GuardedPER: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3GuardedPER: {total} public declarations checked"
-- END RCIC_LR3_GUARDED_PER_ROOTS