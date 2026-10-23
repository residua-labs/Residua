import Lean
import rcic.RcicAnnLR3TaggedKClosure
import rcic.RcicAnnLR3TaggedKEvaluation
import rcic.RcicAnnLR3TaggedKPiFixture
import rcic.RcicAnnLR3TaggedKSeedBoundary
import rcic.RcicAnnLR3TaggedKCoherenceBoundary

/-!
Bounded audit of every public declaration in the five new proof modules,
including generated public declarations and transitive private dependencies.
Only propext and Quot.sound are permitted. This seal does not build the
Foundation target and does not claim a completed semantic model.
closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_TAGGED_K_ROOTS
private def routeCLR3TaggedKModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3TaggedKClosure,
  `rcic.RcicAnnLR3TaggedKEvaluation,
  `rcic.RcicAnnLR3TaggedKPiFixture,
  `rcic.RcicAnnLR3TaggedKSeedBoundary,
  `rcic.RcicAnnLR3TaggedKCoherenceBoundary
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3TaggedKModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3TaggedK: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3TaggedK: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3TaggedK: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3TaggedK: {total} public declarations checked"
-- END RCIC_LR3_TAGGED_K_ROOTS
