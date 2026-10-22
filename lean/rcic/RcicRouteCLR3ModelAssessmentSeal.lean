import Lean
import rcic.RcicAnnLR3StrictProofModelBoundary
import rcic.RcicAnnLR3ModelMembershipBoundary

/-!
Bounded LR3 model-assessment constructor-boundary audit. Check every public declaration originating in the
new modules, including generated public declarations. Compiler-internal
names are not API declarations; dependencies of every public root are
traversed by collectAxioms, including private proof dependencies.
No global row-supply or closure claim is made here. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def routeCLR3ModelAssessmentModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3StrictProofModelBoundary,
  `rcic.RcicAnnLR3ModelMembershipBoundary
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3ModelAssessmentModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3ModelAssessment: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3ModelAssessment: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3ModelAssessment: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3ModelAssessment: {total} public declarations checked"
