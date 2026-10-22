import Lean
import rcic.RcicAnnLR3CandidateUniverse
import rcic.RcicAnnLR3CandidateCompletion
import rcic.RcicAnnLR3NoneUniverseBoundary
import rcic.RcicAnnLR3EnvironmentEval
import rcic.RcicAnnLR3EnvironmentEvalComposition
import rcic.RcicAnnLR3EnvironmentPi
import rcic.RcicAnnLR3EnvironmentEvalControls
import rcic.RcicAnnLR3EnvironmentLiteralBoundary
import rcic.RcicAnnLR3EnvironmentTypedNeutralBoundary
import rcic.RcicAnnLR3EnvironmentLambdaArms
import rcic.RcicAnnLR3EnvironmentArmSupply
import rcic.RcicAnnLR3AdmittedFamilyExtractor
import rcic.RcicAnnLR3AdmittedFamilyControls
import rcic.RcicAnnLR3FamilyLabelQuotient

/-!
Bounded continuation of cc issuecomment-6336496715. Checks every public
root of the new candidate algebra, undefined-level boundaries, actual
environment-aware finite evaluator, uniform eleven-arm cohort, admission
catalog and legal-label quotient producers. Complete candidate-aware source
universes, typed neutral members and generic recursors remain open.
The seal introduces no public API. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_CANDIDATE_ENVIRONMENT_ROOTS
private def routeCLR3CandidateEnvironmentModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3CandidateUniverse,
  `rcic.RcicAnnLR3CandidateCompletion,
  `rcic.RcicAnnLR3NoneUniverseBoundary,
  `rcic.RcicAnnLR3EnvironmentEval,
  `rcic.RcicAnnLR3EnvironmentEvalComposition,
  `rcic.RcicAnnLR3EnvironmentPi,
  `rcic.RcicAnnLR3EnvironmentEvalControls,
  `rcic.RcicAnnLR3EnvironmentLiteralBoundary,
  `rcic.RcicAnnLR3EnvironmentTypedNeutralBoundary,
  `rcic.RcicAnnLR3EnvironmentLambdaArms,
  `rcic.RcicAnnLR3EnvironmentArmSupply,
  `rcic.RcicAnnLR3AdmittedFamilyExtractor,
  `rcic.RcicAnnLR3AdmittedFamilyControls,
  `rcic.RcicAnnLR3FamilyLabelQuotient
]
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3CandidateEnvironmentModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3CandidateEnvironment: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3CandidateEnvironment: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3CandidateEnvironment: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3CandidateEnvironment: {total} public declarations checked"
-- END RCIC_LR3_CANDIDATE_ENVIRONMENT_ROOTS
