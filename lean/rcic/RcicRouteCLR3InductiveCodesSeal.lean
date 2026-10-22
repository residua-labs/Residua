import Lean
import rcic.RcicAnnLR3InductiveFamily
import rcic.RcicAnnLR3InductiveCodes
import rcic.RcicAnnLR3InductiveCodeControls
import rcic.RcicAnnLR3UniverseDecoderBoundary
import rcic.RcicAnnLR3InductiveUniverseSyntaxProbe
import rcic.RcicAnnLR3InductiveApplicationArms
import rcic.RcicAnnLR3InductiveIrrelevance
import rcic.RcicAnnLR3InductiveLambdaArms
import rcic.RcicAnnLR3InductiveEtaArms
import rcic.RcicAnnLR3InductiveFunctionControls
import rcic.RcicAnnLR3InductiveMemberBoundary

/-!
Bounded continuation for positive relational product/fixed-Nat codes,
explicit family representatives, six new exact paired contracts, and
inhabited construction/evaluator boundaries. Every public declaration
from the eleven new proof modules is audited, including generated
public declarations and transitive private proof dependencies.
Full universe closure, all-code neutral reflection, admitted members,
and generic recursors remain open. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_INDUCTIVE_CODES_ROOTS
private def routeCLR3InductiveCodesModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3InductiveFamily,
  `rcic.RcicAnnLR3InductiveCodes,
  `rcic.RcicAnnLR3InductiveCodeControls,
  `rcic.RcicAnnLR3UniverseDecoderBoundary,
  `rcic.RcicAnnLR3InductiveUniverseSyntaxProbe,
  `rcic.RcicAnnLR3InductiveApplicationArms,
  `rcic.RcicAnnLR3InductiveIrrelevance,
  `rcic.RcicAnnLR3InductiveLambdaArms,
  `rcic.RcicAnnLR3InductiveEtaArms,
  `rcic.RcicAnnLR3InductiveFunctionControls,
  `rcic.RcicAnnLR3InductiveMemberBoundary
]
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3InductiveCodesModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3InductiveCodes: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3InductiveCodes: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3InductiveCodes: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3InductiveCodes: {total} public declarations checked"
-- END RCIC_LR3_INDUCTIVE_CODES_ROOTS
