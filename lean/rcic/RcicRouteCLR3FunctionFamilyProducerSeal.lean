import Lean
import rcic.RcicAnnLR3UnifiedPi
import rcic.RcicAnnLR3ReflectionDemand
import rcic.RcicAnnLR3FunctionEval
import rcic.RcicAnnLR3FunctionSaturation
import rcic.RcicAnnLR3DecodedPi
import rcic.RcicAnnLR3DependentFamily
import rcic.RcicAnnLR3FunctionCoreControls

/-!
Bounded continuation for finite-demand dependent reflection, concrete
function evaluation, saturation, and explicit-tree dependent elimination.
Audit every public declaration from the seven new proof modules,
including generated public declarations and all transitive private
proof dependencies. The integrated Pi/family Code grammar, admitted
member interpretation, and full fundamental theorem remain open.
closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_FUNCTION_FAMILY_PRODUCER_ROOTS
private def routeCLR3FunctionFamilyProducerModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3UnifiedPi,
  `rcic.RcicAnnLR3ReflectionDemand,
  `rcic.RcicAnnLR3FunctionEval,
  `rcic.RcicAnnLR3FunctionSaturation,
  `rcic.RcicAnnLR3DecodedPi,
  `rcic.RcicAnnLR3DependentFamily,
  `rcic.RcicAnnLR3FunctionCoreControls
]
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3FunctionFamilyProducerModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3FunctionFamilyProducer: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3FunctionFamilyProducer: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3FunctionFamilyProducer: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3FunctionFamilyProducer: {total} public declarations checked"
-- END RCIC_LR3_FUNCTION_FAMILY_PRODUCER_ROOTS
