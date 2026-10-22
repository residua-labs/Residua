import Lean
import rcic.RcicAnnLR3NeutralCodes
import rcic.RcicAnnLR3NeutralPi
import rcic.RcicAnnLR3NeutralDataFamily
import rcic.RcicAnnLR3PairedStatements
import rcic.RcicAnnLR3PairedArms
import rcic.RcicAnnLR3PairedProducer
import rcic.RcicAnnLR3PairedLit

/-!
Bounded paired logical-relation interfaces and concrete neutral producers.
Check every public declaration originating in the six new proof modules,
including generated public declarations. Compiler internal names are not
API declarations; collectAxioms traverses all dependencies of every public
root, including private proof dependencies. The full source fundamental
theorem and integrated Pi/family Code grammar remain open. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_PAIRED_PRODUCER_ROOTS
private def routeCLR3PairedProducerModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3NeutralCodes,
  `rcic.RcicAnnLR3NeutralPi,
  `rcic.RcicAnnLR3NeutralDataFamily,
  `rcic.RcicAnnLR3PairedStatements,
  `rcic.RcicAnnLR3PairedArms,
  `rcic.RcicAnnLR3PairedProducer,
  `rcic.RcicAnnLR3PairedLit
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3PairedProducerModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3PairedProducer: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3PairedProducer: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3PairedProducer: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3PairedProducer: {total} public declarations checked"
-- END RCIC_LR3_PAIRED_PRODUCER_ROOTS
