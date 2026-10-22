import Lean
import rcic.RcicAnnLR3NeutralPER
import rcic.RcicAnnLR3NeutralK
import rcic.RcicAnnLR3NeutralExtraction
import rcic.RcicAnnLR3NeutralControls
import rcic.RcicAnnLR3NeutralKSource
import rcic.RcicAnnLR3NeutralFamily

/-!
Bounded neutral-PER algebra, positive controls, extraction interface and
inhabited K-guard audit. Check every public declaration originating in the
six new proof modules, including generated public declarations. Compiler
internal names are not API declarations; collectAxioms traverses the
dependencies of every public root, including private proof dependencies.
No global model, all-arm supply or closure claim is made. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_NEUTRAL_PER_ROOTS
private def routeCLR3NeutralPERModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3NeutralPER,
  `rcic.RcicAnnLR3NeutralK,
  `rcic.RcicAnnLR3NeutralExtraction,
  `rcic.RcicAnnLR3NeutralControls,
  `rcic.RcicAnnLR3NeutralKSource,
  `rcic.RcicAnnLR3NeutralFamily
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3NeutralPERModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3NeutralPER: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3NeutralPER: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3NeutralPER: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3NeutralPER: {total} public declarations checked"
-- END RCIC_LR3_NEUTRAL_PER_ROOTS
