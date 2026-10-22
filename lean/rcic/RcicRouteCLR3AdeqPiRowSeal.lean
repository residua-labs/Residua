import Lean
import rcic.RcicAnnLR3AdeqRelation
import rcic.RcicAnnLR3AdeqNeutralObstructions
import rcic.RcicAnnLR3AdeqReadbackLaws

/-!
Bounded seal for the adequacy / readback `piRow` design and kernel-checked
modules (`RcicAnnLR3AdeqRelation`, `RcicAnnLR3AdeqNeutralObstructions`,
`RcicAnnLR3AdeqReadbackLaws`). Every public declaration from the new modules
is audited, including generated public declarations and transitive private
proof dependencies.
closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_ADEQ_PIROW_ROOTS
private def routeCLR3AdeqPiRowModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3AdeqRelation,
  `rcic.RcicAnnLR3AdeqNeutralObstructions,
  `rcic.RcicAnnLR3AdeqReadbackLaws
]
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3AdeqPiRowModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3AdeqPiRow: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3AdeqPiRow: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3AdeqPiRow: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3AdeqPiRow: {total} public declarations checked"
-- END RCIC_LR3_ADEQ_PIROW_ROOTS
