import Lean
import rcic.RcicAnnLR3EnvironmentPorts

/-!
Bounded seal for the swe-zeta EnvironmentEval port layer
(`rcic.RcicAnnLR3EnvironmentPorts`): audits every public declaration of the
literal-expansion and consts arm suppliers and their transport lemmas at the
`internalView E` / `hook E neutralFamilySyntax` composition. The complete
source hierarchy, generic recursors and paired Fundamental remain open. This
seal introduces no public API. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN SWE-ZETA LR3 ENVIRONMENT PORT ROOTS
private def routeCLR3EnvironmentPortsModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3EnvironmentPorts
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3EnvironmentPortsModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3EnvironmentPorts: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3EnvironmentPorts: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3EnvironmentPorts: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3EnvironmentPorts: {total} public declarations checked"
-- END SWE-ZETA LR3 ENVIRONMENT PORT ROOTS
