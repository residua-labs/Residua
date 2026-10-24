import Lean
import rcic.RcicRiskTier
/-!
Bounded audit of every public declaration in `RcicRiskTier`, the additive
kernel soundness tier statement layer. Only propext and Quot.sound are
permitted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_RISK_TIER_ROOTS
private def riskTierModules : Array Lean.Name := #[
  `rcic.RcicRiskTier
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in riskTierModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RiskTier: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RiskTier: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RiskTier: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RiskTier: {total} public declarations checked"
-- END RCIC_RISK_TIER_ROOTS
