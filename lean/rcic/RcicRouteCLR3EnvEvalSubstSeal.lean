import Lean
import rcic.RcicAnnLR3EnvEvalSubst

/-!
Seal audit for `RcicAnnLR3EnvEvalSubst`: every public declaration of the
EnvironmentEval substitution/let group (the paired substitution port, the
let evaluation equation, and `Ty_letE`, `Conv_zeta`, `Conv_letE`,
`Ty_app`, `Conv_app`, `Conv_beta` at the telescope image) is collected
and its axiom set checked against `{propext, Quot.sound}`. The complete
source hierarchy, generic recursors and paired Fundamental remain open.
This seal introduces no public API. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_ENVEVALSUBST_ROOTS
private def routeCLR3EnvEvalSubstModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3EnvEvalSubst
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3EnvEvalSubstModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3EnvEvalSubst: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3EnvEvalSubst: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3EnvEvalSubst: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3EnvEvalSubst: {total} public declarations checked"
-- END RCIC_LR3_ENVEVALSUBST_ROOTS
