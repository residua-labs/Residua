import Lean
import rcic.RcicAnnLR3EnvLookup

/-!
Seal for the EnvironmentEval lookup/lifting-arms module
`RcicAnnLR3EnvLookup`: checks every public declaration originating in
the module, including generated public declarations.  Compiler internal
names are not API declarations; collectAxioms traverses all dependencies
of every public root, including private proof dependencies.

The arm supplies are conditional consumers under the named
`MemberBodyLiftId` (discharged from `EnvWfA` via the supplied telescope
ports) and `FamilyLiftId` (discharged at `hook E neutralFamilySyntax` via
the supplied `HookLiftFixed` leg); the `withBottom`-adjunction is
discharged at `model E H` by `InductiveCodes.code_saturated` on the
decoded `CodeI` fibres (`envBvarRel{L,R,}_of_code`), so the
contract-facing suppliers carry no residual premise.  closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN GLM_SR3_ENVLOOKUP_ROOTS
private def envLookupModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3EnvLookup
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in envLookupModules do
    let some midx := env.getModuleIdx? mod
      | throwError "EnvLookup: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "EnvLookup: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "EnvLookup: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"EnvLookup: {total} public declarations checked"
-- END GLM_SR3_ENVLOOKUP_ROOTS
