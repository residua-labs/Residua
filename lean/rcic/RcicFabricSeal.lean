import Lean
import rcic.RcicFabricQ
import rcic.RcicFabricHonesty
import rcic.RcicFabricPatch

/-!
Seal for the agent-proof-fabric modules (ADR draft #7925 §5, plan #7929 P1): `RcicFabricQ` (slice 1:
`stmt_q` as a composition over the import encoding of #7927), `RcicFabricHonesty` (the honesty rule, Lean-first
for its Conflux gate) and `RcicFabricPatch` (a fact's Conflux patch fields).
It checks every public declaration originating in these modules, including generated public declarations,
against the axiom allowlist {propext, Quot.sound}. The tooling module `RcicFabricIndex` (an executable)
is not sealed and proves nothing. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN CC_FABRIC_SLICE1_ROOTS
private def fabricModules : Array Lean.Name := #[
  `rcic.RcicFabricQ,
  `rcic.RcicFabricHonesty,
  `rcic.RcicFabricPatch
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in fabricModules do
    let some midx := env.getModuleIdx? mod
      | throwError "Fabric: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "Fabric: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "Fabric: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"Fabric: {total} public declarations checked"
-- END CC_FABRIC_SLICE1_ROOTS
