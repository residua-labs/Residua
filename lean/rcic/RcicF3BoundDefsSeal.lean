import Lean
import rcic.RcicF3BoundDefs
/-!
Bounded audit of every public declaration in `RcicF3BoundDefs`, the instance
bound `BoundG` that the F3 consistency theorem takes as an antecedent (with
`RecNode`, `WalkB2`, `σOf`). Only propext and Quot.sound are permitted. No
consistency result is asserted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_F3_BOUND_DEFS_ROOTS
private def f3BoundDefsModules : Array Lean.Name := #[
  `rcic.RcicF3BoundDefs
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in f3BoundDefsModules do
    let some midx := env.getModuleIdx? mod
      | throwError "F3BoundDefs: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "F3BoundDefs: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "F3BoundDefs: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"F3BoundDefs: {total} public declarations checked"
-- END RCIC_F3_BOUND_DEFS_ROOTS
