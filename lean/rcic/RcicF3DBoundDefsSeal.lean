import Lean
import rcic.RcicF3DBoundDefs
import rcic.RcicF3DBoundBridge
/-!
Bounded audit of every public declaration in `RcicF3DBoundDefs` (the class-D
instance bound `BoundDG` and the condition `RecBelowCtors`) and
`RcicF3DBoundBridge` (`BoundDG` from `BoundG` under `RecBelowCtors`). Only
propext and Quot.sound are permitted. No consistency result is asserted.
closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_F3D_BOUND_DEFS_ROOTS
private def f3DBoundDefsModules : Array Lean.Name := #[
  `rcic.RcicF3DBoundDefs,
  `rcic.RcicF3DBoundBridge
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in f3DBoundDefsModules do
    let some midx := env.getModuleIdx? mod
      | throwError "F3DBoundDefs: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "F3DBoundDefs: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "F3DBoundDefs: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"F3DBoundDefs: {total} public declarations checked"
-- END RCIC_F3D_BOUND_DEFS_ROOTS
