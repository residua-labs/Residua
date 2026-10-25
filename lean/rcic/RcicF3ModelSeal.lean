import Lean
import rcic.RcicF3PSet
import rcic.RcicF3Univ
import rcic.RcicF3Small
import rcic.RcicF3Denote
import rcic.RcicF3Sound
import rcic.RcicF3Core
import rcic.RcicF3Fund
import rcic.RcicF3Env
import rcic.RcicF3Stage
import rcic.RcicF3Table
import rcic.RcicF3Tel
import rcic.RcicF3EnvModel
import rcic.RcicF3FalseEnv
import rcic.RcicF3EnvSound
/-!
Bounded audit of every public declaration in the cc F3 set-model and
fundamental-theorem modules (`research/rcic/routec-f3/F3_PLAN.md`), including generated public
declarations and transitive private dependencies. Only propext and
Quot.sound are permitted: the choice operator the plan uses is a theorem
premise, never an axiom. No completed model is asserted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_F3_MODEL_ROOTS
private def f3ModelModules : Array Lean.Name := #[
  `rcic.RcicF3PSet,
  `rcic.RcicF3Univ,
  `rcic.RcicF3Small,
  `rcic.RcicF3Denote,
  `rcic.RcicF3Sound,
  `rcic.RcicF3Core,
  `rcic.RcicF3Fund,
  `rcic.RcicF3Env,
  `rcic.RcicF3Stage,
  `rcic.RcicF3Table,
  `rcic.RcicF3Tel,
  `rcic.RcicF3EnvModel,
  `rcic.RcicF3FalseEnv,
  `rcic.RcicF3EnvSound
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in f3ModelModules do
    let some midx := env.getModuleIdx? mod
      | throwError "F3Model: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "F3Model: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "F3Model: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"F3Model: {total} public declarations checked"
-- END RCIC_F3_MODEL_ROOTS
