import Lean
import rcic.RcicF3Whnf
import rcic.RcicF3WhnfSyn
import rcic.RcicF3DTransfer
import rcic.RcicF3DEnv
import rcic.RcicF3DNorm
import rcic.RcicF3DMinor
import rcic.RcicF3DRec
import rcic.RcicF3DIota
import rcic.RcicF3DCtor
import rcic.RcicF3DRoles
import rcic.RcicF3DMain
import rcic.RcicF3DFixture
import rcic.RcicF3DBoundShape
/-!
Bounded audit of every public declaration in the fable-f3d class D
consistency-model modules (F3 class D, δ-hidden direct recursion;
`research/rcic/routec-f3/F3_PLAN.md`), including generated public
declarations and transitive private dependencies. Only propext and
Quot.sound are permitted: the choice operator the model uses is a theorem
premise (`Premises4`), never an axiom. No completed model is asserted.
closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_F3D_ROOTS
private def f3DModules : Array Lean.Name := #[
  `rcic.RcicF3Whnf,
  `rcic.RcicF3WhnfSyn,
  `rcic.RcicF3DTransfer,
  `rcic.RcicF3DEnv,
  `rcic.RcicF3DNorm,
  `rcic.RcicF3DMinor,
  `rcic.RcicF3DRec,
  `rcic.RcicF3DIota,
  `rcic.RcicF3DCtor,
  `rcic.RcicF3DRoles,
  `rcic.RcicF3DMain,
  `rcic.RcicF3DFixture,
  `rcic.RcicF3DBoundShape
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in f3DModules do
    let some midx := env.getModuleIdx? mod
      | throwError "F3D: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "F3D: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "F3D: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"F3D: {total} public declarations checked"
-- END RCIC_F3D_ROOTS
