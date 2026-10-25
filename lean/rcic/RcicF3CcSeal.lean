import Lean
import rcic.RcicF3KT
import rcic.RcicF3Data
import rcic.RcicF3Fam
import rcic.RcicF3Inv
import rcic.RcicF3Ctor
import rcic.RcicF3Rec
import rcic.RcicF3Syn
import rcic.RcicF3Lvl
import rcic.RcicF3RecMem
import rcic.RcicF3Iota
import rcic.RcicF3SemTel
import rcic.RcicF3PropIota
import rcic.RcicF3IotaIdx
import rcic.RcicF3Agree
import rcic.RcicF3EnvG
import rcic.RcicF3GroupWalk
import rcic.RcicF3Target
import rcic.RcicF3GroupFacts
import rcic.RcicF3GroupSound
import rcic.RcicF3StageFacts
import rcic.RcicF3Layout
import rcic.RcicF3PropEmpty
import rcic.RcicF3LoopFixture
import rcic.RcicF3FieldSmall
import rcic.RcicF3MainG
import rcic.RcicF3ClassFixtures
import rcic.RcicF3NatFixture
import rcic.RcicF3AndFixture
import rcic.RcicF3OrFixture
import rcic.RcicF3VecFixture
import rcic.RcicF3StageN
import rcic.RcicF3NegControl
import rcic.RcicF3Bridge
import rcic.RcicF3FamFix
import rcic.RcicF3LimDef
import rcic.RcicF3FamLim
import rcic.RcicF3RecCore
import rcic.RcicF3MinorRec
import rcic.RcicF3RecMemRec
import rcic.RcicF3RecValRec
/-!
Bounded audit of every public declaration in the cc F3 consistency-model
modules (`research/rcic/routec-f3/F3_PLAN.md`), including generated public
declarations and transitive private dependencies. Only propext and
Quot.sound are permitted: the choice operator the plan uses is a theorem
premise, never an axiom. No completed model is asserted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_F3_CC_ROOTS
private def f3CcModules : Array Lean.Name := #[
  `rcic.RcicF3KT,
  `rcic.RcicF3Data,
  `rcic.RcicF3Fam,
  `rcic.RcicF3Inv,
  `rcic.RcicF3Ctor,
  `rcic.RcicF3Rec,
  `rcic.RcicF3Syn,
  `rcic.RcicF3Lvl,
  `rcic.RcicF3RecMem,
  `rcic.RcicF3Iota,
  `rcic.RcicF3SemTel,
  `rcic.RcicF3PropIota,
  `rcic.RcicF3IotaIdx,
  `rcic.RcicF3Agree,
  `rcic.RcicF3EnvG,
  `rcic.RcicF3GroupWalk,
  `rcic.RcicF3GroupFacts,
  `rcic.RcicF3GroupSound,
  `rcic.RcicF3StageFacts,
  `rcic.RcicF3Layout,
  `rcic.RcicF3PropEmpty,
  `rcic.RcicF3LoopFixture,
  `rcic.RcicF3FieldSmall,
  `rcic.RcicF3MainG,
  `rcic.RcicF3ClassFixtures,
  `rcic.RcicF3NatFixture,
  `rcic.RcicF3AndFixture,
  `rcic.RcicF3OrFixture,
  `rcic.RcicF3VecFixture,
  `rcic.RcicF3StageN,
  `rcic.RcicF3NegControl,
  `rcic.RcicF3Bridge,
  `rcic.RcicF3FamFix,
  `rcic.RcicF3LimDef,
  `rcic.RcicF3FamLim,
  `rcic.RcicF3RecCore,
  `rcic.RcicF3MinorRec,
  `rcic.RcicF3RecMemRec,
  `rcic.RcicF3RecValRec
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in f3CcModules do
    let some midx := env.getModuleIdx? mod
      | throwError "F3Cc: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "F3Cc: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "F3Cc: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"F3Cc: {total} public declarations checked"
-- END RCIC_F3_CC_ROOTS
