import Lean
import rcic.RcicClassCCex
import rcic.RcicClassCRevealed
import rcic.RcicClassCMutant
import rcic.RcicClassCRevealedRows
import rcic.RcicClassCAxSpine

/-!
Bounded audit of every public declaration in the cc-classc modules (`RcicClassCCex`,
`RcicClassCRevealed`, `RcicClassCMutant`, `RcicClassCRevealedRows`, `RcicClassCAxSpine`), including generated public declarations. Only `propext` and `Quot.sound`
are permitted. No row in class (c) is claimed. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_CLASSC_ROOTS
private def classCModules : Array Lean.Name := #[
  `rcic.RcicClassCCex,
  `rcic.RcicClassCRevealed,
  `rcic.RcicClassCMutant,
  `rcic.RcicClassCRevealedRows,
  `rcic.RcicClassCAxSpine
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in classCModules do
    let some midx := env.getModuleIdx? mod
      | throwError "ClassC: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "ClassC: {root} has forbidden axioms {forbidden}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "ClassC: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"[rcic_classc_seal] {total} public declarations checked; axioms ⊆ [propext, Quot.sound]"
-- END RCIC_CLASSC_ROOTS
