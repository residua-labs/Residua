import Lean
import rcic.RcicClassABCex
import rcic.RcicClassABDelta
import rcic.RcicClassABTooth
import rcic.RcicClassABW

/-!
Bounded audit of every public declaration in the cc-classab modules (`RcicClassABCex`,
`RcicClassABDelta`, `RcicClassABTooth`, `RcicClassABW`), including generated public declarations.
Only `propext` and `Quot.sound` are permitted. No row in class (a) or (b) is claimed.
closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_CLASSAB_ROOTS
private def classABModules : Array Lean.Name := #[
  `rcic.RcicClassABCex,
  `rcic.RcicClassABDelta,
  `rcic.RcicClassABTooth,
  `rcic.RcicClassABW
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in classABModules do
    let some midx := env.getModuleIdx? mod
      | throwError "ClassAB: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "ClassAB: {root} has forbidden axioms {forbidden}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "ClassAB: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"[rcic_classab_seal] {total} public declarations checked; axioms ⊆ [propext, Quot.sound]"
-- END RCIC_CLASSAB_ROOTS
