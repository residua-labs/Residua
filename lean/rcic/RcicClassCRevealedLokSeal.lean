import Lean
import rcic.RcicClassCRevealedLok

/-!
Bounded audit of every public declaration of `RcicClassCRevealedLok`. Only `propext` and `Quot.sound`
are permitted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_CLASSCLOK_ROOTS
private def classCLokModules : Array Lean.Name := #[
  `rcic.RcicClassCRevealedLok
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in classCLokModules do
    let some midx := env.getModuleIdx? mod
      | throwError "ClassCLok: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "ClassCLok: {root} has forbidden axioms {forbidden}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "ClassCLok: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"[rcic_classclok_seal] {total} public declarations checked; axioms ⊆ [propext, Quot.sound]"
-- END RCIC_CLASSCLOK_ROOTS
