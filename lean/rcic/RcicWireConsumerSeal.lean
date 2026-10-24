import Lean
import rcic.RcicWireEmit
import rcic.RcicCertEmit
import rcic.RcicWireConsumer

/-!
Bounded audit of every public declaration in the F0 wire-consumer modules (`RcicWireEmit`,
`RcicCertEmit`, `RcicWireConsumer`), including generated public declarations. Only `propext` and
`Quot.sound` are permitted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_WIRECONSUMER_ROOTS
private def wireConsumerModules : Array Lean.Name := #[
  `rcic.RcicWireEmit,
  `rcic.RcicCertEmit,
  `rcic.RcicWireConsumer
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in wireConsumerModules do
    let some midx := env.getModuleIdx? mod
      | throwError "WireConsumer: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "WireConsumer: {root} has forbidden axioms {forbidden}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "WireConsumer: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"[rcic_wireconsumer_seal] {total} public declarations checked; axioms ⊆ [propext, Quot.sound]"
-- END RCIC_WIRECONSUMER_ROOTS
