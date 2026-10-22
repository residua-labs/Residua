import Lean
import rcic.RcicAnnLR3TypedPER
import rcic.RcicAnnLR3UnitContextBoundary
import rcic.RcicAnnLR3TypedInductive
import rcic.RcicAnnLR3TruthAxiomBoundary
import rcic.RcicAnnLR3TypedStatements
import rcic.RcicAnnLR3TypedConstantModel
import rcic.RcicAnnLR3TypedArms
import rcic.RcicAnnLR3TypedArmBoundary
import rcic.RcicAnnLR3TypedCoverageBoundary

/-!
Bounded LR3 typed-layer and inhabited-boundary audit. Check every public declaration originating in the
new modules, including generated public declarations. Compiler-internal
names are not API declarations; dependencies of every public root are
traversed by collectAxioms, including private proof dependencies.
No global row-supply or closure claim is made here. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_TYPED_LAYER_ROOTS
private def routeCLR3TypedLayerModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3TypedPER,
  `rcic.RcicAnnLR3UnitContextBoundary,
  `rcic.RcicAnnLR3TypedInductive,
  `rcic.RcicAnnLR3TruthAxiomBoundary,
  `rcic.RcicAnnLR3TypedStatements,
  `rcic.RcicAnnLR3TypedConstantModel,
  `rcic.RcicAnnLR3TypedArms,
  `rcic.RcicAnnLR3TypedArmBoundary,
  `rcic.RcicAnnLR3TypedCoverageBoundary
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3TypedLayerModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3TypedLayer: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3TypedLayer: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3TypedLayer: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3TypedLayer: {total} public declarations checked"
-- END RCIC_LR3_TYPED_LAYER_ROOTS
