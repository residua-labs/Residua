import Lean
import rcic.RcicAnnLR3SortCoherenceBoundary
import rcic.RcicAnnLR3SortSynthesisDemand
import rcic.RcicAnnLR3FrameSource
import rcic.RcicAnnLR3ReflInferenceBoundary
import rcic.RcicAnnLR3EqErasureReduction
import rcic.RcicAnnLR3GuardHeightBoundary
import rcic.RcicAnnLR3GuardHeightSemantic

/-!
Bounded LR3 coherence and erasure-boundary audit. Check every public declaration originating in the
new modules, including generated public declarations. Compiler-internal
names are not API declarations; dependencies of every public root are
traversed by collectAxioms, including private proof dependencies.
No global row-supply or closure claim is made here. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def routeCLR3CoherenceModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3SortCoherenceBoundary,
  `rcic.RcicAnnLR3SortSynthesisDemand,
  `rcic.RcicAnnLR3FrameSource,
  `rcic.RcicAnnLR3ReflInferenceBoundary,
  `rcic.RcicAnnLR3EqErasureReduction,
  `rcic.RcicAnnLR3GuardHeightBoundary,
  `rcic.RcicAnnLR3GuardHeightSemantic
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3CoherenceModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3Coherence: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3Coherence: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3Coherence: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3Coherence: {total} public declarations checked"
