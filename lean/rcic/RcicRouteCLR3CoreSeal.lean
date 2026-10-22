import Lean
import rcic.RcicAnnSortSynthesisA3
import rcic.RcicAnnLR3Positive
import rcic.RcicAnnLR3Head
import rcic.RcicAnnLR3HeadLayer
import rcic.RcicAnnLR3Chain
import rcic.RcicAnnLR3Sort
import rcic.RcicAnnLR3Family
import rcic.RcicAnnLR3PropEq
import rcic.RcicAnnLR3Core
import rcic.RcicAnnLR3EqHead

/-!
Bounded LR3 core audit. Check every public declaration originating in the
new modules, including generated public declarations. Compiler-internal
names are not API declarations; dependencies of every public root are
traversed by collectAxioms, including private proof dependencies.
No global row-supply or closure claim is made here. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def routeCLR3CoreModules : Array Lean.Name := #[
  `rcic.RcicAnnSortSynthesisA3,
  `rcic.RcicAnnLR3Positive,
  `rcic.RcicAnnLR3Head,
  `rcic.RcicAnnLR3HeadLayer,
  `rcic.RcicAnnLR3Chain,
  `rcic.RcicAnnLR3Sort,
  `rcic.RcicAnnLR3Family,
  `rcic.RcicAnnLR3PropEq,
  `rcic.RcicAnnLR3Core,
  `rcic.RcicAnnLR3EqHead
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3CoreModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3Core: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3Core: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3Core: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3Core: {total} public declarations checked"
