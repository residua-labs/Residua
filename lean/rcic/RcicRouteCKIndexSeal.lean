import Lean
import rcic.RcicRouteCKContextBoundary
import rcic.RcicAnnKIndexLaws
import rcic.RcicAnnKStage
import rcic.RcicAnnKTransport
import rcic.RcicAnnKEqPositive
import rcic.RcicAnnKOldLRBoundary
import rcic.RcicRouteCIndexSyntactic
import rcic.RcicRouteCIndexTransport
import rcic.RcicRouteCIndexFamilyFragment
import rcic.RcicRouteCIndexFamilyPer

/-!
Bounded R1-K / R2 audit. Check every public declaration originating in the
new modules, including generated public declarations. Compiler-internal
names are not API declarations; dependencies of every public root are
traversed by collectAxioms, including private proof dependencies.
No global row-supply or closure claim is made here. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def routeCKIndexModules : Array Lean.Name := #[
  `rcic.RcicRouteCKContextBoundary,
  `rcic.RcicAnnKIndexLaws,
  `rcic.RcicAnnKStage,
  `rcic.RcicAnnKTransport,
  `rcic.RcicAnnKEqPositive,
  `rcic.RcicAnnKOldLRBoundary,
  `rcic.RcicRouteCIndexSyntactic,
  `rcic.RcicRouteCIndexTransport,
  `rcic.RcicRouteCIndexFamilyFragment,
  `rcic.RcicRouteCIndexFamilyPer
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCKIndexModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCKIndex: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCKIndex: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCKIndex: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCKIndex: {total} public declarations checked"
