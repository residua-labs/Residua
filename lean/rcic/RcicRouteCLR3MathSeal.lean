import Lean
import rcic.RcicAnnLR3NormalDemand
import rcic.RcicAnnLR3NormalSubstBoundary
import rcic.RcicAnnLR3SubstLaws
import rcic.RcicAnnLR3LetSubstBoundary
import rcic.RcicAnnLR3SubstReflectionBoundary
import rcic.RcicAnnLR3ProofIndexBoundary
import rcic.RcicAnnLR3SaturatedIndexBoundary
import rcic.RcicAnnLR3SaturatedNormalSubstBoundary
import rcic.RcicAnnLR3AppPrefix
import rcic.RcicAnnLR3NormalWk
import rcic.RcicAnnLR3IndexCrossTransport
import rcic.RcicAnnLR3HeadWk
import rcic.RcicAnnLR3FamilyKey
import rcic.RcicAnnLR3PinFamilyPositive
import rcic.RcicAnnLR3TypeSubstBoundary

/-!
Bounded LR3 mathematical repair audit. Check every public declaration originating in the
new modules, including generated public declarations. Compiler-internal
names are not API declarations; dependencies of every public root are
traversed by collectAxioms, including private proof dependencies.
No global row-supply or closure claim is made here. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def routeCLR3MathModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3NormalDemand,
  `rcic.RcicAnnLR3NormalSubstBoundary,
  `rcic.RcicAnnLR3SubstLaws,
  `rcic.RcicAnnLR3LetSubstBoundary,
  `rcic.RcicAnnLR3SubstReflectionBoundary,
  `rcic.RcicAnnLR3ProofIndexBoundary,
  `rcic.RcicAnnLR3SaturatedIndexBoundary,
  `rcic.RcicAnnLR3SaturatedNormalSubstBoundary,
  `rcic.RcicAnnLR3AppPrefix,
  `rcic.RcicAnnLR3NormalWk,
  `rcic.RcicAnnLR3IndexCrossTransport,
  `rcic.RcicAnnLR3HeadWk,
  `rcic.RcicAnnLR3FamilyKey,
  `rcic.RcicAnnLR3PinFamilyPositive,
  `rcic.RcicAnnLR3TypeSubstBoundary
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3MathModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3Math: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3Math: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3Math: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3Math: {total} public declarations checked"
