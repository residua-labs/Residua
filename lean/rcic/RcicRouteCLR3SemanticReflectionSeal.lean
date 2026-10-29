import Lean
import rcic.RcicAnnLR3GuardedEtaGluing
import rcic.RcicAnnLR3KPiEtaReflection
import rcic.RcicAnnLR3RetainedArmTransfer
import rcic.RcicAnnLR3RetainedOpenEqEvaluation
import rcic.RcicAnnLR3SemanticDomainBoundary
import rcic.RcicAnnLR3UniverseSpineBoundary
import rcic.RcicAnnLR3SemanticPiImageBoundary
import rcic.RcicAnnLR3CertifiedUniverseEta
import rcic.RcicAnnLR3ReflectiveConversionUniverse
import rcic.RcicAnnLR3SemanticPiCode
import rcic.RcicAnnLR3SemanticSpineCompletion
/-!
Bounded audit of every public declaration in the eleven new proof modules,
including generated public declarations and transitive private dependencies.
Only propext and Quot.sound are permitted. No full Foundation build or
completed semantic model is asserted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_SEMANTIC_REFLECTION_ROOTS
private def routeCLR3SemanticReflectionModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3GuardedEtaGluing,
  `rcic.RcicAnnLR3KPiEtaReflection,
  `rcic.RcicAnnLR3RetainedArmTransfer,
  `rcic.RcicAnnLR3RetainedOpenEqEvaluation,
  `rcic.RcicAnnLR3SemanticDomainBoundary,
  `rcic.RcicAnnLR3UniverseSpineBoundary,
  `rcic.RcicAnnLR3SemanticPiImageBoundary,
  `rcic.RcicAnnLR3CertifiedUniverseEta,
  `rcic.RcicAnnLR3ReflectiveConversionUniverse,
  `rcic.RcicAnnLR3SemanticPiCode,
  `rcic.RcicAnnLR3SemanticSpineCompletion
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3SemanticReflectionModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3SemanticReflection: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3SemanticReflection: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3SemanticReflection: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3SemanticReflection: {total} public declarations checked"
-- END RCIC_LR3_SEMANTIC_REFLECTION_ROOTS
