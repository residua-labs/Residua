import Lean
import rcic.RcicAnnLR3OptionSoundUniverse
import rcic.RcicAnnLR3OptionSoundInterface
import rcic.RcicAnnLR3RCodeSoundKripke
import rcic.RcicAnnLR3ImpredicativePiProbe
import rcic.RcicAnnLR3RCodeSoundPiProp
import rcic.RcicAnnLR3SoundUniverseRealizationBoundary
import rcic.RcicAnnLR3TypeZeroTowerProbe
import rcic.RcicAnnLR3TowerCodeSystem
import rcic.RcicAnnLR3TowerSourcePi
import rcic.RcicAnnLR3CandidateTowerProbe
import rcic.RcicAnnLR3CandidateTowerCoherence
import rcic.RcicAnnLR3NonvacuityChecks
import rcic.RcicAnnLR3NeutralReflectionProbe
import rcic.RcicAnnLR3ImageKeyedCodeSystem
import rcic.RcicAnnLR3CandidateCodeSystem
import rcic.RcicAnnLR3CandidateReader
import rcic.RcicAnnLR3KindCandidateProbe
import rcic.RcicAnnLR3EqTracer
import rcic.RcicAnnLR3CandidateSubstitution
import rcic.RcicAnnLR3CandidateReflection
import rcic.RcicAnnLR3CandidateFundamental
import rcic.RcicAnnLR3EqTargetIota
import rcic.RcicAnnLR3IndexFamilyHook
import rcic.RcicAnnLR3EqReflectionChoice
import rcic.RcicAnnLR3EqKLikeHook
import rcic.RcicAnnLR3LevelCodeSystem
import rcic.RcicAnnLR3LevelGirard
import rcic.RcicAnnLR3LevelGirardSystem
import rcic.RcicAnnLR3LevelSubstitution
import rcic.RcicAnnLR3LevelReader
import rcic.RcicAnnLR3LevelFundamental
import rcic.RcicAnnLR3ContentCodes
import rcic.RcicAnnLR3ContentJ
import rcic.RcicAnnLR3ContentJTarget
import rcic.RcicAnnLR3DenoteCont
import rcic.RcicAnnLR3ContentUniverseBoundary
import rcic.RcicAnnLR3LevelGeneric
import rcic.RcicAnnLR3ContentJMutant
import rcic.RcicAnnLR3EqKRepair
import rcic.RcicAnnLR3GenericReflectionBoundary
import rcic.RcicAnnLR3ObservationReflection
/-!
Bounded audit of every public declaration in the cc route-C continuation
modules (stacked on the Sound increment), including generated public
declarations and transitive private dependencies. Only propext and
Quot.sound are permitted. No full Foundation build or completed semantic
model is asserted. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_CC_ROOTS
private def routeCLR3CcModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3OptionSoundUniverse,
  `rcic.RcicAnnLR3OptionSoundInterface,
  `rcic.RcicAnnLR3RCodeSoundKripke,
  `rcic.RcicAnnLR3ImpredicativePiProbe,
  `rcic.RcicAnnLR3RCodeSoundPiProp,
  `rcic.RcicAnnLR3SoundUniverseRealizationBoundary,
  `rcic.RcicAnnLR3TypeZeroTowerProbe,
  `rcic.RcicAnnLR3TowerCodeSystem,
  `rcic.RcicAnnLR3TowerSourcePi,
  `rcic.RcicAnnLR3CandidateTowerProbe,
  `rcic.RcicAnnLR3CandidateTowerCoherence,
  `rcic.RcicAnnLR3NonvacuityChecks,
  `rcic.RcicAnnLR3NeutralReflectionProbe,
  `rcic.RcicAnnLR3ImageKeyedCodeSystem,
  `rcic.RcicAnnLR3CandidateCodeSystem,
  `rcic.RcicAnnLR3CandidateReader,
  `rcic.RcicAnnLR3KindCandidateProbe,
  `rcic.RcicAnnLR3EqTracer,
  `rcic.RcicAnnLR3CandidateSubstitution,
  `rcic.RcicAnnLR3CandidateReflection,
  `rcic.RcicAnnLR3CandidateFundamental,
  `rcic.RcicAnnLR3EqTargetIota,
  `rcic.RcicAnnLR3IndexFamilyHook,
  `rcic.RcicAnnLR3EqReflectionChoice,
  `rcic.RcicAnnLR3EqKLikeHook,
  `rcic.RcicAnnLR3LevelCodeSystem,
  `rcic.RcicAnnLR3LevelGirard,
  `rcic.RcicAnnLR3LevelGirardSystem,
  `rcic.RcicAnnLR3LevelSubstitution,
  `rcic.RcicAnnLR3LevelReader,
  `rcic.RcicAnnLR3LevelFundamental,
  `rcic.RcicAnnLR3ContentCodes,
  `rcic.RcicAnnLR3ContentJ,
  `rcic.RcicAnnLR3ContentJTarget,
  `rcic.RcicAnnLR3DenoteCont,
  `rcic.RcicAnnLR3ContentUniverseBoundary,
  `rcic.RcicAnnLR3LevelGeneric,
  `rcic.RcicAnnLR3ContentJMutant,
  `rcic.RcicAnnLR3EqKRepair,
  `rcic.RcicAnnLR3GenericReflectionBoundary,
  `rcic.RcicAnnLR3ObservationReflection
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3CcModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3Cc: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3Cc: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3Cc: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3Cc: {total} public declarations checked"
-- END RCIC_LR3_CC_ROOTS
