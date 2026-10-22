import Lean
import rcic.RcicAnnLR3EnvironmentPortConditions
import rcic.RcicAnnLR3EnvironmentHookControls
import rcic.RcicAnnLR3NativeMemberValues
import rcic.RcicAnnLR3EnvironmentMemberInsertion
import rcic.RcicAnnLR3EnvironmentMemberControls
import rcic.RcicAnnLR3EnvironmentMemberPorts
import rcic.RcicAnnLR3NativeTelescopeValues
import rcic.RcicAnnLR3EnvironmentTelescopeInsertion
import rcic.RcicAnnLR3EnvironmentTelescopePorts
import rcic.RcicAnnLR3CandidateAction
import rcic.RcicAnnLR3CandidateActionSource
import rcic.RcicAnnLR3CandidateActionProducts
import rcic.RcicAnnLR3EnvironmentTelescopeAction
import rcic.RcicAnnLR3EnvironmentTelescopeActionControls
import rcic.RcicAnnLR3IndexedFamilyDecoder
import rcic.RcicAnnLR3IndexedAccControl
import rcic.RcicAnnLR3IndexedFamilyElimination
import rcic.RcicAnnLR3SelectedFamilyElimination
import rcic.RcicAnnLR3RetainedAccFamily
import rcic.RcicAnnLR3RetainedAccEnvironment

/-!
Bounded continuation of cc issuecomment-6338028752 from f581ae3980.
Audits every public declaration of the named EnvironmentEval ports,
compositional typed-member/telescope policies, retained universe actions,
proof-valued product constructors and indexed legal-tree producers.
The complete source hierarchy, generic recursors and paired Fundamental
remain open. This seal introduces no public API. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_SEMANTIC_ACTION_ROOTS
private def routeCLR3SemanticActionModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3EnvironmentPortConditions,
  `rcic.RcicAnnLR3EnvironmentHookControls,
  `rcic.RcicAnnLR3NativeMemberValues,
  `rcic.RcicAnnLR3EnvironmentMemberInsertion,
  `rcic.RcicAnnLR3EnvironmentMemberControls,
  `rcic.RcicAnnLR3EnvironmentMemberPorts,
  `rcic.RcicAnnLR3NativeTelescopeValues,
  `rcic.RcicAnnLR3EnvironmentTelescopeInsertion,
  `rcic.RcicAnnLR3EnvironmentTelescopePorts,
  `rcic.RcicAnnLR3CandidateAction,
  `rcic.RcicAnnLR3CandidateActionSource,
  `rcic.RcicAnnLR3CandidateActionProducts,
  `rcic.RcicAnnLR3EnvironmentTelescopeAction,
  `rcic.RcicAnnLR3EnvironmentTelescopeActionControls,
  `rcic.RcicAnnLR3IndexedFamilyDecoder,
  `rcic.RcicAnnLR3IndexedAccControl,
  `rcic.RcicAnnLR3IndexedFamilyElimination,
  `rcic.RcicAnnLR3SelectedFamilyElimination,
  `rcic.RcicAnnLR3RetainedAccFamily,
  `rcic.RcicAnnLR3RetainedAccEnvironment
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3SemanticActionModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3SemanticAction: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3SemanticAction: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3SemanticAction: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3SemanticAction: {total} public declarations checked"
-- END RCIC_LR3_SEMANTIC_ACTION_ROOTS
