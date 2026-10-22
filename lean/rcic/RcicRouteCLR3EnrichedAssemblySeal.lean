import Lean
import rcic.RcicAnnLR3RawAttachmentBoundary
import rcic.RcicAnnLR3EnrichedReflectionBoundary
import rcic.RcicAnnLR3ConfiguredAliasBoundary
import rcic.RcicAnnLR3RelationalAssemblyBoundary

/-!
Bounded continuation of cc issuecomment-6338649040 from 24d45b385b.
Audits every public declaration of the unchanged-erasure attachment,
positive-stage relational reflection and configured-alias boundaries.
All source premises of the controls are supplied. The requested enriched
model is not supplied: these boundaries show why the accepted components
cannot be assembled unchanged. No source SortUniq/ZSC counterexample is
claimed. This seal introduces no public API. closure_claim = 0.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN RCIC_LR3_ENRICHED_ASSEMBLY_ROOTS
private def routeCLR3EnrichedAssemblyModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3RawAttachmentBoundary,
  `rcic.RcicAnnLR3EnrichedReflectionBoundary,
  `rcic.RcicAnnLR3ConfiguredAliasBoundary,
  `rcic.RcicAnnLR3RelationalAssemblyBoundary
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3EnrichedAssemblyModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3EnrichedAssembly: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3EnrichedAssembly: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3EnrichedAssembly: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3EnrichedAssembly: {total} public declarations checked"
-- END RCIC_LR3_ENRICHED_ASSEMBLY_ROOTS
