import Lean
import rcic.RcicAnnLR3PairedLookup

/-!
Seal for the paired lookup-arms module `RcicAnnLR3PairedLookup`:
checks every public declaration originating in the module, including
generated public declarations.  Compiler internal names are not API
declarations; collectAxioms traverses all dependencies of every public
root, including private proof dependencies.  The two arm supplies are
conditional consumers under the named `ImageBvarRelL`/`ImageBvarRelR`
residuals; the lookup/`Ty_bvar`/`Conv_zetaLocal` arms themselves remain
open pending those model laws.  closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN GLM_SR3_PAIREDLOOKUP_ROOTS
private def pairedLookupModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3PairedLookup
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in pairedLookupModules do
    let some midx := env.getModuleIdx? mod
      | throwError "PairedLookup: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "PairedLookup: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "PairedLookup: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"PairedLookup: {total} public declarations checked"
-- END GLM_SR3_PAIREDLOOKUP_ROOTS
