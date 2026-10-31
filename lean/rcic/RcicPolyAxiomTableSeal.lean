import Lean
import rcic.RcicPolyAxiomTable

/-!
Audit the arity-preserving shared table fold and its parameterized fixture.
Only table construction and faithfulness are checked. `closure_claim = 0`.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := #[`rcic.RcicF3EnvG, `rcic.RcicPolyAxiomTable]
  let allowed := #[``propext, ``Quot.sound]
  for mod in modules do
    let some midx := env.getModuleIdx? mod
      | throwError "PolyAxiomTable: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        unless forbidden.isEmpty do
          throwError "PolyAxiomTable: {root} has forbidden axioms {forbidden}"
        count := count + 1
    if count == 0 then throwError "PolyAxiomTable: no declarations in {mod}"
    logInfo m!"PolyAxiomTable: {mod}: {count} public declarations axiom-audited"
  let roots := #[``Rcic.F3.PSet.envμBy,
    ``Rcic.F3.PSet.ReadsOKAlong, ``Rcic.F3.PSet.faithfulBy_envμBy,
    ``Rcic.F3.PSet.faithfulR_envμR,
    ``Rcic.F3.PSet.PolyAxiomTable.installed_at_declared_arity,
    ``Rcic.F3.PSet.PolyAxiomTable.wrong_zero_arity_refused,
    ``Rcic.F3.PSet.PolyAxiomTable.selected_faithful]
  for root in roots do
    let _ ← getConstInfo root
  logInfo m!"PolyAxiomTable: {roots.size} named interface roots audited"
