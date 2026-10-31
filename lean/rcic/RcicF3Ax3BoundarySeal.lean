import Lean
import rcic.RcicF3Ax3Boundary

/-!
Historical monomorphic obstruction and arbitrary-axiom counterexample audit.
The obstruction now has the explicit `MonomorphicAxiomAdmissions` premise.
Check the actual
Lean standard declarations' universe arities rather than assigning an arity
to constants from their names. This is an arity audit, not an object-language
translation or a consistency proof. `closure_claim = 0`.
-/

open Lean Elab Command

run_cmd do
  for (name, arity) in #[(``propext, 0), (``Quot.sound, 1), (``Classical.choice, 1)] do
    let info ← getConstInfo name
    unless info.levelParams.length == arity do
      throwError "Ax3Boundary: {name} expected arity {arity}, got {info.levelParams.length}"
    logInfo m!"AX3_SCHEMA {name} arity={arity} type={info.type}"

run_cmd do
  let env ← getEnv
  let mod := `rcic.RcicF3Ax3Boundary
  let some midx := env.getModuleIdx? mod
    | throwError "Ax3Boundary: missing module {mod}"
  let allowed := #[``propext, ``Quot.sound]
  let mut count := 0
  for (root, _) in env.constants.toList do
    if env.getModuleIdxFor? root == some midx && !root.isInternal then
      let axioms ← collectAxioms root
      let forbidden := axioms.filter (fun ax => !allowed.contains ax)
      unless forbidden.isEmpty do
        throwError "Ax3Boundary: {root} has forbidden axioms {forbidden}"
      logInfo m!"CHECKED_ROOT {root} {axioms}"
      count := count + 1
  if count == 0 then
    throwError "Ax3Boundary: no public declarations"
  logInfo m!"Ax3Boundary: {count} public declarations checked"
