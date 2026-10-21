/-
`kernel_rfl_theorem n : lhs = rhs` declares `theorem n : lhs = rhs := Eq.refl rhs`
and hands it to the kernel with `addDecl`; the elaborator does not evaluate
the equation. The kernel still checks `lhs ≡ rhs` by definitional
unfolding, so nothing is assumed. This is the 4.14 stand-in for a
kernel-only `decide`; it exists because elaborator-side `isDefEq` on the
large closed `iotaSchemaAt` evaluations of the K3c regroup takes hours,
while the kernel takes seconds.
-/
import Lean

namespace Rcic.Scm.SrcG
open Lean Elab Command Term Meta

syntax (name := kernelRflTheorem) "kernel_rfl_theorem " ident " : " term : command

@[command_elab kernelRflTheorem] def elabKernelRflTheorem : CommandElab := fun stx => do
  let shortName := stx[1].getId
  let declName := (← getCurrNamespace) ++ shortName
  liftTermElabM do
    let ty ← elabType stx[3]
    synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    if ty.hasMVar then
      throwError "kernel_rfl_theorem: statement still has metavariables"
    let some (α, _, rhs) := ty.eq?
      | throwError "kernel_rfl_theorem: statement is not an equation"
    let u ← getLevel α
    let pf := mkApp2 (mkConst ``Eq.refl [u]) α rhs
    addDecl <| .thmDecl { name := declName, levelParams := [], type := ty, value := pf }

end Rcic.Scm.SrcG
