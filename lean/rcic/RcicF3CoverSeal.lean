import Lean
import rcic.RcicF3Cover
import rcic.RcicF3WalkSeal

/-!
# F3 coverage seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicF3Cover` and `rcic.RcicF3WalkSeal`. Every theorem listed below must
depend on no axiom outside `propext` and `Quot.sound`; the `run_cmd` refuses otherwise.
-/

namespace Rcic.F3.CoverSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.F3.PSet.shapes_nonrec_free,
  ``Rcic.F3.PSet.node_cover,
  ``Rcic.F3.PSet.nodeCovered,
  ``Rcic.F3.PSet.recFieldsDirect_of_notAD,
  ``Rcic.F3.PSet.groupClassAt_of_notADB,
  ``Rcic.F3.PSet.EnvWfT_axiomFree_covered,
  ``Rcic.F3.PSet.covered_of_classG,
  ``Rcic.F3.PSet.gInv_of_steps,
  ``Rcic.F3.PSet.rcicConsistentEmpty_of_cover,
  ``Rcic.F3.PSet.rcicConsistentEmpty_of_covered,
  ``Rcic.F3.PSet.steps_classG,
  ``Rcic.F3.PSet.rcicConsistentEmpty_of_cover_classG,
  ``Rcic.F3.PSet.pwNode_params_ne_one,
  ``Rcic.F3.PSet.pwEnvWfT_pendW,
  ``Rcic.F3.PSet.pwEnvWfT_not_classG,
  ``Rcic.Declarative.pwEnvWfT
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_cover_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_cover_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_cover_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.CoverSeal
