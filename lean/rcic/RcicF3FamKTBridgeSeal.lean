import rcic.RcicF3FamKTBridge

/-!
# Seal for `RcicF3FamKTBridge`

Every sealed declaration's axiom set is audited at compile time: allowed
axioms are exactly `propext` and `Quot.sound` (`P`-elimination is only via
`Premises4.dec`, never `Classical.choice`).  The list covers the §6
alignment chain end to end: the dispatch lemmas, the entry induction, the
fibre cell (the §5 `FibAlign`, discharged), the two subset directions, the
fibre equivalence, and the two bridge statements.

`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.FamKTBridgeSeal

open Lean Elab Command

/-- Declarations sealed by this module. -/
def sealedTheorems : List Name := [
  ``Rcic.F3.PSet.not_mem_denRefsLit,
  ``Rcic.F3.PSet.not_mem_denRefs_of_occursConst,
  ``Rcic.F3.PSet.den_upd_eq_famFree,
  ``Rcic.F3.PSet.den_upd_congr_rec,
  ``Rcic.F3.PSet.famFields_den_of_entry,
  ``Rcic.F3.PSet.fieldsClassA_lift,
  ``Rcic.F3.PSet.iterPhiD_eq,
  ``Rcic.F3.PSet.iterPhiD_env,
  ``Rcic.F3.PSet.iterPhiD_levels,
  ``Rcic.F3.PSet.iterPhiD_ne,
  ``Rcic.F3.PSet.iterPhiD_mem,
  ``Rcic.F3.PSet.famOfD_ext,
  ``Rcic.F3.PSet.canonEntry_typeRead,
  ``Rcic.F3.PSet.famZero_famOfD_zero,
  ``Rcic.F3.PSet.famIter_succ_famOfD,
  ``Rcic.F3.PSet.famIter_famOfD,
  ``Rcic.F3.PSet.famEnd_famEndD_iter,
  ``Rcic.F3.PSet.limEnd_sub_classA,
  ``Rcic.F3.PSet.fibAt_sub_limEnd_classA,
  ``Rcic.F3.PSet.limEnd_famEndD_classA,
  ``Rcic.F3.PSet.famLim_famLfp,
  ``Rcic.F3.PSet.famLim_famKT_type
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_f3_famkt_bridge_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_f3_famkt_bridge_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_f3_famkt_bridge_seal] {sealedTheorems.length} declarations sealed; axioms ⊆ {allowedAxioms}"

end Rcic.F3.FamKTBridgeSeal
