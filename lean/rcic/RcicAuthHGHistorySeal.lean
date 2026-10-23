import Lean
import rcic.RcicAuthHGHistory

/-!
# AH-005 history-form `H_G` seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicAuthHGHistory`. It imports that one module and
neither foundation aggregate. Every theorem listed below must depend on no
axiom outside `propext` and `Quot.sound`; the `run_cmd` refuses otherwise.
-/

namespace Rcic.AuthHGHistorySeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.AuthHGHistory.chainFrom_parent,
  ``Rcic.AuthHGHistory.mem_map_ref,
  ``Rcic.AuthHGHistory.chain_unique,
  ``Rcic.AuthHGHistory.derivedHistory_unique,
  ``Rcic.AuthHGHistory.hg_no_external_after_handoff,
  ``Rcic.AuthHGHistory.hg_external_before_handoff,
  ``Rcic.AuthHGHistory.hg_no_lean_descendant_after_handoff,
  ``Rcic.AuthHGHistory.getLast_mem_split,
  ``Rcic.AuthHGHistory.hg_terminal_native,
  ``Rcic.AuthHGHistory.hg_append_external_refused,
  ``Rcic.AuthHGHistory.omit_interior_underivable,
  ``Rcic.AuthHGHistory.hg_root_binds_ref_list,
  ``Rcic.AuthHGHistory.map_ref_inj,
  ``Rcic.AuthHGHistory.hg_root_binds_history,
  ``Rcic.AuthHGHistory.leanId_not_of_outs,
  ``Rcic.AuthHGHistory.ex_leanId_ne_t,
  ``Rcic.AuthHGHistory.ex_native_t,
  ``Rcic.AuthHGHistory.ex_derived,
  ``Rcic.AuthHGHistory.ex_hg,
  ``Rcic.AuthHGHistory.ex_omit_interior,
  ``Rcic.AuthHGHistory.ex_derived_short,
  ``Rcic.AuthHGHistory.ex_omit_trailing_refused,
  ``Rcic.AuthHGHistory.ex_same_refs_both_accepted
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_auth_hg_history_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_auth_hg_history_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_auth_hg_history_seal] {sealedTheorems.length} theorems sealed; axioms ⊆ {allowedAxioms}"

end Rcic.AuthHGHistorySeal

-- BEGIN RCIC_AUTH_HG_HISTORY_ROOTS
#print axioms Rcic.AuthHGHistory.chainFrom_parent
#print axioms Rcic.AuthHGHistory.mem_map_ref
#print axioms Rcic.AuthHGHistory.chain_unique
#print axioms Rcic.AuthHGHistory.derivedHistory_unique
#print axioms Rcic.AuthHGHistory.hg_no_external_after_handoff
#print axioms Rcic.AuthHGHistory.hg_external_before_handoff
#print axioms Rcic.AuthHGHistory.hg_no_lean_descendant_after_handoff
#print axioms Rcic.AuthHGHistory.getLast_mem_split
#print axioms Rcic.AuthHGHistory.hg_terminal_native
#print axioms Rcic.AuthHGHistory.hg_append_external_refused
#print axioms Rcic.AuthHGHistory.omit_interior_underivable
#print axioms Rcic.AuthHGHistory.hg_root_binds_ref_list
#print axioms Rcic.AuthHGHistory.map_ref_inj
#print axioms Rcic.AuthHGHistory.hg_root_binds_history
#print axioms Rcic.AuthHGHistory.leanId_not_of_outs
#print axioms Rcic.AuthHGHistory.ex_leanId_ne_t
#print axioms Rcic.AuthHGHistory.ex_native_t
#print axioms Rcic.AuthHGHistory.ex_derived
#print axioms Rcic.AuthHGHistory.ex_hg
#print axioms Rcic.AuthHGHistory.ex_omit_interior
#print axioms Rcic.AuthHGHistory.ex_derived_short
#print axioms Rcic.AuthHGHistory.ex_omit_trailing_refused
#print axioms Rcic.AuthHGHistory.ex_same_refs_both_accepted
-- END RCIC_AUTH_HG_HISTORY_ROOTS
