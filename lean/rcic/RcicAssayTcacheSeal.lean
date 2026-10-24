import Lean
import rcic.RcicAssayTcache

/-
P5.4 statement-key seal. `closure_claim = 0`.

The two theorems are `tcache_stmtq_pins` and `tcache_stmtq_distinct`.
-/

namespace Rcic.Assay.TcacheSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.Assay.Tcache.tcache_stmtq_pins,
  ``Rcic.Assay.Tcache.tcache_stmtq_distinct
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[assay_tcache_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[assay_tcache_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[assay_tcache_seal] {sealedTheorems.length} theorems sealed; axioms ⊆ {allowedAxioms}"

end Rcic.Assay.TcacheSeal

-- BEGIN GROK ASSAY P5.4 ROOTS
#print axioms Rcic.Assay.Tcache.tcache_stmtq_pins
#print axioms Rcic.Assay.Tcache.tcache_stmtq_distinct
-- END GROK ASSAY P5.4 ROOTS
