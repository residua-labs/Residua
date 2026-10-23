import Lean
import rcic.RcicEgExplain

/-!
# P5.3 explanation seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicEgExplain`. Every theorem listed below must depend
on no axiom outside `propext` and `Quot.sound`.
-/

namespace Rcic.Assay.EgraphSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.Assay.Egraph.eg_refl,
  ``Rcic.Assay.Egraph.eg_fwd,
  ``Rcic.Assay.Egraph.eg_flip,
  ``Rcic.Assay.Egraph.eg_trans,
  ``Rcic.Assay.Egraph.eg_order,
  ``Rcic.Assay.Egraph.eg_cong,
  ``Rcic.Assay.Egraph.eg_cong_trans
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[assay_eg_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[assay_eg_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[assay_eg_seal] {sealedTheorems.length} theorems sealed; axioms ⊆ {allowedAxioms}"

end Rcic.Assay.EgraphSeal

-- BEGIN GROK ASSAY P5.3 ROOTS
#print axioms Rcic.Assay.Egraph.eg_refl
#print axioms Rcic.Assay.Egraph.eg_fwd
#print axioms Rcic.Assay.Egraph.eg_flip
#print axioms Rcic.Assay.Egraph.eg_trans
#print axioms Rcic.Assay.Egraph.eg_order
#print axioms Rcic.Assay.Egraph.eg_cong
#print axioms Rcic.Assay.Egraph.eg_cong_trans
-- END GROK ASSAY P5.3 ROOTS
