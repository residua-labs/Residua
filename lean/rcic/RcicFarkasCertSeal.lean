import Lean
import rcic.RcicFarkasCert

/-!
# P5.2 Farkas certificate seal

`closure_claim = 0`.

Bounded seal for `rcic.RcicFarkasCert`. It imports that one module and
neither foundation aggregate. Every theorem listed below must depend on no
axiom outside `propext` and `Quot.sound`.
-/

namespace Rcic.Assay.FarkasSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.Assay.Farkas.farkas_sound,
  ``Rcic.Assay.Farkas.nat_no_div,
  ``Rcic.Assay.Farkas.g01, ``Rcic.Assay.Farkas.g01_omega,
  ``Rcic.Assay.Farkas.g02, ``Rcic.Assay.Farkas.g02_omega,
  ``Rcic.Assay.Farkas.g03, ``Rcic.Assay.Farkas.g03_omega,
  ``Rcic.Assay.Farkas.g04, ``Rcic.Assay.Farkas.g04_omega,
  ``Rcic.Assay.Farkas.g05, ``Rcic.Assay.Farkas.g05_omega,
  ``Rcic.Assay.Farkas.g06, ``Rcic.Assay.Farkas.g06_omega,
  ``Rcic.Assay.Farkas.g07, ``Rcic.Assay.Farkas.g07_omega,
  ``Rcic.Assay.Farkas.g08, ``Rcic.Assay.Farkas.g08_omega,
  ``Rcic.Assay.Farkas.g09, ``Rcic.Assay.Farkas.g09_omega,
  ``Rcic.Assay.Farkas.g10, ``Rcic.Assay.Farkas.g10_omega,
  ``Rcic.Assay.Farkas.g11, ``Rcic.Assay.Farkas.g11_omega,
  ``Rcic.Assay.Farkas.g12, ``Rcic.Assay.Farkas.g12_omega,
  ``Rcic.Assay.Farkas.g13, ``Rcic.Assay.Farkas.g13_omega,
  ``Rcic.Assay.Farkas.g14, ``Rcic.Assay.Farkas.g14_omega,
  ``Rcic.Assay.Farkas.g15, ``Rcic.Assay.Farkas.g15_omega,
  ``Rcic.Assay.Farkas.g16, ``Rcic.Assay.Farkas.g16_omega,
  ``Rcic.Assay.Farkas.g17, ``Rcic.Assay.Farkas.g17_omega,
  ``Rcic.Assay.Farkas.g18, ``Rcic.Assay.Farkas.g18_omega,
  ``Rcic.Assay.Farkas.g19, ``Rcic.Assay.Farkas.g19_omega,
  ``Rcic.Assay.Farkas.g20, ``Rcic.Assay.Farkas.g20_omega
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[assay_farkas_cert_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[assay_farkas_cert_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[assay_farkas_cert_seal] {sealedTheorems.length} theorems sealed; axioms ⊆ {allowedAxioms}"

end Rcic.Assay.FarkasSeal

-- BEGIN GROK ASSAY P5.2 ROOTS
#print axioms Rcic.Assay.Farkas.farkas_sound
#print axioms Rcic.Assay.Farkas.nat_no_div
#print axioms Rcic.Assay.Farkas.g01
#print axioms Rcic.Assay.Farkas.g01_omega
#print axioms Rcic.Assay.Farkas.g02
#print axioms Rcic.Assay.Farkas.g02_omega
#print axioms Rcic.Assay.Farkas.g03
#print axioms Rcic.Assay.Farkas.g03_omega
#print axioms Rcic.Assay.Farkas.g04
#print axioms Rcic.Assay.Farkas.g04_omega
#print axioms Rcic.Assay.Farkas.g05
#print axioms Rcic.Assay.Farkas.g05_omega
#print axioms Rcic.Assay.Farkas.g06
#print axioms Rcic.Assay.Farkas.g06_omega
#print axioms Rcic.Assay.Farkas.g07
#print axioms Rcic.Assay.Farkas.g07_omega
#print axioms Rcic.Assay.Farkas.g08
#print axioms Rcic.Assay.Farkas.g08_omega
#print axioms Rcic.Assay.Farkas.g09
#print axioms Rcic.Assay.Farkas.g09_omega
#print axioms Rcic.Assay.Farkas.g10
#print axioms Rcic.Assay.Farkas.g10_omega
#print axioms Rcic.Assay.Farkas.g11
#print axioms Rcic.Assay.Farkas.g11_omega
#print axioms Rcic.Assay.Farkas.g12
#print axioms Rcic.Assay.Farkas.g12_omega
#print axioms Rcic.Assay.Farkas.g13
#print axioms Rcic.Assay.Farkas.g13_omega
#print axioms Rcic.Assay.Farkas.g14
#print axioms Rcic.Assay.Farkas.g14_omega
#print axioms Rcic.Assay.Farkas.g15
#print axioms Rcic.Assay.Farkas.g15_omega
#print axioms Rcic.Assay.Farkas.g16
#print axioms Rcic.Assay.Farkas.g16_omega
#print axioms Rcic.Assay.Farkas.g17
#print axioms Rcic.Assay.Farkas.g17_omega
#print axioms Rcic.Assay.Farkas.g18
#print axioms Rcic.Assay.Farkas.g18_omega
#print axioms Rcic.Assay.Farkas.g19
#print axioms Rcic.Assay.Farkas.g19_omega
#print axioms Rcic.Assay.Farkas.g20
#print axioms Rcic.Assay.Farkas.g20_omega
-- END GROK ASSAY P5.2 ROOTS
