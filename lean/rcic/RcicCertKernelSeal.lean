import Lean
import rcic.RcicCertKernel

/-!
# CertKernel seal

`closure_claim = 0`. Bounded seal for `rcic.RcicCertKernel`; imports that one
module and neither foundation aggregate. Every listed theorem/def must depend
on no axiom outside `propext` and `Quot.sound`.
-/

namespace Rcic.CertKernelSeal

open Lean

def sealedTheorems : List Name := [
  ``Rcic.Machine.RM014T'_whnf_conv,
  ``Rcic.Machine.RM014T'_run_whnf_conv,
  ``Rcic.Machine.RM017T'_conv,
  ``Rcic.Machine.RM017T'_tyConv,
  ``Rcic.Machine.pin_RM014T'_whnf,
  ``Rcic.Machine.pin_RM017T'_conv,
  ``Rcic.Machine.pin_certStep_tyConv_refused
]

def allowedAxioms : List Name := [``propext, ``Quot.sound]

open Elab Command in
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[rcic_cert_kernel_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[rcic_cert_kernel_seal] {t} depends on non-allowlisted axiom {ax}"
  logInfo m!"[rcic_cert_kernel_seal] {sealedTheorems.length} sealed; axioms ⊆ {allowedAxioms}"

end Rcic.CertKernelSeal
