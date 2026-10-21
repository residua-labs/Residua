import rcic.RcicNativeCertifiedK
import rcic.RcicStarStripUnitPeak

/-!
# RcicNativeCertifiedKControl — the #7606 peak is certified in the enlarged relation

`admitted_unit_no_valley` (#7606) shows the K-free `Certified` relation has no valley for the
η-K peak of `trueEnvU`, while the full relation joins it in one `iotaStarKEta` step
(`unitRawKEta`).  Here that step receives its native certificate through
`convT_iotaStarKEta` (legacy ι arm, witness `wTrueRecU`), so the peak closes in `CertifiedK`
with one certified step on the η side and zero on the other: the positive control for the
re-admission.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.CertifiedKControlAudit

open StarStripUnitPeakAudit

/-- The full-relation η-K step of the unit peak is certified natively. -/
def unitRawKEta_certifiedK : CertifiedK unitRawKEta :=
  .iotaStarKEta (convT_iotaStarKEta (w := wTrueRecU) (f := unitPartialRec)
    (envClosed_of_envWfT trueEnvUWfT) rfl trueEnvUF_ty
    unitPartialRecTy unitBoundProofTy trueEnvUtt_ty trueEnvUF_ty (.of wTrueRecU)
    (unitBodyPrep.rightTyped (CoherentCanonicalAudit.nativeLeafIface trueEnvU 0)
      unitBodyContextWf)
    (.sort _ .zero))

/-- The certified η-K step of the unit peak. -/
def unitKEtaCStepK :
    CStepK trueEnvU 0 (Rcic.Declarative.ProofLeaf trueEnvU 0) [] unitPartialRec unitContracted
      unitIndex :=
  ⟨unitRawKEta, unitRawKEta_certifiedK⟩

/-- Its certificate is a native conversion of the two reducts at the common index. -/
def unitKEta_conv : ConvT trueEnvU 0 [] unitPartialRec unitContracted unitIndex :=
  unitKEtaCStepK.toConvT

#print axioms unitRawKEta_certifiedK
#print axioms unitKEtaCStepK
#print axioms unitKEta_conv

end Rcic.Declarative.NativeValleys.CertifiedKControlAudit
