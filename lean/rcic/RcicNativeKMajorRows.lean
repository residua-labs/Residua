import rcic.RcicCoherentCanonical
import rcic.RcicPiRowProj
import rcic.RcicNativeCertifiedK

/-!
# Refiring a K gate after a step of its major

This module reuses the full `ParRedT` and `NativeValley`. It does not
change `Certified` and does not duplicate the K-certificate lane.

When the recursor prefix and the witness stay fixed, an actual major
step at the gate's own proposition `Tm` supplies the new major typing.
The application node's stored target typing supplies the new full call
typing. These data refire exactly the original K witness, giving a
zero/one-step native valley at the original result index.

The restriction to a major step at `Tm` is explicit. An application
child at a separately chosen domain does not satisfy it merely because
its source is the same term. No type exchange, confluence, or index
alignment is claimed. The constructed output is a raw native valley;
its K leg is not silently treated as an old certified step.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.KMajorRowsAudit

open CoherentCanonicalAudit (nativeLeafIface)

variable {E : ResolvedEnv} {n : Nat}

/-- The original fixed-prefix K gate can be refired after any actual
major step at its stored proposition. The two new endpoint typings are
obtained from the major step and the enclosing application's target. -/
def refireK_after_major_step {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (w : IotaWitness E) {major major' Tm rhs T : Expr Nat}
    (rl : Level) (afs : Prop)
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n Γ (iotaLhsOf w) T)
    (q : PiStep E n Γ major major' Tm)
    (hnew : HasTyT E n Γ
      (recCall (.const w.recRef w.ls) w.preMajor major') T)
    (hrhs : HasTyT E n Γ rhs T) :
    PiStep E n Γ
      (recCall (.const w.recRef w.ls) w.preMajor major') rhs T :=
  .iotaStarK Γ w major' Tm rhs T rl afs hrl hsel hfam
    (parRedT_hasTy_right (nativeLeafIface E n).typed hΓ q)
    hmk hTm0 hι hlι hnew hrhs

/-- A concrete fixed-prefix K/app-on-major row: the K reduct remains
fixed, and the changed full call refires the original witness. The
major index and the new call's typing are actual inputs, not inferred
from an unrelated application decoration. -/
def joinK_after_major_step {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (w : IotaWitness E) {major major' Tm rhs T : Expr Nat}
    (rl : Level) (afs : Prop)
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n Γ (iotaLhsOf w) T)
    (q : PiStep E n Γ major major' Tm)
    (hnew : HasTyT E n Γ
      (recCall (.const w.recRef w.ls) w.preMajor major') T)
    (hrhs : HasTyT E n Γ rhs T) :
    NativeValley E n Γ rhs
      (recCall (.const w.recRef w.ls) w.preMajor major') T where
  centre := rhs
  left := .refl Γ rhs T hrhs
  right := .tail
    (refireK_after_major_step hΓ w rl afs hrl hsel hfam hmk hTm0 hι hlι q hnew hrhs)
    (.refl Γ rhs T hrhs)

/-- Certified peak completion for the same fixed-prefix row. The new
K certificate is constructed by reversing the actual second leg
and following the actual first leg. The raw gate is refired using the
major step at `Tm`; no certificate is requested for the produced step. -/
def certified_refireK_after_major_step {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    (w : IotaWitness E) {major major' Tm rhs T : Expr Nat}
    (rl : Level) (afs : Prop)
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (hι : DerivedIotaU E (iotaLhsOf w) rhs)
    (hlι : HasTyT E n Γ (iotaLhsOf w) T)
    (qmajor : PiStep E n Γ major major' Tm)
    (p : CStepK E n (ProofLeaf E n) Γ
      (recCall (.const w.recRef w.ls) w.preMajor major) rhs T)
    (q : CStepK E n (ProofLeaf E n) Γ
      (recCall (.const w.recRef w.ls) w.preMajor major)
      (recCall (.const w.recRef w.ls) w.preMajor major') T) :
    CStepK E n (ProofLeaf E n) Γ
      (recCall (.const w.recRef w.ls) w.preMajor major') rhs T :=
  ⟨refireK_after_major_step hΓ w rl afs hrl hsel hfam hmk hTm0 hι hlι
      qmajor (q.rightTyped (nativeLeafIface E n) hΓ)
      (p.rightTyped (nativeLeafIface E n) hΓ),
    .iotaStarK (.trans _ _ _ _ _ (.symm _ _ _ _ q.toConvT) p.toConvT)⟩

#print axioms refireK_after_major_step
#print axioms joinK_after_major_step
#print axioms certified_refireK_after_major_step

end Rcic.Declarative.NativeValleys.KMajorRowsAudit
