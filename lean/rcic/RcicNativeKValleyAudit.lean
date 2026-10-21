import rcic.RcicNativeKPartialPeak
import rcic.RcicNativeKPartialObstruction
import rcic.RcicNativeKProjection

/-!
# The enlarged peak has no raw or certified native valley

These are negative clients of the separately compiled admitted
countermodel. The positive peak uses Fable's constructed legacy eta-K
certificate, and its two enlarged steps have identical source
decorations. Nevertheless no pair of unrestricted raw stars from their
endpoints can meet. Consequently neither enlarging the certificate
predicate nor forgetting decorations can construct a valley for the
existing raw constructor set.

No alternate modulo equivalence is defined or assumed here. The final
head statement excludes precisely meetings whose raw spine heads are
equal. It does not assert a theorem about unspecified modulo relations.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativeKValleyAudit

open NativeKPartialPeakAudit
open NativeKPartialObstructionAudit

/-- No length of enlarged certified steps joins the actual new peak,
even if its two legs use unrelated indices. -/
theorem admitted_no_enlarged_valley {j T₁ T₂ : Expr Nat}
    (s : CStarK trueEnvU 0 (ProofLeaf trueEnvU 0) [] minorPartialRec j T₁)
    (t : CStarK trueEnvU 0 (ProofLeaf trueEnvU 0) [] minorContracted j T₂) : False :=
  admitted_partial_no_valley s.forget t.forget

/-- The existing full native-valley carrier is empty at these endpoints. -/
theorem admitted_no_raw_valley {T : Expr Nat} :
    ¬ Nonempty (NativeValley trueEnvU 0 [] minorPartialRec minorContracted T) := by
  rintro ⟨V⟩
  exact admitted_partial_no_valley V.left V.right

/-- Even the weak demand that every enlarged one-step peak have raw
joining stars is refuted by the actual eta/lam peak. -/
theorem admitted_no_enlarged_peak_supplier :
    ¬ (∀ {a b c T : Expr Nat},
      CStepK trueEnvU 0 (ProofLeaf trueEnvU 0) [] a b T →
      CStepK trueEnvU 0 (ProofLeaf trueEnvU 0) [] a c T →
      Nonempty (NativeValley trueEnvU 0 [] b c T)) := by
  intro join
  exact admitted_no_raw_valley (join minorEtaStep minorLamStep)

/-- Full raw star confluence fails in the admitted True environment,
without any restriction on the lengths or decorations of joining legs. -/
theorem admitted_no_raw_star_confluence :
    ¬ (∀ {a b c T : Expr Nat},
      PiStar trueEnvU 0 [] a b T → PiStar trueEnvU 0 [] a c T →
      Nonempty (NativeValley trueEnvU 0 [] b c T)) := by
  intro join
  exact admitted_no_raw_valley
    (join
      (.tail minorEtaStep.step (.refl [] minorPartialRec minorIndex minorPartialTy))
      (.tail minorLamStep.step (.refl [] minorContracted minorIndex minorContractedTy)))

/-- The already published global native-conversion-valley proposition
is false for the existing full raw relation, not merely its old fragment. -/
theorem admitted_no_nativeConvValleys : ¬ NativeConvValleys trueEnvU 0 := by
  intro join
  exact admitted_no_raw_valley (join CtxWfT.nil minorConversion)

/-- The data-valued raw producer used by the Pi consumer is likewise
uninhabited here; a larger certificate predicate cannot supply it. -/
theorem admitted_no_nativeConvValleyData :
    ¬ Nonempty (NativeKProjectionAudit.NativeConvValleyData trueEnvU 0) := by
  rintro ⟨join⟩
  exact admitted_no_nativeConvValleys (NativeKProjectionAudit.nativeConvValleys_of_data join)

/-- Raw endpoints cannot even meet modulo equality of their spine
heads. This is an explicit head condition, not an unspecified quotient. -/
theorem admitted_no_equal_head_meeting {j₁ j₂ T₁ T₂ : Expr Nat}
    (s : PiStar trueEnvU 0 [] minorPartialRec j₁ T₁)
    (t : PiStar trueEnvU 0 [] minorContracted j₂ T₂)
    (heads : (appsSpine j₁).1 = (appsSpine j₂).1) : False :=
  admitted_partial_heads_differ s t heads

#print axioms admitted_no_enlarged_valley
#print axioms admitted_no_raw_valley
#print axioms admitted_no_enlarged_peak_supplier
#print axioms admitted_no_raw_star_confluence
#print axioms admitted_no_nativeConvValleys
#print axioms admitted_no_nativeConvValleyData
#print axioms admitted_no_equal_head_meeting

end Rcic.Declarative.NativeValleys.NativeKValleyAudit
