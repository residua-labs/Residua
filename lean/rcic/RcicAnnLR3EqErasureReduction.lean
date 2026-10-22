import rcic.RcicAnnLR3ReflInferenceBoundary
import rcic.RcicSynFamRigid

/-!
# Fixed Eq type images and the exact remaining coherence bridges

The two Eq types at the open assumption-context call have actual enriched
typing derivations.  Their erasures retain the third family argument:
`Eq Prop parameter parameter` has the closed Pi image there, whereas
`Eq Prop parameter (bvar 1)` has the surviving variable `bvar 0`.

Erased family-spine inversion and the landed Pi/variable separation prove
that these images are not convertible under any well-formed table with no
rule at family head 63.  This separation is supplied below; the empty table
inhabits both table premises.  The context, source call, closed substitution,
canonical proof at its stored type, and both type-image derivations are also
supplied, independently of a semantic environment.

Two coherence obligations remain explicitly conditional.  The first is the
fixed-subject type agreement named in `ReflInferenceBoundary`.  The second,
`EqTypeConversionErasureA3`, sends a conversion between these two types to
conversion between their actual erased images.  Neither bridge is supplied
here.  In particular, same-subject erasure coherence for the proof term does
not compare these distinct type subjects.  The final no-frame reduction
consumes both named bridges and is not an unconditional no-frame theorem.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.EqErasureReduction

open Rcic.Declarative Rcic.Syn EqLargeFixture RouteCKContext FrameSource ReflInference

/-- Enriched typing of the stored Eq result type in the actual open context. -/
def canonicalEqTypeP3 :
    TyP eqEnvT 0 (eraseCtx assumptionContext) (erase domain) (.sort .zero) :=
  eqP (parameterP (eraseCtx assumptionContext))

/-- Enriched typing of the Eq type with the independent open index. -/
def actualEqTypeP3 :
    TyP eqEnvT 0 (eraseCtx assumptionContext)
      (erase (eqAt parameter (.bvar 1))) (.sort .zero) :=
  eqP assumptionIndexP

abbrev canonicalEqImageA3 : ETm :=
  ETm.appN (.const 63 []) [.sort .zero, parameterE, parameterE]

abbrev actualEqImageA3 : ETm :=
  ETm.appN (.const 63 []) [.sort .zero, parameterE, .bvar 0]

/-- The canonical type keeps both proposition-valued indices. -/
theorem canonicalEqTypeP3_eps :
    canonicalEqTypeP3.eps id (assumptionContextP.disp id) = canonicalEqImageA3 := rfl

/-- The proof binding drops, so the independent proposition survives as variable 0. -/
theorem actualEqTypeP3_eps :
    actualEqTypeP3.eps id (assumptionContextP.disp id) = actualEqImageA3 := rfl

/-- Actual separation of the two supplied type images.  No annotated
conversion-erasure or declarative type-agreement premise is used. -/
theorem eqTypeImagesSeparatedA3 {tbl : List CRule}
    (hW : TableWF tbl) (hN : NoHeadRule tbl 63) :
    ¬ ConvMod (EStep tbl) LvlEq
      (canonicalEqTypeP3.eps id (assumptionContextP.disp id))
      (actualEqTypeP3.eps id (assumptionContextP.disp id)) := by
  intro hc
  rw [canonicalEqTypeP3_eps, actualEqTypeP3_eps] at hc
  obtain ⟨_, _, hargs⟩ := convE_appN_const_inv_wf hW hN hc
  cases hargs with
  | cons _ hargs =>
    cases hargs with
    | cons _ hargs =>
      cases hargs with
      | cons hindex _ =>
        exact assumptionErasedGuard_fails hW hindex

/-- The precise, still-unsupplied conversion-erasure obligation for this pair
of type subjects and these actual enriched derivations. -/
def EqTypeConversionErasureA3 (tbl : List CRule) : Prop :=
  TyConvA env (iotaIfaceA env) 0 assumptionContext
      domain (eqAt parameter (.bvar 1)) →
    ConvMod (EStep tbl) LvlEq
      (canonicalEqTypeP3.eps id (assumptionContextP.disp id))
      (actualEqTypeP3.eps id (assumptionContextP.disp id))

/-- Conditional reduction of annotated type separation to the named erasure
bridge.  The bridge is a premise, not a theorem proved by this declaration. -/
theorem noActualFamilyConversionA3_of_erasure {tbl : List CRule}
    (hW : TableWF tbl) (hN : NoHeadRule tbl 63)
    (hErase : EqTypeConversionErasureA3 tbl) :
    ¬ Nonempty (TyConvA env (iotaIfaceA env) 0 assumptionContext
      domain (eqAt parameter (.bvar 1))) := by
  rintro ⟨hc⟩
  exact eqTypeImagesSeparatedA3 hW hN (hErase hc)

/-- Conditional reduction for the fixed canonical proof.  Both remaining
coherence hypotheses are displayed explicitly. -/
theorem noCanonicalActualTypingA3_of_bridges {tbl : List CRule}
    (hW : TableWF tbl) (hN : NoHeadRule tbl 63)
    (hType : ReflActualTypeAgreementA3)
    (hErase : EqTypeConversionErasureA3 tbl) :
    ¬ Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext
      (reflAt parameter) (eqAt parameter (.bvar 1))) := by
  rintro ⟨ht⟩
  exact noActualFamilyConversionA3_of_erasure hW hN hErase (hType ht)

/-- Every matching frame, including one with arbitrary declared indices,
reduces to the fixed two coherence obligations.  This is conditional. -/
theorem noMatchingAssumptionFrameA3_of_bridges {tbl : List CRule}
    (hW : TableWF tbl) (hN : NoHeadRule tbl 63)
    (hType : ReflActualTypeAgreementA3)
    (hErase : EqTypeConversionErasureA3 tbl) :
    ¬ ∃ s : KStage.Shape,
      Nonempty (KStage.Frame env (iotaIfaceA env) 0 assumptionContext s) ∧
        s.source = contextCall := by
  rintro ⟨s, ⟨w⟩, he⟩
  exact noCanonicalActualTypingA3_of_bridges hW hN hType hErase
    (assumptionFrameCanonicalActualA3 w he)

/-- All inputs to the supplied erased separation are inhabited on one
admitted fixture.  The two conditional coherence bridges are deliberately
absent from this bundle: they remain obligations. -/
theorem inhabitedEqTypeImagesA3 :
    eraseEnv env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 assumptionContext) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext domain (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext
      (eqAt parameter (.bvar 1)) (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext
      (reflAt parameter) domain) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 assumptionContext contextCall (.sort one)) ∧
    Nonempty (SubstTyA env (iotaIfaceA env) 0 [] closeSubstitution assumptionContext) ∧
    Nonempty (CtxP eqEnvT 0 (eraseCtx assumptionContext)) ∧
    Nonempty (TyP eqEnvT 0 (eraseCtx assumptionContext) (erase domain) (.sort .zero)) ∧
    Nonempty (TyP eqEnvT 0 (eraseCtx assumptionContext)
      (erase (eqAt parameter (.bvar 1))) (.sort .zero)) ∧
    TableWF [] ∧ NoHeadRule [] 63 ∧
    canonicalEqTypeP3.eps id (assumptionContextP.disp id) = canonicalEqImageA3 ∧
    actualEqTypeP3.eps id (assumptionContextP.disp id) = actualEqImageA3 ∧
    ¬ ConvMod (EStep []) LvlEq
      (canonicalEqTypeP3.eps id (assumptionContextP.disp id))
      (actualEqTypeP3.eps id (assumptionContextP.disp id)) :=
  ⟨erase_env, wf, ⟨assumptionContextWf⟩,
    ⟨eqTyped assumptionContextWf parameterTyped parameterTyped⟩,
    ⟨eqTyped assumptionContextWf parameterTyped (indexTyped rfl)⟩,
    ⟨reflTyped assumptionContextWf parameterTyped⟩,
    contextCallTyped assumptionContextWf rfl rfl,
    ⟨assumptionClosingSubstitution⟩, ⟨assumptionContextP⟩,
    ⟨canonicalEqTypeP3⟩, ⟨actualEqTypeP3⟩,
    emptyTable_wf, noHeadRule_empty 63, canonicalEqTypeP3_eps, actualEqTypeP3_eps,
    eqTypeImagesSeparatedA3 emptyTable_wf (noHeadRule_empty 63)⟩

#print axioms canonicalEqTypeP3
#print axioms actualEqTypeP3
#print axioms canonicalEqImageA3
#print axioms actualEqImageA3
#print axioms canonicalEqTypeP3_eps
#print axioms actualEqTypeP3_eps
#print axioms eqTypeImagesSeparatedA3
#print axioms EqTypeConversionErasureA3
#print axioms noActualFamilyConversionA3_of_erasure
#print axioms noCanonicalActualTypingA3_of_bridges
#print axioms noMatchingAssumptionFrameA3_of_bridges
#print axioms inhabitedEqTypeImagesA3

end Rcic.Declarative.Ann.LR3.EqErasureReduction
