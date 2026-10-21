import rcic.RcicNativeTypedModelCovYConcreteFund
import rcic.RcicNativeTypedModelCovYAliasPi
import rcic.RcicNativeTypedModelCovYPolyActionControl
import rcic.RcicNativeTypedModelCovYLetParametric

/-!
# All four requested measurements at the compact-type-code relation

Each positive statement uses the actual model, native context, observed
non-bottom value compact and one specified finite semantic TYPE code.
Nat eta and the impredicative lambda additionally have complete concrete
fundamental motives for every observation and every hereditary substitution.
The alias extension supplies the complete nonempty substitution package.

The old eager-view and raw-entry refutations are not weakened or deleted.
They target different interfaces. These controls do not imply general
caller-code escape, existential-code PER, or a global Fundamental theorem.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelAudit TypedModelCovRelEscapeAudit TypedModelCovNormCov2Audit
open TypedModelCovNormEscapeAudit TypedModelCovXAudit TypedModelCovXEtaAudit
open TypedModelCovYEtaAudit TypedModelCovYPolyPropAudit

/-- Fixture 1 is positive, including the eta-left-only non-bottom table and
the full concrete conversion supplier under the NEW substitution package. -/
theorem covY_fixture_natSucc_eta (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    RelSubstAtCovY (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    Nonempty (HasTyT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (ConvT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) covXNatEtaEmptyRow ∧
    ApproxTK natEnvU n [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) covYNatArrowCode ∧
    LRSCoreCovY (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) covXNatEtaEmptyRow covYNatArrowCode ∧
    HereditaryCovRealizationYAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] EnvT.bot (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode ∧
    FundTyCodeAtCovY (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covYNatArrowCode ∧
    FundConvCodeAtCovY (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (WhStepCK2 natEnvU n) n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) covYNatArrowCode ∧
    covXNatEtaEmptyRow ≠ .bot := by
  obtain ⟨hW, hΓ, hl, hr, hc, hs, he, ha, _, hy, _⟩ := covY_natSucc_eta_control n
  exact ⟨hW, hΓ, relSubstAtCovY_nil (C2 natEnvU) _ _ n []
    EnvT.bot EnvT.bot SubstT.id SubstT.id, hl, hr, hc, hs, he, ha, hy,
    covY_natSucc_eta_hereditary_observed n [] [] EnvT.bot EnvT.bot EnvT.bot _
      (Or.inl he), fundTyCodeAtCovY_natSucc n [], fundConvCodeAtCovY_eta_natSucc n [],
    fun h => CptT.noConfusion h⟩

/-- Fixture 2 is positive at the displayed type code. The old raw-domain
observation is not requested by either the action or hereditary realization. -/
theorem covY_fixture_alias_in_pi (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx covNormAliasIdentity (covNormAliasPi A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot covNormAliasIdentity covNormAliasIdentityCpt ∧
      LRSCoreCovY (C2 eqEnvT) (WhStepCK2 eqEnvT n) n eqGapCtx
        covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
        covNormAliasIdentityCpt covYAliasPiCode ∧
      HereditaryCovRealizationYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
        (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot (covNormAliasPi A B)
        covNormAliasIdentityCpt covYAliasPiCode ∧ covNormAliasIdentityCpt ≠ .bot := by
  obtain ⟨hW, hΓ, henv, A, B, ht, hm, hr, hh, _, hnb⟩ :=
    covY_aliasPi_control (C2 eqEnvT) (C2_includesS eqEnvT) n
  exact ⟨hW, hΓ, henv, A, B, ht, hm, hr, hh, hnb⟩

/-- Fixture 3 is positive. The code for the impredicative domain is bottom,
and every actual domain demand is proved bottom by model inversion. The
function and codomain observations remain non-bottom. -/
theorem covY_fixture_polyPropLam (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n []) ∧
    RelSubstAtCovY (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    Nonempty (HasTyT eqEnvT n [] covXPolyPropLam covXPolyPropLamTy) ∧
    ApproxTK eqEnvT n [] EnvT.bot covXPolyPropLam (.lam [([], .prop)]) ∧
    ApproxTK eqEnvT n [] EnvT.bot covXPolyPropLamTy covYPolyPropCode ∧
    LRSCoreCovY (C2 eqEnvT) (WhStepCK2 eqEnvT n) n []
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy (.lam [([], .prop)])
      covYPolyPropCode ∧
    HereditaryCovRealizationYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
      (WhStepCK2 eqEnvT n) n [] EnvT.bot covXPolyPropLamTy (.lam [([], .prop)])
      covYPolyPropCode ∧
    FundTyCodeAtCovY (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
      n [] covXPolyPropLam covXPolyPropLamTy covYPolyPropCode ∧
    (¬ Nonempty (CovXTypeView eqEnvT (WhStepCK2 eqEnvT n) n [] idPiProp)) ∧
    (.lam [([], .prop)] : CptT) ≠ .bot := by
  have hm := covXPolyPropLam_observed n [] EnvT.bot
  exact ⟨⟨pinEqGroupWfT⟩, ⟨.nil⟩,
    relSubstAtCovY_nil (C2 eqEnvT) _ _ n [] EnvT.bot EnvT.bot SubstT.id SubstT.id,
    ⟨covXPolyPropLam_typed n []⟩, hm, approxTK_covYPolyPropCode n [] EnvT.bot,
    covY_polyProp_related_observed (C2 eqEnvT) (C2_includesS eqEnvT) n [] [] EnvT.bot _ hm,
    covY_polyProp_hereditary_observed (C2 eqEnvT) (C2_includesS eqEnvT)
      n [] [] EnvT.bot EnvT.bot _ hm,
    fundTyCodeAtCovY_polyPropLam (C2 eqEnvT) (C2_includesS eqEnvT) n [],
    not_covXTypeView_idPiProp_eq n [], fun h => CptT.noConfusion h⟩

/-- Fixture 4 is positive for the complete nonempty package, with the same
non-bottom head compact for which the old raw source guard is impossible. -/
theorem covY_fixture_alias_extension (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    ∃ A B : Expr Nat,
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
      RelSubstAtCovY (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
        n eqGapCtx
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      HereditaryCovRealizationYAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
        (WhStepCK2 eqEnvT n) n eqGapCtx EnvT.bot (eqGapDirectAlias A B)
        (.pi .bot []) .prop ∧
      (¬ EnvTypedCovAtP (C2 eqEnvT)
        (ctxModelT_approxTK eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx))
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)) ∧
      (.pi .bot [] : CptT) ≠ .bot := by
  obtain ⟨hW, hΓ, A, B, _, _, hΓ', hN, hm, hs, _, hh, hraw, hnb⟩ :=
    covY_alias_substitution_control (C2 eqEnvT) (C2_includesS eqEnvT) n
  exact ⟨hW, hΓ, A, B, hΓ', hN, hm, hs, hh, hraw, hnb⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_FIXTURES_ROOTS
#print axioms covY_fixture_natSucc_eta
#print axioms covY_fixture_alias_in_pi
#print axioms covY_fixture_polyPropLam
#print axioms covY_fixture_alias_extension
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit
