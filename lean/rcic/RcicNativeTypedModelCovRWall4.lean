import rcic.RcicNativeTypedModelCovRFixtures

/-!
# Fresh candidate witnesses for the relevant-function alias pattern

The inner function demand, its actual native application, and the outer
finite lambda table receive new candidate witnesses. These proofs use the
new stored-row and coverage obligations directly. No old CoreY or hereditary
result is transported. These are primitive ordinary-operator controls;
CovRFixtureSyntax supplies the lexical measurement with the inner Prop
domain represented by a sort quantifier. The exact unlanded #7776 source
remains an external replay; this module supplies its generic operator
template and the concrete nonbottom inner action independently.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelKAudit TypedModelKControlAudit
open ReadbackCKAudit ReadbackCK2Audit
open TypedModelCovXAudit TypedModelCovZAudit TypedModelCovQAudit
open ReadbackCK2ModelObstructionAudit

def covRPropArrowRel (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : CovRRel :=
  covRArrow E n Γ false (.sort .zero) (covRCodeRel E .prop) (covRCodeRel E .prop)

theorem covRPropArrow_isCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CandidateCov E (WhStepCK2 E n) Γ false (covRPropArrowRel E n Γ) :=
  covRArrow_isCandidate (covRProp_isCandidate E _ Γ) (covRProp_isCandidate E _ Γ)

theorem covR_relevant_argument_membership (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (x y : Expr Nat) :
    covRPropArrowRel E n Γ x y (.lam [([.bot], .pi .bot [])]) := by
  apply covRArrow_lam_compact (covRProp_isCandidate E _ Γ)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  refine ⟨?_, covRSupport_intro (covRProp_pi_bot_nil E x y)⟩
  intro u hu
  obtain rfl := List.mem_singleton.mp hu
  exact covRSupport_bot (covRProp_isCandidate E (WhStepCK2 E n) Γ)

def covRRelevantAppRel (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (Dty : Expr Nat) : CovRRel :=
  covRArrow E n Γ false Dty (covRPropArrowRel E n Γ) (covRCodeRel E .prop)

theorem covRRelevantApp_isCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (Dty : Expr Nat) :
    CandidateCov E (WhStepCK2 E n) Γ false (covRRelevantAppRel E n Γ Dty) :=
  covRArrow_isCandidate (covRPropArrow_isCandidate E n Γ)
    (covRProp_isCandidate E _ Γ)

/-- The nonempty stored demand is supplied by the new inner-arrow witness,
rather than left as an assumed relation premise. -/
theorem covR_relevant_app_membership (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (Dty x y : Expr Nat) :
    covRRelevantAppRel E n Γ Dty x y
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) := by
  apply covRArrow_lam_compact (covRProp_isCandidate E _ Γ)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  refine ⟨?_, covRSupport_intro (covRProp_pi_bot_nil E x y)⟩
  intro u hu
  obtain rfl := List.mem_singleton.mp hu
  exact covRSupport_intro (covR_relevant_argument_membership E n Γ
    (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp))

/-- A concrete semantic result for the exact outer expression shape. Its
native alias/type premises are supplied separately by the external replay. -/
theorem covR_relevant_app_core (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (Dty Q : Expr Nat) :
    CoreRAt E n Γ false (covRRelevantAppRel E n Γ Dty)
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) :=
  ⟨covRRelevantApp_isCandidate E n Γ Dty,
    covR_relevant_app_membership E n Γ Dty _ _⟩

/-- The inner demand is inhabited, observed, and actually applied to a
native proposition. The nonbottom result is supplied by arrow elimination. -/
theorem covR_relevant_argument_control (n : Nat) :
    CovRFixtureAt eqEnvT n eqGapCtx EnvT.bot false (covRPropArrowRel eqEnvT n eqGapCtx)
      (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
      (.pi (.sort .zero) (.sort .zero)) (.lam [([.bot], .pi .bot [])]) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (.sort .zero)) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.sort .zero)) ∧
    Nonempty (ConvT eqEnvT n eqGapCtx
      (.app (.lam (.sort .zero) idPiProp) idPiProp)
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.sort .zero)) ∧
    CovXCompactAction eqEnvT (.lam [([.bot], .pi .bot [])]) [.bot] (.pi .bot []) ∧
    ApproxTK eqEnvT n eqGapCtx EnvT.bot
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.pi .bot []) ∧
    CoreRAt eqEnvT n eqGapCtx false (covRCodeRel eqEnvT .prop)
      (.app (.lam (.sort .zero) idPiProp) idPiProp)
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.pi .bot []) ∧
    (CptT.pi .bot []) ≠ .bot := by
  have hF := covZ_relevant_argument_native n
  have hN := hasTyT_idPiProp_ctx eqEnvT n eqGapCtx
  have hO := covZ_relevant_argument_observed n eqGapCtx EnvT.bot
  have hrel := covR_relevant_argument_membership eqEnvT n eqGapCtx
    (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
  have ha : CovXCompactAction eqEnvT (.lam [([.bot], .pi .bot [])])
      [.bot] (.pi .bot []) := by
    refine .app (List.mem_singleton_self _) ?_
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact .bot _ _
  have hdom : ∀ u ∈ [CptT.bot], covRCodeRel eqEnvT .prop idPiProp idPiProp u := by
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact (covRProp_isCandidate eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx).bot _ _
  have hout := covRArrow_apply hrel ha idPiProp idPiProp hN hN
    ⟨.refl _ _ _ hN⟩ hdom
  have hApp : HasTyT eqEnvT n eqGapCtx
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.sort .zero) :=
    .app _ _ _ _ _ hF hN
  have hAppObs : ApproxTK eqEnvT n eqGapCtx EnvT.bot
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.pi .bot []) := by
    refine .app hO (List.mem_singleton_self _) ?_
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact .bot _ _ _
  exact ⟨⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, ⟨hF⟩, ⟨hF⟩,
    ⟨.refl _ _ _ hF⟩, hO, CptT.noConfusion,
    covRPropArrow_isCandidate eqEnvT n eqGapCtx, hrel⟩,
    ⟨hN⟩, ⟨hApp⟩, ⟨.refl _ _ _ hApp⟩, ha, hAppObs,
    ⟨covRProp_isCandidate eqEnvT _ eqGapCtx, hout⟩, CptT.noConfusion⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_WALL4_ROOTS
#print axioms covRPropArrowRel
#print axioms covRPropArrow_isCandidate
#print axioms covR_relevant_argument_membership
#print axioms covRRelevantAppRel
#print axioms covRRelevantApp_isCandidate
#print axioms covR_relevant_app_membership
#print axioms covR_relevant_app_core
#print axioms covR_relevant_argument_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_WALL4_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
