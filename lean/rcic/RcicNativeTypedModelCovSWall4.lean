import rcic.RcicNativeTypedModelCovSFixtures

/-!
# The relevant-function alias replay under observed-template semantics

The normal `Prop → Prop` domain has a rich actual type observation and an
actual S sort quantifier. Its nonempty function demand and application are
supplied below. A raw alias of that domain is a separate measurement: its
displayed raw observation is the unknown-domain Pi and hence a named total
fallback. The native readback and the prior R result remain explicit; no
whole-Pi reduction or observation transport is inferred from that readback.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelKControlAudit ReadbackCKAudit ReadbackCK2Audit
open TypedModelCovXAudit TypedModelCovZAudit TypedModelCovQAudit TypedModelCovRAudit

/-- This outer type row is empty-demand; the value's nonempty function
demand is independently checked by the ordinary operator's stored-row rule. -/
def covSRelevantCode : CptT := .pi covZPropArrowCode [([], .prop)]

theorem covSPropArrowCode_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ApproxTK E n Γ ρ (.pi (.sort .zero) (.sort .zero)) covZPropArrowCode := by
  refine .pi (approxTK_sort_code E n Γ ρ .zero) ?_ ?_
  · intro row hrow u hu
    obtain rfl := List.mem_singleton.mp hrow
    exact (List.not_mem_nil _ hu).elim
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact approxTK_sort_code E n (.assumption (.sort .zero) :: Γ)
      (EnvT.cons (demandT []) ρ) .zero

theorem covSRelevantCode_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ApproxTK E n Γ ρ (.pi (.pi (.sort .zero) (.sort .zero)) (.sort .zero))
      covSRelevantCode := by
  refine .pi (covSPropArrowCode_observed E n Γ ρ) ?_ ?_
  · intro row hrow u hu
    obtain rfl := List.mem_singleton.mp hrow
    exact (List.not_mem_nil _ hu).elim
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact approxTK_sort_code E n
      (.assumption (.pi (.sort .zero) (.sort .zero)) :: Γ)
      (EnvT.cons (demandT []) ρ) .zero

theorem covSObsInterp_prop_arrow (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) :
    covSObsInterp E n Γ v covZPropArrowCode =
      covSForall E n Γ .zero true (fun _ _ => covRCodeRel E .prop) := by
  simp [covSObsInterp, covZPropArrowCode, templateOfObs, interpretObsTemplate,
    covSBuildRows, CovSDataCandidate.allProp, covSRows_singleton_relation,
    CovSDataCandidate.prop]

theorem covSObsInterp_relevant (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) :
    covSObsInterp E n Γ v covSRelevantCode =
      covSMeet (fun Dty : Expr Nat => covRArrow E n Γ false Dty
        (covSForall E n Γ .zero true (fun _ _ => covRCodeRel E .prop))
        (covRCodeRel E .prop)) := by
  simp [covSObsInterp, covSRelevantCode, covZPropArrowCode, templateOfObs,
    interpretObsTemplate, covSBuildRows, CovSDataCandidate.ordinary,
    CovSDataCandidate.allProp, covSRows_singleton_relation, CovSDataCandidate.prop]

/-- A fresh S quantifier proof: every output belongs to the constant Prop
leaf independently of the universally quantified positive candidate. -/
theorem covS_relevant_argument_membership (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (x y : Expr Nat) :
    covSObsInterp E n Γ (covSBaseVal E n Γ) covZPropArrowCode
      x y (.lam [([.bot], .pi .bot [])]) := by
  rw [covSObsInterp_prop_arrow]
  refine covSForall_intro (Or.inr (Or.inl ⟨_, rfl⟩)) ?_
  intro ds out ha T hT S hS
  cases ha with
  | bot => exact (covRProp_isCandidate E (WhStepCK2 E n) Γ).bot _ _
  | app hs _ =>
      obtain rfl := List.mem_singleton.mp hs
      exact covRProp_pi_bot_nil E _ _

/-- The nonempty stored function demand is supplied at the inner S
quantifier. The outer operator keeps its unchanged strict stored rows. -/
theorem covS_relevant_app_membership (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (x y : Expr Nat) :
    covSObsInterp E n Γ (covSBaseVal E n Γ) covSRelevantCode x y
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) := by
  rw [covSObsInterp_relevant]
  intro Dty
  apply covRArrow_lam_compact (covRProp_isCandidate E _ Γ)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  refine ⟨?_, covRSupport_intro (covRProp_pi_bot_nil E x y)⟩
  intro u hu
  obtain rfl := List.mem_singleton.mp hu
  have h := covS_relevant_argument_membership E n Γ
    (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
  rw [covSObsInterp_prop_arrow] at h
  exact covRSupport_intro h

theorem covS_relevant_app_joint (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (Q : Expr Nat) :
    CandidateCovS E (WhStepCK2 E n) Γ false
      (covSObsInterp E n Γ (covSBaseVal E n Γ) covSRelevantCode) ∧
    CovSJoint E n Γ (covSBaseVal E n Γ) false covSRelevantCode
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) :=
  ⟨covSObsInterp_isCandidate E n Γ _ covSRelevantCode,
    covSJoint_of_related (covS_relevant_app_membership E n Γ _ _)⟩

/-- The quantified argument candidate is actually supplied as total and
the elimination is exercised at the native proposition idPiProp. Native
typing, model observation, and the prior R fixture remain inhabited. -/
theorem covS_relevant_argument_control (n : Nat) :
    CovRInterpretedFixtureAt eqEnvT n eqGapCtx EnvT.bot (covRPropArrowSyntax eqEnvT)
      (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
      (.pi (.sort .zero) (.sort .zero)) (.lam [([.bot], .pi .bot [])]) ∧
    CovSFixtureAt eqEnvT n eqGapCtx EnvT.bot
      (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
      (.pi (.sort .zero) (.sort .zero)) (.lam [([.bot], .pi .bot [])]) covZPropArrowCode ∧
    CandidateCovS eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx true covSTotalRel ∧
    CovXCompactAction eqEnvT (.lam [([.bot], .pi .bot [])]) [.bot] (.pi .bot []) ∧
    CovSFixtureAt eqEnvT n eqGapCtx EnvT.bot
      (.app (.lam (.sort .zero) idPiProp) idPiProp)
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.sort .zero) (.pi .bot []) .prop := by
  obtain ⟨_, hr, ha, hApp⟩ := covR_syntax_relevant_argument_control n
  have hrel := covS_relevant_argument_membership eqEnvT n eqGapCtx
    (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
  have hforall := hrel
  rw [covSObsInterp_prop_arrow] at hforall
  have hD := covSTotal_isCandidate eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx true
  have hout := covSForall_apply hforall ha idPiProp
    (hasTyT_idPiProp_ctx eqEnvT n eqGapCtx) covSTotalRel hD
  refine ⟨hr, covSFixture_reframe hr.1
    (covSPropArrowCode_observed eqEnvT n eqGapCtx EnvT.bot) hrel, hD, ha,
    covSFixture_reframe hApp.1 (approxTK_sort_code _ _ _ _ .zero) ?_⟩
  rw [covSObsInterp_prop]
  exact hout

/-- External replay packaging. All native/environment/model certificates
are explicit inputs for the exact #7776 terms. Native endpoint typing at
the normalized Pi is a separate input. The fresh rich S fixture is at that
independently typed and observed normalized type; the raw original alias Pi is
reported only at its actual unknown-domain observation. This wrapper does
not infer a whole-Pi readback or a general native result supply. -/
theorem covS_relevant_app_replay {E : ResolvedEnv} (n : Nat) {Γ : LCtx}
    (ρ : EnvT) {D Q : Expr Nat} (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (hread : RedR (WhStepCK2 E n) Γ D (.pi (.sort .zero) (.sort .zero)))
    (ht : HasTyT E n Γ
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi D (.sort .zero)))
    (htNormal : HasTyT E n Γ
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi (.pi (.sort .zero) (.sort .zero)) (.sort .zero)))
    (ho : ApproxTK E n Γ ρ
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])])) :
    RedR (WhStepCK2 E n) Γ D (.pi (.sort .zero) (.sort .zero)) ∧
    CovRInterpretedFixtureAt E n Γ ρ (covRRelevantSyntax E)
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi D (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) ∧
    CovSFixtureAt E n Γ ρ
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi (.pi (.sort .zero) (.sort .zero)) (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) covSRelevantCode ∧
    covSObsInterp E n Γ (covSBaseVal E n Γ) (.pi .bot []) = covSTotalRel ∧
    CovSFixtureAt E n Γ ρ
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi D (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) (.pi .bot []) := by
  obtain ⟨hCore, hJoint⟩ := covR_syntax_relevant_app_core E n Γ Q
  have hf : CovRFixtureAt E n Γ ρ false
      (covRInterpret E n Γ (covRRelevantSyntax E) (fun _ => false) (covRBaseVal E))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi D (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) :=
    ⟨⟨hW⟩, ⟨hΓ⟩, ⟨ht⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩, ho, CptT.noConfusion, hCore⟩
  have hfNormal : CovRFixtureAt E n Γ ρ false
      (covRInterpret E n Γ (covRRelevantSyntax E) (fun _ => false) (covRBaseVal E))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.pi (.pi (.sort .zero) (.sort .zero)) (.sort .zero))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) :=
    ⟨⟨hW⟩, ⟨hΓ⟩, ⟨htNormal⟩, ⟨htNormal⟩, ⟨.refl _ _ _ htNormal⟩,
      ho, CptT.noConfusion, hCore⟩
  refine ⟨hread, ⟨hf, hJoint⟩,
    covSFixture_reframe hfNormal (covSRelevantCode_observed E n Γ ρ)
      (covS_relevant_app_membership E n Γ _ _), covSObsInterp_unknownPi _ _ _ _,
    covSFixture_reframe hf (approxTK_pi_bot_nil _ _ _ _ _ _) ?_⟩
  rw [covSObsInterp_unknownPi]
  trivial

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_WALL4_ROOTS
#print axioms covSRelevantCode
#print axioms covSPropArrowCode_observed
#print axioms covSRelevantCode_observed
#print axioms covSObsInterp_prop_arrow
#print axioms covSObsInterp_relevant
#print axioms covS_relevant_argument_membership
#print axioms covS_relevant_app_membership
#print axioms covS_relevant_app_joint
#print axioms covS_relevant_argument_control
#print axioms covS_relevant_app_replay
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_WALL4_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
