import rcic.RcicNativeTypedModelCovRArrow
import rcic.RcicNativeTypedModelCovZFixtures
import rcic.RcicNativeTypedModelCovPWall4

/-!
# Eight observations at explicit new candidate predicates

The result gate below contains the new candidate laws and actual membership
in the displayed predicate. Old CoreY and hereditary result witnesses are
not fields of this gate and are not used to supply it. Existing controls
provide only their independent native and model certificates.

The predicates are concrete finite templates: a Nat leaf, the ordinary Nat
arrow, an alias-domain Prop arrow, and a positive-domain sort arrow. The
Prop-domain arrows here are primitive operator controls; the lexical
sort-binder measurements are supplied separately in CovRFixtureSyntax.
These explicit predicates are not a global native type interpretation.
The nonempty extension also has a
fresh candidate-demand substitution certificate, with native substitution
typing/conversion, both actual model coherence guards, and all four demand
edges. Its per-index predicates are supplied explicitly; no canonical
assignment to arbitrary native context types is asserted.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open PiProbeRelIotaAudit TypedModelCovRelAudit TypedModelCovRelEscapeAudit
open TypedModelCovNormCov2Audit
open TypedModelCovNormEscapeAudit TypedModelCovNormSubstAudit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit
open TypedModelCovYEtaAudit TypedModelCovYPolyPropAudit TypedModelCovZAudit
open TypedModelCovPAudit TypedModelCovQAudit

/-- The actual new result relation includes supplied candidate laws. -/
def CoreRAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (positive : Bool)
    (S : CovRRel) (x y : Expr Nat) (c : CptT) : Prop :=
  CandidateCov E (WhStepCK2 E n) Γ positive S ∧ S x y c

/-- A concrete native/model inhabitant and a fresh candidate result. The
observed compact belongs to the left endpoint, as required by the eta test. -/
def CovRFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (positive : Bool) (S : CovRRel) (x y A : Expr Nat) (c : CptT) : Prop :=
  Nonempty (EnvWfT E) ∧ Nonempty (CtxWfT E n Γ) ∧
  Nonempty (HasTyT E n Γ x A) ∧ Nonempty (HasTyT E n Γ y A) ∧
  Nonempty (ConvT E n Γ x y A) ∧ ApproxTK E n Γ ρ x c ∧ c ≠ .bot ∧
  CoreRAt E n Γ positive S x y c

/-- Supported rows directly supply the ordinary operator when its output
predicate is a compact leaf. This is not transport of an old core relation. -/
theorem covRArrow_lam_compact {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {Dty : Expr Nat} {D : CovRRel} {G : CptT → Prop}
    {rows : List (List CptT × CptT)}
    (hB : CandidateCov E (WhStepCK2 E n) Γ false (covRCompactRel G))
    (hrows : CovRLambdaRows D (covRCompactRel G) (.lam rows)) (x y : Expr Nat) :
    covRArrow E n Γ false Dty D (covRCompactRel G) x y (.lam rows) := by
  refine covRArrow_intro (Or.inr (Or.inl ⟨rows, rfl⟩)) hrows ?_ ?_ ?_
  · intro he
    cases he
  · intro ds out ha _
    cases ha with
    | bot => exact covRSupport_bot hB
    | app hs _ => exact (hrows _ hs).2
  · intro ds out ha N N' _ _ _ _
    cases ha with
    | bot => exact hB.bot _ _
    | app hs _ =>
        obtain ⟨a, b, h⟩ := (hrows _ hs).2
        exact h

theorem covRProp_pi_bot_nil (E : ResolvedEnv) (x y : Expr Nat) :
    covRCodeRel E .prop x y (.pi .bot []) :=
  ctyCovQ_univProp (.pi .bot (by simp))

theorem covRNat_not_positive : ¬ IsPropCTP natEnvU (.spine 0 []) :=
  fun h => not_isPropCT_natEnvU_nat_spine [] (isPropCT_of_isPropCTP h)

theorem covRNat_isCandidate (n : Nat) (Γ : LCtx) :
    CandidateCov natEnvU (WhStepCK2 natEnvU n) Γ false
      (covRCodeRel natEnvU (.spine 0 [])) :=
  covRSpine_isCandidate natEnvU _ Γ 0 [] covRNat_not_positive

theorem covRNat_spine (x y : Expr Nat) (r : Nat) (us : List CptT) :
    covRCodeRel natEnvU (.spine 0 []) x y (.spine r us) :=
  ctyCovQ_of_P (CTyCovP2.spine covRNat_not_positive)

def covRNatArrowRel (n : Nat) (Γ : LCtx) : CovRRel :=
  covRArrow natEnvU n Γ false (.const 0 [])
    (covRCodeRel natEnvU (.spine 0 [])) (covRCodeRel natEnvU (.spine 0 []))

theorem covRNatArrow_isCandidate (n : Nat) (Γ : LCtx) :
    CandidateCov natEnvU (WhStepCK2 natEnvU n) Γ false (covRNatArrowRel n Γ) :=
  covRArrow_isCandidate (covRNat_isCandidate n Γ) (covRNat_isCandidate n Γ)

theorem covRNatArrow_eta (n : Nat) (Γ : LCtx) (x y : Expr Nat) :
    covRNatArrowRel n Γ x y covXNatEtaEmptyRow := by
  apply covRArrow_lam_compact (covRNat_isCandidate n Γ)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  exact ⟨fun u hu => (List.not_mem_nil u hu).elim,
    covRSupport_intro (covRNat_spine x y 2 [.bot])⟩

/-- Successor is a constructor. Its candidate actions are checked directly;
the body-free ordinary-neutral reflection rule is not applied to it. -/
theorem covRNatArrow_succ (n : Nat) (Γ : LCtx) (x y : Expr Nat) :
    covRNatArrowRel n Γ x y (.spine 2 []) := by
  refine covRArrow_intro (Or.inr (Or.inr ⟨2, [], rfl⟩)) trivial ?_ ?_ ?_
  · intro he
    cases he
  · intro ds out ha _
    cases ha with
    | bot => exact covRSupport_bot (covRNat_isCandidate n Γ)
    | appSpine _ => exact covRSupport_intro (covRNat_spine x y 2 _)
  · intro ds out ha N N' _ _ _ _
    cases ha with
    | bot => exact (covRNat_isCandidate n Γ).bot _ _
    | appSpine _ => exact covRNat_spine _ _ 2 _

def covRAliasArrowRel (n : Nat) (A B : Expr Nat) : CovRRel :=
  covRArrow eqEnvT n eqGapCtx false (eqGapDirectAlias A B)
    (covRCodeRel eqEnvT .prop) (covRCodeRel eqEnvT .prop)

theorem covRAliasArrow_isCandidate (n : Nat) (A B : Expr Nat) :
    CandidateCov eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx false
      (covRAliasArrowRel n A B) :=
  covRArrow_isCandidate (covRProp_isCandidate eqEnvT _ eqGapCtx)
    (covRProp_isCandidate eqEnvT _ eqGapCtx)

theorem covRAliasArrow_identity (n : Nat) (A B x y : Expr Nat) :
    covRAliasArrowRel n A B x y covNormAliasIdentityCpt := by
  apply covRArrow_lam_compact (covRProp_isCandidate eqEnvT _ eqGapCtx)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  refine ⟨?_, covRSupport_intro (covRProp_pi_bot_nil eqEnvT x y)⟩
  intro u hu
  obtain rfl := List.mem_singleton.mp hu
  exact covRSupport_intro (covRProp_pi_bot_nil eqEnvT x y)

def covRPolyPropArrowRel (n : Nat) (Γ : LCtx) : CovRRel :=
  covRArrow eqEnvT n Γ false idPiProp covRPositiveRel (covRCodeRel eqEnvT .sort)

theorem covRPolyPropArrow_isCandidate (n : Nat) (Γ : LCtx) :
    CandidateCov eqEnvT (WhStepCK2 eqEnvT n) Γ false (covRPolyPropArrowRel n Γ) :=
  covRArrow_isCandidate (covRPositive_isCandidate eqEnvT _ Γ)
    (covRSort_isCandidate eqEnvT _ Γ)

theorem covRPolyPropArrow_lam (n : Nat) (Γ : LCtx) (x y : Expr Nat) :
    covRPolyPropArrowRel n Γ x y (.lam [([], .prop)]) := by
  apply covRArrow_lam_compact (covRSort_isCandidate eqEnvT _ Γ)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  exact ⟨fun u hu => (List.not_mem_nil u hu).elim,
    covRSupport_intro (covRSort_accepts_prop eqEnvT x y)⟩

/-- Fresh demand evidence for explicitly supplied per-index predicates.
Native substitutions and model let coherence are retained independently. -/
structure CovRDemandSubstAt (E : ResolvedEnv) (n : Nat) (Δ : LCtx)
    (positive : Nat → Bool) (S : Nat → CovRRel)
    (ρ ρ' : EnvT) (σ σ' : SubstT) (Γ : LCtx) : Prop where
  candidates : ∀ i, CandidateCov E (WhStepCK2 E n) Δ (positive i) (S i)
  typedL : TypedSubstT E n Δ σ Γ
  typedR : TypedSubstT E n Δ σ' Γ
  conv : ConvSubstT E n Δ σ σ' Γ
  ctxL : CtxEnvM (ctxModelT_approxTK E n Γ) Γ ρ
  ctxR : CtxEnvM (ctxModelT_approxTK E n Γ) Γ ρ'
  edges : ∀ i c, ρ i c ∨ ρ' i c →
    S i (σ i) (σ' i) c ∧ S i (σ' i) (σ i) c ∧
    S i (σ i) (σ i) c ∧ S i (σ' i) (σ' i) c

/-- The actual extension has one nonbottom demanded head and a bottom
tail. Each of its four candidate edges is constructed directly. -/
theorem covR_alias_demand_substitution (n : Nat) (A B : Expr Nat)
    (hN : HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) :
    CovRDemandSubstAt eqEnvT n eqGapCtx (fun _ => false)
      (fun _ => covRCodeRel eqEnvT .prop)
      (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
      (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
      (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
      (.assumption (eqGapDirectAlias A B) :: eqGapCtx) := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  have hid := typedSubstT_id (envClosed_of_envWfT pinEqGroupWfT) hΓ
  have ht := cov_typedSubst_cons hid (by simpa only [substT_id] using hN)
  have hctx (ρ : EnvT) :
      CtxEnvM (ctxModelT_approxTK eqEnvT n
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx))
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ρ := by
    intro i v hv
    cases i with
    | zero => cases hv
    | succ i =>
        rw [lookupValue_cons_succ, lookupValue_eqGapCtx_none] at hv
        exact Option.noConfusion hv
  refine ⟨fun _ => covRProp_isCandidate eqEnvT _ eqGapCtx,
    ht, ht, ?_, hctx _, hctx _, ?_⟩
  · intro i T hT
    obtain ⟨h⟩ := ht.1 i T hT
    exact ⟨.refl _ _ _ h⟩
  · intro i c hc
    have hm := hc.elim id id
    cases i with
    | zero =>
        change c ∈ [CptT.pi .bot []] at hm
        obtain rfl := List.mem_singleton.mp hm
        have h := covRProp_pi_bot_nil eqEnvT idPiProp idPiProp
        exact ⟨h, h, h, h⟩
    | succ i =>
        change c = .bot at hm
        subst c
        have h := (covRProp_isCandidate eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx).bot
          ((SubstT.cons idPiProp SubstT.id) (i + 1))
          ((SubstT.cons idPiProp SubstT.id) (i + 1))
        exact ⟨h, h, h, h⟩

theorem covR_fixture_natSucc_eta (n : Nat) :
    CovRFixtureAt natEnvU n [] EnvT.bot false (covRNatArrowRel n [])
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) covXNatEtaEmptyRow := by
  obtain ⟨hW, hΓ, hl, hr, hc, ho, _, hnb⟩ :=
    covY_natSucc_eta_hereditary_control n
  exact ⟨hW, hΓ, hl, hr, hc, ho, hnb, covRNatArrow_isCandidate n [],
    covRNatArrow_eta n [] _ _⟩

theorem covR_fixture_alias_in_pi (n : Nat) :
    ∃ A B, RedR (WhStepCK2 eqEnvT n) eqGapCtx (eqGapDirectAlias A B) (.sort .zero) ∧
      CovRFixtureAt eqEnvT n eqGapCtx EnvT.bot false (covRAliasArrowRel n A B)
        covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
        covNormAliasIdentityCpt := by
  obtain ⟨A, B, hW, hΓ, hx, hy, hc, _, ho, hnb, _⟩ :=
    covZ_fixture_alias_in_pi n
  exact ⟨A, B, eqGapAlias_type_read n A B, hW, hΓ, hx, hy, hc,
    ho.elim id id, hnb, covRAliasArrow_isCandidate n A B,
    covRAliasArrow_identity n A B _ _⟩

theorem covR_fixture_polyPropLam (n : Nat) :
    CovRFixtureAt eqEnvT n [] EnvT.bot false (covRPolyPropArrowRel n [])
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy (.lam [([], .prop)]) := by
  obtain ⟨hW, hΓ, hx, hy, hc, _, ho, hnb, _⟩ := covZ_fixture_polyPropLam n
  exact ⟨hW, hΓ, hx, hy, hc, ho.elim id id, hnb,
    covRPolyPropArrow_isCandidate n [], covRPolyPropArrow_lam n [] _ _⟩

theorem covR_fixture_alias_extension (n : Nat) :
    ∃ A B,
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovRDemandSubstAt eqEnvT n eqGapCtx (fun _ => false)
        (fun _ => covRCodeRel eqEnvT .prop)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      CovRFixtureAt eqEnvT n eqGapCtx EnvT.bot false (covRCodeRel eqEnvT .prop)
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) := by
  obtain ⟨hW, hΓ, A, B, hΓ', ⟨ht⟩, ho, _, _, _, hnb⟩ :=
    covY_fixture_alias_extension n
  exact ⟨A, B, hΓ', covR_alias_demand_substitution n A B ht,
    hW, hΓ, ⟨ht⟩, ⟨ht⟩, ⟨.refl _ _ _ ht⟩, ho, hnb,
    covRProp_isCandidate eqEnvT _ eqGapCtx, covRProp_pi_bot_nil eqEnvT _ _⟩

/-- The two Nat boundary cases now exhibit the ordinary arrow predicate
itself and its actual semantic coverage. No old finite code is a result gate. -/
theorem covR_fixture_nat_coverage_shape (n : Nat) :
    covRNatArrowRel n [] = covRArrow natEnvU n [] false (.const 0 [])
      (covRCodeRel natEnvU (.spine 0 [])) (covRCodeRel natEnvU (.spine 0 [])) ∧
    CovRArrowCoverage natEnvU (covRCodeRel natEnvU (.spine 0 []))
      (covRCodeRel natEnvU (.spine 0 [])) (.spine 2 []) ∧
    CovRFixtureAt natEnvU n [] EnvT.bot false (covRNatArrowRel n [])
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) := by
  obtain ⟨_, _, hW, hΓ, hx, hy, hc, _, ho, hnb, _⟩ :=
    covZ_fixture_nat_coverage_and_shape n
  have hrel := covRNatArrow_succ n [] (.const 2 []) (.const 2 [])
  exact ⟨rfl, covRArrow_coverage hrel, hW, hΓ, hx, hy, hc, ho.elim id id, hnb,
    covRNatArrow_isCandidate n [], hrel⟩

theorem covR_fixture_eq_anchor (n : Nat) :
    CovRFixtureAt eqEnvT n eqGapCtx EnvT.bot false (covRCodeRel eqEnvT .prop)
      idPiProp idPiProp (.sort .zero) (.pi .bot []) := by
  obtain ⟨hW, hΓ, hx, hy, hc, _, ho, hnb, _⟩ := covZ_fixture_eq_anchor n
  exact ⟨hW, hΓ, hx, hy, hc, ho.elim id id, hnb,
    covRProp_isCandidate eqEnvT _ eqGapCtx, covRProp_pi_bot_nil eqEnvT _ _⟩

theorem covR_fixture_nat_anchor (n : Nat) :
    CovRFixtureAt natEnvU n [] EnvT.bot false (covRCodeRel natEnvU (.spine 0 []))
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) := by
  obtain ⟨hW, hΓ, hx, hy, hc, _, ho, hnb, _⟩ := covZ_fixture_nat_anchor n
  exact ⟨hW, hΓ, hx, hy, hc, ho.elim id id, hnb,
    covRNat_isCandidate n [], covRNat_spine _ _ 1 []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_FIXTURES_ROOTS
#print axioms CoreRAt
#print axioms CovRFixtureAt
#print axioms covRArrow_lam_compact
#print axioms covRProp_pi_bot_nil
#print axioms covRNat_not_positive
#print axioms covRNat_isCandidate
#print axioms covRNat_spine
#print axioms covRNatArrowRel
#print axioms covRNatArrow_isCandidate
#print axioms covRNatArrow_eta
#print axioms covRNatArrow_succ
#print axioms covRAliasArrowRel
#print axioms covRAliasArrow_isCandidate
#print axioms covRAliasArrow_identity
#print axioms covRPolyPropArrowRel
#print axioms covRPolyPropArrow_isCandidate
#print axioms covRPolyPropArrow_lam
#print axioms CovRDemandSubstAt
#print axioms covR_alias_demand_substitution
#print axioms covR_fixture_natSucc_eta
#print axioms covR_fixture_alias_in_pi
#print axioms covR_fixture_polyPropLam
#print axioms covR_fixture_alias_extension
#print axioms covR_fixture_nat_coverage_shape
#print axioms covR_fixture_eq_anchor
#print axioms covR_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
