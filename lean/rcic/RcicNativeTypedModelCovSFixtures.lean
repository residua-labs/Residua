import rcic.RcicNativeTypedModelCovSInterpret
import rcic.RcicNativeTypedModelCovRFixtureSyntax

/-!
# Eight fixtures at explicitly selected observed type compacts

Every new result below is at the S interpretation of an actual displayed
type observation. Native/model certificates and the stronger existing R
measurements are retained separately. The S edge is constructed from its
new operators, not obtained from an old CoreY or hereditary result.

Nat uses the genuine empty-demand Nat arrow code. The impredicative lambda
uses a nonbottom observed domain Pi and the observed sort output. The raw
alias-in-Pi and raw alias-extension measurements select unknown
information; their total fallback is named and is not a general supplier.
The separate normalized relevant-function measurement uses its rich actual
Pi observation, while the exact external alias replay retains its explicit
per-domain readback obligation. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelKFragmentAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelCovRelEscapeAudit TypedModelCovNormEscapeAudit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit
open TypedModelCovYEtaAudit TypedModelCovZAudit TypedModelCovQAudit TypedModelCovRAudit

/-- Fresh native/model/type-observation evidence and the actual interpreted
S edge, together with its candidate laws and both PER diagonals. -/
def CovSFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (x y A : Expr Nat) (c a : CptT) : Prop :=
  Nonempty (EnvWfT E) ∧ Nonempty (CtxWfT E n Γ) ∧
  Nonempty (HasTyT E n Γ x A) ∧ Nonempty (HasTyT E n Γ y A) ∧
  Nonempty (ConvT E n Γ x y A) ∧ ApproxTK E n Γ ρ x c ∧ c ≠ .bot ∧
  ApproxTK E n Γ ρ A a ∧
  CandidateCovS E (WhStepCK2 E n) Γ false
    (covSObsInterp E n Γ (covSBaseVal E n Γ) a) ∧
  CovSJoint E n Γ (covSBaseVal E n Γ) false a x y c

/-- Packaging only. The new interpreted edge and actual type observation
are supplied independently; the old R result field is not used. -/
theorem covSFixture_reframe {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {p : Bool} {S : CovRRel} {x y A : Expr Nat} {c a : CptT}
    (hr : CovRFixtureAt E n Γ ρ p S x y A c)
    (ha : ApproxTK E n Γ ρ A a)
    (h : covSObsInterp E n Γ (covSBaseVal E n Γ) a x y c) :
    CovSFixtureAt E n Γ ρ x y A c a := by
  obtain ⟨hW, hΓ, hx, hy, hc, ho, hnb, _⟩ := hr
  exact ⟨hW, hΓ, hx, hy, hc, ho, hnb, ha,
    covSObsInterp_isCandidate E n Γ _ a, covSJoint_of_related h⟩

theorem covSRows_singleton_relation {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ds : List CptT) (B : CovSDataCandidate E n Γ) :
    (CovSDataCandidate.rows [(ds, B)]).relation = B.relation := by
  funext x y c
  apply propext
  change (∀ row : {row // row ∈ [(ds, B)]}, row.val.2.relation x y c) ↔ B.relation x y c
  constructor
  · intro h
    exact h ⟨(ds, B), List.mem_singleton_self _⟩
  · intro h row
    have he := List.mem_singleton.mp row.property
    simpa only [he] using h

theorem covSRows_nil_relation (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    (CovSDataCandidate.rows (E := E) (n := n) (Γ := Γ) []).relation = covSTotalRel := by
  funext x y c
  apply propext
  change (∀ row : {row // row ∈ ([] : List (List CptT × CovSDataCandidate E n Γ))},
    row.val.2.relation x y c) ↔ True
  exact ⟨fun _ => trivial, fun _ row => (List.not_mem_nil _ row.property).elim⟩

theorem covSObsInterp_rigid (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (r : Nat) (us : List CptT) :
    covSObsInterp E n Γ v (.spine r us) = covSRigidRel := by
  unfold covSObsInterp
  rw [templateOfObs_spine, interpretObsTemplate]
  rfl

theorem covSObsInterp_nat_arrow (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate natEnvU n Γ) :
    covSObsInterp natEnvU n Γ v covYNatArrowCode =
      covSMeet (fun Dty : Expr Nat =>
        covRArrow natEnvU n Γ false Dty covSRigidRel covSRigidRel) := by
  simp [covSObsInterp, covYNatArrowCode, templateOfObs, interpretObsTemplate,
    covSBuildRows, CovSDataCandidate.ordinary, covSRows_singleton_relation,
    CovSDataCandidate.rigid]

theorem covS_nat_arrow_eta (n : Nat) (Γ : LCtx) (x y : Expr Nat) :
    covSObsInterp natEnvU n Γ (covSBaseVal natEnvU n Γ) covYNatArrowCode
      x y covXNatEtaEmptyRow := by
  rw [covSObsInterp_nat_arrow]
  intro Dty
  apply covRArrow_lam_compact
    (candidateCovR_of_S_false (covSRigid_isCandidate natEnvU n Γ))
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  exact ⟨fun u hu => (List.not_mem_nil u hu).elim,
    ⟨x, y, Or.inr ⟨2, [.bot], rfl⟩⟩⟩

/-- Constructor actions are checked directly at the new rigid leaf.
No axiom-like neutral reflection rule is applied to Nat.succ. -/
theorem covS_nat_arrow_succ (n : Nat) (Γ : LCtx) (x y : Expr Nat) :
    covSObsInterp natEnvU n Γ (covSBaseVal natEnvU n Γ) covYNatArrowCode
      x y (.spine 2 []) := by
  rw [covSObsInterp_nat_arrow]
  intro Dty
  have hB := candidateCovR_of_S_false (covSRigid_isCandidate natEnvU n Γ)
  refine covRArrow_intro (Or.inr (Or.inr ⟨2, [], rfl⟩)) trivial ?_ ?_ ?_
  · intro he
    cases he
  · intro ds out ha _
    cases ha with
    | bot => exact covRSupport_bot hB
    | appSpine _ => exact ⟨x, y, Or.inr ⟨2, _, rfl⟩⟩
  · intro ds out ha N N' _ _ _ _
    cases ha with
    | bot => exact hB.bot _ _
    | appSpine _ => exact Or.inr ⟨2, _, rfl⟩

def covSPolyPropCode : CptT := .pi (.pi .prop []) [([], .sort)]

theorem covSPolyPropCode_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK eqEnvT n Γ ρ covXPolyPropLamTy covSPolyPropCode := by
  refine .pi (a := .pi .prop []) ?_ ?_ ?_
  · exact .pi (approxTK_sort_code eqEnvT n Γ ρ .zero)
      (fun row hrow => (List.not_mem_nil _ hrow).elim)
      (fun row hrow => (List.not_mem_nil _ hrow).elim)
  · intro row hrow u hu
    obtain rfl := List.mem_singleton.mp hrow
    exact (List.not_mem_nil _ hu).elim
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact approxTK_sort_code eqEnvT n (.assumption idPiProp :: Γ)
      (EnvT.cons (demandT []) ρ) (.succ .zero)

theorem covSObsInterp_polyProp (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) :
    covSObsInterp E n Γ v covSPolyPropCode =
      covSMeet (fun Dty : Expr Nat => covRArrow E n Γ false Dty
        (covSForall E n Γ .zero true (fun _ _ => covSTotalRel))
        (covRCodeRel E .sort)) := by
  simp [covSObsInterp, covSPolyPropCode, templateOfObs, interpretObsTemplate,
    covSBuildRows, CovSDataCandidate.ordinary, covSRows_singleton_relation,
    CovSDataCandidate.allProp, covSRows_nil_relation, CovSDataCandidate.sort]

theorem covS_polyProp_lam (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (x y : Expr Nat) :
    covSObsInterp E n Γ (covSBaseVal E n Γ) covSPolyPropCode
      x y (.lam [([], .prop)]) := by
  rw [covSObsInterp_polyProp]
  intro Dty
  apply covRArrow_lam_compact (covRSort_isCandidate E _ Γ)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  exact ⟨fun u hu => (List.not_mem_nil _ hu).elim,
    covRSupport_intro (covRSort_accepts_prop E x y)⟩

theorem covS_fixture_natSucc_eta (n : Nat) :
    CovRInterpretedFixtureAt natEnvU n [] EnvT.bot covRNatArrowSyntax
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) covXNatEtaEmptyRow ∧
    CovSFixtureAt natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) covXNatEtaEmptyRow covYNatArrowCode := by
  have hr := (covR_syntax_fixture_natSucc_eta n).2
  exact ⟨hr, covSFixture_reframe hr.1 (approxTK_covYNatArrowCode n [] EnvT.bot)
    (covS_nat_arrow_eta n [] _ _)⟩

/-- This raw alias Pi selects the actual unknown-domain observation. Its
S membership is explicitly a total fallback; the stronger R edge and the
domain's native readback certificate remain separate evidence. -/
theorem covS_fixture_alias_in_pi_fallback (n : Nat) :
    ∃ A B, RedR (WhStepCK2 eqEnvT n) eqGapCtx (eqGapDirectAlias A B) (.sort .zero) ∧
      CovRInterpretedFixtureAt eqEnvT n eqGapCtx EnvT.bot (covRPropArrowSyntax eqEnvT)
        covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
        covNormAliasIdentityCpt ∧
      covSObsInterp eqEnvT n eqGapCtx (covSBaseVal eqEnvT n eqGapCtx)
        (.pi .bot []) = covSTotalRel ∧
      CovSFixtureAt eqEnvT n eqGapCtx EnvT.bot
        covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
        covNormAliasIdentityCpt (.pi .bot []) := by
  obtain ⟨A, B, hd, _, hr⟩ := covR_syntax_fixture_alias_in_pi n
  refine ⟨A, B, hd, hr, covSObsInterp_unknownPi _ _ _ _,
    covSFixture_reframe hr.1 (approxTK_pi_bot_nil _ _ _ _ _ _) ?_⟩
  rw [covSObsInterp_unknownPi]
  trivial

theorem covS_fixture_polyPropLam (n : Nat) :
    CovRInterpretedFixtureAt eqEnvT n [] EnvT.bot (covRPolyPropSyntax eqEnvT)
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy (.lam [([], .prop)]) ∧
    CovSFixtureAt eqEnvT n [] EnvT.bot covXPolyPropLam covXPolyPropLam
      covXPolyPropLamTy (.lam [([], .prop)]) covSPolyPropCode := by
  have hr := (covR_syntax_fixture_polyPropLam n).2
  exact ⟨hr, covSFixture_reframe hr.1 (covSPolyPropCode_observed n [] EnvT.bot)
    (covS_polyProp_lam eqEnvT n [] _ _)⟩

/-- Candidate-demand evidence is a new structure. No semantic substitution
identity is asserted by its per-index relation supplies. -/
structure CovSDemandSubstAt (E : ResolvedEnv) (n : Nat) (Δ : LCtx)
    (S : Nat → CovSRel) (ρ ρ' : EnvT) (σ σ' : SubstT) (Γ : LCtx) : Prop where
  candidates : ∀ i, CandidateCovS E (WhStepCK2 E n) Δ false (S i)
  typedL : TypedSubstT E n Δ σ Γ
  typedR : TypedSubstT E n Δ σ' Γ
  conv : ConvSubstT E n Δ σ σ' Γ
  ctxL : CtxEnvM (ctxModelT_approxTK E n Γ) Γ ρ
  ctxR : CtxEnvM (ctxModelT_approxTK E n Γ) Γ ρ'
  edges : ∀ i c, ρ i c ∨ ρ' i c →
    S i (σ i) (σ' i) c ∧ S i (σ' i) (σ i) c ∧
    S i (σ i) (σ i) c ∧ S i (σ' i) (σ' i) c

/-- The raw alias's unknown type observation supplies the total predicate.
Only native substitution/model coherence fields are imported; all four new
candidate edges are supplied directly. This is the named fallback case. -/
theorem covS_alias_demand_substitution_fallback (n : Nat) (A B : Expr Nat)
    (hN : HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) :
    CovSDemandSubstAt eqEnvT n eqGapCtx (fun _ => covSTotalRel)
      (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
      (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
      (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
      (.assumption (eqGapDirectAlias A B) :: eqGapCtx) := by
  have hr := covR_alias_demand_substitution n A B hN
  exact ⟨fun _ => covSTotal_isCandidate eqEnvT _ eqGapCtx false,
    hr.typedL, hr.typedR, hr.conv, hr.ctxL, hr.ctxR,
    fun _ _ _ => ⟨trivial, trivial, trivial, trivial⟩⟩

theorem covS_fixture_alias_extension_fallback (n : Nat) :
    ∃ A B, RedR (WhStepCK2 eqEnvT n) eqGapCtx (eqGapDirectAlias A B) (.sort .zero) ∧
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovRDemandSubstAt eqEnvT n eqGapCtx (fun _ => false)
        (fun _ => covRCodeRel eqEnvT .prop)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      CovSDemandSubstAt eqEnvT n eqGapCtx (fun _ => covSTotalRel)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      CovRInterpretedFixtureAt eqEnvT n eqGapCtx EnvT.bot .prop
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) ∧
      CovSFixtureAt eqEnvT n eqGapCtx EnvT.bot
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) .bot := by
  obtain ⟨A, B, hd, _, hΓ, hσ, hr⟩ := covR_syntax_fixture_alias_extension n
  obtain ⟨hN⟩ := hr.1.2.2.1
  exact ⟨A, B, hd, hΓ, hσ, covS_alias_demand_substitution_fallback n A B hN,
    hr, covSFixture_reframe hr.1 (.bot _ _ _) (covS_unknown_accepts_all _ _ _ _ _ _ _)⟩

/-- Shape and coverage are measured at the exact new observed Nat arrow
predicate, with every erased native-domain choice quantified explicitly. -/
theorem covS_fixture_nat_coverage_shape (n : Nat) :
    CovRInterpretedFixtureAt natEnvU n [] EnvT.bot covRNatArrowSyntax
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) ∧
    (∀ Dty : Expr Nat, covRArrow natEnvU n [] false Dty
      covSRigidRel covSRigidRel (.const 2 []) (.const 2 []) (.spine 2 [])) ∧
    CovRArrowCoverage natEnvU covSRigidRel covSRigidRel (.spine 2 []) ∧
    CovSFixtureAt natEnvU n [] EnvT.bot (.const 2 []) (.const 2 [])
      (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) covYNatArrowCode := by
  obtain ⟨_, _, _, hr⟩ := covR_syntax_fixture_nat_coverage_shape n
  have hm := covS_nat_arrow_succ n [] (.const 2 []) (.const 2 [])
  have hall := hm
  rw [covSObsInterp_nat_arrow] at hall
  exact ⟨hr, hall, covRArrow_coverage (hall (.const 0 [])),
    covSFixture_reframe hr.1 (approxTK_covYNatArrowCode n [] EnvT.bot) hm⟩

theorem covS_fixture_eq_anchor (n : Nat) :
    CovRInterpretedFixtureAt eqEnvT n eqGapCtx EnvT.bot .prop
      idPiProp idPiProp (.sort .zero) (.pi .bot []) ∧
    CovSFixtureAt eqEnvT n eqGapCtx EnvT.bot
      idPiProp idPiProp (.sort .zero) (.pi .bot []) .prop := by
  have hr := (covR_syntax_fixture_eq_anchor n).2
  refine ⟨hr, covSFixture_reframe hr.1 (approxTK_sort_code _ _ _ _ .zero) ?_⟩
  rw [covSObsInterp_prop]
  exact covRProp_pi_bot_nil eqEnvT _ _

theorem covS_fixture_nat_anchor (n : Nat) :
    CovRInterpretedFixtureAt natEnvU n [] EnvT.bot covRNatSyntax
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) ∧
    CovSFixtureAt natEnvU n [] EnvT.bot
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) := by
  have hr := (covR_syntax_fixture_nat_anchor n).2
  refine ⟨hr, covSFixture_reframe hr.1 ?_ ?_⟩
  · exact .free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)
  · rw [covSObsInterp_rigid]
    exact Or.inr ⟨1, [], rfl⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_FIXTURES_ROOTS
#print axioms CovSFixtureAt
#print axioms covSFixture_reframe
#print axioms covSRows_singleton_relation
#print axioms covSRows_nil_relation
#print axioms covSObsInterp_rigid
#print axioms covSObsInterp_nat_arrow
#print axioms covS_nat_arrow_eta
#print axioms covS_nat_arrow_succ
#print axioms covSPolyPropCode
#print axioms covSPolyPropCode_observed
#print axioms covSObsInterp_polyProp
#print axioms covS_polyProp_lam
#print axioms covS_fixture_natSucc_eta
#print axioms covS_fixture_alias_in_pi_fallback
#print axioms covS_fixture_polyPropLam
#print axioms CovSDemandSubstAt
#print axioms covS_alias_demand_substitution_fallback
#print axioms covS_fixture_alias_extension_fallback
#print axioms covS_fixture_nat_coverage_shape
#print axioms covS_fixture_eq_anchor
#print axioms covS_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
