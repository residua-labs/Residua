import rcic.RcicNativeTypedModelCovRSyntax
import rcic.RcicNativeTypedModelCovRWall4

/-!
# The eight observations at the lexical candidate interpretation

These supplies use the final lexical interpretation, including its sort
quantifier at a native Prop-domain binder. The fresh joints are derived
from the supplied candidate edge. No old CoreY or hereditary result is a
field or a source for that edge.

The alias-in-Pi control has a per-domain CK2 readback certificate. It does
not assert that weak-head readback reduces inside a native Pi. Its original
native type is retained, and the separately displayed normalized domain
determines the semantic template. The exact #7776 replay has the same
per-domain obligation. These explicit controls do not supply a general
recursive native-view theorem. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelCovRelEscapeAudit TypedModelCovNormEscapeAudit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit TypedModelCovZAudit
open TypedModelCovQAudit

/-- Same explicitly supplied predicate and compact. This is PER closure
of the result gate, not a native symmetry-case supplier. -/
theorem coreRAt_symm {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {p : Bool} {S : CovRRel} {x y : Expr Nat} {c : CptT}
    (h : CoreRAt E n Γ p S x y c) : CoreRAt E n Γ p S y x c :=
  ⟨h.1, h.1.symm h.2⟩

/-- Transitivity is at one fixed predicate and compact. No code order or
comparison between different interpretations is assumed. -/
theorem coreRAt_trans {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {p : Bool} {S : CovRRel} {x y z : Expr Nat} {c : CptT}
    (hxy : CoreRAt E n Γ p S x y c) (hyz : CoreRAt E n Γ p S y z c) :
    CoreRAt E n Γ p S x z c :=
  ⟨hxy.1, hxy.1.trans hxy.2 hyz.2⟩

/-- An actual interpreted result, its PER-derived joint, and the unchanged
independent native/model premises. A native view is displayed separately. -/
def CovRInterpretedFixtureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (t : CovRSyntax E) (x y A : Expr Nat) (c : CptT) : Prop :=
  CovRFixtureAt E n Γ ρ (covRTag t (fun _ => false))
    (covRInterpret E n Γ t (fun _ => false) (covRBaseVal E)) x y A c ∧
  CovRJoint E n Γ t (fun _ => false) (covRBaseVal E) x y c

/-- Packaging only: the new interpreted edge is an explicit premise, and
only the independent native/model fields are copied from the first input. -/
theorem covRInterpretedFixture_reframe {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {p : Bool} {S : CovRRel} {t : CovRSyntax E}
    {x y A : Expr Nat} {c : CptT}
    (hf : CovRFixtureAt E n Γ ρ p S x y A c)
    (h : covRInterpret E n Γ t (fun _ => false) (covRBaseVal E) x y c) :
    CovRInterpretedFixtureAt E n Γ ρ t x y A c := by
  obtain ⟨hW, hΓ, hx, hy, hc, ho, hnb, _⟩ := hf
  exact ⟨⟨hW, hΓ, hx, hy, hc, ho, hnb,
    covRInterpret_isCandidate E n Γ t _ _ (covRBaseVal_valid E n Γ), h⟩,
    covRJoint_of_related E n Γ t _ _ (covRBaseVal_valid E n Γ) h⟩

/-- A constant leaf body supplies every sort-binder action when each stored
output belongs to that leaf. Candidate predicates remain universally
quantified; the proof does not replace the binder by an ordinary arrow. -/
theorem covRForall_lam_compact {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {sortLevel : Level} {inputPositive : Bool} {G : CptT → Prop}
    {rows : List (List CptT × CptT)}
    (hB : CandidateCov E (WhStepCK2 E n) Γ false (covRCompactRel G))
    (hout : ∀ row ∈ rows, G row.2) (x y : Expr Nat) :
    covRForall E n Γ sortLevel inputPositive false
      (fun _ _ => covRCompactRel G) x y (.lam rows) := by
  refine covRForall_intro (Or.inr (Or.inl ⟨rows, rfl⟩)) ?_ ?_
  · intro he
    cases he
  · intro ds out ha T hT S hS
    cases ha with
    | bot => exact hB.bot _ _
    | app hs _ => exact hout _ hs

def covRNatSyntax : CovRSyntax natEnvU := .atom 0 covRNat_not_positive

def covRNatArrowSyntax : CovRSyntax natEnvU := .arrow covRNatSyntax covRNatSyntax

def covRPropArrowSyntax (E : ResolvedEnv) : CovRSyntax E := .allProp .prop

def covRPolyPropSyntax (E : ResolvedEnv) : CovRSyntax E :=
  .arrow (.allProp (.var 0)) .sort

def covRRelevantSyntax (E : ResolvedEnv) : CovRSyntax E :=
  .arrow (.allProp .prop) .prop

theorem covRNatSyntax_native_view (n : Nat) (Γ : LCtx) :
    CovRNativeView natEnvU n Γ (.const 0 []) covRNatSyntax (covRBaseVal natEnvU) :=
  ⟨trivial, .refl _, normalR_famAppCK2 natEnvUWfT
    (rfl : natEnvU.members 0 = some natFamMember) rfl Γ [] []⟩

theorem covRNatArrowSyntax_native_view (n : Nat) (Γ : LCtx) :
    CovRNativeView natEnvU n Γ (.pi (.const 0 []) (.const 0 []))
      covRNatArrowSyntax (covRBaseVal natEnvU) :=
  ⟨⟨trivial, trivial, trivial⟩, .refl _,
    normalR_piCK2 Γ (.const 0 []) (.const 0 [])⟩

theorem covRPropSyntax_native_view (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovRNativeView E n Γ (.sort .zero) .prop (covRBaseVal E) :=
  ⟨trivial, .refl _, normalR_sortCK2 Γ .zero⟩

theorem covRPropArrowSyntax_native_view (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovRNativeView E n Γ (.pi (.sort .zero) (.sort .zero))
      (covRPropArrowSyntax E) (covRBaseVal E) :=
  ⟨trivial, .refl _, normalR_piCK2 Γ (.sort .zero) (.sort .zero)⟩

theorem covRPolyPropSyntax_native_view (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovRNativeView E n Γ covXPolyPropLamTy (covRPolyPropSyntax E) (covRBaseVal E) :=
  ⟨⟨trivial, trivial, trivial⟩, .refl _,
    normalR_piCK2 Γ idPiProp (.sort (.succ .zero))⟩

theorem covRRelevantSyntax_native_view (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovRNativeView E n Γ
      (.pi (.pi (.sort .zero) (.sort .zero)) (.sort .zero))
      (covRRelevantSyntax E) (covRBaseVal E) :=
  ⟨⟨trivial, trivial, trivial⟩, .refl _,
    normalR_piCK2 Γ (.pi (.sort .zero) (.sort .zero)) (.sort .zero)⟩

theorem covRPropArrowSyntax_lam (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (rows : List (List CptT × CptT))
    (hout : ∀ row ∈ rows, CTyCovQ E row.2 .prop) (x y : Expr Nat) :
    covRInterpret E n Γ (covRPropArrowSyntax E) (fun _ => false)
      (covRBaseVal E) x y (.lam rows) :=
  covRForall_lam_compact (covRProp_isCandidate E _ Γ) hout x y

/-- The positive domain is itself the interpretation of `forall P, P`.
The outer empty demand row needs no guessed finite code for that domain. -/
theorem covRPolyPropSyntax_lam (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (x y : Expr Nat) :
    covRInterpret E n Γ (covRPolyPropSyntax E) (fun _ => false)
      (covRBaseVal E) x y (.lam [([], .prop)]) := by
  apply covRArrow_lam_compact (covRSort_isCandidate E _ Γ)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  exact ⟨fun u hu => (List.not_mem_nil u hu).elim,
    covRSupport_intro (covRSort_accepts_prop E x y)⟩

theorem covR_syntax_fixture_natSucc_eta (n : Nat) :
    CovRNativeView natEnvU n [] (.pi (.const 0 []) (.const 0 []))
      covRNatArrowSyntax (covRBaseVal natEnvU) ∧
    CovRInterpretedFixtureAt natEnvU n [] EnvT.bot covRNatArrowSyntax
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) covXNatEtaEmptyRow :=
  ⟨covRNatArrowSyntax_native_view n [],
    covRInterpretedFixture_reframe (covR_fixture_natSucc_eta n)
      (covRNatArrow_eta n [] _ _)⟩

/-- Per-domain alias readback only. The displayed view is for the normal
Pi built from that domain; the native fixture still has its original Pi. -/
theorem covR_syntax_fixture_alias_in_pi (n : Nat) :
    ∃ A B,
      RedR (WhStepCK2 eqEnvT n) eqGapCtx (eqGapDirectAlias A B) (.sort .zero) ∧
      CovRNativeView eqEnvT n eqGapCtx (.pi (.sort .zero) (.sort .zero))
        (covRPropArrowSyntax eqEnvT) (covRBaseVal eqEnvT) ∧
      CovRInterpretedFixtureAt eqEnvT n eqGapCtx EnvT.bot (covRPropArrowSyntax eqEnvT)
        covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
        covNormAliasIdentityCpt := by
  obtain ⟨A, B, hr, hf⟩ := covR_fixture_alias_in_pi n
  refine ⟨A, B, hr, covRPropArrowSyntax_native_view eqEnvT n eqGapCtx,
    covRInterpretedFixture_reframe hf ?_⟩
  apply covRPropArrowSyntax_lam
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  exact covRProp_pi_bot_nil eqEnvT covNormAliasIdentity covNormAliasIdentity

theorem covR_syntax_fixture_polyPropLam (n : Nat) :
    CovRNativeView eqEnvT n [] covXPolyPropLamTy
      (covRPolyPropSyntax eqEnvT) (covRBaseVal eqEnvT) ∧
    CovRInterpretedFixtureAt eqEnvT n [] EnvT.bot (covRPolyPropSyntax eqEnvT)
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy (.lam [([], .prop)]) :=
  ⟨covRPolyPropSyntax_native_view eqEnvT n [],
    covRInterpretedFixture_reframe (covR_fixture_polyPropLam n)
      (covRPolyPropSyntax_lam eqEnvT n [] _ _)⟩

theorem covR_syntax_fixture_alias_extension (n : Nat) :
    ∃ A B,
      RedR (WhStepCK2 eqEnvT n) eqGapCtx (eqGapDirectAlias A B) (.sort .zero) ∧
      CovRNativeView eqEnvT n eqGapCtx (eqGapDirectAlias A B) .prop (covRBaseVal eqEnvT) ∧
      Nonempty (CtxWfT eqEnvT n (.assumption (eqGapDirectAlias A B) :: eqGapCtx)) ∧
      CovRDemandSubstAt eqEnvT n eqGapCtx (fun _ => false)
        (fun _ => covRCodeRel eqEnvT .prop)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      CovRInterpretedFixtureAt eqEnvT n eqGapCtx EnvT.bot .prop
        idPiProp idPiProp (eqGapDirectAlias A B) (.pi .bot []) := by
  obtain ⟨A, B, hΓ, hσ, hf⟩ := covR_fixture_alias_extension n
  have hr := eqGapAlias_type_read n A B
  exact ⟨A, B, hr, ⟨trivial, hr, normalR_sortCK2 eqGapCtx .zero⟩, hΓ, hσ,
    covRInterpretedFixture_reframe hf (covRProp_pi_bot_nil eqEnvT _ _)⟩

/-- Coverage and shape share the actual Nat constructor fixture, while the
candidate predicate is definitionally the displayed ordinary operator. -/
theorem covR_syntax_fixture_nat_coverage_shape (n : Nat) :
    covRInterpret natEnvU n [] covRNatArrowSyntax (fun _ => false) (covRBaseVal natEnvU) =
      covRArrow natEnvU n [] false (.const 0 [])
        (covRCodeRel natEnvU (.spine 0 [])) (covRCodeRel natEnvU (.spine 0 [])) ∧
    CovRNativeView natEnvU n [] (.pi (.const 0 []) (.const 0 []))
      covRNatArrowSyntax (covRBaseVal natEnvU) ∧
    CovRArrowCoverage natEnvU (covRCodeRel natEnvU (.spine 0 []))
      (covRCodeRel natEnvU (.spine 0 [])) (.spine 2 []) ∧
    CovRInterpretedFixtureAt natEnvU n [] EnvT.bot covRNatArrowSyntax
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) := by
  obtain ⟨_, hc, hf⟩ := covR_fixture_nat_coverage_shape n
  exact ⟨rfl, covRNatArrowSyntax_native_view n [], hc,
    covRInterpretedFixture_reframe hf (covRNatArrow_succ n [] _ _)⟩

theorem covR_syntax_fixture_eq_anchor (n : Nat) :
    CovRNativeView eqEnvT n eqGapCtx (.sort .zero) .prop (covRBaseVal eqEnvT) ∧
    CovRInterpretedFixtureAt eqEnvT n eqGapCtx EnvT.bot .prop
      idPiProp idPiProp (.sort .zero) (.pi .bot []) :=
  ⟨covRPropSyntax_native_view eqEnvT n eqGapCtx,
    covRInterpretedFixture_reframe (covR_fixture_eq_anchor n)
      (covRProp_pi_bot_nil eqEnvT _ _)⟩

theorem covR_syntax_fixture_nat_anchor (n : Nat) :
    CovRNativeView natEnvU n [] (.const 0 []) covRNatSyntax (covRBaseVal natEnvU) ∧
    CovRInterpretedFixtureAt natEnvU n [] EnvT.bot covRNatSyntax
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) :=
  ⟨covRNatSyntax_native_view n [],
    covRInterpretedFixture_reframe (covR_fixture_nat_anchor n)
      (covRNat_spine _ _ 1 [])⟩

/-- The #7776 inner function is a sort-binder candidate. Its output proof
does not inspect or assume the universally quantified positive candidate. -/
theorem covR_syntax_relevant_argument_membership (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (x y : Expr Nat) :
    covRInterpret E n Γ (covRPropArrowSyntax E) (fun _ => false)
      (covRBaseVal E) x y (.lam [([.bot], .pi .bot [])]) := by
  apply covRPropArrowSyntax_lam
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  exact covRProp_pi_bot_nil E x y

/-- The outer ordinary row has a supplied nonempty domain demand at the
inner forall interpretation. The original native alias domain is a separate
readback premise in the external replay, not a whole-Pi native view. -/
theorem covR_syntax_relevant_app_membership (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (x y : Expr Nat) :
    covRInterpret E n Γ (covRRelevantSyntax E) (fun _ => false)
      (covRBaseVal E) x y
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) := by
  apply covRArrow_lam_compact (covRProp_isCandidate E _ Γ)
  intro row hrow
  obtain rfl := List.mem_singleton.mp hrow
  refine ⟨?_, covRSupport_intro (covRProp_pi_bot_nil E x y)⟩
  intro u hu
  obtain rfl := List.mem_singleton.mp hu
  exact covRSupport_intro (covR_syntax_relevant_argument_membership E n Γ
    (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp))

theorem covR_syntax_relevant_app_core (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (Q : Expr Nat) :
    CoreRAt E n Γ false
      (covRInterpret E n Γ (covRRelevantSyntax E) (fun _ => false) (covRBaseVal E))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) ∧
    CovRJoint E n Γ (covRRelevantSyntax E) (fun _ => false) (covRBaseVal E)
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
      (.lam [([.lam [([.bot], .pi .bot [])]], .pi .bot [])]) := by
  have h := covR_syntax_relevant_app_membership E n Γ
    (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
    (.lam (.pi (.sort .zero) (.sort .zero)) (.app (.bvar 0) (lift 0 1 Q)))
  exact ⟨⟨covRInterpret_isCandidate E n Γ (covRRelevantSyntax E)
      (fun _ => false) (covRBaseVal E) (covRBaseVal_valid E n Γ), h⟩,
    covRJoint_of_related E n Γ (covRRelevantSyntax E)
      (fun _ => false) (covRBaseVal E) (covRBaseVal_valid E n Γ) h⟩

/-- The sort-binder elimination is exercised at an actual native
proposition and an inhabited positive candidate. Its nonbottom result has
fresh native/model and interpreted joint evidence. -/
theorem covR_syntax_relevant_argument_control (n : Nat) :
    CovRNativeView eqEnvT n eqGapCtx (.pi (.sort .zero) (.sort .zero))
      (covRPropArrowSyntax eqEnvT) (covRBaseVal eqEnvT) ∧
    CovRInterpretedFixtureAt eqEnvT n eqGapCtx EnvT.bot (covRPropArrowSyntax eqEnvT)
      (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
      (.pi (.sort .zero) (.sort .zero)) (.lam [([.bot], .pi .bot [])]) ∧
    CovXCompactAction eqEnvT (.lam [([.bot], .pi .bot [])]) [.bot] (.pi .bot []) ∧
    CovRInterpretedFixtureAt eqEnvT n eqGapCtx EnvT.bot .prop
      (.app (.lam (.sort .zero) idPiProp) idPiProp)
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.sort .zero) (.pi .bot []) := by
  obtain ⟨hf, ⟨hN⟩, hApp, hConv, ha, hObs, _, hnb⟩ :=
    covR_relevant_argument_control n
  have hrel := covR_syntax_relevant_argument_membership eqEnvT n eqGapCtx
    (.lam (.sort .zero) idPiProp) (.lam (.sort .zero) idPiProp)
  have hout := covRForall_apply hrel ha idPiProp hN covRPositiveRel
    (covRPositive_isCandidate eqEnvT (WhStepCK2 eqEnvT n) eqGapCtx)
  have hnew := covRInterpretedFixture_reframe hf hrel
  obtain ⟨hW, hΓ, _, _, _, _, _, _⟩ := hf
  have happ : CovRFixtureAt eqEnvT n eqGapCtx EnvT.bot false (covRCodeRel eqEnvT .prop)
      (.app (.lam (.sort .zero) idPiProp) idPiProp)
      (.app (.lam (.sort .zero) idPiProp) idPiProp) (.sort .zero) (.pi .bot []) :=
    ⟨hW, hΓ, hApp, hApp, hConv, hObs, hnb,
      covRProp_isCandidate eqEnvT _ eqGapCtx, hout⟩
  exact ⟨covRPropArrowSyntax_native_view eqEnvT n eqGapCtx, hnew, ha,
    covRInterpretedFixture_reframe happ hout⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_FIXTURE_SYNTAX_ROOTS
#print axioms coreRAt_symm
#print axioms coreRAt_trans
#print axioms CovRInterpretedFixtureAt
#print axioms covRInterpretedFixture_reframe
#print axioms covRForall_lam_compact
#print axioms covRNatSyntax
#print axioms covRNatArrowSyntax
#print axioms covRPropArrowSyntax
#print axioms covRPolyPropSyntax
#print axioms covRRelevantSyntax
#print axioms covRNatSyntax_native_view
#print axioms covRNatArrowSyntax_native_view
#print axioms covRPropSyntax_native_view
#print axioms covRPropArrowSyntax_native_view
#print axioms covRPolyPropSyntax_native_view
#print axioms covRRelevantSyntax_native_view
#print axioms covRPropArrowSyntax_lam
#print axioms covRPolyPropSyntax_lam
#print axioms covR_syntax_fixture_natSucc_eta
#print axioms covR_syntax_fixture_alias_in_pi
#print axioms covR_syntax_fixture_polyPropLam
#print axioms covR_syntax_fixture_alias_extension
#print axioms covR_syntax_fixture_nat_coverage_shape
#print axioms covR_syntax_fixture_eq_anchor
#print axioms covR_syntax_fixture_nat_anchor
#print axioms covR_syntax_relevant_argument_membership
#print axioms covR_syntax_relevant_app_membership
#print axioms covR_syntax_relevant_app_core
#print axioms covR_syntax_relevant_argument_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_FIXTURE_SYNTAX_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
