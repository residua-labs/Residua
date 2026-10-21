import rcic.RcicNativeTypedModelCovRLambdaBoundary
import rcic.RcicNativeTypedModelCovROpaqueArrow
import rcic.RcicNativeTypedModelCovRSyntax

/-!
# Opaque-variable substitution and concrete sort binders

The native identity at Prop -> Prop has the same endpoints, native domain,
domain candidate, codomain candidate, and compact in both tests below.
The opaque arrow admits `polyIdOut0`; the strict arrow rejects its unsupported
stored `.prop` demand. Thus these predicates are unequal, including pointwise
at this natively typed identity. The final lexical comparison also appears
below: the concrete Prop-domain template is `.allProp .prop`, whose forall
clause rejects this compact. Both final templates reify to Prop -> Prop.

The compact is actually observed at the original polymorphic identity.
After the native Prop argument is substituted, the resulting identity does
not observe `polyIdOut0` in ApproxTK. The control supplies the original
observation and its actual native beta readback; it does not claim an
observed intermediate compact or refute an observation-restricted bridge.
This is the precise unconditional type-substitution coherence boundary.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit ReadbackCK2Audit TypedModelCovXAudit TypedModelCovPAudit
open PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit

theorem covRSubstitution_opaque_identity (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    covROpaqueArrow E n Γ false (.sort .zero)
      (covRCodeRel E .prop) (covRCodeRel E .prop)
      covPPropArrowId covPPropArrowId polyIdOut0 :=
  covROpaqueArrow_polyIdOut0 (covRProp_isCandidate E (WhStepCK2 E n) Γ)
    (.sort .zero)

theorem covRSubstitution_strict_rejects_identity
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ¬ covRArrow E n Γ false (.sort .zero)
      (covRCodeRel E .prop) (covRCodeRel E .prop)
      covPPropArrowId covPPropArrowId polyIdOut0 :=
  covRStrictIdentityBody_rejects_polyIdOut0 E n Γ (.sort .zero)
    covPPropArrowId covPPropArrowId

/-- Pointwise semantic equality already fails at one natively typed
identity and one explicit compact. No function extensionality is needed. -/
theorem covRSubstitution_identity_not_iff (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ¬ (covROpaqueArrow E n Γ false (.sort .zero)
        (covRCodeRel E .prop) (covRCodeRel E .prop)
        covPPropArrowId covPPropArrowId polyIdOut0 ↔
      covRArrow E n Γ false (.sort .zero)
        (covRCodeRel E .prop) (covRCodeRel E .prop)
        covPPropArrowId covPPropArrowId polyIdOut0) := by
  intro he
  exact covRSubstitution_strict_rejects_identity E n Γ
    (he.mp (covRSubstitution_opaque_identity E n Γ))

theorem covRSubstitution_arrow_predicates_ne (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    covROpaqueArrow E n Γ false (.sort .zero)
      (covRCodeRel E .prop) (covRCodeRel E .prop) ≠
    covRArrow E n Γ false (.sort .zero)
      (covRCodeRel E .prop) (covRCodeRel E .prop) := by
  intro he
  have hp := covRSubstitution_opaque_identity E n Γ
  rw [he] at hp
  exact covRSubstitution_strict_rejects_identity E n Γ hp

/-- This is an actual compact action. Its `.prop` demand is not supported
by the Prop candidate, as the imported support refutation states. -/
theorem covRSubstitution_identity_action (E : ResolvedEnv) :
    CovXCompactAction E polyIdOut0 [.prop] .prop := by
  apply AppCptT.app (List.mem_singleton_self _)
  intro u hu
  exact .bvar hu

/-- The application is natively typed at the same concrete arrow as the
contracted lambda. The original lambda derivation is imported unchanged. -/
def covRSubstitution_native_application_hasTy (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] (.app cexPolyId (.sort .zero)) covPPropArrow :=
  .app [] cexPolyId (.sort .zero) (.sort (.succ .zero))
    (.pi (.bvar 0) (.bvar 1)) (hasTyT_cexPolyId E n) (.sort [] .zero)

theorem covRSubstitution_native_beta_readback (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) :
    RedR (WhStepCK2 E n) Γ (.app cexPolyId (.sort .zero)) covPPropArrowId :=
  covROpaqueArrow_cexPolyId_readback (.sort .zero)

/-- The positive predicate witness is not an observation of the
instantiated lambda. The native Prop annotation permits only bottom or
the `.prop` type code, neither of which types the stored `.prop` demand. -/
theorem covRSubstitution_identity_not_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTK E n Γ ρ covPPropArrowId polyIdOut0 := by
  intro ho
  rcases approxT_lam_inv (approxTK_forget ho) with hb |
    ⟨a, rows, he, hA, _, hrows⟩
  · exact CptT.noConfusion hb
  · have hrowsEq : [([CptT.prop], CptT.prop)] = rows := CptT.lam.inj he
    subst rows
    have ht : CTyS E .prop a :=
      (hrows ([.prop], .prop) (List.mem_singleton_self _)).1
        .prop (List.mem_singleton_self _)
    rcases approxT_sort_inv hA with rfl | rfl
    · exact CptT.noConfusion (ctyS_bot_inv ht)
    · rw [sortCode_zero] at ht
      rcases ctyS_prop_inv ht with hb | hp
      · exact CptT.noConfusion hb
      · cases hp

/-- The exact native/candidate premises and actual actions are inhabited.
The positive and negative semantic witnesses use literally the same native
identity. The separate observation fact is at its polymorphic origin. -/
theorem covRSubstitution_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT emptyEnv n [] covPPropArrow (.sort (.succ .zero))) ∧
    Nonempty (HasTyT emptyEnv n [] covPPropArrowId covPPropArrow) ∧
    Nonempty (ConvT emptyEnv n [] covPPropArrowId covPPropArrowId covPPropArrow) ∧
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    ApproxTK emptyEnv n [] ρ cexPolyId polyIdCpt0 ∧
    Nonempty (HasTyT emptyEnv n [] (.app cexPolyId (.sort .zero)) covPPropArrow) ∧
    RedR (WhStepCK2 emptyEnv n) []
      (.app cexPolyId (.sort .zero)) covPPropArrowId ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] false
      (covRCodeRel emptyEnv .prop) ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] false
      (covROpaqueArrow emptyEnv n [] false (.sort .zero)
        (covRCodeRel emptyEnv .prop) (covRCodeRel emptyEnv .prop)) ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] false
      (covRArrow emptyEnv n [] false (.sort .zero)
        (covRCodeRel emptyEnv .prop) (covRCodeRel emptyEnv .prop)) ∧
    CovXCompactAction emptyEnv polyIdCpt0 [.sort] polyIdOut0 ∧
    CovXCompactAction emptyEnv polyIdOut0 [.prop] .prop ∧
    polyIdCpt0 ≠ .bot ∧ polyIdOut0 ≠ .bot ∧
    covROpaqueArrow emptyEnv n [] false (.sort .zero)
      (covRCodeRel emptyEnv .prop) (covRCodeRel emptyEnv .prop)
      covPPropArrowId covPPropArrowId polyIdOut0 ∧
    ¬ covRArrow emptyEnv n [] false (.sort .zero)
      (covRCodeRel emptyEnv .prop) (covRCodeRel emptyEnv .prop)
      covPPropArrowId covPPropArrowId polyIdOut0 ∧
    ¬ ApproxTK emptyEnv n [] ρ covPPropArrowId polyIdOut0 := by
  have hS := covRProp_isCandidate emptyEnv (WhStepCK2 emptyEnv n) []
  exact ⟨⟨.empty⟩, ⟨.nil⟩, ⟨.sort [] .zero⟩,
    ⟨covPPropArrow_hasTy emptyEnv n []⟩, ⟨covPPropArrowId_hasTy emptyEnv n []⟩,
    ⟨.refl _ _ _ (covPPropArrowId_hasTy emptyEnv n [])⟩,
    ⟨hasTyT_cexPolyId emptyEnv n⟩, covRLambdaIdentity_observed emptyEnv n [] ρ,
    ⟨covRSubstitution_native_application_hasTy emptyEnv n⟩,
    covRSubstitution_native_beta_readback emptyEnv n [], hS,
    covROpaqueArrow_isCandidate hS hS, covRArrow_isCandidate hS hS,
    covRPolyIdCpt0_action emptyEnv, covRSubstitution_identity_action emptyEnv,
    CptT.noConfusion, CptT.noConfusion,
    covRSubstitution_opaque_identity emptyEnv n [],
    covRSubstitution_strict_rejects_identity emptyEnv n [],
    covRSubstitution_identity_not_observed emptyEnv n [] ρ⟩

/-- The final concrete sort-binder clause tests every compact action at
an actual proposition and an actual positive candidate. Here the resulting
`.prop` output would have to belong to the exact Prop universe candidate. -/
theorem covRSubstitution_forall_rejects_identity
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (x y : Expr Nat) :
    ¬ covRForall E n Γ .zero true false (fun _ _ => covRCodeRel E .prop)
      x y polyIdOut0 := by
  intro h
  have hout : covRCodeRel E .prop (.app x idPiProp) (.app y idPiProp) .prop :=
    covRForall_apply h (covRSubstitution_identity_action E) idPiProp
      (hasTyT_idPiProp_ctx E n Γ) covRPositiveRel
      (covRPositive_isCandidate E (WhStepCK2 E n) Γ)
  exact covRProp_support_not_prop E (covRSupport_intro hout)

/-- The valuation instance of A -> A and the concrete sort-binder
template have definitionally identical native reifications. -/
theorem covRSubstitution_lexical_native (E : ResolvedEnv) :
    covRNative (E := E) (.arrow (.var 0) (.var 0)) (covRBaseVal E).native =
        covPPropArrow ∧
      covRNative (E := E) (.allProp .prop) (covRBaseVal E).native =
        covPPropArrow :=
  ⟨rfl, rfl⟩

theorem covRSubstitution_lexical_views (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovRNativeView E n Γ covPPropArrow (.arrow (.var 0) (.var 0))
        (covRBaseVal E) ∧
      CovRNativeView E n Γ covPPropArrow (.allProp .prop) (covRBaseVal E) :=
  ⟨⟨⟨True.intro, True.intro, True.intro⟩, .refl _,
      normalR_piCK2 Γ (.sort .zero) (.sort .zero)⟩,
    ⟨True.intro, .refl _, normalR_piCK2 Γ (.sort .zero) (.sort .zero)⟩⟩

theorem covRSubstitution_lexical_identity (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    covRInterpret E n Γ (.arrow (.var 0) (.var 0))
      (fun _ => false) (covRBaseVal E)
      covPPropArrowId covPPropArrowId polyIdOut0 :=
  covRSubstitution_opaque_identity E n Γ

theorem covRSubstitution_lexical_rejects_identity
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ¬ covRInterpret E n Γ (.allProp .prop) (fun _ => false) (covRBaseVal E)
      covPPropArrowId covPPropArrowId polyIdOut0 :=
  covRSubstitution_forall_rejects_identity E n Γ covPPropArrowId covPPropArrowId

/-- This is the final interpreter's pointwise mismatch, not merely an
inequality between two lower-level arrow operators. Both native views are
supplied above, and the same native identity appears at both endpoints. -/
theorem covRSubstitution_lexical_not_iff (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ¬ (covRInterpret E n Γ (.arrow (.var 0) (.var 0))
        (fun _ => false) (covRBaseVal E)
        covPPropArrowId covPPropArrowId polyIdOut0 ↔
      covRInterpret E n Γ (.allProp .prop) (fun _ => false) (covRBaseVal E)
        covPPropArrowId covPPropArrowId polyIdOut0) := by
  intro he
  exact covRSubstitution_lexical_rejects_identity E n Γ
    (he.mp (covRSubstitution_lexical_identity E n Γ))

theorem covRSubstitution_lexical_predicates_ne
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    covRInterpret E n Γ (.arrow (.var 0) (.var 0))
        (fun _ => false) (covRBaseVal E) ≠
      covRInterpret E n Γ (.allProp .prop) (fun _ => false) (covRBaseVal E) := by
  intro he
  have hp := covRSubstitution_lexical_identity E n Γ
  rw [he] at hp
  exact covRSubstitution_lexical_rejects_identity E n Γ hp

/-- Actual final-template counterexample with inhabited native views,
valuation, candidates and the proposition argument used in the refutation.
The observation remains at the original polymorphic source; the compact is
proved absent from the instantiated identity's observations. -/
theorem covRSubstitution_lexical_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n []) ∧
    Nonempty (HasTyT emptyEnv n [] covPPropArrow (.sort (.succ .zero))) ∧
    Nonempty (HasTyT emptyEnv n [] covPPropArrowId covPPropArrow) ∧
    Nonempty (ConvT emptyEnv n [] covPPropArrowId covPPropArrowId covPPropArrow) ∧
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    ApproxTK emptyEnv n [] ρ cexPolyId polyIdCpt0 ∧
    Nonempty (HasTyT emptyEnv n [] (.app cexPolyId (.sort .zero)) covPPropArrow) ∧
    RedR (WhStepCK2 emptyEnv n) []
      (.app cexPolyId (.sort .zero)) covPPropArrowId ∧
    CovRNativeView emptyEnv n [] covPPropArrow (.arrow (.var 0) (.var 0))
      (covRBaseVal emptyEnv) ∧
    CovRNativeView emptyEnv n [] covPPropArrow (.allProp .prop) (covRBaseVal emptyEnv) ∧
    CovRValValid emptyEnv n [] (fun _ => false) (covRBaseVal emptyEnv) ∧
    Nonempty (HasTyT emptyEnv n [] idPiProp (.sort .zero)) ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] true covRPositiveRel ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] false
      (covRInterpret emptyEnv n [] (.arrow (.var 0) (.var 0))
        (fun _ => false) (covRBaseVal emptyEnv)) ∧
    CandidateCov emptyEnv (WhStepCK2 emptyEnv n) [] false
      (covRInterpret emptyEnv n [] (.allProp .prop)
        (fun _ => false) (covRBaseVal emptyEnv)) ∧
    CovXCompactAction emptyEnv polyIdCpt0 [.sort] polyIdOut0 ∧
    CovXCompactAction emptyEnv polyIdOut0 [.prop] .prop ∧
    polyIdCpt0 ≠ .bot ∧ polyIdOut0 ≠ .bot ∧
    covRInterpret emptyEnv n [] (.arrow (.var 0) (.var 0))
      (fun _ => false) (covRBaseVal emptyEnv)
      covPPropArrowId covPPropArrowId polyIdOut0 ∧
    ¬ covRInterpret emptyEnv n [] (.allProp .prop)
      (fun _ => false) (covRBaseVal emptyEnv)
      covPPropArrowId covPPropArrowId polyIdOut0 ∧
    ¬ ApproxTK emptyEnv n [] ρ covPPropArrowId polyIdOut0 := by
  obtain ⟨hE, hΓ, _, hA, ht, hc, hpoly, ho, happ, hread, _, _, _,
      houter, hinner, hnb, hnb', _, _, hno⟩ := covRSubstitution_control n ρ
  obtain ⟨hv₁, hv₂⟩ := covRSubstitution_lexical_views emptyEnv n []
  have hval := covRBaseVal_valid emptyEnv n []
  exact ⟨hE, hΓ, hA, ht, hc, hpoly, ho, happ, hread, hv₁, hv₂, hval,
    ⟨hasTyT_idPiProp_ctx emptyEnv n []⟩,
    covRPositive_isCandidate emptyEnv (WhStepCK2 emptyEnv n) [],
    covRInterpret_isCandidate emptyEnv n [] (.arrow (.var 0) (.var 0))
      (fun _ => false) (covRBaseVal emptyEnv) hval,
    covRInterpret_isCandidate emptyEnv n [] (.allProp .prop)
      (fun _ => false) (covRBaseVal emptyEnv) hval,
    houter, hinner, hnb, hnb', covRSubstitution_lexical_identity emptyEnv n [],
    covRSubstitution_lexical_rejects_identity emptyEnv n [], hno⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_SUBSTITUTION_BOUNDARY_ROOTS
#print axioms covRSubstitution_opaque_identity
#print axioms covRSubstitution_strict_rejects_identity
#print axioms covRSubstitution_identity_not_iff
#print axioms covRSubstitution_arrow_predicates_ne
#print axioms covRSubstitution_identity_action
#print axioms covRSubstitution_native_application_hasTy
#print axioms covRSubstitution_native_beta_readback
#print axioms covRSubstitution_identity_not_observed
#print axioms covRSubstitution_control
#print axioms covRSubstitution_forall_rejects_identity
#print axioms covRSubstitution_lexical_native
#print axioms covRSubstitution_lexical_views
#print axioms covRSubstitution_lexical_identity
#print axioms covRSubstitution_lexical_rejects_identity
#print axioms covRSubstitution_lexical_not_iff
#print axioms covRSubstitution_lexical_predicates_ne
#print axioms covRSubstitution_lexical_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_SUBSTITUTION_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
