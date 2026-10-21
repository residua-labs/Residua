import rcic.RcicNativeTypedModelCovWMatrixKHead

/-!
# Proof-major irrelevance across the two guarded recursor rules

The actual eta-index Eq context contains a neutral equality proof. Native
eta converts the literal reflexivity constructor into that same proposition,
so native irrelevance relates the two majors. Replacing only this major in
the same recursor prefix gives natively convertible terms of Sort 1.

The constructor call has a direct structured-iota observation at `prop`.
The neutral call has only bottom observations, by the complete landed
eta-index exclusion. The positive derivation uses no `appSpine`: it uses
the unchanged old source filter, structured iota, and the RHS sort rule.
Thus changing only the rigid field rule cannot repair this comparison while
retaining those rules. The actual context, closing realizer and strict output
typing are supplied. No claim is made about the closed substituted comparison.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open PiProbeModelBoundaryAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelKTransportAudit TypedModelCovVAudit TypedModelCovWAudit
open TypedModelCovWIrrelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open ReadbackCK2InputsAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWMatrixMajorCtorCall : Expr Nat :=
  recCall (.const 65 [.succ (.succ .zero)])
    [indexFn, .bvar 1, etaIndexMot, .sort .zero, etaIndex] etaIndexCtor

/-- All stored schema obligations are checked on the actual admitted Eq
members. The pre-major index is etaIndex; the constructor repeats bvar 1. -/
def covWMatrixMajorWitness : IotaWitnessS eqEnvT where
  recRef := 65
  ctorRef := 64
  ls := [.succ (.succ .zero)]
  lsC := []
  recMember := eqRecT
  ctorMember := eqReflT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [indexFn, .bvar 1, etaIndexMot, .sort .zero, etaIndex]
  fields := []
  ctorParams := [indexFn, .bvar 1]
  familyRef := 63
  famMember := eqFamT
  hfam := rfl
  hfamK := rfl
  nparams := 2
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  ctorDoms := [.sort (.succ .zero), .bvar 0]
  ctorResult := foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 0]
  hpeel := rfl
  hfamApp := rfl
  recDoms := [.sort (.succ .zero), .bvar 0, eqMotT, eqMinorT, .bvar 3,
    foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 0
  shapes := []
  hshapes := rfl
  schema := .bvar 1
  hschema := rfl
  hstable := fun _ _ => ⟨rfl, rfl⟩
  hschemaScope := rfl

theorem covWMatrix_major_witness_lhs :
    iotaLhsOfS covWMatrixMajorWitness = covWMatrixMajorCtorCall := rfl

theorem covWMatrix_major_witness_rhs :
    iotaRhsOfS covWMatrixMajorWitness = .sort .zero := rfl

/-- The two literal indices really differ; their agreement is native eta. -/
theorem covWMatrix_major_indices_distinct : (.bvar 1 : Expr Nat) ≠ etaIndex := by
  intro h
  cases h

def covWMatrixMajorFamilyConv (n : Nat) :
    ConvT eqEnvT n etaEqCtx (etaIndexFamily (.bvar 1))
      (etaIndexFamily etaIndex) (.sort .zero) :=
  .app _ _ _ _ _ _ _
    (.app _ _ _ _ _ _ _
      (.app _ _ _ _ _ _ _ (.refl _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl))
        (.refl _ _ _ (indexFnTy eqEnvT n etaEqCtx)))
      (.refl _ _ _ (etaIndexParamTy n)))
    (.symm _ _ _ _ (etaIndexConv n))

/-- The constructor is typed at the same proposition as the neutral major. -/
def covWMatrixMajorCtor_ty (n : Nat) :
    HasTyT eqEnvT n etaEqCtx etaIndexCtor (etaIndexFamily etaIndex) :=
  .conv _ _ _ _ _ (etaIndexCtorTy n) (covWMatrixMajorFamilyConv n)

def covWMatrixMajorNeutral_ty (n : Nat) :
    HasTyT eqEnvT n etaEqCtx (.bvar 0) (etaIndexFamily etaIndex) :=
  .bvar _ 0 _ rfl

/-- The comparison is an actual native irrelevance constructor. -/
def covWMatrixMajorIrr (n : Nat) :
    ConvT eqEnvT n etaEqCtx (.bvar 0) etaIndexCtor (etaIndexFamily etaIndex) :=
  .irr _ _ _ _ (etaIndexFamilyTy n (etaIndexTy n))
    (covWMatrixMajorNeutral_ty n) (covWMatrixMajorCtor_ty n)

def covWMatrixMajorCtorCall_ty (n : Nat) :
    HasTyT eqEnvT n etaEqCtx covWMatrixMajorCtorCall (.sort (.succ .zero)) :=
  etaIndexRecTy n (covWMatrixMajorCtor_ty n)

def covWMatrixMajorNeutralCall_ty (n : Nat) :
    HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero)) :=
  etaIndexRecTy n (covWMatrixMajorNeutral_ty n)

/-- Application congruence transports the proof-major irrelevance through
the unchanged native prefix; the constant motive supplies the result cast. -/
def covWMatrixMajorCongr (n : Nat) :
    ConvT eqEnvT n etaEqCtx etaIndexRedex covWMatrixMajorCtorCall
      (.sort (.succ .zero)) := by
  have hminor : HasTyT eqEnvT n etaEqCtx (.sort .zero)
      (.app (.app etaIndexMot (.bvar 1)) etaIndexCtor) :=
    .conv _ _ _ _ _ (.sort _ _)
      (.symm _ _ _ _ (etaIndexMotAtConv n (etaIndexParamTy n) (etaIndexCtorTy n)))
  have hpre : HasTyT eqEnvT n etaEqCtx
      (foldApps (.const 65 [.succ (.succ .zero)])
        [indexFn, .bvar 1, etaIndexMot, .sort .zero, etaIndex]) _ :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _
            (.app _ _ _ _ _ (.const _ 65 [.succ (.succ .zero)] eqRecT rfl rfl rfl)
              (indexFnTy eqEnvT n etaEqCtx)) (etaIndexParamTy n))
          (etaIndexMotTy n)) hminor) (etaIndexTy n)
  have hc : ConvT eqEnvT n etaEqCtx etaIndexRedex covWMatrixMajorCtorCall
      (.app (.app etaIndexMot etaIndex) (.bvar 0)) :=
    .app _ _ _ _ _ _ _ (.refl _ _ _ hpre) (covWMatrixMajorIrr n)
  exact .tyConv _ _ _ _ _ _ hc
    (etaIndexMotAtConv n (etaIndexTy n) (covWMatrixMajorNeutral_ty n))

theorem covWMatrix_major_ctor_is_constructor : IsCtorSpine eqEnvT etaIndexCtor :=
  ⟨64, [], [indexFn, .bvar 1], eqReflT, rfl, rfl, rfl⟩

theorem covWMatrix_major_ctor_iota_step (n : Nat) :
    WhStepCK2 eqEnvT n etaEqCtx covWMatrixMajorCtorCall (.sort .zero) :=
  .ctx (.iota (.ofUS covWMatrixMajorWitness))

/-- Eq's existing native eligibility supplies the actual old source filter. -/
theorem covWMatrix_major_source_filter (ρ : EnvT) :
    ApproxTN eqEnvT ρ covWMatrixMajorCtorCall .prop :=
  covV_approxT_of_native_heads covV_eq_native_heads
    (eqRec_model_minor_backward (approxT_sort_code eqEnvT ρ .zero))

/-- This positive derivation has no rigid-spine argument field. -/
theorem covWMatrix_major_ctor_observed (n : Nat) (ρ : EnvWIrrel) :
    ApproxTKWIrrel eqEnvT n etaEqCtx ρ covWMatrixMajorCtorCall .prop :=
  .iota covWMatrixMajorWitness (covWMatrix_major_source_filter (covWIrrelEnvErase ρ))
    (covWIrrel_sort_observed eqEnvT n etaEqCtx ρ .zero)

/-- Both proof majors, their native congruence, admission, context, closing
realizer and strictly typed differing observations coexist at the same cell. -/
theorem covWMatrix_major_irrel_inhabited (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx (etaIndexFamily etaIndex) (.sort .zero)) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx (.bvar 0) (etaIndexFamily etaIndex)) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexCtor (etaIndexFamily etaIndex)) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx (.bvar 0) etaIndexCtor (etaIndexFamily etaIndex)) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero))) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx covWMatrixMajorCtorCall (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex covWMatrixMajorCtorCall
      (.sort (.succ .zero))) ∧
    CovWIrrelRealized eqEnvT n 1 etaEqCtx EnvWIrrel.bot covWMatrixKSubst ∧
    CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot (.sort (.succ .zero)) .sort ∧
    CTyS eqEnvT .prop .sort ∧
    CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot covWMatrixMajorCtorCall .prop ∧
    (¬ CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot etaIndexRedex .prop) :=
  ⟨⟨pinEqGroupWfT⟩, ⟨etaEqCtxWf n⟩, ⟨etaIndexFamilyTy n (etaIndexTy n)⟩,
    ⟨covWMatrixMajorNeutral_ty n⟩, ⟨covWMatrixMajorCtor_ty n⟩,
    ⟨covWMatrixMajorIrr n⟩, ⟨covWMatrixMajorNeutralCall_ty n⟩,
    ⟨covWMatrixMajorCtorCall_ty n⟩, ⟨covWMatrixMajorCongr n⟩,
    covWMatrix_K_realized n 1, covWMatrix_K_type_observed n,
    covWMatrix_K_compact_typed,
    covWIrrel_observation_of (covWMatrix_major_ctor_observed n EnvWIrrel.bot),
    covWMatrix_K_source_excluded n EnvWIrrel.bot⟩

theorem covWMatrix_major_irrel_no_typed_equality (n : Nat) :
    ¬ (∀ c : CptT, CTyS eqEnvT c .sort →
      (CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot etaIndexRedex c ↔
       CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot covWMatrixMajorCtorCall c)) := by
  intro heq
  exact covWMatrix_K_source_excluded n EnvWIrrel.bot
    ((heq .prop covWMatrix_K_compact_typed).mpr
      (covWIrrel_observation_of (covWMatrix_major_ctor_observed n EnvWIrrel.bot)))

/-- A refinement that retains the ordinary iota rule and its RHS sort
observation still fails this proof-major comparison. The source filter is
the actual fixed filter already supplied above, not a hypothetical premise. -/
theorem covWMatrix_major_field_restriction_wall (n : Nat)
    (Obs : Expr Nat → CptT → Prop)
    (hforget : ∀ e c, Obs e c →
      CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot e c)
    (hiota : ∀ (w : IotaWitnessS eqEnvT) (c : CptT),
      ApproxTN eqEnvT (covWIrrelEnvErase EnvWIrrel.bot) (iotaLhsOfS w) c →
      Obs (iotaRhsOfS w) c → Obs (iotaLhsOfS w) c)
    (hsort : Obs (.sort .zero) .prop) :
    ¬ (∀ c : CptT, CTyS eqEnvT c .sort →
      (Obs etaIndexRedex c ↔ Obs covWMatrixMajorCtorCall c)) := by
  intro heq
  have hctor := hiota covWMatrixMajorWitness .prop (covWMatrix_major_source_filter _) hsort
  exact covWMatrix_K_source_excluded n EnvWIrrel.bot
    (hforget _ _ ((heq .prop covWMatrix_K_compact_typed).mpr hctor))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_MAJOR_IRREL_ROOTS
#print axioms covWMatrixMajorCtorCall
#print axioms covWMatrixMajorWitness
#print axioms covWMatrix_major_witness_lhs
#print axioms covWMatrix_major_witness_rhs
#print axioms covWMatrix_major_indices_distinct
#print axioms covWMatrixMajorFamilyConv
#print axioms covWMatrixMajorCtor_ty
#print axioms covWMatrixMajorNeutral_ty
#print axioms covWMatrixMajorIrr
#print axioms covWMatrixMajorCtorCall_ty
#print axioms covWMatrixMajorNeutralCall_ty
#print axioms covWMatrixMajorCongr
#print axioms covWMatrix_major_ctor_is_constructor
#print axioms covWMatrix_major_ctor_iota_step
#print axioms covWMatrix_major_source_filter
#print axioms covWMatrix_major_ctor_observed
#print axioms covWMatrix_major_irrel_inhabited
#print axioms covWMatrix_major_irrel_no_typed_equality
#print axioms covWMatrix_major_field_restriction_wall
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_MAJOR_IRREL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit
