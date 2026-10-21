import rcic.RcicNativeTypedModelCovWMatrixKHead

/-!
# Ordinary constructor iota fails at a strictly typed head observation

The admitted higher-order proposition recursor is instantiated at an actual
closed constructor major. Its structured witness supplies an ordinary iota
step. The constant minor makes the RHS observable at `prop` by two empty
demands, while the old `ApproxTN` source filter rejects every nonbottom
observation of this recursor, even at constructor majors. The complete
current grammar inherits that exclusion, including all typed eta branches.

This is independent of native K: the step uses `WhStepCK2.ctx` and ordinary
`DerivedIotaU.ofUS`. Native typing, the closed identity realizer, and strict
compact typing are supplied. The higher-order recursor has no legacy iota
witness, so this is a CK2 step failure; no `ConvT.iota` certificate is claimed.
No normalization claim is made for the unused field. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelKTransportAudit TypedModelCovTAudit TypedModelCovVAudit
open TypedModelCovWAudit TypedModelCovWIrrelAudit
open TypedModelAudit.TypingFin TypedModelCovWEtaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWMatrixIotaField : Expr Nat := .lam (.sort .zero) covUHoMajor

def covWMatrixIotaMajor : Expr Nat := .app (.const 64 []) covWMatrixIotaField

def covWMatrixIotaWitness : IotaWitnessS covUHoEnv :=
  covW_iota_action_instance covUHoWitness [.succ (.succ .zero)] []
    [covUHoMotive, covUHoMinor] [] [covWMatrixIotaField] rfl rfl rfl rfl

def covWMatrixIotaSource : Expr Nat := iotaLhsOfS covWMatrixIotaWitness

def covWMatrixIotaTarget : Expr Nat := iotaRhsOfS covWMatrixIotaWitness

private def ho_motive_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covUHoMotive
      (.pi (.const 63 []) (.sort (.succ (.succ .zero)))) :=
  .lam _ _ _ _ _ (.const _ 63 [] covUHoFam rfl rfl rfl) (.sort _ _)

private def ho_field_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covUHoField (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ _ _ _ _ (.sort _ _) (.const _ 63 [] covUHoFam rfl rfl rfl)

private def ho_ih_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n (.assumption covUHoField :: Γ) covUHoIhTy
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) := by
  have hf : HasTyT covUHoEnv n
      (.assumption (.sort .zero) :: .assumption covUHoField :: Γ)
      (.bvar 1) covUHoField := .bvar _ 1 _ rfl
  have hp : HasTyT covUHoEnv n
      (.assumption (.sort .zero) :: .assumption covUHoField :: Γ)
      (.bvar 0) (.sort .zero) := .bvar _ 0 _ rfl
  exact .pi _ _ _ _ _ (.sort _ _)
    (.app _ _ _ _ _ (ho_motive_ty n _) (.app _ _ _ _ _ hf hp))

private def ho_minor_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covUHoMinor (instantiate0 covUHoMotive covUHoMinTy) := by
  let Δ := .assumption covUHoIhTy :: .assumption covUHoField :: Γ
  have hf : HasTyT covUHoEnv n Δ (.bvar 1) covUHoField := .bvar _ 1 _ rfl
  have hc : HasTyT covUHoEnv n Δ (.app (.const 64 []) (.bvar 1)) (.const 63 []) :=
    .app _ _ _ _ _ (.const _ 64 [] covUHoCtor rfl rfl rfl) hf
  have hb : ConvT covUHoEnv n Δ
      (.app covUHoMotive (.app (.const 64 []) (.bvar 1))) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
    .beta _ _ _ _ _ _ (.const _ 63 [] covUHoFam rfl rfl rfl) (.sort _ _) hc
  exact .lam _ _ _ _ _ (ho_field_ty n Γ)
    (.lam _ _ _ _ _ (ho_ih_ty n Γ)
      (.conv _ _ _ _ _ (.sort _ .zero) (.symm _ _ _ _ hb)))

private def ho_partial_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ
      (foldApps (.const 65 [.succ (.succ .zero)]) [covUHoMotive, covUHoMinor])
      (.pi (.const 63 []) (.app covUHoMotive (.bvar 0))) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (.const _ 65 [.succ (.succ .zero)] covUHoRec rfl rfl rfl)
      (ho_motive_ty n Γ)) (ho_minor_ty n Γ)

private def ho_call_ty (n : Nat) (Γ : LCtx) {a : Expr Nat}
    (ha : HasTyT covUHoEnv n Γ a (.const 63 [])) :
    HasTyT covUHoEnv n Γ
      (recCall (.const 65 [.succ (.succ .zero)]) [covUHoMotive, covUHoMinor] a)
      (.app covUHoMotive a) :=
  .app _ _ _ _ _ (ho_partial_ty n Γ) ha

private def ho_motive_app_conv (n : Nat) (Γ : LCtx) {a : Expr Nat}
    (ha : HasTyT covUHoEnv n Γ a (.const 63 [])) :
    ConvT covUHoEnv n Γ (.app covUHoMotive a) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
  .beta Γ (.const 63 []) (.sort (.succ .zero)) a
    (.sort (.succ (.succ .zero))) .zero
    (.const Γ 63 [] covUHoFam rfl rfl rfl) (.sort _ _) ha

def covWMatrixIotaField_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWMatrixIotaField covUHoField :=
  .lam _ _ _ _ _ (.sort _ .zero) (covUHoMajor_hasTy n _)

def covWMatrixIotaMajor_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWMatrixIotaMajor (.const 63 []) :=
  .app _ _ _ _ _ (.const _ 64 [] covUHoCtor rfl rfl rfl)
    (covWMatrixIotaField_ty n Γ)

def covWMatrixIotaSource_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWMatrixIotaSource (.sort (.succ .zero)) :=
  .conv _ _ _ _ _ (ho_call_ty n Γ (covWMatrixIotaMajor_ty n Γ))
    (ho_motive_app_conv n Γ (covWMatrixIotaMajor_ty n Γ))

private def ho_actual_ih_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ
      (.lam (.sort .zero)
        (recCall (.const 65 [.succ (.succ .zero)]) [covUHoMotive, covUHoMinor]
          (.app covWMatrixIotaField (.bvar 0))))
      (.pi (.sort .zero) (.app covUHoMotive (.app covWMatrixIotaField (.bvar 0)))) :=
  .lam _ _ _ _ _ (.sort _ .zero)
    (ho_call_ty n _ (.app _ _ _ _ _ (covWMatrixIotaField_ty n _)
      (.bvar _ 0 _ rfl)))

def covWMatrixIotaTarget_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWMatrixIotaTarget (.sort (.succ .zero)) := by
  have hfirst := HasTyT.app Γ _ _ _ _ (ho_minor_ty n Γ) (covWMatrixIotaField_ty n Γ)
  have hraw := HasTyT.app Γ _ _ _ _ hfirst (ho_actual_ih_ty n Γ)
  exact .conv _ _ _ _ _ hraw (ho_motive_app_conv n Γ (covWMatrixIotaMajor_ty n Γ))

/-- The major is an actual constructor spine, not a neutral K major. -/
theorem covWMatrix_iota_constructor_major : IsCtorSpine covUHoEnv covWMatrixIotaMajor := by
  exact ⟨64, [], [covWMatrixIotaField], covUHoCtor, rfl, rfl, rfl⟩

theorem covWMatrix_iota_step (n : Nat) (Γ : LCtx) :
    WhStepCK2 covUHoEnv n Γ covWMatrixIotaSource covWMatrixIotaTarget :=
  .ctx (.iota (.ofUS covWMatrixIotaWitness))

/-- The structured step cannot be presented as the legacy `ConvT.iota`
generator at this recursor: there is no matching legacy witness. -/
theorem covWMatrix_iota_no_legacy_witness (w : IotaWitness covUHoEnv) :
    w.recRef ≠ 65 := covUHo_no_legacy_witness w

/-- The RHS directly consumes the constant minor's two empty-demand rows. -/
theorem covWMatrix_iota_rhs_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covUHoEnv n Γ ρ covWMatrixIotaTarget .prop := by
  change ApproxTKWIrrel covUHoEnv n Γ ρ (.app (.app covUHoMinor _) _) .prop
  apply covWIrrel_empty_app
  apply covWIrrel_empty_app
  apply covWIrrel_empty_lam (by intro h; cases h)
  apply covWIrrel_empty_lam (by intro h; cases h)
  exact covWIrrel_sort_observed covUHoEnv n _ _ .zero

/-- The old source filter fails even at this actual constructor-major call. -/
theorem covWMatrix_iota_source_filter_fails (ρ : EnvT) :
    ¬ ApproxTN covUHoEnv ρ covWMatrixIotaSource .prop := by
  intro h
  exact CptT.noConfusion
    (covVHo_foldApps_only_bot ρ [.succ (.succ .zero)]
      [covUHoMotive, covUHoMinor, covWMatrixIotaMajor] h)

theorem covWMatrix_iota_source_only_bot {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {c : CptWIrrel}
    (h : ApproxTKWIrrel covUHoEnv n Γ ρ covWMatrixIotaSource c) : c = .bot :=
  covWIrrel_ineligible_prop_head_only_bot covUHoWitness
    (covVHo_rec_family_prop covUHoWitness rfl)
    covUHo_not_kFreeRec covUHo_not_kProjRec h rfl

theorem covWMatrix_iota_source_excluded (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ CovWIrrelObservation covUHoEnv n Γ ρ covWMatrixIotaSource .prop := by
  rintro ⟨d, he, hd⟩
  have hb := covWMatrix_iota_source_only_bot hd
  subst d
  cases he

theorem covWMatrix_iota_compact_typed : CTyS covUHoEnv .prop .sort := by
  rw [CTyS]
  exact Or.inr .prop

/-- This is a finite-valuation certificate for the erased old eta model;
the actual source and target observations use the current grammar. -/
theorem covWMatrix_iota_erased_valuation (n : Nat) :
    EnvTypedFinAtT (⟨ApproxTKWEta covUHoEnv n []⟩ : CtxModelT covUHoEnv)
      [] (covWIrrelEnvErase EnvWIrrel.bot) :=
  envTypedFinAtT_nil _ _

theorem covWMatrix_iota_erased_coherence (n : Nat) :
    CtxEnvM (⟨ApproxTKWEta covUHoEnv n []⟩ : CtxModelT covUHoEnv)
      [] (covWIrrelEnvErase EnvWIrrel.bot) :=
  fun _ _ hv => Option.noConfusion hv

/-- A closed, inhabited ordinary-iota failure at the exact strict output demand. -/
theorem covWMatrix_iota_inhabited (n : Nat) :
    Nonempty (EnvWfT covUHoEnv) ∧ Nonempty (CtxWfT covUHoEnv n []) ∧
    Nonempty (HasTyT covUHoEnv n [] covWMatrixIotaSource (.sort (.succ .zero))) ∧
    Nonempty (HasTyT covUHoEnv n [] covWMatrixIotaTarget (.sort (.succ .zero))) ∧
    (∀ w : IotaWitness covUHoEnv, w.recRef ≠ 65) ∧
    IsCtorSpine covUHoEnv covWMatrixIotaMajor ∧
    WhStepCK2 covUHoEnv n [] covWMatrixIotaSource covWMatrixIotaTarget ∧
    CovWIrrelRealized covUHoEnv n 1 [] EnvWIrrel.bot SubstT.id ∧
    CovWIrrelObservation covUHoEnv n [] EnvWIrrel.bot (.sort (.succ .zero)) .sort ∧
    CTyS covUHoEnv .prop .sort ∧
    CovWIrrelObservation covUHoEnv n [] EnvWIrrel.bot covWMatrixIotaTarget .prop ∧
    (¬ CovWIrrelObservation covUHoEnv n [] EnvWIrrel.bot covWMatrixIotaSource .prop) ∧
    ¬ ApproxTN covUHoEnv (covWIrrelEnvErase EnvWIrrel.bot) covWMatrixIotaSource .prop :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, ⟨covWMatrixIotaSource_ty n []⟩,
    ⟨covWMatrixIotaTarget_ty n []⟩, covWMatrix_iota_no_legacy_witness,
    covWMatrix_iota_constructor_major, covWMatrix_iota_step n [],
    covWIrrel_realized_nil covUHoEnv n 1,
    covWIrrel_observation_of (covWIrrel_sort_observed covUHoEnv n [] EnvWIrrel.bot (.succ .zero)),
    covWMatrix_iota_compact_typed,
    covWIrrel_observation_of (covWMatrix_iota_rhs_observed n [] EnvWIrrel.bot),
    covWMatrix_iota_source_excluded n [] EnvWIrrel.bot,
    covWMatrix_iota_source_filter_fails _⟩

theorem covWMatrix_iota_no_typed_head_expansion (n : Nat) :
    ¬ (∀ c a : CptT,
      CovWIrrelObservation covUHoEnv n [] EnvWIrrel.bot (.sort (.succ .zero)) a →
      CTyS covUHoEnv c a →
      CovWIrrelObservation covUHoEnv n [] EnvWIrrel.bot covWMatrixIotaTarget c →
      CovWIrrelObservation covUHoEnv n [] EnvWIrrel.bot covWMatrixIotaSource c) := by
  intro h
  exact covWMatrix_iota_source_excluded n [] EnvWIrrel.bot
    (h .prop .sort
      (covWIrrel_observation_of
        (covWIrrel_sort_observed covUHoEnv n [] EnvWIrrel.bot (.succ .zero)))
      covWMatrix_iota_compact_typed
      (covWIrrel_observation_of (covWMatrix_iota_rhs_observed n [] EnvWIrrel.bot)))

theorem covWMatrix_iota_restriction_not_equal (n : Nat)
    (Obs : Expr Nat → CptT → Prop)
    (hforget : ∀ e c, Obs e c →
      CovWIrrelObservation covUHoEnv n [] EnvWIrrel.bot e c)
    (hrhs : Obs covWMatrixIotaTarget .prop) :
    ¬ (∀ c : CptT, CTyS covUHoEnv c .sort →
      (Obs covWMatrixIotaSource c ↔ Obs covWMatrixIotaTarget c)) := by
  intro heq
  exact covWMatrix_iota_source_excluded n [] EnvWIrrel.bot
    (hforget _ _ ((heq .prop covWMatrix_iota_compact_typed).mpr hrhs))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_IOTA_HEAD_ROOTS
#print axioms covWMatrixIotaField
#print axioms covWMatrixIotaMajor
#print axioms covWMatrixIotaWitness
#print axioms covWMatrixIotaSource
#print axioms covWMatrixIotaTarget
#print axioms covWMatrixIotaField_ty
#print axioms covWMatrixIotaMajor_ty
#print axioms covWMatrixIotaSource_ty
#print axioms covWMatrixIotaTarget_ty
#print axioms covWMatrix_iota_constructor_major
#print axioms covWMatrix_iota_step
#print axioms covWMatrix_iota_no_legacy_witness
#print axioms covWMatrix_iota_rhs_observed
#print axioms covWMatrix_iota_source_filter_fails
#print axioms covWMatrix_iota_source_only_bot
#print axioms covWMatrix_iota_source_excluded
#print axioms covWMatrix_iota_compact_typed
#print axioms covWMatrix_iota_erased_valuation
#print axioms covWMatrix_iota_erased_coherence
#print axioms covWMatrix_iota_inhabited
#print axioms covWMatrix_iota_no_typed_head_expansion
#print axioms covWMatrix_iota_restriction_not_equal
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_IOTA_HEAD_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit
