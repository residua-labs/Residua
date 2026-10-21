import rcic.RcicNativeTypedModelCovWNativeComputations
import rcic.RcicNativeTypedModelCovWNativeHoControl
import rcic.RcicNativeTypedModelCovWMatrixRawCongruence

/-!
# A native proof argument refutes guarded context congruence

The hole contains two actual closed proofs of the admitted higher-order
proposition W. Their typed observations agree at every observed code of W,
including its nonbottom rigid code. Native irrelevance relates the proofs.
The same one-application recursor context has actual native occurrence typing
on both sides and natively convertible results of Sort 1. Constructor iota
observes Prop on one side; the divergent neutral-major call has only bottom.

The counterexample consumes no assumed observation-transport theorem. Its
positive computation has no rigid field, so restricting appSpine fields cannot
remove it. Raw-context congruence remains the separate landed raw theorem.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelCovTAudit
open TypedModelCovVAudit TypedModelCovWAudit TypedModelCovWIrrelAudit
open TypedModelCovWMatrixAudit ReadbackCKAudit ReadbackCK2Audit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def CovWNativeTypedEqAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (a : CptT) (left right : Expr Nat) : Prop :=
  ∀ c, CTyS E c a →
    (CovWNativeObservation E n Γ ρ left c ↔ CovWNativeObservation E n Γ ρ right c)

def CovWNativeTypedInvariant (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (A left right : Expr Nat) : Prop :=
  ∀ a, CovWNativeObservation E n Γ ρ A a →
    CovWNativeTypedEqAt E n Γ ρ a left right

abbrev CovWNativeContext := CovWMatrixRawContext
abbrev covWNativeFill := covWMatrixRawFill

theorem covWNative_positive_code_demands (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWIrrel) (left right : Expr Nat)
    {a : CptT} (hP : IsPropCT E a) :
    CovWNativeTypedEqAt E n Γ ρ a left right := by
  intro c hc
  have hb := ctyT_prop_bot hP (ctyT_of_ctyS a c hc)
  subst c
  exact ⟨fun _ => ⟨.bot, rfl, .bot _ _ _⟩,
    fun _ => ⟨.bot, rfl, .bot _ _ _⟩⟩

/-- This finite shape includes every native eta alternative. -/
theorem covWNative_rigid_const_shape {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvWIrrel} {r : Nat} {ls : List Level} {c : CptWIrrel}
    (hr : RigidConst E r) (h : ApproxTKWNative E n Γ ρ (.const r ls) c) :
    c = .bot ∨ c = .spine r ls [] ∨ ∃ rows, c = .lam rows := by
  generalize he : Expr.const r ls = e at h
  cases h with
  | bot => exact Or.inl rfl
  | bvar => cases he
  | sort => cases he
  | const => cases he; exact Or.inr (Or.inl rfl)
  | recursor ls hp hpre hfields h =>
      cases he
      exact ((hr _ ‹IotaWitnessS E›.hrec).2 ‹IotaWitnessS E›.hrecK).elim
  | pi => cases he
  | lam => cases he
  | app => cases he
  | appSpine => cases he
  | delta hd _ =>
      cases he
      exact (not_rigidConst_of_deltaConst hd hr).elim
  | letE => cases he
  | lit => cases he
  | iota w _ =>
      simp only [iotaLhsOfS, recCall_eq_app] at he
      cases he
  | recursorPropK w x _ _ _ _ _ =>
      simp only [recCall_eq_app] at he
      cases he
  | eta => exact Or.inr (Or.inr ⟨_, rfl⟩)

def covWNativeHoPrefix : Expr Nat :=
  foldApps (.const 65 [.succ (.succ .zero)]) [covUHoMotive, covUHoMinor]

def covWNativeHoContext : CovWNativeContext := .appArgument covWNativeHoPrefix .hole

theorem covWNativeHo_fill_neutral :
    covWNativeFill covWNativeHoContext covUHoMajor = covUHoType := rfl

theorem covWNativeHo_fill_constructor :
    covWNativeFill covWNativeHoContext covWMatrixIotaMajor = covWMatrixIotaSource := rfl

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

def covWNativeHo_prefix_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWNativeHoPrefix
      (.pi (.const 63 []) (.app covUHoMotive (.bvar 0))) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (.const _ 65 [.succ (.succ .zero)] covUHoRec rfl rfl rfl)
      (ho_motive_ty n Γ)) (ho_minor_ty n Γ)

def covWNativeHo_major_irrel (n : Nat) (Γ : LCtx) :
    ConvT covUHoEnv n Γ covUHoMajor covWMatrixIotaMajor (.const 63 []) :=
  .irr _ _ _ _ (.const _ 63 [] covUHoFam rfl rfl rfl)
    (covUHoMajor_hasTy n Γ) (covWMatrixIotaMajor_ty n Γ)

/-- Native application congruence is actually supplied; it is not assumed
to preserve the finite observation relation. -/
def covWNativeHo_context_conv (n : Nat) (Γ : LCtx) :
    ConvT covUHoEnv n Γ covUHoType covWMatrixIotaSource (.sort (.succ .zero)) := by
  have hc : ConvT covUHoEnv n Γ covUHoType covWMatrixIotaSource
      (.app covUHoMotive covUHoMajor) :=
    .app _ _ _ _ _ _ _ (.refl _ _ _ (covWNativeHo_prefix_ty n Γ))
      (covWNativeHo_major_irrel n Γ)
  have hb : ConvT covUHoEnv n Γ (.app covUHoMotive covUHoMajor)
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .beta Γ (.const 63 []) (.sort (.succ .zero)) covUHoMajor
      (.sort (.succ (.succ .zero))) .zero
      (.const Γ 63 [] covUHoFam rfl rfl rfl) (.sort _ _)
      (covUHoMajor_hasTy n Γ)
  exact .tyConv _ _ _ _ _ _ hc hb

theorem covWNativeHo_occurrences (n : Nat) (Γ : LCtx) :
    CovWNativeOccurrence covUHoEnv n Γ covWNativeHoPrefix covUHoMajor
      (.const 63 []) (.app covUHoMotive (.bvar 0)) ∧
    CovWNativeOccurrence covUHoEnv n Γ covWNativeHoPrefix covWMatrixIotaMajor
      (.const 63 []) (.app covUHoMotive (.bvar 0)) ∧
    CovWNativeField covUHoEnv n Γ covWNativeHoPrefix covUHoMajor .bot ∧
    CovWNativeField covUHoEnv n Γ covWNativeHoPrefix covWMatrixIotaMajor .bot :=
  ⟨⟨⟨covWNativeHo_prefix_ty n Γ⟩, ⟨covUHoMajor_hasTy n Γ⟩⟩,
    ⟨⟨covWNativeHo_prefix_ty n Γ⟩, ⟨covWMatrixIotaMajor_ty n Γ⟩⟩,
    covWNative_field_bot (covWNativeHo_prefix_ty n Γ) (covUHoMajor_hasTy n Γ),
    covWNative_field_bot (covWNativeHo_prefix_ty n Γ) (covWMatrixIotaMajor_ty n Γ)⟩

theorem covWNativeHo_family_rigid : RigidConst covUHoEnv 63 :=
  rigidConst_of_inductiveM covUHoEnv_wf (m := covUHoFam) rfl rfl

theorem covWNativeHo_family_not_propCtor : ¬ PropCtorT covUHoEnv 63 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covUHoFam := Option.some.inj hm.symm
  subst m
  cases hk

theorem covWNativeHo_code_prop : IsPropCT covUHoEnv (.spine 63 []) :=
  .spine (m := covUHoFam) rfl rfl

theorem covWNativeHo_type_code (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    CovWNativeObservation covUHoEnv n Γ ρ (.const 63 []) (.spine 63 []) :=
  covWNative_observation_of
    (.const Γ ρ 63 [] covWNativeHo_family_rigid covWNativeHo_family_not_propCtor)

theorem covWNativeHo_majors_equal_at_code (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    CovWNativeTypedEqAt covUHoEnv n Γ ρ (.spine 63 [])
      covUHoMajor covWMatrixIotaMajor :=
  covWNative_positive_code_demands _ _ _ _ _ _ covWNativeHo_code_prop

/-- Every observed type code of W enforces the same bottom-only demand.
The lambda-code case includes all finite native eta derivations. -/
theorem covWNativeHo_type_demands {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {a c : CptT} (ha : CovWNativeObservation covUHoEnv n Γ ρ (.const 63 []) a)
    (hc : CTyS covUHoEnv c a) : c = .bot := by
  obtain ⟨d, rfl, hd⟩ := ha
  rcases covWNative_rigid_const_shape covWNativeHo_family_rigid hd with
    rfl | rfl | ⟨rows, rfl⟩
  · exact ctyS_bot_inv hc
  · exact ctyS_prop_bot covWNativeHo_code_prop hc
  · exact ctyS_lam_inv hc

/-- This compares all typed observations at every observed W code. -/
theorem covWNativeHo_majors_typed_equal (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    CovWNativeTypedInvariant covUHoEnv n Γ ρ (.const 63 [])
      covUHoMajor covWMatrixIotaMajor := by
  intro a ha c hc
  have hb := covWNativeHo_type_demands ha hc
  subst c
  exact ⟨fun _ => ⟨.bot, rfl, .bot _ _ _⟩,
    fun _ => ⟨.bot, rfl, .bot _ _ _⟩⟩

def covWNativeHo_major_pair (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covUHoMajor covWMatrixIotaMajor
      (.const 63 []) .zero where
  envWf := ⟨covUHoEnv_wf⟩
  ctxWf := ⟨.nil⟩
  leftTy := ⟨covUHoMajor_hasTy n []⟩
  rightTy := ⟨covWMatrixIotaMajor_ty n []⟩
  typeTy := ⟨.const [] 63 [] covUHoFam rfl rfl rfl⟩
  conversion := ⟨covWNativeHo_major_irrel n []⟩

def covWNativeHo_context_pair (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covUHoType covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) where
  envWf := ⟨covUHoEnv_wf⟩
  ctxWf := ⟨.nil⟩
  leftTy := ⟨covUHoType_hasTy n []⟩
  rightTy := ⟨covWMatrixIotaSource_ty n []⟩
  typeTy := ⟨.sort [] (.succ .zero)⟩
  conversion := ⟨covWNativeHo_context_conv n []⟩

theorem covWNativeHo_context_prop_absent (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ CovWNativeObservation covUHoEnv n Γ ρ covUHoType .prop := by
  intro h
  have he := (covWNativeHo_type_observation_iff n Γ ρ .prop).mp h
  cases he

theorem covWNativeHo_context_not_typed_equal (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) :
    ¬ CovWNativeTypedInvariant covUHoEnv n Γ ρ (.sort (.succ .zero))
      (covWNativeFill covWNativeHoContext covUHoMajor)
      (covWNativeFill covWNativeHoContext covWMatrixIotaMajor) := by
  intro heq
  apply covWNativeHo_context_prop_absent n Γ ρ
  exact (heq .sort (covWNative_observation_of (.sort Γ ρ (.succ .zero)))
    .prop covWMatrix_iota_compact_typed).mpr
    (covWNative_observation_of (covWNative_iota_source_prop n Γ ρ))

/-- A single application is already a finite context. Native occurrence
typing, proof conversion, common result typing, and full typed hole equality
do not imply preservation of the observation relation. -/
def CovWNativeAppArgumentCongruence : Prop :=
  ∀ (E : ResolvedEnv) (n : Nat) (f left right D B A : Expr Nat) (u v : Level),
    EnvWfT E → HasTyT E n [] D (.sort u) → HasTyT E n [] A (.sort v) →
    HasTyT E n [] f (.pi D B) → HasTyT E n [] left D → HasTyT E n [] right D →
    HasTyT E n [] (.app f left) A → HasTyT E n [] (.app f right) A →
    ConvT E n [] left right D →
    CovWNativeTypedInvariant E n [] EnvWIrrel.bot D left right →
    CovWNativeTypedInvariant E n [] EnvWIrrel.bot A (.app f left) (.app f right)

theorem covWNative_app_argument_congruence_false :
    ¬ CovWNativeAppArgumentCongruence := by
  intro hc
  exact covWNativeHo_context_not_typed_equal 0 [] EnvWIrrel.bot
    (hc covUHoEnv 0 covWNativeHoPrefix covUHoMajor covWMatrixIotaMajor
      (.const 63 []) (.app covUHoMotive (.bvar 0)) (.sort (.succ .zero))
      .zero (.succ (.succ .zero)) covUHoEnv_wf
      (.const [] 63 [] covUHoFam rfl rfl rfl) (.sort [] (.succ .zero))
      (covWNativeHo_prefix_ty 0 []) (covUHoMajor_hasTy 0 [])
      (covWMatrixIotaMajor_ty 0 []) (covUHoType_hasTy 0 [])
      (covWMatrixIotaSource_ty 0 []) (covWNativeHo_major_irrel 0 [])
      (covWNativeHo_majors_typed_equal 0 [] EnvWIrrel.bot))

/-- Every certificate in the counterexample is supplied. The hole code is
nonbottom, while the equality premise quantifies over all observed codes. -/
theorem covWNativeHo_context_failure_inhabited (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covUHoMajor covWMatrixIotaMajor
      (.const 63 []) .zero ∧
    CovWMatrixNativePair covUHoEnv n covUHoType covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    CovWNativeRealized covUHoEnv n 1 [] EnvWIrrel.bot SubstT.id ∧
    CovWNativeOccurrence covUHoEnv n [] covWNativeHoPrefix covUHoMajor
      (.const 63 []) (.app covUHoMotive (.bvar 0)) ∧
    CovWNativeOccurrence covUHoEnv n [] covWNativeHoPrefix covWMatrixIotaMajor
      (.const 63 []) (.app covUHoMotive (.bvar 0)) ∧
    CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot (.const 63 []) (.spine 63 []) ∧
    (.spine 63 [] : CptT) ≠ .bot ∧
    CovWNativeTypedInvariant covUHoEnv n [] EnvWIrrel.bot (.const 63 [])
      covUHoMajor covWMatrixIotaMajor ∧
    CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot (.sort (.succ .zero)) .sort ∧
    CTyS covUHoEnv .prop .sort ∧
    CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot covWMatrixIotaSource .prop ∧
    (¬ CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot covUHoType .prop) ∧
    ¬ CovWNativeTypedInvariant covUHoEnv n [] EnvWIrrel.bot (.sort (.succ .zero))
      (covWNativeFill covWNativeHoContext covUHoMajor)
      (covWNativeFill covWNativeHoContext covWMatrixIotaMajor) :=
  ⟨covWNativeHo_major_pair n, covWNativeHo_context_pair n,
    covWNative_realized_nil covUHoEnv n 1,
    (covWNativeHo_occurrences n []).1, (covWNativeHo_occurrences n []).2.1,
    covWNativeHo_type_code n [] EnvWIrrel.bot, (by intro h; cases h),
    covWNativeHo_majors_typed_equal n [] EnvWIrrel.bot,
    covWNative_observation_of (.sort [] EnvWIrrel.bot (.succ .zero)),
    covWMatrix_iota_compact_typed,
    covWNative_observation_of (covWNative_iota_source_prop n [] EnvWIrrel.bot),
    covWNativeHo_context_prop_absent n [] EnvWIrrel.bot,
    covWNativeHo_context_not_typed_equal n [] EnvWIrrel.bot⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_CONTEXT_ROOTS
#print axioms CovWNativeTypedEqAt
#print axioms CovWNativeTypedInvariant
#print axioms CovWNativeContext
#print axioms covWNativeFill
#print axioms covWNative_positive_code_demands
#print axioms covWNative_rigid_const_shape
#print axioms covWNativeHoPrefix
#print axioms covWNativeHoContext
#print axioms covWNativeHo_fill_neutral
#print axioms covWNativeHo_fill_constructor
#print axioms covWNativeHo_prefix_ty
#print axioms covWNativeHo_major_irrel
#print axioms covWNativeHo_context_conv
#print axioms covWNativeHo_occurrences
#print axioms covWNativeHo_family_rigid
#print axioms covWNativeHo_family_not_propCtor
#print axioms covWNativeHo_code_prop
#print axioms covWNativeHo_type_code
#print axioms covWNativeHo_majors_equal_at_code
#print axioms covWNativeHo_type_demands
#print axioms covWNativeHo_majors_typed_equal
#print axioms covWNativeHo_major_pair
#print axioms covWNativeHo_context_pair
#print axioms covWNativeHo_context_prop_absent
#print axioms covWNativeHo_context_not_typed_equal
#print axioms CovWNativeAppArgumentCongruence
#print axioms covWNative_app_argument_congruence_false
#print axioms covWNativeHo_context_failure_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_CONTEXT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
