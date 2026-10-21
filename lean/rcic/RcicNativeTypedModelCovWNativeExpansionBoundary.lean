import rcic.RcicNativeTypedModelCovWNativeContext
import rcic.RcicNativeTypedModelCovWMatrixCells

/-!
# Beta and zeta cannot expose the newly admitted constructor computation

The direct constructor-major call observes Prop. Before substitution the
same recursor body has a variable major, so the already checked Ho invariant
forces bottom. Finite typed eta cannot manufacture a nonbottom graph: its
fresh application has the same lambda/let head. This refutes subject expansion
using an actual native beta step, independently of declarative head adequacy.
All original declarations are unchanged. closure_claim = 0.
-/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovTAudit TypedModelCovWIrrelAudit TypedModelCovWMatrixAudit
open ReadbackCKAudit ReadbackCK2Audit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWNativeHoBetaBody : Expr Nat := .app covWNativeHoPrefix (.bvar 0)
def covWNativeHoBetaFn : Expr Nat := .lam (.const 63 []) covWNativeHoBetaBody
def covWNativeHoBetaSource : Expr Nat := .app covWNativeHoBetaFn covWMatrixIotaMajor
def covWNativeHoLetSource : Expr Nat :=
  .letE (.const 63 []) covWMatrixIotaMajor covWNativeHoBetaBody

theorem covWNativeHo_beta_substitution :
    instantiate0 covWMatrixIotaMajor covWNativeHoBetaBody = covWMatrixIotaSource := rfl

def covWNativeHo_beta_body_ty (n : Nat) (Γ : LCtx)
    (hx : HasTyT covUHoEnv n Γ (.bvar 0) (.const 63 [])) :
    HasTyT covUHoEnv n Γ covWNativeHoBetaBody (.sort (.succ .zero)) := by
  have ht : HasTyT covUHoEnv n Γ covWNativeHoBetaBody
      (.app covUHoMotive (.bvar 0)) :=
    .app _ _ _ _ _ (covWNativeHo_prefix_ty n Γ) hx
  exact .conv _ _ _ _ _ ht
    (.beta _ _ _ _ _ _ (.const Γ 63 [] covUHoFam rfl rfl rfl) (.sort _ _) hx)

def covWNativeHo_beta_fn_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWNativeHoBetaFn
      (.pi (.const 63 []) (.sort (.succ .zero))) :=
  .lam _ _ _ _ _ (.const Γ 63 [] covUHoFam rfl rfl rfl)
    (covWNativeHo_beta_body_ty n _ (.bvar _ 0 _ rfl))

def covWNativeHo_beta_source_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWNativeHoBetaSource (.sort (.succ .zero)) :=
  .app _ _ _ _ _ (covWNativeHo_beta_fn_ty n Γ) (covWMatrixIotaMajor_ty n Γ)

def covWNativeHo_let_source_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covWNativeHoLetSource (.sort (.succ .zero)) :=
  .letE _ _ _ _ _ _ (.const Γ 63 [] covUHoFam rfl rfl rfl)
    (covWMatrixIotaMajor_ty n Γ) (covWNativeHo_beta_body_ty n _ (.bvar _ 0 _ rfl))

def covWNativeHo_beta_conv (n : Nat) (Γ : LCtx) :
    ConvT covUHoEnv n Γ covWNativeHoBetaSource covWMatrixIotaSource
      (.sort (.succ .zero)) :=
  .beta _ _ _ _ _ _ (.const Γ 63 [] covUHoFam rfl rfl rfl)
    (covWNativeHo_beta_body_ty n _ (.bvar _ 0 _ rfl)) (covWMatrixIotaMajor_ty n Γ)

def covWNativeHo_let_conv (n : Nat) (Γ : LCtx) :
    ConvT covUHoEnv n Γ covWNativeHoLetSource covWMatrixIotaSource
      (.sort (.succ .zero)) :=
  .zeta _ _ _ _ _ _ (.const Γ 63 [] covUHoFam rfl rfl rfl)
    (covWMatrixIotaMajor_ty n Γ) (covWNativeHo_beta_body_ty n _ (.bvar _ 0 _ rfl))

theorem covWNativeHo_beta_step (n : Nat) (Γ : LCtx) :
    WhStepCK2 covUHoEnv n Γ covWNativeHoBetaSource covWMatrixIotaSource :=
  .ctx (.beta _ _ _)

theorem covWNativeHo_let_step (n : Nat) (Γ : LCtx) :
    WhStepCK2 covUHoEnv n Γ covWNativeHoLetSource covWMatrixIotaSource :=
  .ctx (.zeta _ _ _)

private def hoAliasHead (e : Expr Nat) : Prop :=
  (appsSpine e).1 = covWNativeHoBetaFn ∨ (appsSpine e).1 = covWNativeHoLetSource

private theorem hoAliasHead_eta {e : Expr Nat} (h : hoAliasHead e) :
    hoAliasHead (.app (lift 0 1 e) (.bvar 0)) := by
  rcases h with h | h
  · apply Or.inl
    change (appsSpine (lift 0 1 e)).1 = _
    rw [appsSpine_lift]
    change lift 0 1 (appsSpine e).1 = _
    rw [h]
    rfl
  · apply Or.inr
    change (appsSpine (lift 0 1 e)).1 = _
    rw [appsSpine_lift]
    change lift 0 1 (appsSpine e).1 = _
    rw [h]
    rfl

private theorem ho_alias_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWNative covUHoEnv n Γ ρ e c) : hoAliasHead e → c = .bot := by
  induction h with
  | bot => intro _; rfl
  | bvar => rintro (h | h) <;> cases h
  | sort => rintro (h | h) <;> cases h
  | const => rintro (h | h) <;> cases h
  | recursor => rintro (h | h) <;> cases h
  | pi => rintro (h | h) <;> cases h
  | @lam Γ ρ A b a g hA ht hne hb ihA ihb =>
      rintro (he | he)
      · change Expr.lam A b = Expr.lam (.const 63 []) covWNativeHoBetaBody at he
        cases he
        obtain ⟨s, hs, hn⟩ := hne
        exact (hn (covWNativeHo_nonconstant_major_only_bot (x := .bvar 0) rfl (hb s hs))).elim
      · cases he
  | app hf hs ha ihf iha =>
      intro hh
      cases ihf hh
  | appSpine hf ha hslot hfield ihf iha =>
      intro hh
      cases ihf hh
  | delta => rintro (h | h) <;> cases h
  | @letE Γ ρ A v b c h ih =>
      rintro (he | he)
      · cases he
      · change Expr.letE A v b = Expr.letE (.const 63 []) covWMatrixIotaMajor covWNativeHoBetaBody at he
        cases he
        exact ih (Or.inl rfl)
  | lit => rintro (h | h) <;> cases h
  | iota w h ih =>
      rintro (hh | hh) <;>
        simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const] at hh <;> cases hh
  | recursorPropK w x hk hn hi hc h ih =>
      rintro (hh | hh) <;>
        simp only [recCall, appsSpine_foldApps_const] at hh <;> cases hh
  | eta he hD ht hne hb ihD ihb =>
      intro hh
      obtain ⟨s, hs, hn⟩ := hne
      exact (hn (ihb s hs (hoAliasHead_eta hh))).elim

theorem covWNativeHo_beta_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel}
    (h : ApproxTKWNative covUHoEnv n Γ ρ covWNativeHoBetaSource c) : c = .bot :=
  ho_alias_only_bot h (Or.inl rfl)

theorem covWNativeHo_let_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel}
    (h : ApproxTKWNative covUHoEnv n Γ ρ covWNativeHoLetSource c) : c = .bot :=
  ho_alias_only_bot h (Or.inr rfl)

theorem covWNativeHo_beta_observation_iff (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (c : CptT) :
    CovWNativeObservation covUHoEnv n Γ ρ covWNativeHoBetaSource c ↔ c = .bot := by
  constructor
  · rintro ⟨d, he, hd⟩
    have hb := covWNativeHo_beta_only_bot hd
    subst d
    exact he.symm
  · rintro rfl
    exact covWNative_observation_of (.bot _ _ _)

theorem covWNativeHo_let_observation_iff (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (c : CptT) :
    CovWNativeObservation covUHoEnv n Γ ρ covWNativeHoLetSource c ↔ c = .bot := by
  constructor
  · rintro ⟨d, he, hd⟩
    have hb := covWNativeHo_let_only_bot hd
    subst d
    exact he.symm
  · rintro rfl
    exact covWNative_observation_of (.bot _ _ _)

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovTAudit TypedModelCovWIrrelAudit TypedModelCovWMatrixAudit
open ReadbackCKAudit ReadbackCK2Audit

def covWNativeHo_beta_pair (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covWNativeHoBetaSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, ⟨covWNativeHo_beta_source_ty n []⟩,
    ⟨covWMatrixIotaSource_ty n []⟩, ⟨.sort [] (.succ .zero)⟩,
    ⟨covWNativeHo_beta_conv n []⟩⟩

def covWNativeHo_let_pair (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covWNativeHoLetSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, ⟨covWNativeHo_let_source_ty n []⟩,
    ⟨covWMatrixIotaSource_ty n []⟩, ⟨.sort [] (.succ .zero)⟩,
    ⟨covWNativeHo_let_conv n []⟩⟩

theorem covWNativeHo_beta_prop_absent (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ CovWNativeObservation covUHoEnv n Γ ρ covWNativeHoBetaSource .prop := by
  intro h
  cases (covWNativeHo_beta_observation_iff n Γ ρ .prop).mp h

theorem covWNativeHo_let_prop_absent (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ CovWNativeObservation covUHoEnv n Γ ρ covWNativeHoLetSource .prop := by
  intro h
  cases (covWNativeHo_let_observation_iff n Γ ρ .prop).mp h

theorem covWNativeHo_beta_not_typed_equal (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ CovWNativeTypedInvariant covUHoEnv n Γ ρ (.sort (.succ .zero))
      covWNativeHoBetaSource covWMatrixIotaSource := by
  intro heq
  exact covWNativeHo_beta_prop_absent n Γ ρ
    ((heq .sort (covWNative_observation_of (.sort Γ ρ (.succ .zero)))
      .prop covWMatrix_iota_compact_typed).mpr
        (covWNative_observation_of (covWNative_iota_source_prop n Γ ρ)))

theorem covWNativeHo_let_not_typed_equal (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ CovWNativeTypedInvariant covUHoEnv n Γ ρ (.sort (.succ .zero))
      covWNativeHoLetSource covWMatrixIotaSource := by
  intro heq
  exact covWNativeHo_let_prop_absent n Γ ρ
    ((heq .sort (covWNative_observation_of (.sort Γ ρ (.succ .zero)))
      .prop covWMatrix_iota_compact_typed).mpr
        (covWNative_observation_of (covWNative_iota_source_prop n Γ ρ)))

/-- A closed, typed fragment of subject expansion. Its failure already
refutes a universal supplier; no readback or completeness premise appears. -/
def CovWNativeClosedSubjectExpansion : Prop :=
  ∀ (E : ResolvedEnv) (n stage : Nat) (e e' A : Expr Nat)
      (l : Level) (c a : CptT),
    EnvWfT E → HasTyT E n [] e A → HasTyT E n [] e' A →
    HasTyT E n [] A (.sort l) →
    CovWNativeRealized E n stage [] EnvWIrrel.bot SubstT.id →
    WhStepCK2 E n [] e e' →
    CovWNativeObservation E n [] EnvWIrrel.bot A a →
    CTyS E c a → c ≠ .bot →
    CovWNativeObservation E n [] EnvWIrrel.bot e' c →
    CovWNativeObservation E n [] EnvWIrrel.bot e c

theorem covWNative_subject_expansion_false : ¬ CovWNativeClosedSubjectExpansion := by
  intro h
  exact covWNativeHo_beta_prop_absent 0 [] EnvWIrrel.bot
    (h covUHoEnv 0 1 covWNativeHoBetaSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) .prop .sort
      covUHoEnv_wf (covWNativeHo_beta_source_ty 0 []) (covWMatrixIotaSource_ty 0 [])
      (.sort [] (.succ .zero)) (covWNative_realized_nil covUHoEnv 0 1)
      (covWNativeHo_beta_step 0 [])
      (covWNative_observation_of (.sort [] EnvWIrrel.bot (.succ .zero)))
      covWMatrix_iota_compact_typed (by intro he; cases he)
      (covWNative_observation_of (covWNative_iota_source_prop 0 [] EnvWIrrel.bot)))

theorem covWNativeHo_beta_failure_inhabited (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covWNativeHoBetaSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    Nonempty (HasTyT covUHoEnv n [.assumption (.const 63 [])]
      covWNativeHoBetaBody (.sort (.succ .zero))) ∧
    Nonempty (HasTyT covUHoEnv n [] covWMatrixIotaMajor (.const 63 [])) ∧
    CovWNativeRealized covUHoEnv n 1 [] EnvWIrrel.bot SubstT.id ∧
    WhStepCK2 covUHoEnv n [] covWNativeHoBetaSource covWMatrixIotaSource ∧
    CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot
      (.sort (.succ .zero)) .sort ∧
    CTyS covUHoEnv .prop .sort ∧
    (CptT.prop ≠ .bot) ∧
    ApproxTKWNativeStage covUHoEnv n 1 [] EnvWIrrel.bot covWMatrixIotaSource .prop ∧
    (∀ c, ApproxTKWNative covUHoEnv n [] EnvWIrrel.bot covWNativeHoBetaSource c →
      c = .bot) ∧
    ¬ CovWNativeTypedInvariant covUHoEnv n [] EnvWIrrel.bot (.sort (.succ .zero))
      covWNativeHoBetaSource covWMatrixIotaSource := by
  refine ⟨covWNativeHo_beta_pair n,
    ⟨covWNativeHo_beta_body_ty n _ (.bvar _ 0 _ rfl)⟩,
    ⟨covWMatrixIotaMajor_ty n []⟩, covWNative_realized_nil covUHoEnv n 1,
    covWNativeHo_beta_step n [],
    covWNative_observation_of (.sort [] EnvWIrrel.bot (.succ .zero)),
    covWMatrix_iota_compact_typed, (by intro h; cases h),
    ⟨covWNative_iota_source_prop n [] EnvWIrrel.bot, ?_⟩,
    (fun _ h => covWNativeHo_beta_only_bot h),
    covWNativeHo_beta_not_typed_equal n [] EnvWIrrel.bot⟩
  simp [covTObservationBudget, covWIrrelErase]

theorem covWNativeHo_let_failure_inhabited (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covWNativeHoLetSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    Nonempty (HasTyT covUHoEnv n [.letBinding (.const 63 []) covWMatrixIotaMajor]
      covWNativeHoBetaBody (.sort (.succ .zero))) ∧
    CovWNativeRealized covUHoEnv n 1 [] EnvWIrrel.bot SubstT.id ∧
    WhStepCK2 covUHoEnv n [] covWNativeHoLetSource covWMatrixIotaSource ∧
    CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot
      (.sort (.succ .zero)) .sort ∧
    CTyS covUHoEnv .prop .sort ∧
    (CptT.prop ≠ .bot) ∧
    ApproxTKWNativeStage covUHoEnv n 1 [] EnvWIrrel.bot covWMatrixIotaSource .prop ∧
    (∀ c, ApproxTKWNative covUHoEnv n [] EnvWIrrel.bot covWNativeHoLetSource c →
      c = .bot) ∧
    ¬ CovWNativeTypedInvariant covUHoEnv n [] EnvWIrrel.bot (.sort (.succ .zero))
      covWNativeHoLetSource covWMatrixIotaSource := by
  refine ⟨covWNativeHo_let_pair n,
    ⟨covWNativeHo_beta_body_ty n _ (.bvar _ 0 _ rfl)⟩,
    covWNative_realized_nil covUHoEnv n 1, covWNativeHo_let_step n [],
    covWNative_observation_of (.sort [] EnvWIrrel.bot (.succ .zero)),
    covWMatrix_iota_compact_typed, (by intro h; cases h),
    ⟨covWNative_iota_source_prop n [] EnvWIrrel.bot, ?_⟩,
    (fun _ h => covWNativeHo_let_only_bot h),
    covWNativeHo_let_not_typed_equal n [] EnvWIrrel.bot⟩
  simp [covTObservationBudget, covWIrrelErase]

/-- The same strict singleton binder test distinguishes both native aliases
from their constructor-positive reduct. -/
theorem covWNativeHo_expansion_binder_test (n : Nat) :
    (∀ c ∈ [CptT.prop], CTyS covUHoEnv c .sort) ∧
    CovWMatrixFiniteDemands (CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot)
      [.prop] covWMatrixIotaSource ∧
    ¬ CovWMatrixFiniteDemands (CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot)
      [.prop] covWNativeHoBetaSource ∧
    ¬ CovWMatrixFiniteDemands (CovWNativeObservation covUHoEnv n [] EnvWIrrel.bot)
      [.prop] covWNativeHoLetSource := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact covWMatrix_iota_compact_typed
  · exact (covWMatrix_finite_demands_singleton _ _ _).mpr
      (covWNative_observation_of (covWNative_iota_source_prop n [] EnvWIrrel.bot))
  · intro h
    exact covWNativeHo_beta_prop_absent n [] EnvWIrrel.bot
      ((covWMatrix_finite_demands_singleton _ _ _).mp h)
  · intro h
    exact covWNativeHo_let_prop_absent n [] EnvWIrrel.bot
      ((covWMatrix_finite_demands_singleton _ _ _).mp h)

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
open TypedModelCovTAudit TypedModelCovWIrrelAudit

theorem covWNativeHo_beta_fn_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel}
    (h : ApproxTKWNative covUHoEnv n Γ ρ covWNativeHoBetaFn c) : c = .bot :=
  ho_alias_only_bot h (Or.inl rfl)

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_EXPANSION_BOUNDARY_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoBetaBody
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoBetaFn
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoBetaSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHoLetSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_substitution
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_body_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_fn_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_source_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_source_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_pair
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_pair
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_prop_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_prop_absent
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_not_typed_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_not_typed_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.CovWNativeClosedSubjectExpansion
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNative_subject_expansion_false
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_failure_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_let_failure_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_expansion_binder_test
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit.covWNativeHo_beta_fn_only_bot
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_EXPANSION_BOUNDARY_ROOTS
