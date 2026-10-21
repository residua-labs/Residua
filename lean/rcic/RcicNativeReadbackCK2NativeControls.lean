import rcic.RcicNativeReadbackCK2Conv
import rcic.RcicNativeReadbackCK2Index

/-!
# Typed positive controls for the native-index CK2 K head

These controls use exactly the native gate and the same binder and eta
recursors that refute the one-sided weak-head index scheduler.  Delta is
tested at an index head and underneath a binder in the checked extension.
The readback core may lift each `KNativeHead` proof through its native arm.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit

theorem kNativeHead_binder (n : Nat) :
    KNativeHead eqEnvT n binderEqCtx binderIndexRedex (.sort .zero) :=
  kNativeHead_eq_of_indexConv (fun _ _ h => h) binderIndexMot (.sort .zero)
    (indexFnTy eqEnvT n binderEqCtx) (indexIdTy eqEnvT n binderEqCtx)
    (indexBinderBetaTy eqEnvT n binderEqCtx)
    (.bvar binderEqCtx 0 _ rfl) (indexBinderBetaConv eqEnvT n binderEqCtx)
    not_isCtorSpine_bvar

theorem kNativeHead_eta (n : Nat) :
    KNativeHead eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) :=
  kNativeHead_eq_of_indexConv (fun _ _ h => h) etaIndexMot (.sort .zero)
    (indexFnTy eqEnvT n etaEqCtx) (etaIndexParamTy n) (etaIndexTy n)
    (.bvar etaEqCtx 0 _ rfl) (etaIndexConv n) not_isCtorSpine_bvar

/-- The complete binder control: admitted environment and context, a native
conversion of the full recursor, and the repaired native K head. -/
theorem native_binder_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n binderEqCtx) ∧
    Nonempty (ConvT eqEnvT n binderEqCtx binderIndexRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KNativeHead eqEnvT n binderEqCtx binderIndexRedex (.sort .zero) :=
  ⟨⟨pinEqGroupWfT⟩, ⟨binderEqCtxWf n⟩, ⟨binderIndexRedexConv n⟩, kNativeHead_binder n⟩

/-- The complete eta control uses the same genuinely neutral function index. -/
theorem native_eta_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KNativeHead eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) :=
  ⟨⟨pinEqGroupWfT⟩, ⟨etaEqCtxWf n⟩, ⟨etaIndexRedexConv n⟩, kNativeHead_eta n⟩

/-- The checked delta environment preserves all exact Eq declarations. -/
theorem deltaEqExtends : ExtendsEqEnv deltaEqEnv :=
  fun _ _ hm => members_extendEnv_of_some eqEnvT 66 deltaEqMember rfl hm

def deltaConstTy (n : Nat) (Γ : LCtx) :
    HasTyT deltaEqEnv n Γ (.const 66 []) indexFn :=
  .const _ 66 [] deltaEqMember rfl rfl rfl

def deltaBinderTy (n : Nat) (Γ : LCtx) :
    HasTyT deltaEqEnv n Γ deltaBinderIndex indexFn :=
  .lam _ _ _ _ _ (.sort _ _)
    (.app _ _ _ _ _ (deltaConstTy n _) (.bvar _ 0 _ rfl))

def deltaFamilyTy (n : Nat) (Γ : LCtx) {b : Expr Nat}
    (hb : HasTyT deltaEqEnv n Γ b indexFn) :
    HasTyT deltaEqEnv n Γ (binderIndexFamily b) (.sort .zero) :=
  .app _ _ _ _ _
    (eqFamilyPartialTy deltaEqExtends
      (indexFnTy deltaEqEnv n Γ) (indexIdTy deltaEqEnv n Γ)) hb

def deltaCtorTy (n : Nat) (Γ : LCtx) :
    HasTyT deltaEqEnv n Γ binderIndexCtor (binderIndexFamily indexId) :=
  eqReflApplyTy deltaEqExtends (indexFnTy deltaEqEnv n Γ) (indexIdTy deltaEqEnv n Γ)

def deltaMotTy (n : Nat) (Γ : LCtx) :
    HasTyT deltaEqEnv n Γ binderIndexMot
      (.pi indexFn (.pi (binderIndexFamily (.bvar 0)) (.sort (.succ (.succ .zero))))) :=
  hasTyT_extendEnv (r := 66) (m := deltaEqMember) rfl (binderIndexMotTy n Γ)

/-- The same typed constant motive computes at every delta-environment index. -/
def deltaMotAtConv (n : Nat) (Γ : LCtx) {b p : Expr Nat}
    (hb : HasTyT deltaEqEnv n Γ b indexFn)
    (hp : HasTyT deltaEqEnv n Γ p (binderIndexFamily b)) :
    ConvT deltaEqEnv n Γ (.app (.app binderIndexMot b) p)
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
  have hbody := hasTyT_extendEnv (r := 66) (m := deltaEqMember) rfl
    (binderIndexMotBodyTy n Γ)
  have hc : ConvT deltaEqEnv n Γ (.app binderIndexMot b)
      (.lam (binderIndexFamily b) (.sort (.succ .zero)))
      (.pi (binderIndexFamily b) (.sort (.succ (.succ .zero)))) :=
    .beta _ _ _ _ _ _ (indexFnTy deltaEqEnv n Γ) hbody hb
  exact .trans _ _ _ _ _
    (.app _ _ _ _ _ _ _ hc (.refl _ _ _ hp))
    (.beta _ _ _ _ _ _ (deltaFamilyTy n Γ hb) (.sort _ _) hp)

/-- Native typing of the full recursor for any well-typed delta-environment index. -/
def deltaRecTy (n : Nat) (Γ : LCtx) {b p : Expr Nat}
    (hb : HasTyT deltaEqEnv n Γ b indexFn)
    (hp : HasTyT deltaEqEnv n Γ p (binderIndexFamily b)) :
    HasTyT deltaEqEnv n Γ
      (recCall (.const 65 [.succ (.succ .zero)])
        [indexFn, indexId, binderIndexMot, .sort .zero, b] p)
      (.sort (.succ .zero)) := by
  have hminor : HasTyT deltaEqEnv n Γ (.sort .zero)
      (.app (.app binderIndexMot indexId) binderIndexCtor) :=
    .conv _ _ _ _ _ (.sort _ _)
      (.symm _ _ _ _ (deltaMotAtConv n Γ
        (indexIdTy deltaEqEnv n Γ) (deltaCtorTy n Γ)))
  have hpre : HasTyT deltaEqEnv n Γ
      (foldApps (.const 65 [.succ (.succ .zero)])
        [indexFn, indexId, binderIndexMot, .sort .zero, b]) _ :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _
            (.app _ _ _ _ _ (.const _ 65 [.succ (.succ .zero)] eqRecT rfl rfl rfl)
              (indexFnTy deltaEqEnv n Γ)) (indexIdTy deltaEqEnv n Γ))
          (deltaMotTy n Γ)) hminor) hb
  have hres : HasTyT deltaEqEnv n Γ
      (recCall (.const 65 [.succ (.succ .zero)])
        [indexFn, indexId, binderIndexMot, .sort .zero, b] p)
      (.app (.app binderIndexMot b) p) := by
    have h := HasTyT.app Γ _ p (binderIndexFamily b)
      (.app (.app binderIndexMot (lift 0 1 b)) (.bvar 0)) hpre hp
    change HasTyT deltaEqEnv n Γ _
      (.app (.app binderIndexMot (instantiate0 p (lift 0 1 b))) p) at h
    simpa only [instantiate0, instantiate_lift_id] using h
  exact .conv _ _ _ _ _ hres (deltaMotAtConv n Γ hb hp)

def deltaRedex (b : Expr Nat) : Expr Nat :=
  recCall (.const 65 [.succ (.succ .zero)])
    [indexFn, indexId, binderIndexMot, .sort .zero, b] (.bvar 0)

/-- The full delta control is natively convertible to its minor; this uses the
existing variable-major K certification theorem after the explicit index conversion. -/
def deltaRedexConv (n : Nat) (Γ : LCtx) {b : Expr Nat}
    (hb : HasTyT deltaEqEnv n Γ b indexFn)
    (hp : HasTyT deltaEqEnv n Γ (.bvar 0) (binderIndexFamily b))
    (ci : ConvT deltaEqEnv n Γ b indexId indexFn) :
    ConvT deltaEqEnv n Γ (deltaRedex b) (.sort .zero) (.sort (.succ .zero)) := by
  have hf := eqFamilyPartialTy deltaEqExtends
    (indexFnTy deltaEqEnv n Γ) (indexIdTy deltaEqEnv n Γ)
  have cf : ConvT deltaEqEnv n Γ (binderIndexFamily indexId)
      (binderIndexFamily b) (.sort .zero) :=
    .app _ _ _ _ _ _ _ (.refl _ _ _ hf) (.symm _ _ _ _ ci)
  have hc : HasTyT deltaEqEnv n Γ binderIndexCtor (binderIndexFamily b) :=
    .conv _ _ _ _ _ (deltaCtorTy n Γ) cf
  exact convT_iotaStarK_bvar
    (w := eqConvW deltaEqExtends indexFn indexId b binderIndexMot (.sort .zero))
    hp hc (deltaFamilyTy n Γ hb) (deltaRecTy n Γ hb hc) (.sort _ _)
    (deltaRecTy n Γ hb hp)

def deltaHeadEqCtx : LCtx := [.assumption (binderIndexFamily (.const 66 []))]
def deltaUnderBinderEqCtx : LCtx := [.assumption (binderIndexFamily deltaBinderIndex)]

def deltaHeadEqCtxWf (n : Nat) : CtxWfT deltaEqEnv n deltaHeadEqCtx :=
  .assumption _ _ _ .nil (deltaFamilyTy n [] (deltaConstTy n []))

def deltaUnderBinderEqCtxWf (n : Nat) : CtxWfT deltaEqEnv n deltaUnderBinderEqCtx :=
  .assumption _ _ _ .nil (deltaFamilyTy n [] (deltaBinderTy n []))

theorem kNativeHead_delta (n : Nat) :
    KNativeHead deltaEqEnv n deltaHeadEqCtx (deltaRedex (.const 66 [])) (.sort .zero) :=
  kNativeHead_eq_of_indexConv deltaEqExtends binderIndexMot (.sort .zero)
    (indexFnTy deltaEqEnv n deltaHeadEqCtx) (indexIdTy deltaEqEnv n deltaHeadEqCtx)
    (deltaConstTy n deltaHeadEqCtx) (.bvar deltaHeadEqCtx 0 _ rfl)
    (deltaIndexConv n deltaHeadEqCtx) not_isCtorSpine_bvar

theorem kNativeHead_delta_under_binder (n : Nat) :
    KNativeHead deltaEqEnv n deltaUnderBinderEqCtx (deltaRedex deltaBinderIndex) (.sort .zero) :=
  kNativeHead_eq_of_indexConv deltaEqExtends binderIndexMot (.sort .zero)
    (indexFnTy deltaEqEnv n deltaUnderBinderEqCtx) (indexIdTy deltaEqEnv n deltaUnderBinderEqCtx)
    (deltaBinderTy n deltaUnderBinderEqCtx) (.bvar deltaUnderBinderEqCtx 0 _ rfl)
    (deltaBinderIndexConv n deltaUnderBinderEqCtx) not_isCtorSpine_bvar

/-- Delta at the head: native admission, full native conversion and repaired K. -/
theorem native_delta_control (n : Nat) :
    Nonempty (EnvWfT deltaEqEnv) ∧ Nonempty (CtxWfT deltaEqEnv n deltaHeadEqCtx) ∧
    Nonempty (ConvT deltaEqEnv n deltaHeadEqCtx (deltaRedex (.const 66 []))
      (.sort .zero) (.sort (.succ .zero))) ∧
    KNativeHead deltaEqEnv n deltaHeadEqCtx (deltaRedex (.const 66 [])) (.sort .zero) :=
  ⟨⟨deltaEqEnvWf⟩, ⟨deltaHeadEqCtxWf n⟩,
    ⟨deltaRedexConv n deltaHeadEqCtx (deltaConstTy n deltaHeadEqCtx)
      (.bvar deltaHeadEqCtx 0 _ rfl) (deltaIndexConv n deltaHeadEqCtx)⟩,
    kNativeHead_delta n⟩

/-- The same delta under a binder also succeeds through native conversion. -/
theorem native_delta_under_binder_control (n : Nat) :
    Nonempty (EnvWfT deltaEqEnv) ∧ Nonempty (CtxWfT deltaEqEnv n deltaUnderBinderEqCtx) ∧
    Nonempty (ConvT deltaEqEnv n deltaUnderBinderEqCtx (deltaRedex deltaBinderIndex)
      (.sort .zero) (.sort (.succ .zero))) ∧
    KNativeHead deltaEqEnv n deltaUnderBinderEqCtx (deltaRedex deltaBinderIndex) (.sort .zero) :=
  ⟨⟨deltaEqEnvWf⟩, ⟨deltaUnderBinderEqCtxWf n⟩,
    ⟨deltaRedexConv n deltaUnderBinderEqCtx (deltaBinderTy n deltaUnderBinderEqCtx)
      (.bvar deltaUnderBinderEqCtx 0 _ rfl) (deltaBinderIndexConv n deltaUnderBinderEqCtx)⟩,
    kNativeHead_delta_under_binder n⟩

-- BEGIN RCIC_NATIVE_READBACK_CK2_NATIVE_CONTROL_ROOTS
#print axioms kNativeHead_binder
#print axioms kNativeHead_eta
#print axioms native_binder_control
#print axioms native_eta_control
#print axioms deltaEqExtends
#print axioms deltaConstTy
#print axioms deltaBinderTy
#print axioms deltaFamilyTy
#print axioms deltaCtorTy
#print axioms deltaMotTy
#print axioms deltaMotAtConv
#print axioms deltaRecTy
#print axioms deltaRedex
#print axioms deltaRedexConv
#print axioms deltaHeadEqCtx
#print axioms deltaUnderBinderEqCtx
#print axioms deltaHeadEqCtxWf
#print axioms deltaUnderBinderEqCtxWf
#print axioms kNativeHead_delta
#print axioms kNativeHead_delta_under_binder
#print axioms native_delta_control
#print axioms native_delta_under_binder_control
-- END RCIC_NATIVE_READBACK_CK2_NATIVE_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
