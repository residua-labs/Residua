import rcic.RcicNativeTypedModelCovUOmegaCore
import rcic.RcicNormalizingFalsePinLoop

/-!
# A closed native cyclic proposition with a specified proposition as codomain

The existing admitted Loop recursor is reused at the minor `ih → P`.
Actual native constants supply `t : Loop` and `P : Prop`. Proof irrelevance,
one ordinary iota step, and two beta conversions give `X = X → P`.
No model interpretation or normalization premise is used. The environment
lookups and the two constant typings are explicit inputs to these helpers;
the eventual concrete boundary must supply them. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit ReadbackCK2Audit

def covUCycleBody (pref : Nat) : Expr Nat := .pi (.bvar 0) (.const pref [])
def covUCycleIhLam (pref : Nat) : Expr Nat :=
  .lam (.app loopMotTT (.bvar 0)) (covUCycleBody pref)
def covUCycleMinor (pref : Nat) : Expr Nat := .lam loopTyT (covUCycleIhLam pref)
def covUCycleF (pref : Nat) : Expr Nat :=
  .app (.app (.const 62 [.succ .zero]) loopMotTT) (covUCycleMinor pref)
def covUCycleX (pref tref : Nat) : Expr Nat := .app (covUCycleF pref) (.const tref [])

private def covUCycle_loopTy {E : ResolvedEnv} (n : Nat) (Γ : LCtx)
    (h60 : E.members 60 = some pinLoopFamT) :
    HasTyT E n Γ loopTyT (.sort .zero) :=
  .const Γ 60 [] pinLoopFamT h60 rfl rfl

private def covUCycle_mkTy {E : ResolvedEnv} (n : Nat) (Γ : LCtx)
    (h61 : E.members 61 = some pinLoopMkT) :
    HasTyT E n Γ (.const 61 []) (.pi loopTyT loopTyT) :=
  .const Γ 61 [] pinLoopMkT h61 rfl rfl

private def covUCycle_motiveTy {E : ResolvedEnv} (n : Nat) (Γ : LCtx)
    (h60 : E.members 60 = some pinLoopFamT) :
    HasTyT E n Γ loopMotTT (.pi loopTyT (.sort (.succ .zero))) :=
  .lam Γ loopTyT .zero _ _ (covUCycle_loopTy n Γ h60) (.sort _ .zero)

private def covUCycle_motiveBeta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h60 : E.members 60 = some pinLoopFamT) {a : Expr Nat}
    (ha : HasTyT E n Γ a loopTyT) :
    ConvT E n Γ (.app loopMotTT a) (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ loopTyT (.sort .zero) a (.sort (.succ .zero)) .zero
    (covUCycle_loopTy n Γ h60) (.sort _ .zero) ha

private def covUCycle_sortImax00 {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    ConvT E n Γ (.sort (.imax .zero .zero)) (.sort .zero) (.sort (.succ .zero)) :=
  .tyConv _ _ _ _ _ _ (.sorts _ _ _ eqN_imax00) (.sorts _ _ _ eqN_succ_imax00)

private def covUCycle_bodyTy {E : ResolvedEnv} {n : Nat} (pref : Nat) (Γ : LCtx)
    (h60 : E.members 60 = some pinLoopFamT)
    (h61 : E.members 61 = some pinLoopMkT)
    (hP : ∀ Δ, HasTyT E n Δ (.const pref []) (.sort .zero)) :
    HasTyT E n (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      (covUCycleBody pref) (.app loopMotTT (.app (.const 61 []) (.bvar 1))) := by
  have hl : HasTyT E n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      (.bvar 1) loopTyT := .bvar _ 1 _ rfl
  have hd : HasTyT E n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      (.bvar 0) (.sort .zero) :=
    .conv _ _ _ _ (.succ .zero) (.bvar _ 0 (.app loopMotTT (.bvar 1)) rfl)
      (covUCycle_motiveBeta h60 hl)
  have hp := HasTyT.pi _ (.bvar 0) .zero (.const pref []) .zero hd (hP _)
  have hm := covUCycle_motiveBeta h60
    (HasTyT.app _ _ _ _ _ (covUCycle_mkTy n _ h61) hl)
  exact .conv _ _ _ _ (.succ .zero) hp
    (.trans _ _ _ _ _ covUCycle_sortImax00 (.symm _ _ _ _ hm))

private def covUCycle_ihLamTy {E : ResolvedEnv} {n : Nat} (pref : Nat) (Γ : LCtx)
    (h60 : E.members 60 = some pinLoopFamT)
    (h61 : E.members 61 = some pinLoopMkT)
    (hP : ∀ Δ, HasTyT E n Δ (.const pref []) (.sort .zero)) :
    HasTyT E n (.assumption loopTyT :: Γ) (covUCycleIhLam pref)
      (.pi (.app loopMotTT (.bvar 0))
        (.app loopMotTT (.app (.const 61 []) (.bvar 1)))) :=
  .lam _ _ (.succ .zero) _ _
    (.app _ _ _ _ _ (covUCycle_motiveTy n _ h60) (.bvar _ 0 loopTyT rfl))
    (covUCycle_bodyTy pref Γ h60 h61 hP)

private def covUCycle_minorTy {E : ResolvedEnv} {n : Nat} (pref : Nat) (Γ : LCtx)
    (h60 : E.members 60 = some pinLoopFamT)
    (h61 : E.members 61 = some pinLoopMkT)
    (hP : ∀ Δ, HasTyT E n Δ (.const pref []) (.sort .zero)) :
    HasTyT E n Γ (covUCycleMinor pref)
      (.pi loopTyT (.pi (.app loopMotTT (.bvar 0))
        (.app loopMotTT (.app (.const 61 []) (.bvar 1))))) :=
  .lam Γ loopTyT .zero _ _ (covUCycle_loopTy n Γ h60)
    (covUCycle_ihLamTy pref Γ h60 h61 hP)

private def covUCycle_fTy {E : ResolvedEnv} {n : Nat} (pref : Nat) (Γ : LCtx)
    (h60 : E.members 60 = some pinLoopFamT)
    (h61 : E.members 61 = some pinLoopMkT)
    (h62 : E.members 62 = some pinLoopRecT)
    (hP : ∀ Δ, HasTyT E n Δ (.const pref []) (.sort .zero)) :
    HasTyT E n Γ (covUCycleF pref) (.pi loopTyT (.app loopMotTT (.bvar 0))) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (.const Γ 62 [.succ .zero] pinLoopRecT h62 rfl rfl)
      (covUCycle_motiveTy n Γ h60))
    (covUCycle_minorTy pref Γ h60 h61 hP)

def covUCycleX_hasTy {E : ResolvedEnv} {n : Nat} (pref tref : Nat) (Γ : LCtx)
    (h60 : E.members 60 = some pinLoopFamT)
    (h61 : E.members 61 = some pinLoopMkT)
    (h62 : E.members 62 = some pinLoopRecT)
    (hP : ∀ Δ, HasTyT E n Δ (.const pref []) (.sort .zero))
    (ht : ∀ Δ, HasTyT E n Δ (.const tref []) loopTyT) :
    HasTyT E n Γ (covUCycleX pref tref) (.sort .zero) :=
  .conv _ _ _ _ (.succ .zero)
    (.app _ _ _ _ _ (covUCycle_fTy pref Γ h60 h61 h62 hP) (ht Γ))
    (covUCycle_motiveBeta h60 (ht Γ))

/-- Only the proof fields and the actual minor/field are changed from the
landed ordinary Loop witness. -/
def covUCycleWitness {E : ResolvedEnv} (pref tref : Nat)
    (h60 : E.members 60 = some pinLoopFamT)
    (h61 : E.members 61 = some pinLoopMkT)
    (h62 : E.members 62 = some pinLoopRecT) : IotaWitness E :=
  { pinLoopWitness with
    hrec := h62
    hctor := h61
    hfam := h60
    preMajor := [loopMotTT, covUCycleMinor pref]
    fields := [.const tref []]
    minor := covUCycleMinor pref
    hminor := rfl }

/-- The cycle is derived using native irrelevance, ordinary iota and beta.
The target P is the actual supplied proposition constant. -/
def covUCycle_conversion {E : ResolvedEnv} {n : Nat} (pref tref : Nat) (Γ : LCtx)
    (h60 : E.members 60 = some pinLoopFamT)
    (h61 : E.members 61 = some pinLoopMkT)
    (h62 : E.members 62 = some pinLoopRecT)
    (hP : ∀ Δ, HasTyT E n Δ (.const pref []) (.sort .zero))
    (ht : ∀ Δ, HasTyT E n Δ (.const tref []) loopTyT) :
    ConvT E n Γ (covUCycleX pref tref)
      (.pi (covUCycleX pref tref) (.const pref [])) (.sort .zero) := by
  have hf := covUCycle_fTy pref Γ h60 h61 h62 hP
  have hm := covUCycle_minorTy pref Γ h60 h61 hP
  have hmk := HasTyT.app _ _ _ _ _ (covUCycle_mkTy n Γ h61) (ht Γ)
  have hx : HasTyT E n Γ (covUCycleX pref tref)
      (.app loopMotTT (.const tref [])) := .app _ _ _ _ _ hf (ht Γ)
  have hirr : ConvT E n Γ (.const tref []) (.app (.const 61 []) (.const tref []))
      loopTyT := .irr _ _ _ _ (covUCycle_loopTy n Γ h60) (ht Γ) hmk
  have hmajor : ConvT E n Γ (covUCycleX pref tref)
      (.app (covUCycleF pref) (.app (.const 61 []) (.const tref [])))
      (.app loopMotTT (.const tref [])) :=
    .app _ _ _ _ _ _ _ (.refl _ _ _ hf) hirr
  have hiota : ConvT E n Γ
      (.app (covUCycleF pref) (.app (.const 61 []) (.const tref [])))
      (.app (.app (covUCycleMinor pref) (.const tref [])) (covUCycleX pref tref))
      (.app loopMotTT (.app (.const 61 []) (.const tref []))) :=
    .iota _ _ _ _ (.of (covUCycleWitness pref tref h60 h61 h62))
      (.app _ _ _ _ _ hf hmk)
      (.app _ _ _ _ _ (.app _ _ _ _ _ hm (ht Γ)) hx)
  have hb1 : ConvT E n Γ (.app (covUCycleMinor pref) (.const tref []))
      (.lam (.app loopMotTT (.const tref [])) (covUCycleBody pref))
      (.pi (.app loopMotTT (.const tref []))
        (.app loopMotTT (.app (.const 61 []) (.const tref [])))) :=
    .beta Γ loopTyT (covUCycleIhLam pref) (.const tref []) _ .zero
      (covUCycle_loopTy n Γ h60) (covUCycle_ihLamTy pref Γ h60 h61 hP) (ht Γ)
  have hbody : HasTyT E n (.assumption (.app loopMotTT (.const tref [])) :: Γ)
      (covUCycleBody pref) (.app loopMotTT (.app (.const 61 []) (.const tref []))) := by
    have hd : HasTyT E n (.assumption (.app loopMotTT (.const tref [])) :: Γ)
        (.bvar 0) (.sort .zero) :=
      .conv _ _ _ _ (.succ .zero) (.bvar _ 0 (.app loopMotTT (.const tref [])) rfl)
        (covUCycle_motiveBeta h60 (ht _))
    have hp := HasTyT.pi _ (.bvar 0) .zero (.const pref []) .zero hd (hP _)
    have hmb := covUCycle_motiveBeta
      (Γ := .assumption (.app loopMotTT (.const tref [])) :: Γ) h60
      (HasTyT.app _ _ _ _ _ (covUCycle_mkTy n _ h61) (ht _))
    exact .conv _ _ _ _ (.succ .zero) hp
      (.trans _ _ _ _ _ covUCycle_sortImax00 (.symm _ _ _ _ hmb))
  have hb2 : ConvT E n Γ
      (.app (.lam (.app loopMotTT (.const tref [])) (covUCycleBody pref))
        (covUCycleX pref tref))
      (.pi (covUCycleX pref tref) (.const pref []))
      (.app loopMotTT (.app (.const 61 []) (.const tref []))) :=
    .beta Γ (.app loopMotTT (.const tref [])) (covUCycleBody pref)
      (covUCycleX pref tref) _ (.succ .zero)
      (.app _ _ _ _ _ (covUCycle_motiveTy n Γ h60) (ht Γ)) hbody hx
  have hb1app : ConvT E n Γ
      (.app (.app (covUCycleMinor pref) (.const tref [])) (covUCycleX pref tref))
      (.app (.lam (.app loopMotTT (.const tref [])) (covUCycleBody pref))
        (covUCycleX pref tref))
      (.app loopMotTT (.app (.const 61 []) (.const tref []))) :=
    .app _ _ _ _ _ _ _ hb1 (.refl _ _ _ hx)
  exact .trans _ _ _ _ _
    (.tyConv _ _ _ _ _ _ hmajor (covUCycle_motiveBeta h60 (ht Γ)))
    (.tyConv _ _ _ _ _ _
      (.trans _ _ _ _ _ hiota (.trans _ _ _ _ _ hb1app hb2))
      (covUCycle_motiveBeta h60 hmk))

theorem covUCycleX_closed (pref tref k : Nat) : lift k 1 (covUCycleX pref tref) =
    covUCycleX pref tref := by
  simp [covUCycleX, covUCycleF, covUCycleMinor, covUCycleIhLam, covUCycleBody,
    loopMotTT, loopTyT, lift]

/-- A concrete cyclic conversion pays the typing premise of self-application.
The eventual environment witness, not this helper, supplies the two constants. -/
def covUCycle_omega_hasTy {E : ResolvedEnv} {n : Nat} (pref tref : Nat) (Γ : LCtx)
    (hW : EnvWfT E)
    (h60 : E.members 60 = some pinLoopFamT)
    (h61 : E.members 61 = some pinLoopMkT)
    (h62 : E.members 62 = some pinLoopRecT)
    (hP : ∀ Δ, HasTyT E n Δ (.const pref []) (.sort .zero))
    (ht : ∀ Δ, HasTyT E n Δ (.const tref []) loopTyT) :
    HasTyT E n Γ (covUOmega (covUCycleX pref tref)) (.const pref []) :=
  covUOmega_hasTy_of_cycle hW (covUCycleX_closed pref tref) (fun _ => rfl)
    (covUCycleX_hasTy pref tref Γ h60 h61 h62 hP ht)
    (covUCycle_conversion pref tref Γ h60 h61 h62 hP ht)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_U_CYCLE_ROOTS
#print axioms covUCycleBody
#print axioms covUCycleIhLam
#print axioms covUCycleMinor
#print axioms covUCycleF
#print axioms covUCycleX
#print axioms covUCycleX_hasTy
#print axioms covUCycleWitness
#print axioms covUCycle_conversion
#print axioms covUCycleX_closed
#print axioms covUCycle_omega_hasTy
-- END RCIC_NATIVE_TYPED_MODEL_COV_U_CYCLE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit
