import rcic.RcicNativeSpineHead
import rcic.RcicNativeHeadAdequacyObstruction
import rcic.RcicNativeKPartialPeak

set_option autoImplicit false

/-! A positive control for the exact admitted source that has no root-only
Pi observation. Both beta certificates are constructed. closure_claim = 0. -/

namespace Rcic.Declarative.NativeValleys.NativeSpineHead

open NativeHeadAdequacyObstruction NativePiHeadObs

private abbrev controlOne : Level := .succ .zero
private abbrev controlTwo : Level := .succ controlOne
private abbrev controlPiSort : Level := .imax controlOne controlOne

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

def spineFunctionStep (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) :
    Step E n Γ
      (.app (.lam (.sort controlOne) spineFunction) (.sort .zero))
      spineFunction (.pi (.sort controlOne) (.sort controlPiSort)) :=
  Step.beta hW hΓ (.sort controlOne) spineFunction (.sort .zero)
    (.pi (.sort controlOne) (.sort controlPiSort)) controlTwo
    (.sort Γ controlOne)
    (spineFunctionTy E n (.assumption (.sort controlOne) :: Γ))
    (.sort Γ .zero)

/-- Descent changes only the function, with its written native Pi index. -/
def spineFirstStep (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) :
    Step E n Γ spineSource (.app spineFunction (.sort .zero))
      (.sort controlPiSort) :=
  .appHead (spineFunctionStep hW hΓ) (.sort Γ .zero)

def spineSecondStep (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) :
    Step E n Γ (.app spineFunction (.sort .zero)) betaPiHead
      (.sort controlPiSort) :=
  Step.beta hW hΓ (.sort controlOne) betaPiHead (.sort .zero)
    (.sort controlPiSort) controlTwo (.sort Γ controlOne)
    (betaPiHeadTy E n (.assumption (.sort controlOne) :: Γ))
    (.sort Γ .zero)

def spineTrace (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) :
    SortTrace E n Γ spineSource betaPiHead :=
  .cons controlPiSort (spineFirstStep hW hΓ)
    (.cons controlPiSort (spineSecondStep hW hΓ) (.refl betaPiHead))

theorem spineTrace_isPriority (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) :
    (spineTrace hW hΓ).IsPriority := by
  simp only [spineTrace, SortTrace.IsPriority, spineFirstStep, spineFunctionStep,
    spineSecondStep, Step.beta, Step.IsPriority]
  exact ⟨⟨spineSource_headNormal E n Γ, True.intro⟩, True.intro, True.intro⟩

def spineTrace_nativeCert (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) :
    TyConvT E n Γ spineSource betaPiHead :=
  (spineTrace hW hΓ).toTyConv

/-- Closed positive control in the already admitted empty environment. -/
def admitted_spineTrace : SortTrace emptyEnv 0 [] spineSource betaPiHead :=
  spineTrace .empty .nil

theorem admitted_spineTrace_isPriority : admitted_spineTrace.IsPriority :=
  spineTrace_isPriority .empty .nil

/-- A well-formed let context whose stored value is the same literal Pi. -/
def localPiCtx : LCtx := [.letBinding (.sort controlPiSort) betaPiHead]

def localPiCtxWf (E : ResolvedEnv) (n : Nat) : CtxWfT E n localPiCtx :=
  .letBinding [] (.sort controlPiSort) (.succ controlPiSort) betaPiHead .nil
    (.sort [] controlPiSort) (betaPiHeadTy E n [])

/-- The context-aware computation is certified directly by native zetaLocal. -/
def localPiTrace (E : ResolvedEnv) (n : Nat) :
    SortTrace E n localPiCtx (.bvar 0) betaPiHead :=
  .single (.localZeta 0 (.sort controlPiSort) betaPiHead rfl rfl
    (betaPiHeadTy E n localPiCtx))

theorem localPiTrace_isPriority (E : ResolvedEnv) (n : Nat) :
    (localPiTrace E n).IsPriority := by
  simp only [localPiTrace, SortTrace.single, SortTrace.IsPriority, Step.IsPriority]
  exact ⟨True.intro, True.intro⟩

open StarStripUnitPeakAudit NativeKPartialPeakAudit

/-- The already admitted eta-K repair enters with its constructed native certificate. -/
def unitKSpineStep : Step trueEnvU 0 [] unitPartialRec unitContracted unitIndex :=
  .kRoot unitKStep (by trivial)

def unitKSpineTrace : Trace trueEnvU 0 [] unitPartialRec unitContracted unitIndex :=
  .single unitKSpineStep

/-- Supplemental eta-K support is not silently included in the priority theorem. -/
theorem unitKSpineStep_not_priority : ¬ unitKSpineStep.IsPriority := by
  simp only [unitKSpineStep, Step.IsPriority, not_false_eq_true]

end Rcic.Declarative.NativeValleys.NativeSpineHead
