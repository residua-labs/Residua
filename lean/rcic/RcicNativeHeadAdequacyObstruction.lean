import rcic.RcicNativePiHeadObs

set_option autoImplicit false

/-!
# A native beta-spine obstruction to root-only head adequacy

The paper's logical relation observes weak head reduction through a
function spine. The landed `HeadStepT` deliberately contracts only roots.
These are different contracts. This module constructs a closed, typed
two-argument beta example in admitted `emptyEnv`, with a native conversion
to a literal Pi, and proves that the source has no `HeadStepT` successor
at any index. Thus no finite `HeadTrace` can observe its Pi head.

This refutes observation production for this particular root-only
relation, not Pi injectivity or the paper's semantic method. In particular,
adding an unproved conversion-closure field to `PiHeadObs` would give a
false contract already in the beta fragment, before proof irrelevance,
eta, K, or family admission is involved.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativeHeadAdequacyObstruction

open NativePiHeadObs

private abbrev one : Level := .succ .zero
private abbrev two : Level := .succ one
private abbrev piSort : Level := .imax one one

/-- The inner lambda, whose one-argument beta redex is the already
constructed `betaPiSource`. -/
def spineFunction : Expr Nat := .lam (.sort one) betaPiHead

/-- Two arguments are present. The leftmost beta redex lies inside the
outer function position, outside the landed root-only contraction set. -/
def spineSource : Expr Nat :=
  .app (.app (.lam (.sort one) spineFunction) (.sort .zero)) (.sort .zero)

def spineFunctionTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ spineFunction (.pi (.sort one) (.sort piSort)) :=
  .lam Γ (.sort one) two betaPiHead (.sort piSort) (.sort _ _)
    (betaPiHeadTy E n (.assumption (.sort one) :: Γ))

/-- The first beta conversion, still at a function type. -/
def spineFunctionBeta (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ConvT E n Γ (.app (.lam (.sort one) spineFunction) (.sort .zero))
      spineFunction (.pi (.sort one) (.sort piSort)) :=
  .beta Γ (.sort one) spineFunction (.sort .zero)
    (.pi (.sort one) (.sort piSort)) two (.sort _ _)
    (spineFunctionTy E n (.assumption (.sort one) :: Γ)) (.sort _ _)

/-- Native application congruence performs the function-spine step.
Both of its children are constructed, with their written Pi data. -/
def spineCongruence (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ConvT E n Γ spineSource betaPiSource (.sort piSort) :=
  .app Γ _ _ (.sort .zero) (.sort .zero) (.sort one) (.sort piSort)
    (spineFunctionBeta E n Γ) (.refl _ _ _ (.sort _ _))

/-- A native sorting-indexed conversion from the stuck root-only source
to a literal Pi. The second leg is the ordinary root beta rule. -/
def spineConversion (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ConvT E n Γ spineSource betaPiHead (.sort piSort) :=
  .trans Γ _ _ _ _ (spineCongruence E n Γ)
    (.beta Γ (.sort one) betaPiHead (.sort .zero) (.sort piSort) two
      (.sort _ _) (betaPiHeadTy E n (.assumption (.sort one) :: Γ)) (.sort _ _))

def spineSourceTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ spineSource (.sort piSort) :=
  .app Γ _ _ (.sort one) (.sort piSort)
    (.app Γ _ _ (.sort one) (.pi (.sort one) (.sort piSort))
      (.lam Γ (.sort one) two spineFunction (.pi (.sort one) (.sort piSort))
        (.sort _ _) (spineFunctionTy E n (.assumption (.sort one) :: Γ)))
      (.sort _ _))
    (.sort _ _)

/-- The source's spine head is a lambda, so it cannot be a recursor
call; its immediate function is an application, so it is not root beta. -/
theorem spineSource_headNormal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HeadNormal E n Γ spineSource := by
  intro z T h
  cases headStepT_inv_app h (show spineSource = .app
      (.app (.lam (.sort one) spineFunction) (.sort .zero)) (.sort .zero) from rfl) with
  | beta A body B u v w hf hz => exact Expr.noConfusion hf
  | iota w heq hz =>
      have he := congrArg appsSpine heq
      rw [headStepT_iotaLhs_spine] at he
      exact Expr.noConfusion (congrArg Prod.fst he)
  | iotaStarK w major Tm rl afs heq hfam hmajor hcv hn hfields hz =>
      have he := congrArg appsSpine heq
      rw [appsSpine_recCall] at he
      exact Expr.noConfusion (congrArg Prod.fst he)
  | iotaStarKField w major Tm rl afs heq hfam hmajor hcv hn hfields hnctor hz =>
      have he := congrArg appsSpine heq
      rw [appsSpine_recCall] at he
      exact Expr.noConfusion (congrArg Prod.fst he)

/-- No finite root-contraction observation can expose a Pi from this
source, independently of the proposed observed components. -/
theorem spineSource_no_pi_trace {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B : Expr Nat} (h : HeadTrace E n Γ spineSource (.pi A B)) : False :=
  Expr.noConfusion (HeadTrace.eq_of_normal h (spineSource_headNormal E n Γ))

theorem spineSource_no_observation {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Expr Nat} (h : PiHeadObs E n Γ spineSource t) : False :=
  spineSource_no_pi_trace h.leftTrace

/-- Exact false conversion-closure contract for the current root-only
observations. It is named for a negative test, never assumed by a
positive consumer. -/
def RootPiObservationTransfer (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b t : Expr Nat},
    TyConvT E n Γ a b → PiHeadObs E n Γ b t → PiHeadObs E n Γ a t

/-- An admitted-environment counterexample, with its actual environment
and context witnesses, native typing and conversion. -/
def admitted_beta_spine :
    EnvWfT emptyEnv × CtxWfT emptyEnv 0 [] ×
      HasTyT emptyEnv 0 [] spineSource (.sort piSort) ×
      ConvT emptyEnv 0 [] spineSource betaPiHead (.sort piSort) :=
  ⟨.empty, .nil, spineSourceTy emptyEnv 0 [], spineConversion emptyEnv 0 []⟩

/-- Even admitted emptyEnv refutes unrestricted native conversion
closure of the existing root-only Pi observations. -/
theorem admitted_no_rootPiObservationTransfer
    (transfer : RootPiObservationTransfer emptyEnv 0) : False :=
  spineSource_no_observation
    (transfer .nil (.of _ _ _ _ (spineConversion emptyEnv 0 []))
      (PiHeadObs.refl (.sort .zero) (.sort .zero)))

#print axioms spineFunctionBeta
#print axioms spineCongruence
#print axioms spineConversion
#print axioms spineSource_headNormal
#print axioms spineSource_no_pi_trace
#print axioms admitted_beta_spine
#print axioms admitted_no_rootPiObservationTransfer

end Rcic.Declarative.NativeValleys.NativeHeadAdequacyObstruction
