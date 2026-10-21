import rcic.RcicNativeTypedModelCovWNativeFollowupSeal

/-!
An explicit native-convertible Pi pair separates weak-head CK2 valleys from the
NativeValley interface.  The pair has native typing at one common universe and
an actual NativeValley; neither endpoint has an outgoing weak-head CK2 step.

This file does not refute PiConvValleyData.  ParRedT.pi can use the native beta
conversion between the domains, while weak-head CK2 does not inspect a Pi body
or domain.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open FamModelLRSAudit ReadbackCKAudit ReadbackCK2Audit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

private def u1 : Level := .succ .zero
private def u2 : Level := .succ u1

/-- A closed beta redex whose native type is `Sort 2`. -/
def convValleyDomain : Expr Nat :=
  .app (.lam (.sort u2) (.bvar 0)) (.sort u1)

def convValleyPiLeft : Expr Nat :=
  .pi convValleyDomain (.sort u1)

def convValleyPiRight : Expr Nat :=
  .pi (.sort u1) (.sort u1)

/-- Keep the universe syntax exact: no universe-normalization theorem is used. -/
def convValleyUniverse : Expr Nat :=
  .sort (.imax u2 u2)

def convValleyDomain_hasTy :
    HasTyT E n Γ convValleyDomain (.sort u2) := by
  have hDomain :
      HasTyT E n Γ (.sort u2) (.sort (.succ u2)) :=
    .sort Γ u2
  have hBody :
      HasTyT E n (.assumption (.sort u2) :: Γ)
        (.bvar 0) (.sort u2) :=
    .bvar (.assumption (.sort u2) :: Γ) 0 (.sort u2) rfl
  have hFn :
      HasTyT E n Γ (.lam (.sort u2) (.bvar 0))
        (.pi (.sort u2) (.sort u2)) :=
    .lam Γ (.sort u2) (.succ u2) (.bvar 0) (.sort u2)
      hDomain hBody
  have hArg : HasTyT E n Γ (.sort u1) (.sort u2) :=
    .sort Γ u1
  exact .app Γ (.lam (.sort u2) (.bvar 0)) (.sort u1)
    (.sort u2) (.sort u2) hFn hArg

def convValleyDomain_conv :
    ConvT E n Γ convValleyDomain (.sort u1) (.sort u2) := by
  exact .beta Γ (.sort u2) (.bvar 0) (.sort u1) (.sort u2)
    (.succ u2)
    (.sort Γ u2)
    (.bvar (.assumption (.sort u2) :: Γ) 0 (.sort u2) rfl)
    (.sort Γ u1)

def convValleyPiLeft_hasTy :
    HasTyT E n Γ convValleyPiLeft convValleyUniverse := by
  exact .pi Γ convValleyDomain u2 (.sort u1) u2
    convValleyDomain_hasTy
    (.sort (.assumption convValleyDomain :: Γ) u1)

def convValleyPiRight_hasTy :
    HasTyT E n Γ convValleyPiRight convValleyUniverse := by
  exact .pi Γ (.sort u1) u2 (.sort u1) u2
    (.sort Γ u1)
    (.sort (.assumption (.sort u1) :: Γ) u1)

def convValleyPi_nativeConv :
    ConvT E n Γ convValleyPiLeft convValleyPiRight
      convValleyUniverse := by
  exact .pi Γ convValleyDomain (.sort u1) (.sort u1) (.sort u1)
    u2 u2
    convValleyDomain_conv
    (.refl (.assumption convValleyDomain :: Γ)
      (.sort u1) (.sort u2)
      (.sort (.assumption convValleyDomain :: Γ) u1))

theorem convValleyPi_distinct :
    convValleyPiLeft ≠ convValleyPiRight := by
  intro h
  cases h

/-- NativeValley is inhabited directly, without assuming PiInj or SortRetype. -/
def convValleyPi_actualNativeValley :
    NativeValley E n Γ convValleyPiLeft convValleyPiRight
      convValleyUniverse where
  centre := convValleyPiRight
  left := .tail
    (.pi Γ convValleyDomain (.sort u1) (.sort u1) (.sort u1)
      u2 u2
      convValleyDomain_hasTy
      convValleyDomain_conv
      (.sort (.assumption convValleyDomain :: Γ) u1)
      (.refl (.assumption convValleyDomain :: Γ)
        (.sort u1) (.sort u2)
        (.sort (.assumption convValleyDomain :: Γ) u1))
      convValleyPiRight_hasTy)
    (.refl Γ convValleyPiRight convValleyUniverse
      convValleyPiRight_hasTy)
  right := .refl Γ convValleyPiRight convValleyUniverse
    convValleyPiRight_hasTy

/-- Both Pi heads are CK2-normal, so distinct endpoints cannot join under CK2. -/
theorem convValleyPi_noCK2Valley :
    ¬ ∃ centre : Expr Nat,
      RedR (WhStepCK2 E n) Γ convValleyPiLeft centre ∧
      RedR (WhStepCK2 E n) Γ convValleyPiRight centre := by
  rintro ⟨centre, hLeft, hRight⟩
  have hLeftEq : centre = convValleyPiLeft :=
    redR_of_normal
      (normalR_piCK2 Γ convValleyDomain (.sort u1)) hLeft
  have hRightEq : centre = convValleyPiRight :=
    redR_of_normal
      (normalR_piCK2 Γ (.sort u1) (.sort u1)) hRight
  exact convValleyPi_distinct (hLeftEq.symm.trans hRightEq)

/--
The prospective CK2 requirement, with actual typing of both Pi endpoints and
their native conversion all at the same type.  This is a CK2 property, not the
landed PiConvValleyData contract.
-/
def CovWConvCK2PiValleys (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ (Γ : LCtx) (A₁ A₂ B₁ B₂ T : Expr Nat),
    HasTyT E n Γ (.pi A₁ B₁) T →
    HasTyT E n Γ (.pi A₂ B₂) T →
    ConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) T →
    ∃ centre : Expr Nat,
      RedR (WhStepCK2 E n) Γ (.pi A₁ B₁) centre ∧
      RedR (WhStepCK2 E n) Γ (.pi A₂ B₂) centre

theorem not_CovWConvCK2PiValleys :
    ¬ CovWConvCK2PiValleys E n := by
  intro h
  have hValley := h [] convValleyDomain (.sort u1)
    (.sort u1) (.sort u1) convValleyUniverse
    convValleyPiLeft_hasTy convValleyPiRight_hasTy convValleyPi_nativeConv
  exact convValleyPi_noCK2Valley (Γ := []) hValley

/--
An explicitly inhabited witness package in the empty context.  It exhibits
native typing, native conversion, and an actual NativeValley alongside the
failure of the CK2 valley.  No uninhabited environment premise is used.
-/
theorem covWConvCK2PiValleys_inhabited_counterexample :
    ∃ P Q T : Expr Nat,
      Nonempty (HasTyT E n [] P T) ∧
      Nonempty (HasTyT E n [] Q T) ∧
      Nonempty (ConvT E n [] P Q T) ∧
      Nonempty (NativeValley E n [] P Q T) ∧
      ¬ ∃ centre : Expr Nat,
        RedR (WhStepCK2 E n) [] P centre ∧
        RedR (WhStepCK2 E n) [] Q centre := by
  exact ⟨convValleyPiLeft, convValleyPiRight, convValleyUniverse,
    ⟨convValleyPiLeft_hasTy⟩, ⟨convValleyPiRight_hasTy⟩,
    ⟨convValleyPi_nativeConv⟩, ⟨convValleyPi_actualNativeValley⟩,
    convValleyPi_noCK2Valley⟩

#print axioms convValleyDomain_hasTy
#print axioms convValleyDomain_conv
#print axioms convValleyPiLeft_hasTy
#print axioms convValleyPiRight_hasTy
#print axioms convValleyPi_nativeConv
#print axioms convValleyPi_actualNativeValley
#print axioms convValleyPi_noCK2Valley
#print axioms not_CovWConvCK2PiValleys
#print axioms covWConvCK2PiValleys_inhabited_counterexample

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
