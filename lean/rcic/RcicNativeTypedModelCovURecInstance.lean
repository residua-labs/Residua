import rcic.RcicNativeTypedModelCovURealized
import rcic.RcicNativeTypedModelCovTRecursor
import rcic.RcicNativeTypedModelCovTViewFixtures

/-!
# Native instances of the type-valued Nat recursor control

The semantic successor demand is realized by the closed native `succ zero`.
The old open recursor consequently has a native sort readback after this
substitution.  These supplies address the concrete earlier witness; they do
not assert observation soundness for every old-model rule.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovPAudit TypedModelCovRAudit TypedModelCovSAudit

def covURecMajor : Expr Nat := .app (.const 2 []) (.const 1 [])

def covURecSubst : SubstT := fun _ => covURecMajor

def covURecMajor_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ covURecMajor (.const 0 []) :=
  .app Γ _ _ _ _ (hasTyT_natEnvU_succ n Γ) (hasTyT_natEnvU_zero n Γ)

theorem covURecMajor_observed (n : Nat) :
    ApproxTKStage natEnvU n 1 [] EnvT.bot covURecMajor covTRecMajorCode := by
  refine ⟨.free (kFreeT_natEnvU _) ?_, by simp [covTObservationBudget, covTRecMajorCode]⟩
  exact .appSpine
    (.const EnvT.bot 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ)
    (.bot _ _)

theorem covURecSubst_typed (n : Nat) :
    TypedSubstT natEnvU n [] covURecSubst covTRecCtx := by
  constructor
  · intro i A hi
    cases i with
    | zero =>
        obtain rfl := Option.some.inj hi
        exact ⟨covURecMajor_hasTy n []⟩
    | succ i => simp [covTRecCtx, lookupType] at hi
  · intro i v hi
    cases i with
    | zero => cases hi
    | succ i => simp [covTRecCtx, lookupValue] at hi

theorem covURecEnv_realized (n : Nat) :
    CovTRealized natEnvU n 1 covTRecCtx covTRecEnv covURecSubst := by
  refine ⟨covURecSubst_typed n, ?_⟩
  intro i c hc
  cases i with
  | zero =>
      change c = covTRecMajorCode at hc
      subst c
      exact covURecMajor_observed n
  | succ i =>
      change c = .bot at hc
      subst c
      exact approxTKStage_bot _ _ _ _ _ _

def covURecInstance : Expr Nat := substT covURecSubst (covTRecTypeAt 0)

def covURecInstance_hasTy (n : Nat) :
    HasTyT natEnvU n [] covURecInstance (.sort (.succ .zero)) := by
  exact hasTyT_subst0_of_envWfT natEnvUWfT
    (covTRecTypeAt_hasTy n covTRecCtx 0 (.bvar _ 0 _ rfl))
    (covURecMajor_hasTy n [])

theorem covURecInstance_observed (n : Nat) :
    ApproxTKStage natEnvU n 1 [] EnvT.bot covURecInstance .prop := by
  apply (covURecEnv_realized n).stage_of_kFree (kFreeT_natEnvU _)
  exact ⟨covTRecTypeAt_observed n covTRecCtx covTRecEnv 0 rfl,
    by simp [covTObservationBudget]⟩

/-- The existing admitted successor witness, at these actual native arguments. -/
def covURecWitness : IotaWitness natEnvU :=
  { wSuccU with
    ls := [.succ (.succ .zero)]
    preMajor := [covTRecMotive, .sort .zero, covTRecMinor]
    fields := [.const 1 []]
    minor := covTRecMinor
    hminor := rfl }

theorem covURecInstance_read (n : Nat) :
    RedR (WhStepCK2 natEnvU n) [] covURecInstance (.sort .zero) := by
  exact .step (.ctx (.iota (.ofU covURecWitness)))
    (.step (.ctx (.appHead (.beta _ _ _)))
      (.step (.ctx (.beta _ _ _)) (.refl _)))

theorem covURecInstance_head_observed (n : Nat) :
    Nonempty (HasTyT natEnvU n [] covURecInstance (.sort (.succ .zero))) ∧
    ApproxTKStage natEnvU n 1 [] EnvT.bot covURecInstance .prop ∧
    RedR (WhStepCK2 natEnvU n) [] covURecInstance (.sort .zero) ∧
    ApproxTKStage natEnvU n 1 [] EnvT.bot (.sort .zero) .prop :=
  ⟨⟨covURecInstance_hasTy n⟩, covURecInstance_observed n,
    covURecInstance_read n,
    ⟨approxTK_sort_code natEnvU n [] EnvT.bot .zero, by simp [covTObservationBudget]⟩⟩

/-- Both type-variable origins are realized by the closed native `Prop`.
The tail also realizes the source valuation's out-of-scope entries. -/
def covUOriginSubst : SubstT := fun _ => .sort .zero

theorem covUOriginEnv_realized (E : ResolvedEnv) (n : Nat) :
    CovTRealized E n 1 covSOriginCtx covSOriginEnv covUOriginSubst := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro i A hi
      obtain rfl := covSOrigin_lookup hi
      exact ⟨.sort [] .zero⟩
    · intro i v hi
      cases i with
      | zero => cases hi
      | succ i =>
          cases i with
          | zero => cases hi
          | succ i => simp [covSOriginCtx, lookupValue] at hi
  · intro i c hc
    change c = .prop at hc
    subst c
    exact ⟨approxTK_sort_code E n [] EnvT.bot .zero, by simp [covTObservationBudget]⟩

/-- A concrete closing substitution for the Eq-gap fixture context:
`α := Prop`, `a := (Π P : Prop, P)`, and the equality proof is reflexivity,
cast along the actual beta-redex index. -/
def covUEqProof : Expr Nat :=
  foldApps (.const 64 []) [.sort .zero, idPiProp]

def covUEqSubst : SubstT
  | 0 => covUEqProof
  | 1 => idPiProp
  | _ + 2 => .sort .zero

def covUEqProof_hasTy (n : Nat) :
    HasTyT eqEnvT n [] covUEqProof
      (foldApps (.const 63 []) [.sort .zero, idPiProp,
        .app (.lam (.sort .zero) (.bvar 0)) idPiProp]) := by
  have hP := hasTyT_idPiProp_ctx eqEnvT n []
  have hf := eqFamilyPartialTy (E := eqEnvT) (fun _ _ h => h)
    (.sort [] .zero) hP
  have hr := eqReflApplyTy (E := eqEnvT) (fun _ _ h => h)
    (.sort [] .zero) hP
  have hb : ConvT eqEnvT n []
      (.app (.lam (.sort .zero) (.bvar 0)) idPiProp) idPiProp (.sort .zero) :=
    .beta [] (.sort .zero) (.bvar 0) idPiProp (.sort .zero) (.succ .zero)
      (.sort [] .zero) (.bvar _ 0 _ rfl) hP
  exact .conv [] _ _ _ .zero hr
    (.app [] _ _ _ _ _ _ (.refl [] _ _ hf) (.symm [] _ _ _ hb))

theorem covUEqSubst_typed (n : Nat) :
    TypedSubstT eqEnvT n [] covUEqSubst eqGapCtx := by
  constructor
  · intro i A hi
    cases i with
    | zero =>
        obtain rfl := Option.some.inj hi
        exact ⟨covUEqProof_hasTy n⟩
    | succ i =>
        cases i with
        | zero =>
            obtain rfl := Option.some.inj hi
            exact ⟨hasTyT_idPiProp_ctx eqEnvT n []⟩
        | succ i =>
            cases i with
            | zero =>
                obtain rfl := Option.some.inj hi
                exact ⟨.sort [] .zero⟩
            | succ i => simp [eqGapCtx, lookupType] at hi
  · intro i v hi
    cases i with
    | zero => cases hi
    | succ i =>
        cases i with
        | zero => cases hi
        | succ i =>
            cases i with
            | zero => cases hi
            | succ i => simp [eqGapCtx, lookupValue] at hi

/-- This same realizer covers the alias-in-Pi, alias-extension value and
Eq-anchor rows, and the exact relevant-function replay, at their bottom
valuations.  It does not require closing the additional assumption mentioned
only by the alias-extension row's context-well-formedness control. -/
theorem covUEqEnv_realized (n stage : Nat) :
    CovTRealized eqEnvT n stage eqGapCtx EnvT.bot covUEqSubst :=
  covU_realized_bot_of_typed (covUEqSubst_typed n)

def covUSubstitutionSubst : SubstT := fun _ => cexPolyIdTy

theorem covUSubstitutionEnv_realized (E : ResolvedEnv) (n : Nat) :
    CovTRealized E n (covTObservationBudget covSSubstitutionDeep)
      covSSubstitutionCtx covSSubstitutionEnv covUSubstitutionSubst := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro i A hi
      cases i with
      | zero =>
          obtain rfl := Option.some.inj hi
          exact ⟨covSSubstitution_argument_hasTy E n []⟩
      | succ i => simp [covSSubstitutionCtx, lookupType] at hi
    · intro i v hi
      cases i with
      | zero => cases hi
      | succ i => simp [covSSubstitutionCtx, lookupValue] at hi
  · intro i c hc
    cases i with
    | zero =>
        obtain rfl := List.mem_singleton.mp hc
        exact ⟨covSSubstitution_deep_observed E n [] EnvT.bot, Nat.le_refl _⟩
    | succ i =>
        change c = .bot at hc
        subst c
        exact approxTKStage_bot _ _ _ _ _ _

def covURecZero : Expr Nat :=
  recCall (.const 3 [.succ (.succ .zero)])
    [covTRecMotive, .sort .zero, covTRecMinor] (.const 1 [])

def covURecZero_hasTy (n : Nat) :
    HasTyT natEnvU n [] covURecZero (.sort (.succ .zero)) :=
  hasTyT_subst0_of_envWfT natEnvUWfT
    (covTRecTypeAt_hasTy n covTRecCtx 0 (.bvar _ 0 _ rfl))
    (hasTyT_natEnvU_zero n [])

def covURecZero_motive_hasTy (n : Nat) :
    HasTyT natEnvU n [] covURecZero (.app covTRecMotive (.const 1 [])) :=
  .conv [] _ _ _ (.succ (.succ .zero)) (covURecZero_hasTy n)
    (.symm [] _ _ _
      (covTRecMotive_beta n [] (.const 1 []) (hasTyT_natEnvU_zero n [])))

/-- A second native typing of the actual minor, with its already constant
codomain displayed as Sort 1. This does not change the recursor declaration. -/
def covURecMinorBody_hasTy (n : Nat) :
    HasTyT natEnvU n [.assumption (.const 0 [])]
      (.lam (.app covTRecMotive (.bvar 0)) (.sort .zero))
      (.pi (.app covTRecMotive (.bvar 0)) (.sort (.succ .zero))) :=
  .lam _ _ (.succ (.succ .zero)) _ _
    (.app _ covTRecMotive (.bvar 0) (.const 0 [])
      (.sort (.succ (.succ .zero)))
      (covTRecMotive_hasTy n _) (.bvar _ 0 _ rfl))
    (.sort _ .zero)

def covURecMinorZero_beta (n : Nat) :
    ConvT natEnvU n [] (.app covTRecMinor (.const 1 []))
      (.lam (.app covTRecMotive (.const 1 [])) (.sort .zero))
      (.pi (.app covTRecMotive (.const 1 [])) (.sort (.succ .zero))) :=
  .beta [] (.const 0 [])
    (.lam (.app covTRecMotive (.bvar 0)) (.sort .zero)) (.const 1 [])
    (.pi (.app covTRecMotive (.bvar 0)) (.sort (.succ .zero)))
    (.succ .zero) (hasTyT_natEnvU_nat n [])
    (covURecMinorBody_hasTy n) (hasTyT_natEnvU_zero n [])

def covURecRhs_hasTy (n : Nat) :
    HasTyT natEnvU n [] (iotaRhsOf covURecWitness) (.sort (.succ .zero)) :=
  .app [] _ covURecZero (.app covTRecMotive (.const 1 []))
    (.sort (.succ .zero))
    (.app [] covTRecMinor (.const 1 []) (.const 0 [])
      (.pi (.app covTRecMotive (.bvar 0)) (.sort (.succ .zero)))
      (.lam [] (.const 0 []) (.succ .zero) _ _
        (hasTyT_natEnvU_nat n []) (covURecMinorBody_hasTy n))
      (hasTyT_natEnvU_zero n []))
    (covURecZero_motive_hasTy n)

/-- The actual native instance equals Prop by ι and two typed β conversions.
The construction uses no general observation-soundness hypothesis. -/
def covURecInstance_conv (n : Nat) :
    ConvT natEnvU n [] covURecInstance (.sort .zero) (.sort (.succ .zero)) := by
  have hi : ConvT natEnvU n [] covURecInstance (iotaRhsOf covURecWitness)
      (.sort (.succ .zero)) :=
    .iota [] _ _ _ (.of covURecWitness)
      (covURecInstance_hasTy n) (covURecRhs_hasTy n)
  have hb1 : ConvT natEnvU n [] (iotaRhsOf covURecWitness)
      (.app (.lam (.app covTRecMotive (.const 1 [])) (.sort .zero)) covURecZero)
      (.sort (.succ .zero)) :=
    .app [] _ _ _ _ (.app covTRecMotive (.const 1 [])) (.sort (.succ .zero))
      (covURecMinorZero_beta n) (.refl [] _ _ (covURecZero_motive_hasTy n))
  have hb2 : ConvT natEnvU n []
      (.app (.lam (.app covTRecMotive (.const 1 [])) (.sort .zero)) covURecZero)
      (.sort .zero) (.sort (.succ .zero)) :=
    .beta [] (.app covTRecMotive (.const 1 [])) (.sort .zero) covURecZero
      (.sort (.succ .zero)) (.succ (.succ .zero))
      (.app [] covTRecMotive (.const 1 []) (.const 0 [])
        (.sort (.succ (.succ .zero)))
        (covTRecMotive_hasTy n []) (hasTyT_natEnvU_zero n []))
      (.sort _ .zero) (covURecZero_motive_hasTy n)
  exact .trans [] _ _ _ _ hi (.trans [] _ _ _ _ hb1 hb2)

def covURecExtSubst : SubstT
  | 0 => idPiProp
  | _ + 1 => covURecMajor

def covURecExtY_hasTy (n : Nat) :
    HasTyT natEnvU n [] idPiProp covURecInstance :=
  .conv [] _ _ _ (.succ .zero) (hasTyT_idPiProp_ctx natEnvU n [])
    (.symm [] _ _ _ (covURecInstance_conv n))

theorem covURecExtY_observed (n : Nat) :
    ApproxTKStage natEnvU n 1 [] EnvT.bot idPiProp covTProbe := by
  refine ⟨?_, ?_⟩
  · exact .pi (.bot _ _ _) (fun _ h => (List.not_mem_nil _ h).elim)
      (fun _ h => (List.not_mem_nil _ h).elim)
  · simp [covTProbe, covTObservationBudget]

theorem covURecExtSubst_typed (n : Nat) :
    TypedSubstT natEnvU n [] covURecExtSubst covTRecExtCtx := by
  constructor
  · intro i A hi
    cases i with
    | zero =>
        obtain rfl := Option.some.inj hi
        exact ⟨covURecExtY_hasTy n⟩
    | succ i =>
        cases i with
        | zero =>
            obtain rfl := Option.some.inj hi
            exact ⟨covURecMajor_hasTy n []⟩
        | succ i => simp [covTRecExtCtx, lookupType] at hi
  · intro i v hi
    cases i with
    | zero => cases hi
    | succ i =>
        cases i with
        | zero => cases hi
        | succ i => simp [covTRecExtCtx, lookupValue] at hi

theorem covURecExtEnv_realized (n : Nat) :
    CovTRealized natEnvU n 1 covTRecExtCtx covTRecExtEnv covURecExtSubst := by
  refine ⟨covURecExtSubst_typed n, ?_⟩
  intro i c hc
  cases i with
  | zero =>
      change c = covTProbe at hc
      subst c
      exact covURecExtY_observed n
  | succ i =>
      cases i with
      | zero =>
          change c = covTRecMajorCode at hc
          subst c
          exact covURecMajor_observed n
      | succ i =>
          change c = .bot at hc
          subst c
          exact approxTKStage_bot _ _ _ _ _ _


-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_U_REC_INSTANCE_ROOTS
#print axioms covURecMajor
#print axioms covURecSubst
#print axioms covURecMajor_hasTy
#print axioms covURecMajor_observed
#print axioms covURecSubst_typed
#print axioms covURecEnv_realized
#print axioms covURecInstance
#print axioms covURecInstance_hasTy
#print axioms covURecInstance_observed
#print axioms covURecWitness
#print axioms covURecInstance_read
#print axioms covURecInstance_head_observed
#print axioms covUOriginSubst
#print axioms covUOriginEnv_realized
#print axioms covUEqProof
#print axioms covUEqSubst
#print axioms covUEqProof_hasTy
#print axioms covUEqSubst_typed
#print axioms covUEqEnv_realized
#print axioms covUSubstitutionSubst
#print axioms covUSubstitutionEnv_realized
#print axioms covURecZero
#print axioms covURecZero_hasTy
#print axioms covURecZero_motive_hasTy
#print axioms covURecMinorBody_hasTy
#print axioms covURecMinorZero_beta
#print axioms covURecRhs_hasTy
#print axioms covURecInstance_conv
#print axioms covURecExtSubst
#print axioms covURecExtY_hasTy
#print axioms covURecExtY_observed
#print axioms covURecExtSubst_typed
#print axioms covURecExtEnv_realized
-- END RCIC_NATIVE_TYPED_MODEL_COV_U_REC_INSTANCE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit
