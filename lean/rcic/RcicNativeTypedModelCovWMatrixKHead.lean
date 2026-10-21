import rcic.RcicNativeTypedModelCovWIrrelKControls
import rcic.RcicNativeTypedModelCovWIrrelFixtures

/-!
# A native K step already obstructs typed head expansion

The unchanged native K head uses native index conversion and common typing.
The observation grammar imposes a stronger, independent DI index guard.
The admitted eta-index call satisfies the native gates and has an actual
`WhStepCK2` step, but every current-grammar observation of its source is
bottom. Its RHS supplies the strictly typed nonbottom compact `prop`.

The open context has an explicit native closing substitution and a new-model
realizer. Observations are measured in that context and valuation; no claim
is made that the substituted closed source has the same exclusion.
The final theorems show that restricting observations cannot repair this
head failure while retaining the displayed RHS (and actual type code for
the fully typed interface). The grammar is unchanged. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelKGuardAudit TypedModelKControlAudit TypedModelKObstructionAudit
open TypedModelKTransportAudit TypedModelCovTAudit TypedModelCovWIrrelAudit
open TypedModelAudit.TypingFin TypedModelCovWEtaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open ReadbackCK2ModelObstructionAudit ReadbackCK2InputsAudit

def covWMatrixKWitness : IotaWitness eqEnvT :=
  eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex etaIndexMot (.sort .zero)

/-- These are the actual native gates, including common typing. -/
theorem covWMatrix_K_native_gates (n : Nat) :
    KCanonW covWMatrixKWitness (.bvar 0) ∧
    (¬ IsCtorSpine eqEnvT (.bvar 0)) ∧
    KIndexConvAt eqEnvT n etaEqCtx covWMatrixKWitness ∧
    KCommonAt eqEnvT n etaEqCtx covWMatrixKWitness (.bvar 0) := by
  obtain ⟨hi, hc⟩ := eqKGate_of_indexConv (fun _ _ h => h)
    etaIndexMot (.sort .zero) (indexFnTy eqEnvT n etaEqCtx)
    (etaIndexParamTy n) (etaIndexTy n) (.bvar etaEqCtx 0 _ rfl) (etaIndexConv n)
  exact ⟨Or.inl ⟨rfl, rfl, rfl⟩, not_isCtorSpine_bvar, hi, hc⟩

theorem covWMatrix_K_native_head (n : Nat) :
    KNativeHead eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) := by
  obtain ⟨hk, hn, hi, hc⟩ := covWMatrix_K_native_gates n
  exact .intro (w := covWMatrixKWitness) hk hn hi hc

/-- The failure is an actual step of the currently used native readback. -/
theorem covWMatrix_K_step (n : Nat) :
    WhStepCK2 eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) :=
  .native (covWMatrix_K_native_head n)

/-- Only the additional model guard fails; the native gates above are supplied. -/
theorem covWMatrix_K_model_guard_fails (n : Nat) :
    ¬ KIndexGuardAt eqEnvT n etaEqCtx covWMatrixKWitness :=
  not_kIndexGuardAt_eta n

/-- The context's function is closed by the identity on propositions.
Its equality assumption is realized by reflexivity, cast along the actual
eta expansion of that identity. -/
def covWMatrixKSubst : SubstT
  | 0 => binderIndexCtor
  | 1 => indexId
  | _ + 2 => .sort .zero

def covWMatrixKProof_ty (n : Nat) :
    HasTyT eqEnvT n [] binderIndexCtor (binderIndexFamily indexBinderBeta) := by
  have hf := eqFamilyPartialTy (E := eqEnvT) (fun _ _ h => h)
    (indexFnTy eqEnvT n []) (indexIdTy eqEnvT n [])
  exact .conv [] _ _ _ .zero (binderIndexCtorTy n [])
    (.app [] _ _ _ _ _ _ (.refl [] _ _ hf)
      (.symm [] _ _ _ (indexBinderBetaConv eqEnvT n [])))

theorem covWMatrixKSubst_typed (n : Nat) :
    TypedSubstT eqEnvT n [] covWMatrixKSubst etaEqCtx := by
  constructor
  · intro i A hi
    cases i with
    | zero =>
        obtain rfl := Option.some.inj hi
        exact ⟨covWMatrixKProof_ty n⟩
    | succ i =>
        cases i with
        | zero =>
            obtain rfl := Option.some.inj hi
            exact ⟨indexIdTy eqEnvT n []⟩
        | succ i => simp [etaEqCtx, lookupType] at hi
  · intro i v hi
    cases i with
    | zero => cases hi
    | succ i =>
        cases i with
        | zero => cases hi
        | succ i => simp [etaEqCtx, lookupValue] at hi

theorem covWMatrix_K_realized (n stage : Nat) :
    CovWIrrelRealized eqEnvT n stage etaEqCtx EnvWIrrel.bot covWMatrixKSubst := by
  refine ⟨covWMatrixKSubst_typed n, ?_⟩
  intro i c hc
  cases hc
  exact ⟨.bot _ _ _, by simp [covWIrrelErase, covTObservationBudget]⟩

/-- Finite typing of the erased valuation belongs to the old eta model.
The observation and realizer statements above use the current grammar. -/
theorem covWMatrix_K_erased_valuation (n : Nat) :
    EnvTypedFinAtT (⟨ApproxTKWEta eqEnvT n etaEqCtx⟩ : CtxModelT eqEnvT)
      etaEqCtx (covWIrrelEnvErase EnvWIrrel.bot) := by
  rw [covWIrrel_env_erase_bot]
  exact envTypedFinAtT_bot _ (fun ρ e => ApproxTKWEta.bot etaEqCtx ρ e) etaEqCtx

/-- The displayed context contains only assumptions, so its erased
valuation has no local-definition coherence obligations. -/
theorem covWMatrix_K_erased_coherence (n : Nat) :
    CtxEnvM (⟨ApproxTKWEta eqEnvT n etaEqCtx⟩ : CtxModelT eqEnvT)
      etaEqCtx (covWIrrelEnvErase EnvWIrrel.bot) := by
  intro i v hv
  cases i with
  | zero => cases hv
  | succ i =>
      cases i with
      | zero => cases hv
      | succ i => simp [etaEqCtx, lookupValue] at hv

theorem covWMatrix_K_compact_typed : CTyS eqEnvT .prop .sort := by
  rw [CTyS]
  exact Or.inr .prop

theorem covWMatrix_K_rhs_observed (n : Nat) :
    CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot (.sort .zero) .prop :=
  covWIrrel_observation_of (covWIrrel_sort_observed eqEnvT n etaEqCtx EnvWIrrel.bot .zero)

theorem covWMatrix_K_type_observed (n : Nat) :
    CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot (.sort (.succ .zero)) .sort :=
  covWIrrel_observation_of
    (covWIrrel_sort_observed eqEnvT n etaEqCtx EnvWIrrel.bot (.succ .zero))

theorem covWMatrix_K_source_excluded (n : Nat) (ρ : EnvWIrrel) :
    ¬ CovWIrrelObservation eqEnvT n etaEqCtx ρ etaIndexRedex .prop := by
  intro h
  exact CptT.noConfusion ((covWIrrel_etaIndex_observation_iff n etaEqCtx ρ .prop).mp h)

/-- Every native, semantic, strict-typing and closing-realizer premise is
supplied for the same open head step. -/
theorem covWMatrix_K_inhabited (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero))) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) (.sort (.succ .zero))) ∧
    KCanonW covWMatrixKWitness (.bvar 0) ∧
    (¬ IsCtorSpine eqEnvT (.bvar 0)) ∧
    KIndexConvAt eqEnvT n etaEqCtx covWMatrixKWitness ∧
    KCommonAt eqEnvT n etaEqCtx covWMatrixKWitness (.bvar 0) ∧
    WhStepCK2 eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) ∧
    CovWIrrelRealized eqEnvT n 1 etaEqCtx EnvWIrrel.bot covWMatrixKSubst ∧
    CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot (.sort (.succ .zero)) .sort ∧
    CTyS eqEnvT .prop .sort ∧
    CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot (.sort .zero) .prop ∧
    (¬ CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot etaIndexRedex .prop) ∧
    ¬ KIndexGuardAt eqEnvT n etaEqCtx covWMatrixKWitness := by
  obtain ⟨hW, hΓ, ht, hc, _, _, _, _, _⟩ := covWIrrel_K_eta_guard_control n
  obtain ⟨hk, hn, hi, hcommon⟩ := covWMatrix_K_native_gates n
  exact ⟨hW, hΓ, ht, ⟨.sort _ .zero⟩, hc, hk, hn, hi, hcommon,
    covWMatrix_K_step n, covWMatrix_K_realized n 1,
    covWMatrix_K_type_observed n, covWMatrix_K_compact_typed,
    covWMatrix_K_rhs_observed n, covWMatrix_K_source_excluded n EnvWIrrel.bot,
    covWMatrix_K_model_guard_fails n⟩

theorem covWMatrix_K_no_typed_head_expansion (n : Nat) :
    ¬ (∀ c a : CptT,
      CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot (.sort (.succ .zero)) a →
      CTyS eqEnvT c a →
      CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot (.sort .zero) c →
      CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot etaIndexRedex c) := by
  intro h
  exact covWMatrix_K_source_excluded n EnvWIrrel.bot
    (h .prop .sort (covWMatrix_K_type_observed n) covWMatrix_K_compact_typed
      (covWMatrix_K_rhs_observed n))

/-- Any restriction retaining the displayed RHS still fails head equality.
This theorem consumes a forgetting map; it does not postulate a new model. -/
theorem covWMatrix_K_restriction_not_equal (n : Nat)
    (Obs : Expr Nat → CptT → Prop)
    (hforget : ∀ e c, Obs e c →
      CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot e c)
    (hrhs : Obs (.sort .zero) .prop) :
    ¬ (∀ c : CptT, CTyS eqEnvT c .sort →
      (Obs etaIndexRedex c ↔ Obs (.sort .zero) c)) := by
  intro heq
  exact covWMatrix_K_source_excluded n EnvWIrrel.bot
    (hforget _ _ ((heq .prop covWMatrix_K_compact_typed).mpr hrhs))

/-- The fully typed restricted interface also retains the actual type-code
observation, so the obstruction is not obtained from an uninhabited code. -/
theorem covWMatrix_K_restriction_no_typed_expansion (n : Nat)
    (Obs : Expr Nat → CptT → Prop)
    (hforget : ∀ e c, Obs e c →
      CovWIrrelObservation eqEnvT n etaEqCtx EnvWIrrel.bot e c)
    (hrhs : Obs (.sort .zero) .prop)
    (htype : Obs (.sort (.succ .zero)) .sort) :
    ¬ (∀ c a : CptT, Obs (.sort (.succ .zero)) a → CTyS eqEnvT c a →
      Obs (.sort .zero) c → Obs etaIndexRedex c) := by
  intro hexpand
  exact covWMatrix_K_source_excluded n EnvWIrrel.bot
    (hforget _ _ (hexpand .prop .sort htype covWMatrix_K_compact_typed hrhs))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_K_HEAD_ROOTS
#print axioms covWMatrixKWitness
#print axioms covWMatrix_K_native_gates
#print axioms covWMatrix_K_native_head
#print axioms covWMatrix_K_step
#print axioms covWMatrix_K_model_guard_fails
#print axioms covWMatrixKSubst
#print axioms covWMatrixKProof_ty
#print axioms covWMatrixKSubst_typed
#print axioms covWMatrix_K_realized
#print axioms covWMatrix_K_erased_valuation
#print axioms covWMatrix_K_erased_coherence
#print axioms covWMatrix_K_compact_typed
#print axioms covWMatrix_K_rhs_observed
#print axioms covWMatrix_K_type_observed
#print axioms covWMatrix_K_source_excluded
#print axioms covWMatrix_K_inhabited
#print axioms covWMatrix_K_no_typed_head_expansion
#print axioms covWMatrix_K_restriction_not_equal
#print axioms covWMatrix_K_restriction_no_typed_expansion
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_K_HEAD_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit
