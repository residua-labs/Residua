import rcic.RcicNativeTypedModelCovRLambdaBoundary

/-!
# Actual observations for independently observed type substitution

The substituted body is the native variable `B = bvar 0`, and the native
argument is the closed polymorphic identity type. The argument and body
have the same deep, nonbottom observation in matching valuations. The
substituted type also has actual bottom and shallow Pi observations,
including an empty-row observation retaining its Sort domain.
The tested term is the landed, natively typed polymorphic identity at its
actual nonbottom compact `polyIdCpt0`.

These data expose independent finite observation depths. They do not assert
that a deep observation factors through a shallow one, or choose a semantic
interpretation for any observation. The subsequent substitution diagnostic
must state its decoder and semantic rejection separately. No old semantic
core supplies a fresh candidate edge here. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit TypedModelCovRAudit

/-- This observation records the functional observation of the type variable
in the inner arrow. It has just one outer row. -/
def covSSubstitutionDeep : CptT :=
  .pi .sort [([polyIdDom1], polyIdTyCod1)]

theorem covSSubstitutionDeep_tyCode : TyCodeCT covSSubstitutionDeep := by
  refine .pi .sort ?_
  intro row hrow
  rcases List.mem_singleton.mp hrow with rfl
  refine .pi tyCodeCT_polyIdDom1 ?_
  intro row hrow
  rcases List.mem_singleton.mp hrow with rfl
  exact tyCodeCT_polyIdDom1

/-- The type argument is actually typed at Sort 2. The universe equation
is supplied by the native sort-conversion constructor. -/
def covSSubstitution_argument_hasTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ cexPolyIdTy (.sort (.succ (.succ .zero))) :=
  .conv Γ cexPolyIdTy
    (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero))))
    (.sort (.succ (.succ .zero)))
    (.succ (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero))))
    (.pi Γ (.sort (.succ .zero)) (.succ (.succ .zero))
      (.pi (.bvar 0) (.bvar 1)) (.imax (.succ .zero) (.succ .zero))
      (.sort Γ (.succ .zero))
      (.pi (.assumption (.sort (.succ .zero)) :: Γ)
        (.bvar 0) (.succ .zero) (.bvar 1) (.succ .zero)
        (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl)))
    (.sorts Γ
      (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))
      (.succ (.succ .zero)) (fun _ => rfl))

theorem covSSubstitution_deep_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ApproxTK E n Γ ρ cexPolyIdTy covSSubstitutionDeep := by
  refine ApproxTK.pi ?_ ?_ ?_
  · simpa only [sortCode_succ] using
      approxTK_sort_code E n Γ ρ (.succ .zero)
  · intro row hrow u hu
    rcases List.mem_singleton.mp hrow with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_polyIdDom1_sort E
  · intro row hrow
    rcases List.mem_singleton.mp hrow with rfl
    exact .free (kFreeT_pi (kFreeT_bvar E 0) (kFreeT_bvar E 1))
      (approxT_polyIdTyCod1 E ρ (List.mem_singleton_self _))

def covSSubstitutionCtx : LCtx :=
  [.assumption (.sort (.succ (.succ .zero)))]

/-- The variable's valuation is exactly the argument observation, with the
empty-context bottom valuation as its tail. -/
def covSSubstitutionEnv : EnvT :=
  EnvT.cons (demandT [covSSubstitutionDeep]) EnvT.bot

def covSSubstitutionCtx_wf (E : ResolvedEnv) (n : Nat) :
    CtxWfT E n covSSubstitutionCtx :=
  .assumption [] (.sort (.succ (.succ .zero)))
    (.succ (.succ (.succ .zero))) .nil (.sort [] (.succ (.succ .zero)))

def covSSubstitution_body_hasTy (E : ResolvedEnv) (n : Nat) :
    HasTyT E n covSSubstitutionCtx (.bvar 0) (.sort (.succ (.succ .zero))) :=
  .bvar covSSubstitutionCtx 0 (.sort (.succ (.succ .zero))) rfl

/-- The extended valuation satisfies the landed finite-joint environment
typing interface. Its sole value is a type code at the actual universe. -/
theorem covSSubstitution_env_typed (E : ResolvedEnv) (n : Nat) :
    EnvTypedFinAtT (ctxModelT_approxTK E n covSSubstitutionCtx)
      covSSubstitutionCtx covSSubstitutionEnv := by
  intro i A hA us hus
  cases i with
  | zero =>
      have he : A = .sort (.succ (.succ .zero)) := (Option.some.inj hA).symm
      subst A
      refine ⟨.sort, ?_, ?_⟩
      · simpa only [sortCode_succ] using
          approxTK_sort_code E n covSSubstitutionCtx covSSubstitutionEnv
            (.succ (.succ .zero))
      · intro u hu
        have hm : u ∈ [covSSubstitutionDeep] := hus u hu
        rcases List.mem_singleton.mp hm with rfl
        rw [CTyS]
        exact Or.inr covSSubstitutionDeep_tyCode
  | succ i => simp [covSSubstitutionCtx, lookupType] at hA

theorem covSSubstitution_ctx_coherent (E : ResolvedEnv) (n : Nat) :
    CtxEnvM (ctxModelT_approxTK E n covSSubstitutionCtx)
      covSSubstitutionCtx covSSubstitutionEnv := by
  intro i v hv
  cases i with
  | zero => cases hv
  | succ i => simp [covSSubstitutionCtx, lookupValue] at hv

theorem covSSubstitution_body_observed (E : ResolvedEnv) (n : Nat) :
    ApproxTK E n covSSubstitutionCtx covSSubstitutionEnv
      (.bvar 0) covSSubstitutionDeep :=
  .free (kFreeT_bvar E 0) (.bvar (List.mem_singleton_self _))

/-- Every value assigned to the substituted variable is actually observed
at the native argument. This is not an arbitrary or unrelated valuation. -/
theorem covSSubstitution_argument_observes_valuation (E : ResolvedEnv) (n : Nat) :
    ∀ d, covSSubstitutionEnv 0 d → ApproxTK E n [] EnvT.bot cexPolyIdTy d := by
  intro d hd
  have hm : d ∈ [covSSubstitutionDeep] := hd
  rcases List.mem_singleton.mp hm with rfl
  exact covSSubstitution_deep_observed E n [] EnvT.bot

theorem covSSubstitution_native_inst :
    instantiate0 cexPolyIdTy (.bvar 0) = cexPolyIdTy := rfl

theorem covSSubstitution_result_shallow_observed (E : ResolvedEnv) (n : Nat) :
    ApproxTK E n [] EnvT.bot (instantiate0 cexPolyIdTy (.bvar 0))
      (.pi .bot []) :=
  approxTK_pi_bot_nil E n [] EnvT.bot _ _

/-- Even retaining the actual Sort-domain observation does not couple the
finite output rows of the result observation to those of the argument. -/
theorem covSSubstitution_result_sort_nil_observed (E : ResolvedEnv) (n : Nat) :
    ApproxTK E n [] EnvT.bot (instantiate0 cexPolyIdTy (.bvar 0))
      (.pi .sort []) := by
  refine ApproxTK.pi ?_ ?_ ?_
  · simpa only [sortCode_succ] using
      approxTK_sort_code E n [] EnvT.bot (.succ .zero)
  · intro row hrow
    exact (List.not_mem_nil row hrow).elim
  · intro row hrow
    exact (List.not_mem_nil row hrow).elim

/-- All native and observational premises used by the substitution test.
The three result observations are independent choices at the same actual
native substituted type; the nonbottom term observation is fixed. -/
structure CovSSubstitutionNativeData (n : Nat) : Prop where
  env_wf : Nonempty (EnvWfT emptyEnv)
  empty_ctx_wf : Nonempty (CtxWfT emptyEnv n [])
  binder_ctx_wf : Nonempty (CtxWfT emptyEnv n covSSubstitutionCtx)
  argument_hasTy : Nonempty
    (HasTyT emptyEnv n [] cexPolyIdTy (.sort (.succ (.succ .zero))))
  body_hasTy : Nonempty (HasTyT emptyEnv n covSSubstitutionCtx
    (.bvar 0) (.sort (.succ (.succ .zero))))
  result_hasTy : Nonempty (HasTyT emptyEnv n []
    (instantiate0 cexPolyIdTy (.bvar 0)) (.sort (.succ (.succ .zero))))
  term_hasTy : Nonempty (HasTyT emptyEnv n [] cexPolyId
    (instantiate0 cexPolyIdTy (.bvar 0)))
  term_refl : Nonempty (ConvT emptyEnv n [] cexPolyId cexPolyId
    (instantiate0 cexPolyIdTy (.bvar 0)))
  empty_env_typed : EnvTypedFinAtT (ctxModelT_approxTK emptyEnv n []) [] EnvT.bot
  empty_ctx_coherent : CtxEnvM (ctxModelT_approxTK emptyEnv n []) [] EnvT.bot
  extended_env_typed : EnvTypedFinAtT (ctxModelT_approxTK emptyEnv n covSSubstitutionCtx)
    covSSubstitutionCtx covSSubstitutionEnv
  extended_ctx_coherent : CtxEnvM (ctxModelT_approxTK emptyEnv n covSSubstitutionCtx)
    covSSubstitutionCtx covSSubstitutionEnv
  argument_observed : ApproxTK emptyEnv n [] EnvT.bot cexPolyIdTy covSSubstitutionDeep
  body_observed : ApproxTK emptyEnv n covSSubstitutionCtx covSSubstitutionEnv
    (.bvar 0) covSSubstitutionDeep
  result_bot_observed : ApproxTK emptyEnv n [] EnvT.bot
    (instantiate0 cexPolyIdTy (.bvar 0)) .bot
  result_shallow_observed : ApproxTK emptyEnv n [] EnvT.bot
    (instantiate0 cexPolyIdTy (.bvar 0)) (.pi .bot [])
  result_sort_nil_observed : ApproxTK emptyEnv n [] EnvT.bot
    (instantiate0 cexPolyIdTy (.bvar 0)) (.pi .sort [])
  term_observed : ApproxTK emptyEnv n [] EnvT.bot cexPolyId polyIdCpt0
  term_nonbottom : polyIdCpt0 ≠ .bot
  deep_nonbottom : covSSubstitutionDeep ≠ .bot
  shallow_nonbottom : (CptT.pi .bot []) ≠ .bot
  sort_nil_nonbottom : (CptT.pi .sort []) ≠ .bot
  argument_observes_valuation : ∀ d, covSSubstitutionEnv 0 d →
    ApproxTK emptyEnv n [] EnvT.bot cexPolyIdTy d

theorem covSSubstitution_native_data (n : Nat) : CovSSubstitutionNativeData n where
  env_wf := ⟨.empty⟩
  empty_ctx_wf := ⟨.nil⟩
  binder_ctx_wf := ⟨covSSubstitutionCtx_wf emptyEnv n⟩
  argument_hasTy := ⟨covSSubstitution_argument_hasTy emptyEnv n []⟩
  body_hasTy := ⟨covSSubstitution_body_hasTy emptyEnv n⟩
  result_hasTy := ⟨covSSubstitution_argument_hasTy emptyEnv n []⟩
  term_hasTy := ⟨hasTyT_cexPolyId emptyEnv n⟩
  term_refl := ⟨.refl _ _ _ (hasTyT_cexPolyId emptyEnv n)⟩
  empty_env_typed := envTypedFinAtT_nil _ EnvT.bot
  empty_ctx_coherent := by
    intro i v hv
    simp [lookupValue] at hv
  extended_env_typed := covSSubstitution_env_typed emptyEnv n
  extended_ctx_coherent := covSSubstitution_ctx_coherent emptyEnv n
  argument_observed := covSSubstitution_deep_observed emptyEnv n [] EnvT.bot
  body_observed := covSSubstitution_body_observed emptyEnv n
  result_bot_observed := .bot [] EnvT.bot _
  result_shallow_observed := covSSubstitution_result_shallow_observed emptyEnv n
  result_sort_nil_observed := covSSubstitution_result_sort_nil_observed emptyEnv n
  term_observed := covRLambdaIdentity_observed emptyEnv n [] EnvT.bot
  term_nonbottom := CptT.noConfusion
  deep_nonbottom := CptT.noConfusion
  shallow_nonbottom := CptT.noConfusion
  sort_nil_nonbottom := CptT.noConfusion
  argument_observes_valuation := covSSubstitution_argument_observes_valuation emptyEnv n

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_SUBSTITUTION_DATA_ROOTS
#print axioms covSSubstitutionDeep
#print axioms covSSubstitutionDeep_tyCode
#print axioms covSSubstitution_argument_hasTy
#print axioms covSSubstitution_deep_observed
#print axioms covSSubstitutionCtx
#print axioms covSSubstitutionEnv
#print axioms covSSubstitutionCtx_wf
#print axioms covSSubstitution_body_hasTy
#print axioms covSSubstitution_env_typed
#print axioms covSSubstitution_ctx_coherent
#print axioms covSSubstitution_body_observed
#print axioms covSSubstitution_argument_observes_valuation
#print axioms covSSubstitution_native_inst
#print axioms covSSubstitution_result_shallow_observed
#print axioms covSSubstitution_result_sort_nil_observed
#print axioms CovSSubstitutionNativeData
#print axioms covSSubstitution_native_data
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_SUBSTITUTION_DATA_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
