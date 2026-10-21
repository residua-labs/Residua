import rcic.RcicNativeTypedModelCovNormConvCases

/-!
# Extensional eta: beta action and the observation boundary

The action of an eta expansion reduces by an actual beta step, without a
head-form premise on the function. The successor controls supply the whole
native argument-conversion action at every compact argument, using the landed
base-spine clause only after application has reached the base Nat type.

The separate model diagnostic records why an extensional core must retain the
landed motive's either-endpoint observation gate: asking for the same raw
compact at both endpoints would still reject successor eta. This diagnostic
does not add such a conjunct to the proposed model-free relation.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelKAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit
open TypedModelCovRelRealizationAudit TypedModelCovNormCov2Audit
open TypedModelCovNormAppAudit TypedModelCovNormConvCasesAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- Applying the native eta syntax performs precisely one beta step. -/
theorem covX_eta_app_readback (hL : ReadbackLaws E R)
    (Γ : LCtx) (D f x : Expr Nat) :
    RedR R Γ (.app (.lam D (.app (lift 0 1 f) (.bvar 0))) x) (.app f x) := by
  simpa only [instantiate0_eta] using
    redR_single (hL.beta Γ D (.app (lift 0 1 f) (.bvar 0)) x)

/-- The pure eta action law for any output relation closed under left
readback expansion. It uses the existing action of the function, and has no
endpoint model-observation premise. -/
theorem covX_eta_action_of_beta
    (hL : ReadbackLaws E R) (Γ : LCtx) (D f g : Expr Nat)
    (Args : Expr Nat → Expr Nat → Prop)
    (Out : Expr Nat → Expr Nat → Expr Nat → Expr Nat → Prop)
    (hexpand : ∀ a a' x x' y, RedR R Γ x x' → Out a a' x' y → Out a a' x y)
    (haction : ∀ a a', Args a a' → Out a a' (.app f a) (.app g a')) :
    ∀ a a', Args a a' →
      Out a a' (.app (.lam D (.app (lift 0 1 f) (.bvar 0))) a) (.app g a') := by
  intro a a' ha
  exact hexpand a a' _ _ _ (covX_eta_app_readback hL Γ D f a)
    (haction a a' ha)

/-- Successor's declared-domain port holds at arbitrary two arguments.
No shape-disjointness row is reproved: both normality facts are the landed
constructor-spine theorem, and the telescope is the pinned declaration. -/
theorem covX_natSucc_native_port (n : Nat) (Γ : LCtx) (a a' : Expr Nat) :
    CovSpineAppNativeAt natEnvU (WhStepCK2 natEnvU n) n Γ 2 natSuccMember
      [] [] [] [] (.const 0 []) (.const 0 []) a a' := by
  refine ⟨⟨.const 0 [], .const 0 [], rfl, ⟨.refl Γ (.const 0 [])⟩⟩,
    normalR_ctorSpineCK2 natEnvUWfT
      (rfl : natEnvU.members 2 = some natSuccMember) rfl Γ [] [a],
    normalR_ctorSpineCK2 natEnvUWfT
      (rfl : natEnvU.members 2 = some natSuccMember) rfl Γ [] [a'], ?_⟩
  intro _ hind
  exact MemberClass.noConfusion hind

/-- Successor has the full non-bottom base-output action at any compact
argument; native argument conversion aligns its actual declared telescope. -/
theorem covX_natSucc_spine_action (n : Nat) (Γ : LCtx)
    (a a' : Expr Nat) (u : CptT)
    (hconv : ConvT natEnvU n Γ a a' (.const 0 [])) :
    SpineClauseS (WhStepCK2 natEnvU n) natEnvU n Γ
      (.app (.const 2 []) a) (.app (.const 2 []) a') (.const 0 []) 2 [u] := by
  apply (lrSCoreCov_spine_iff (C2 natEnvU) Γ _ _ _ 2 [u]).mp
  exact lrSCoreCov_spine_snoc_of_native (C2 natEnvU)
    (readbackLaws_whStepCK2 natEnvU n)
    (args := []) (u := u) (xs := []) (xs' := [])
    (rfl : natEnvU.members 2 = some natSuccMember) (.refl _) (.refl _)
    (by trivial) (by decide) (by decide) (.nil _) hconv
    (covX_natSucc_native_port n Γ a a')

/-- The eta-expanded successor has the same full base-output action.
The lambda is never inspected as a spine: beta is used after application. -/
theorem covX_natSucc_eta_spine_action (n : Nat) (Γ : LCtx)
    (a a' : Expr Nat) (u : CptT)
    (hconv : ConvT natEnvU n Γ a a' (.const 0 [])) :
    SpineClauseS (WhStepCK2 natEnvU n) natEnvU n Γ
      (.app (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) a)
      (.app (.const 2 []) a') (.const 0 []) 2 [u] := by
  apply (lrSCoreCov_spine_iff (C2 natEnvU) Γ _ _ _ 2 [u]).mp
  apply lrSCoreCov_expand_red (C2 natEnvU) (readbackLaws_whStepCK2 natEnvU n)
    (covX_eta_app_readback (readbackLaws_whStepCK2 natEnvU n) Γ
      (.const 0 []) (.const 2 []) a)
  exact (lrSCoreCov_spine_iff (C2 natEnvU) Γ _ _ _ 2 [u]).mpr
    (covX_natSucc_spine_action n Γ a a' u hconv)

/-- No syntactic lambda has a raw rigid-spine observation in ApproxTK.
This is a model inversion, not a readback or recursive-relation theorem. -/
theorem covX_not_approxTK_lam_spine (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (D body : Expr Nat) (r : Nat) (us : List CptT) :
    ¬ ApproxTK E n Γ ρ (.lam D body) (.spine r us) := by
  intro h
  rcases approxTK_lam_inv h with h | ⟨a, g, h, _⟩
  · exact CptT.noConfusion h
  · exact CptT.noConfusion h

/-- A measured model-side eta-expansion law at one function. This is not
assumed by the extensional relation. -/
def CovXModelEtaObservationAt (M : CtxModelT E) (D f : Expr Nat) : Prop :=
  ∀ ρ c, M.Ap ρ f c → M.Ap ρ (.lam D (.app (lift 0 1 f) (.bvar 0))) c

/-- The model-side eta-expansion law is false at the actual successor.
The right observation is non-bottom and holds at every valuation. -/
theorem covX_not_modelEtaObservation_natSucc (n : Nat) (Γ : LCtx) :
    ¬ CovXModelEtaObservationAt (ctxModelT_approxTK natEnvU n Γ)
      (.const 0 []) (.const 2 []) := by
  intro h
  apply covX_not_approxTK_lam_spine natEnvU n Γ EnvT.bot _ _ 2 []
  exact h EnvT.bot (.spine 2 [])
    (ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine EnvT.bot))

/-- Both native endpoints, the environment guard, actual non-bottom right
observation and positive C2 type realization coexist with the false raw
eta-observation law. This does not refute an extensional model-free core. -/
theorem covX_eta_observation_boundary (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (ConvT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    EnvTypedCovAtP (C2 natEnvU) (ctxModelT_approxTK natEnvU n []) [] EnvT.bot ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    NormalizedCovRealization (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) ∧
    (.spine 2 [] : CptT) ≠ .bot ∧
    ¬ CovXModelEtaObservationAt (ctxModelT_approxTK natEnvU n [])
      (.const 0 []) (.const 2 []) := by
  obtain ⟨hW, hΓ, hl, hr, hc, hρ, hm, ht, hne, _⟩ :=
    natSucc_eta_C2_counterexample n
  exact ⟨hW, hΓ, hl, hr, hc, hρ, hm, ht, hne,
    covX_not_modelEtaObservation_natSucc n []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_ROOTS
#print axioms covX_eta_app_readback
#print axioms covX_eta_action_of_beta
#print axioms covX_natSucc_native_port
#print axioms covX_natSucc_spine_action
#print axioms covX_natSucc_eta_spine_action
#print axioms covX_not_approxTK_lam_spine
#print axioms CovXModelEtaObservationAt
#print axioms covX_not_modelEtaObservation_natSucc
#print axioms covX_eta_observation_boundary
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit
