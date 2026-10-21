import rcic.RcicNativeTypedModelCovXCore
import rcic.RcicNativeTypedModelCovXEtaObserved

/-!
# The successor eta counterexample becomes an extensional positive

The native Nat and Nat-arrow type views below are explicit inhabitants.
The positive result handles observations at either endpoint and every compact,
including lambda tables observed only at the eta-expanded left endpoint.
The rigid compact has an actual C2 Pi gate. Native zero supplies an observed,
related non-bottom argument, so the application condition is not empty.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelKAudit
open TypedModelKFragmentAudit TypedModelKTransportAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit
open TypedModelCovNormCov2Audit TypedModelCovNormAppAudit
open TypedModelCovNormConvCasesAudit TypedModelCovXAudit

/-- An explicit admitted base-type view, using the imported normality law
for the pinned inductive family head. -/
def covXNatView (n : Nat) (Γ : LCtx) :
    CovXTypeView natEnvU (WhStepCK2 natEnvU n) n Γ (.const 0 []) := by
  have hn : NormalR (WhStepCK2 natEnvU n) Γ (.const 0 []) :=
    normalR_famAppCK2 natEnvUWfT
      (rfl : natEnvU.members 0 = some natFamMember) rfl Γ [] []
  exact .base (.const 0 []) (.refl _) hn
    (by rintro ⟨l, h⟩; exact Expr.noConfusion (redR_of_normal hn h))
    (by rintro ⟨D, B, h⟩; exact Expr.noConfusion (redR_of_normal hn h))

/-- The nondependent Nat-arrow view supplies every codomain child at the
same actual Nat type, including the open-binder child. -/
def covXNatArrowView (n : Nat) (Γ : LCtx) :
    CovXTypeView natEnvU (WhStepCK2 natEnvU n) n Γ
      (.pi (.const 0 []) (.const 0 [])) :=
  .pi (.const 0 []) (.const 0 []) (.refl _) (covXNatView n Γ)
    (covXNatView n (.assumption (.const 0 []) :: Γ))
    (fun _ _ => covXNatView n Γ)

/-- The rigid function observation really meets the C2 Pi gate. -/
theorem covX_natSucc_pi_gate : CovXPiGate (C2 natEnvU) (.spine 2 []) := by
  refine ⟨.spine 0 [], [([.spine 0 []], .spine 0 [])], ?_⟩
  exact ctyCov2_natSucc_spine (approxT_natNat_covCode EnvT.bot)
    not_isPropCT_natNatCovCode

/-- A full native base-output action supplies the rigid function relation
at the Nat-arrow view. Its compact output may grow after application. -/
theorem covX_natArrow_spine_of_action (n : Nat) (Γ : LCtx)
    (x y : Expr Nat)
    (haction : ∀ a a' u, ConvT natEnvU n Γ a a' (.const 0 []) →
      SpineClauseS (WhStepCK2 natEnvU n) natEnvU n Γ
        (.app x a) (.app y a') (.const 0 []) 2 [u]) :
    LRSCoreCovXAt (C2 natEnvU) (covXNatArrowView n Γ) x y (.spine 2 []) := by
  refine ⟨covX_natSucc_pi_gate, ?_⟩
  intro ds out action a a' ha ha' hc hd
  cases action with
  | bot =>
      exact ⟨lrSCoreCov_bot (C2 natEnvU) _ _ _ _,
        lrSCoreCov_bot (C2 natEnvU) _ _ _ _⟩
  | @appSpine r args arg u hu =>
      obtain ⟨hc⟩ := hc
      have hrel := (lrSCoreCov_spine_iff (C2 natEnvU) Γ _ _ _ 2 [u]).mpr
        (haction a a' u hc)
      exact ⟨hrel, hrel⟩

/-- The same native action supplies all successor-shaped observed lambda
rows. The matching compact typing gate is an explicit input. -/
theorem covX_natArrow_lam_of_rows (n : Nat) (Γ : LCtx)
    (x y : Expr Nat) (g : List (List CptT × CptT))
    (hgate : CovXPiGate (C2 natEnvU) (.lam g))
    (hrows : ∀ s ∈ g, s.2 = .bot ∨ ∃ u, s.2 = .spine 2 [u])
    (haction : ∀ a a' u, ConvT natEnvU n Γ a a' (.const 0 []) →
      SpineClauseS (WhStepCK2 natEnvU n) natEnvU n Γ
        (.app x a) (.app y a') (.const 0 []) 2 [u]) :
    LRSCoreCovXAt (C2 natEnvU) (covXNatArrowView n Γ) x y (.lam g) := by
  refine ⟨hgate, ?_⟩
  intro ds out action a a' ha ha' hc hd
  cases action with
  | bot =>
      exact ⟨lrSCoreCov_bot (C2 natEnvU) _ _ _ _,
        lrSCoreCov_bot (C2 natEnvU) _ _ _ _⟩
  | @app g' s arg hs hu =>
      rcases hrows s hs with hb | ⟨u, he⟩
      · rw [hb]
        exact ⟨lrSCoreCov_bot (C2 natEnvU) _ _ _ _,
          lrSCoreCov_bot (C2 natEnvU) _ _ _ _⟩
      · rw [he]
        obtain ⟨hc⟩ := hc
        have hrel := (lrSCoreCov_spine_iff (C2 natEnvU) Γ _ _ _ 2 [u]).mpr
          (haction a a' u hc)
        exact ⟨hrel, hrel⟩

/-- The old rigid-spine counterexample is positive at the explicit
extensional Pi view, with the same native terms and the same compact. -/
theorem covX_natSucc_eta_at_spine (n : Nat) (Γ : LCtx) :
    LRSCoreCovXAt (C2 natEnvU) (covXNatArrowView n Γ)
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.spine 2 []) :=
  covX_natArrow_spine_of_action n Γ _ _ (covX_natSucc_eta_spine_action n Γ)

/-- All observations at either eta endpoint are handled, including every
left-only lambda row table. The model and relation contexts remain separate;
the terms in this fixture are closed. -/
theorem covX_natSucc_eta_observed (n : Nat) (Ξ Γ : LCtx) (ρ ρ' : EnvT)
    (c : CptT)
    (h : ApproxTK natEnvU n Ξ ρ
        (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c ∨
      ApproxTK natEnvU n Ξ ρ' (.const 2 []) c) :
    LRSCoreCovXAt (C2 natEnvU) (covXNatArrowView n Γ)
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) c := by
  rcases h with h | h
  · have hgate := covX_natSucc_eta_pi_gate h
    rcases covX_natSucc_eta_observation h with rfl |
      ⟨a, g, rfl, _, _, _, hrows⟩
    · exact lrSCoreCovXAt_bot (C2 natEnvU) (covXNatArrowView n Γ) _ _
    · exact covX_natArrow_lam_of_rows n Γ _ _ g hgate hrows
        (covX_natSucc_eta_spine_action n Γ)
  · rcases approxT_rigid_const_inv rigidConst_natEnvU_succ
      (approxTK_forget h) with rfl | rfl
    · exact lrSCoreCovXAt_bot (C2 natEnvU) (covXNatArrowView n Γ) _ _
    · exact covX_natSucc_eta_at_spine n Γ

/-- Native zero supplies a non-bottom, observed related argument for the
new Nat domain view. This does not follow from an empty function demand. -/
theorem covX_natZero_related (n : Nat) (Γ : LCtx) :
    LRSCoreCovXAt (C2 natEnvU) (covXNatView n Γ)
      (.const 1 []) (.const 1 []) (.spine 1 []) :=
  lrSCoreCov_natZero_spine (C2 natEnvU) n Γ

/-- An inhabited native eta control with its actual old counterexample
compact, positive C2 Pi gate, and an observed related non-bottom argument. -/
theorem covX_natSucc_eta_control (n : Nat) :
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
    CovXPiGate (C2 natEnvU) (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 1 []) (.spine 1 []) ∧
    LRSCoreCovXAt (C2 natEnvU) (covXNatView n [])
      (.const 1 []) (.const 1 []) (.spine 1 []) ∧
    LRSCoreCovXAt (C2 natEnvU) (covXNatArrowView n [])
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.spine 2 []) ∧
    (.spine 1 [] : CptT) ≠ .bot ∧ (.spine 2 [] : CptT) ≠ .bot := by
  obtain ⟨hW, hΓ, hl, hr, hc, hρ, hm, _, hne, _⟩ :=
    natSucc_eta_C2_counterexample n
  exact ⟨hW, hΓ, hl, hr, hc, hρ, hm, covX_natSucc_pi_gate,
    ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero),
    covX_natZero_related n [], covX_natSucc_eta_at_spine n [],
    (fun h => CptT.noConfusion h), hne⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_CONTROL_ROOTS
#print axioms covXNatView
#print axioms covXNatArrowView
#print axioms covX_natSucc_pi_gate
#print axioms covX_natArrow_spine_of_action
#print axioms covX_natArrow_lam_of_rows
#print axioms covX_natSucc_eta_at_spine
#print axioms covX_natSucc_eta_observed
#print axioms covX_natZero_related
#print axioms covX_natSucc_eta_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit
