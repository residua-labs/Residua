import rcic.RcicNativeTypedModelCovXRealization
import rcic.RcicNativeTypedModelCovXEtaControl

/-!
# Hereditary realization at the actual rigid Nat function

The Nat base view restricts related observations to bottom or rigid spines.
Each such observation is realized at the observed Nat family code, at every
valuation, including the binder valuation. Consequently the successor's
actual rigid function observation realizes all three codomain children and
every related argument demand. Native zero witnesses a non-bottom argument.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelKAudit
open ReadbackCK2ModelObstructionAudit TypedModelKControlAudit
open TypedModelKFragmentAudit TypedModelKTransportAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit
open TypedModelCovRelEscapeAudit TypedModelCovRelRealizationAudit
open TypedModelCovNormCov2Audit TypedModelCovXAudit
open TypedModelCovNormBoundaryAudit TypedModelCovNormEscapeAudit
open TypedModelCovXEtaAudit TypedModelCovXRealizationAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- This is compact-shape inversion of the imported relation. It consumes
the two negative readback fields of a base view, without proving any new
native shape-disjointness assertion. -/
theorem covX_base_related_compact_shape (C : CovTyping E)
    {Γ : LCtx} {A x y : Expr Nat} {c : CptT}
    (hs : ¬ ∃ l, RedR R Γ A (.sort l))
    (hp : ¬ ∃ D B, RedR R Γ A (.pi D B))
    (h : LRSCoreCov C R n Γ x y A c) :
    c = .bot ∨ ∃ r args, c = .spine r args := by
  cases c with
  | bot => exact Or.inl rfl
  | prop =>
      rw [LRSCoreCov.eq_def] at h
      exact (hs h.1).elim
  | sort =>
      rw [LRSCoreCov.eq_def] at h
      exact (hs h.1).elim
  | pi a f =>
      rw [LRSCoreCov.eq_def] at h
      exact (hs h.1).elim
  | lam f =>
      rw [LRSCoreCov.eq_def] at h
      obtain ⟨D, B, hr, _⟩ := h
      exact (hp ⟨D, B, hr⟩).elim
  | spine r args => exact Or.inr ⟨r, args, rfl⟩

/-- Every rigid spine is compact-typed at the actual non-proposition Nat
family code. This uses the imported strict-to-covariant inclusion. -/
theorem covX_nat_spine_realization (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (r : Nat) (args : List CptT) :
    HereditaryCovRealizationXAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (covXNatView n Γ) ρ (.spine r args) := by
  refine ⟨.const 0 [], .spine 0 [], .refl _, ?_, ?_, ?_⟩
  · exact normalR_famAppCK2 natEnvUWfT
      (rfl : natEnvU.members 0 = some natFamMember) rfl Γ [] []
  · exact ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)
  · apply C2_includesS natEnvU
    rw [CTyS]
    exact Or.inr ⟨⟨r, args, rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

/-- Relatedness at the actual Nat base view supplies hereditary realization
for all compacts and all valuations, not only the displayed zero witness. -/
theorem covX_nat_realization_of_related (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (x y : Expr Nat) (c : CptT)
    (h : LRSCoreCovXAt (C2 natEnvU) (covXNatView n Γ) x y c) :
    HereditaryCovRealizationXAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (covXNatView n Γ) ρ c := by
  have hn : NormalR (WhStepCK2 natEnvU n) Γ (.const 0 []) :=
    normalR_famAppCK2 natEnvUWfT
      (rfl : natEnvU.members 0 = some natFamMember) rfl Γ [] []
  have hs : ¬ ∃ l, RedR (WhStepCK2 natEnvU n) Γ (.const 0 []) (.sort l) := by
    rintro ⟨l, hr⟩
    exact Expr.noConfusion (redR_of_normal hn hr)
  have hp : ¬ ∃ D B, RedR (WhStepCK2 natEnvU n) Γ (.const 0 []) (.pi D B) := by
    rintro ⟨D, B, hr⟩
    exact Expr.noConfusion (redR_of_normal hn hr)
  rcases covX_base_related_compact_shape (C2 natEnvU) hs hp h with rfl | ⟨r, args, rfl⟩
  · exact hereditaryCovRealizationXAt_bot (C2 natEnvU) n (covXNatView n Γ) ρ
  · exact covX_nat_spine_realization n Γ ρ r args

/-- The successor's non-bottom rigid function compact has complete
hereditary realization. Application may grow its compact spine. -/
theorem covX_natSucc_hereditary_realization (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    HereditaryCovRealizationXAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (covXNatArrowView n Γ) ρ (.spine 2 []) := by
  refine ⟨covX_natSucc_pi_gate, ?_⟩
  intro ds out ha hnb N N' hN hN' hc hd
  cases ha with
  | bot => exact (hnb rfl).elim
  | @appSpine r args arg u hu =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro c hc
        exact covX_nat_realization_of_related n Γ ρ N N' c (hd c hc)
      · exact covX_nat_spine_realization n (.assumption (.const 0 []) :: Γ)
          (EnvT.cons (demandT ds) ρ) 2 [u]
      · exact covX_nat_spine_realization n Γ ρ 2 [u]
      · exact covX_nat_spine_realization n Γ ρ 2 [u]

/-- Both repaired witnesses inhabit the same recursive target: the Eq alias
at concrete C2, and rigid successor in the admitted Nat environment. -/
theorem covX_eq_and_nat_hereditary_controls (n : Nat) (A B : Expr Nat) :
    HereditaryCovRealizationXAt (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n)
      (covXAliasPiView n A B) EnvT.bot covNormAliasIdentityCpt ∧
    HereditaryCovRealizationXAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n)
      (covXNatArrowView n []) EnvT.bot (.spine 2 []) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 1 []) (.spine 1 []) ∧
    LRSCoreCovXAt (C2 natEnvU) (covXNatView n [])
      (.const 1 []) (.const 1 []) (.spine 1 []) ∧
    (.spine 1 [] : CptT) ≠ .bot := by
  exact ⟨hereditaryCovRealizationXAt_covNormAliasPi (C2 eqEnvT)
      (C2_includesS eqEnvT) n EnvT.bot A B,
    covX_natSucc_hereditary_realization n [] EnvT.bot,
    ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero),
    covX_natZero_related n [], fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_REALIZATION_NAT_ROOTS
#print axioms covX_base_related_compact_shape
#print axioms covX_nat_spine_realization
#print axioms covX_nat_realization_of_related
#print axioms covX_natSucc_hereditary_realization
#print axioms covX_eq_and_nat_hereditary_controls
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_REALIZATION_NAT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXRealizationNatAudit
