import rcic.RcicNativeTypedModelKInherited
import rcic.RcicNativeTypedModelTypingFin

/-!
# Covariant typing of the inherited closed counterexample

`CTyCov` is imported without alteration.  Its original environment and global
typing statements are hardwired to `ApproxT`; the new `M` names below expose
the same interface for a context model and specialize definitionally to the
original statements.  In particular, let-value coherence is retained.

The old closed `cexTerm` and `cexType` satisfy covariant typing for every
valuation and every observation.  Two imported lambda cases, and two imported
Pi cases, respectively prove the statements; no global induction supplier is
assumed.  Agreement on the K-free expressions transports them to `ApproxTK`.

This local success does not make global covariant typing satisfiable.  The
imported rigid `Nat.succ` compact still has no covariant type at any observation
of its declared Pi type.  The model-parametric theorem gives the exact three-way boundary
for any model retaining those observations.  Both sides of the measurement use
actual native typing and non-bottom observations.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovKAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit
open Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit

variable {E : ResolvedEnv} {M N : CtxModelT E}

/-- The imported covariant compact typing, with a model-parametric type observation. -/
def ElTCovM (M : CtxModelT E) (ρ : EnvT) (A : Expr Nat) (u : CptT) : Prop :=
  ∃ a, M.Ap ρ A a ∧ CTyCov E u a

/-- Pointwise covariant variable typing together with actual let-value coherence. -/
def EnvTypedCovAtM (M : CtxModelT E) (Γ : LCtx) (ρ : EnvT) : Prop :=
  (∀ i A, lookupType Γ i = some A → ∀ u, ρ i u → ElTCovM M ρ A u) ∧
    CtxEnvM M Γ ρ

/-- The local covariant typing obligation at a fixed term and declared type. -/
def CovTypingAtM (M : CtxModelT E) (Γ : LCtx) (e A : Expr Nat) : Prop :=
  ∀ {ρ : EnvT}, EnvTypedCovAtM M Γ ρ → ∀ u, M.Ap ρ e u → ElTCovM M ρ A u

/-- The exact model-parametric counterpart of the imported global typing statement. -/
def TypingLemmaEnvCovM (M : CtxModelT E) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {e A : Expr Nat}, HasTyT E n Γ e A → CovTypingAtM M Γ e A

theorem elTCovM_approxT_iff (ρ : EnvT) (A : Expr Nat) (u : CptT) :
    ElTCovM (ctxModelT_approxT E) ρ A u ↔ ElTCov E ρ A u := Iff.rfl

theorem envTypedCovAtM_approxT_iff (Γ : LCtx) (ρ : EnvT) :
    EnvTypedCovAtM (ctxModelT_approxT E) Γ ρ ↔ EnvTypedCovAtT E Γ ρ := Iff.rfl

theorem typingLemmaEnvCovM_approxT_iff (n : Nat) :
    TypingLemmaEnvCovM (ctxModelT_approxT E) n ↔ TypingLemmaEnvCovT E n := Iff.rfl

theorem envTypedCovAtM_nil (M : CtxModelT E) (ρ : EnvT) :
    EnvTypedCovAtM M [] ρ :=
  ⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩

/-- A supplied old pointwise environment typing transports in the valid
direction; let-value coherence is a separate, retained premise. -/
theorem envTypedCovAtM_of_envTypedAtT {Γ : LCtx} {ρ : EnvT}
    (hρ : EnvTypedAtT M Γ ρ) (hV : CtxEnvM M Γ ρ) : EnvTypedCovAtM M Γ ρ := by
  refine ⟨?_, hV⟩
  intro i A hA u hu
  obtain ⟨a, ha, hua⟩ := hρ i A hA u hu
  exact ⟨a, ha, ctyCov_of_ctyS a u hua⟩

/-- Only agreement at the type expression is needed to move this typing witness. -/
theorem elTCovM_congr {A : Expr Nat} (hA : ModelAgreementAtT M N A)
    (ρ : EnvT) (u : CptT) : ElTCovM M ρ A u ↔ ElTCovM N ρ A u := by
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, (hA ρ a).mp ha, hu⟩
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, (hA ρ a).mpr ha, hu⟩

/-- All observations of the old closed term are covariantly typed. -/
theorem covTyping_cexTerm (E : ResolvedEnv) (ρ : EnvT) {u : CptT}
    (hu : ApproxT E ρ cexTerm u) : ElTCov E ρ cexType u := by
  apply covTyping_lam (envTypedCovAtT_nil E ρ) ?_ hu
  intro ρ₁ hρ₁ c hc
  apply covTyping_lam hρ₁ ?_ hc
  intro ρ₂ _ d hd
  exact covTyping_sort E ρ₂ .zero hd

/-- All observations of the declared type are covariantly typed at its native universe. -/
theorem covTyping_cexType (E : ResolvedEnv) (ρ : EnvT) {u : CptT}
    (hu : ApproxT E ρ cexType u) :
    ElTCov E ρ (.sort (.imax U2 (.imax U1 U2))) u := by
  apply covTyping_pi (envTypedCovAtT_nil E ρ) ?_ ?_ hu
  · intro ρ₁ _ c hc
    exact covTyping_sort E ρ₁ U1 hc
  · intro ρ₁ hρ₁ c hc
    apply covTyping_pi hρ₁ ?_ ?_ hc
    · intro ρ₂ hρ₂ d hd
      exact covTyping_bvar hρ₂ (i := 0) (A := .sort U1) rfl hd
    · intro ρ₂ _ d hd
      exact covTyping_sort E ρ₂ U1 hd

/-- K-free transport of the complete local typing statement, not one selected compact. -/
theorem covTyping_cexTerm_approxTK (E : ResolvedEnv) (n : Nat) (Ξ : LCtx) :
    CovTypingAtM (ctxModelT_approxTK E n Ξ) [] cexTerm cexType := by
  intro ρ _ u hu
  obtain ⟨a, ha, hua⟩ := covTyping_cexTerm E ρ (approxTK_forget hu)
  exact ⟨a, ApproxTK.free (kFreeT_cexType E) ha, hua⟩

theorem covTyping_cexType_approxTK (E : ResolvedEnv) (n : Nat) (Ξ : LCtx) :
    CovTypingAtM (ctxModelT_approxTK E n Ξ) [] cexType
      (.sort (.imax U2 (.imax U1 U2))) := by
  intro ρ _ u hu
  obtain ⟨a, ha, hua⟩ := covTyping_cexType E ρ (approxTK_forget hu)
  exact ⟨a, ApproxTK.free (kFreeT_sort E _) ha, hua⟩

/-- The exact old counterexample now has an actually realized non-bottom type code. -/
theorem closed_cex_cov_control_approxTK (E : ResolvedEnv) (n : Nat) :
    Nonempty (HasTyT E n [] cexTerm cexType) ∧
    Nonempty (HasTyT E n [] cexType (.sort (.imax U2 (.imax U1 U2)))) ∧
    EnvTypedCovAtM (ctxModelT_approxTK E n []) [] EnvT.bot ∧
    ApproxTK E n [] EnvT.bot cexTerm cexCpt ∧ cexCpt ≠ .bot ∧
    ∃ a, ApproxTK E n [] EnvT.bot cexType a ∧ CTyCov E cexCpt a ∧ a ≠ .bot := by
  have hρ := envTypedCovAtM_nil (ctxModelT_approxTK E n []) EnvT.bot
  have he := approxTK_cexTerm E n []
  obtain ⟨a, ha, hca⟩ := covTyping_cexTerm_approxTK E n [] hρ cexCpt he
  refine ⟨⟨hasTyT_cexTerm E n⟩, ⟨hasTyT_cexType E n⟩, hρ, he,
    (fun h => CptT.noConfusion h), a, ha, hca, ?_⟩
  intro h
  subst a
  exact CptT.noConfusion (ctyCov_bot_inv hca)

/-- The local positive is inhabited in both requested admitted environments. -/
theorem closed_cex_cov_eq_nat_controls (n : Nat) :
    (Nonempty (EnvWfT eqEnvT) ∧
      ElTCovM (ctxModelT_approxTK eqEnvT n []) EnvT.bot cexType cexCpt) ∧
    (Nonempty (EnvWfT natEnvU) ∧
      ElTCovM (ctxModelT_approxTK natEnvU n []) EnvT.bot cexType cexCpt) := by
  refine ⟨⟨⟨pinEqGroupWfT⟩, ?_⟩, ⟨⟨natEnvUWfT⟩, ?_⟩⟩
  · exact covTyping_cexTerm_approxTK eqEnvT n [] (envTypedCovAtM_nil _ _)
      cexCpt (approxTK_cexTerm eqEnvT n [])
  · exact covTyping_cexTerm_approxTK natEnvU n [] (envTypedCovAtM_nil _ _)
      cexCpt (approxTK_cexTerm natEnvU n [])

/-- Fixed `CptT / CTyCov`: preserving the rigid successor observation and
the old Pi-type observations excludes the old global covariant typing shape.
Only source observation and target inclusion are used, not full model equality. -/
theorem not_cov_global_of_natSucc_observations (M : CtxModelT natEnvU) (n : Nat)
    (he : M.Ap EnvT.bot (.const 2 []) (.spine 2 []))
    (hA : ∀ a, M.Ap EnvT.bot (.pi (.const 0 []) (.const 0 [])) a →
      ApproxT natEnvU EnvT.bot (.pi (.const 0 []) (.const 0 [])) a) :
    ¬ TypingLemmaEnvCovM M n := by
  intro hTL
  obtain ⟨a, ha, hca⟩ := hTL (hasTyT_natEnvU_succ n [])
    (envTypedCovAtM_nil M EnvT.bot) (.spine 2 []) he
  exact not_elTCov_natSucc_spine EnvT.bot ⟨a, hA a ha, hca⟩

/-- The covariant global obstruction is K-free and survives the new K clause. -/
theorem not_typingLemmaEnvCovM_approxTK_natEnvU (n : Nat) (Ξ : LCtx) :
    ¬ TypingLemmaEnvCovM (ctxModelT_approxTK natEnvU n Ξ) n :=
  not_cov_global_of_natSucc_observations _ n
    (ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine EnvT.bot))
    (fun _ h => approxTK_forget h)

/-- A fully typed, non-bottom witness of the remaining covariant obstruction. -/
theorem nat_succ_cov_obstruction_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    EnvTypedCovAtM (ctxModelT_approxTK natEnvU n []) [] EnvT.bot ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    CptT.spine 2 [] ≠ .bot ∧
    ¬ ElTCovM (ctxModelT_approxTK natEnvU n []) EnvT.bot
      (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) := by
  refine ⟨⟨natEnvUWfT⟩, ⟨hasTyT_natEnvU_succ n []⟩,
    envTypedCovAtM_nil _ _,
    ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine EnvT.bot),
    (fun h => CptT.noConfusion h), ?_⟩
  rintro ⟨a, ha, hca⟩
  exact not_elTCov_natSucc_spine EnvT.bot ⟨a, approxTK_forget ha, hca⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_K_TYPING_ROOTS
#print axioms ElTCovM
#print axioms EnvTypedCovAtM
#print axioms CovTypingAtM
#print axioms TypingLemmaEnvCovM
#print axioms elTCovM_approxT_iff
#print axioms envTypedCovAtM_approxT_iff
#print axioms typingLemmaEnvCovM_approxT_iff
#print axioms envTypedCovAtM_nil
#print axioms envTypedCovAtM_of_envTypedAtT
#print axioms elTCovM_congr
#print axioms covTyping_cexTerm
#print axioms covTyping_cexType
#print axioms covTyping_cexTerm_approxTK
#print axioms covTyping_cexType_approxTK
#print axioms closed_cex_cov_control_approxTK
#print axioms closed_cex_cov_eq_nat_controls
#print axioms not_cov_global_of_natSucc_observations
#print axioms not_typingLemmaEnvCovM_approxTK_natEnvU
#print axioms nat_succ_cov_obstruction_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_K_TYPING_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovKAudit
