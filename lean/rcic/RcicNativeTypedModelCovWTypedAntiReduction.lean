import rcic.RcicNativeTypedModelCovWControls
import rcic.RcicNativeTypedModelCovWBasicK

/-!
# Inhabited typed-demand failures of backward CK2 observation

The guarded eta-index call is natively typed at `Sort 1` and takes a native
CK2 step to `Sort 0`. The latter has the nonbottom observation `.prop`,
typed by `CTyS` at the actual `.sort` observation of `Sort 1`. The source
has only bottom observations because the unchanged independent DI index
guard fails. Its explicit normal reduct rules out a normalization reading
of this obstruction.

The strict raw relation has a separate, simpler failure at the actual True
K call. Every Prop recursor spine is bottom-only in that relation. Native
typing, the K guard, the native step, and the guarded source observation
are nevertheless supplied. Thus the raw failure does not assert failure
of the guarded True control.

Both instances carry the actual finite-joint typed bottom valuation. The
guarded source, reduct, and native type observations coexist at stage 1;
native universe-parameter arity remains the independent parameter `n`.
No closed realizer, global adequacy supplier, or new axiom is assumed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelKFragmentAudit TypedModelKIndexFreeAudit TypedModelKGuardAudit
open TypedModelKFailureAudit TypedModelKObstructionAudit TypedModelW6IotaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit ReadbackCK2IndexAudit
open ReadbackCK2NativeControlAudit ReadbackCK2ModelObstructionAudit
open TypedModelCovVAudit TypedModelCovSAudit TypedModelCovTAudit TypedModelCovWAudit

/-- The requested backward implication, even with admission, native typing
of both endpoints and the native type, an actual finite-joint typed
valuation, an observed native type code, and a nonbottom typed demand. -/
def covWTyped_antiReductionAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (M : CtxModelT E) (R : Expr Nat → Expr Nat → Prop) : Prop :=
  ∀ (ρ : EnvT) (e e' T : Expr Nat) (u : Level) (c a : CptT),
    Nonempty (EnvWfT E) → Nonempty (CtxWfT E n Γ) →
    EnvTypedFinAtT M Γ ρ →
    Nonempty (HasTyT E n Γ e T) → Nonempty (HasTyT E n Γ e' T) →
    Nonempty (HasTyT E n Γ T (.sort u)) →
    R e e' → M.Ap ρ e' c → M.Ap ρ T a → CTyS E c a → c ≠ .bot →
    M.Ap ρ e c

/-- Every premise is stored as evidence, including the normal reduct and
the actual observations. This is not a conditional head supplier. -/
structure covWTyped_failureAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (M : CtxModelT E) (e e' T : Expr Nat) (u : Level) (c a : CptT) : Prop where
  envWf : Nonempty (EnvWfT E)
  ctxWf : Nonempty (CtxWfT E n Γ)
  valuation : EnvTypedFinAtT M Γ EnvT.bot
  sourceTy : Nonempty (HasTyT E n Γ e T)
  reductTy : Nonempty (HasTyT E n Γ e' T)
  typeTy : Nonempty (HasTyT E n Γ T (.sort u))
  conversion : Nonempty (ConvT E n Γ e e' T)
  native : KNativeHead E n Γ e e'
  step : WhStepCK2 E n Γ e e'
  readback : RedR (WhStepCK2 E n) Γ e e'
  normal : NormalR (WhStepCK2 E n) Γ e'
  sourceBot : M.Ap EnvT.bot e .bot
  reductObservation : M.Ap EnvT.bot e' c
  typeObservation : M.Ap EnvT.bot T a
  demand : CTyS E c a
  nonbottom : c ≠ .bot
  sourceOnlyBot : ∀ (ρ : EnvT) (d : CptT), M.Ap ρ e d → d = .bot

theorem covWTyped_failureAt.refutes {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {M : CtxModelT E} {e e' T : Expr Nat} {u : Level} {c a : CptT}
    (h : covWTyped_failureAt E n Γ M e e' T u c a)
    {R : Expr Nat → Expr Nat → Prop} (hR : R e e') :
    ¬ covWTyped_antiReductionAt E n Γ M R := by
  intro hback
  exact h.nonbottom (h.sourceOnlyBot EnvT.bot c
    (hback EnvT.bot e e' T u c a h.envWf h.ctxWf h.valuation
      h.sourceTy h.reductTy h.typeTy hR h.reductObservation
      h.typeObservation h.demand h.nonbottom))

theorem covWTyped_guarded_bot_valuation (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    EnvTypedFinAtT (⟨ApproxTKW E n Γ⟩ : CtxModelT E) Γ EnvT.bot :=
  envTypedFinAtT_bot _ (fun ρ e => ApproxTKW.bot Γ ρ e) Γ

theorem covWTyped_raw_bot_valuation (E : ResolvedEnv) (Γ : LCtx) :
    EnvTypedFinAtT (⟨ApproxTW E⟩ : CtxModelT E) Γ EnvT.bot :=
  envTypedFinAtT_bot _ (fun ρ e => ApproxTW.bot ρ e) Γ

theorem covWTyped_prop_demand (E : ResolvedEnv) : CTyS E .prop .sort := by
  rw [CTyS]
  exact Or.inr TyCodeCT.prop

/-- The failure of the independent DI guard survives the entire guarded
observation grammar, not merely the displayed K introduction. -/
theorem covWTyped_eta_only_bot {n : Nat} {ρ : EnvT} {c : CptT}
    (h : ApproxTKW eqEnvT n etaEqCtx ρ etaIndexRedex c) : c = .bot :=
  covS_K_eta_observation_bot (covW_forget_old h)

theorem covWTyped_eta_failure (n : Nat) :
    covWTyped_failureAt eqEnvT n etaEqCtx
      (⟨ApproxTKW eqEnvT n etaEqCtx⟩ : CtxModelT eqEnvT)
      etaIndexRedex (.sort .zero) (.sort (.succ .zero))
      (.succ (.succ .zero)) .prop .sort := by
  obtain ⟨hW, hΓ, ht, hc, hk, hb, hp, honly, _⟩ := covW_K_eta_guard_control n
  exact {
    envWf := hW
    ctxWf := hΓ
    valuation := covWTyped_guarded_bot_valuation eqEnvT n etaEqCtx
    sourceTy := ht
    reductTy := ⟨.sort _ .zero⟩
    typeTy := ⟨.sort _ (.succ .zero)⟩
    conversion := hc
    native := hk
    step := .native hk
    readback := redR_single (.native hk)
    normal := normalR_sortCK2 etaEqCtx .zero
    sourceBot := hb
    reductObservation := hp
    typeObservation := covW_sort_observed eqEnvT n etaEqCtx EnvT.bot (.succ .zero)
    demand := covWTyped_prop_demand eqEnvT
    nonbottom := fun he => CptT.noConfusion he
    sourceOnlyBot := honly }

/-- All three actual observations use the same finite stage. The stage is
one even when the native universe-parameter arity `n` is zero. -/
theorem covWTyped_eta_same_stage (n : Nat) :
    ApproxTKWStage eqEnvT n 1 etaEqCtx EnvT.bot etaIndexRedex .bot ∧
    ApproxTKWStage eqEnvT n 1 etaEqCtx EnvT.bot (.sort .zero) .prop ∧
    ApproxTKWStage eqEnvT n 1 etaEqCtx EnvT.bot (.sort (.succ .zero)) .sort := by
  have h := covWTyped_eta_failure n
  exact ⟨⟨h.sourceBot, by simp [covTObservationBudget]⟩,
    ⟨h.reductObservation, by simp [covTObservationBudget]⟩,
    ⟨h.typeObservation, by simp [covTObservationBudget]⟩⟩

theorem covWTyped_no_guarded_step_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt eqEnvT n etaEqCtx
      (⟨ApproxTKW eqEnvT n etaEqCtx⟩ : CtxModelT eqEnvT)
      (WhStepCK2 eqEnvT n etaEqCtx) :=
  (covWTyped_eta_failure n).refutes (covWTyped_eta_failure n).step

theorem covWTyped_no_guarded_red_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt eqEnvT n etaEqCtx
      (⟨ApproxTKW eqEnvT n etaEqCtx⟩ : CtxModelT eqEnvT)
      (RedR (WhStepCK2 eqEnvT n) etaEqCtx) :=
  (covWTyped_eta_failure n).refutes (covWTyped_eta_failure n).readback

/-- Strict raw observation has no rule that can observe a Prop recursor
constant nontrivially, regardless of native K eligibility. -/
theorem covWTyped_raw_prop_const_only_bot {E : ResolvedEnv}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    {ρ : EnvT} {r : Nat} {ls : List Level} {c : CptT} (hr : r = w.recRef)
    (h : ApproxTW E ρ (.const r ls) c) : c = .bot := by
  cases h with
  | bot => rfl
  | const _ _ _ hrigid _ =>
      subst r
      exact (not_rigidConst_of_recursor w hrigid).elim
  | delta hd _ =>
      subst r
      exact (not_deltaConst_of_recursor w hd).elim
  | recursor _ hnp _ _ _ =>
      exact (hnp ((propFamilyS_iff_recRef_eq hr).mpr hP)).elim

theorem covWTyped_raw_app_only_bot {E : ResolvedEnv} {ρ : EnvT}
    {f x : Expr Nat} {c : CptT}
    (hf : ∀ d, ApproxTW E ρ f d → d = .bot)
    (h : ApproxTW E ρ (.app f x) c) : c = .bot := by
  cases h with
  | bot => rfl
  | app hfun _ _ => exact CptT.noConfusion (hf _ hfun)
  | appSpine hfun _ => exact CptT.noConfusion (hf _ hfun)

theorem covWTyped_raw_foldApps_only_bot {E : ResolvedEnv} {ρ : EnvT}
    (args : List (Expr Nat)) : ∀ f : Expr Nat,
    (∀ d, ApproxTW E ρ f d → d = .bot) →
    ∀ c, ApproxTW E ρ (foldApps f args) c → c = .bot := by
  induction args with
  | nil => intro f hf c hc; exact hf c hc
  | cons x args ih =>
      intro f hf c hc
      exact ih (.app f x) (fun _ h => covWTyped_raw_app_only_bot hf h) c hc

theorem covWTyped_raw_prop_spine_only_bot {E : ResolvedEnv}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    (ρ : EnvT) (ls : List Level) (args : List (Expr Nat))
    {c : CptT} (h : ApproxTW E ρ (foldApps (.const w.recRef ls) args) c) :
    c = .bot :=
  covWTyped_raw_foldApps_only_bot args (.const w.recRef ls)
    (fun _ hc => covWTyped_raw_prop_const_only_bot w hP rfl hc) c h

theorem covWTyped_raw_true_only_bot {ρ : EnvT} {c : CptT}
    (h : ApproxTW trueEnvU ρ (kRec (.bvar 0)) c) : c = .bot :=
  covWTyped_raw_prop_spine_only_bot covVTrueWitness (by rfl) ρ
    [.succ (.succ .zero)] [kMot, .sort .zero, .bvar 0] h

/-- The True K failure is specific to the strict raw relation; the
guarded relation positively observes this same typed native call. -/
theorem covWTyped_raw_true_failure (n : Nat) :
    covWTyped_failureAt trueEnvU n kVarCtx
      (⟨ApproxTW trueEnvU⟩ : CtxModelT trueEnvU)
      (kRec (.bvar 0)) (.sort .zero) (.sort (.succ .zero))
      (.succ (.succ .zero)) .prop .sort := by
  have hc := kRec_conv_sort (kVar_ty n)
  have he := convEnds trueEnvUWfT (kVarCtx_wf n) hc
  have hk := covW_trueK_native_head n
  exact {
    envWf := ⟨trueEnvUWfT⟩
    ctxWf := ⟨kVarCtx_wf n⟩
    valuation := covWTyped_raw_bot_valuation trueEnvU kVarCtx
    sourceTy := ⟨he.2.1⟩
    reductTy := ⟨.sort _ .zero⟩
    typeTy := ⟨.sort _ (.succ .zero)⟩
    conversion := ⟨.symm _ _ _ _ hc⟩
    native := hk
    step := .native hk
    readback := redR_single (.native hk)
    normal := normalR_sortCK2 kVarCtx .zero
    sourceBot := .bot _ _
    reductObservation := .sort _ .zero
    typeObservation := .sort _ (.succ .zero)
    demand := covWTyped_prop_demand trueEnvU
    nonbottom := fun he => CptT.noConfusion he
    sourceOnlyBot := fun _ _ h => covWTyped_raw_true_only_bot h }

theorem covWTyped_raw_true_guarded_control (n : Nat) :
    KIndexGuardAt trueEnvU n kVarCtx wTrueRecU ∧
    KCommonAt trueEnvU n kVarCtx wTrueRecU (.bvar 0) ∧
    ApproxTKWStage trueEnvU n 1 kVarCtx EnvT.bot (kRec (.bvar 0)) .prop :=
  ⟨covW_trueK_index n, covW_trueK_common n,
    covW_trueK_observed n EnvT.bot, by simp [covTObservationBudget]⟩

theorem covWTyped_no_raw_step_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt trueEnvU n kVarCtx
      (⟨ApproxTW trueEnvU⟩ : CtxModelT trueEnvU)
      (WhStepCK2 trueEnvU n kVarCtx) :=
  (covWTyped_raw_true_failure n).refutes (covWTyped_raw_true_failure n).step

theorem covWTyped_no_raw_red_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt trueEnvU n kVarCtx
      (⟨ApproxTW trueEnvU⟩ : CtxModelT trueEnvU)
      (RedR (WhStepCK2 trueEnvU n) kVarCtx) :=
  (covWTyped_raw_true_failure n).refutes (covWTyped_raw_true_failure n).readback

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_TYPED_ANTI_REDUCTION_ROOTS
#print axioms covWTyped_antiReductionAt
#print axioms covWTyped_failureAt
#print axioms covWTyped_failureAt.refutes
#print axioms covWTyped_guarded_bot_valuation
#print axioms covWTyped_raw_bot_valuation
#print axioms covWTyped_prop_demand
#print axioms covWTyped_eta_only_bot
#print axioms covWTyped_eta_failure
#print axioms covWTyped_eta_same_stage
#print axioms covWTyped_no_guarded_step_antiReduction
#print axioms covWTyped_no_guarded_red_antiReduction
#print axioms covWTyped_raw_prop_const_only_bot
#print axioms covWTyped_raw_app_only_bot
#print axioms covWTyped_raw_foldApps_only_bot
#print axioms covWTyped_raw_prop_spine_only_bot
#print axioms covWTyped_raw_true_only_bot
#print axioms covWTyped_raw_true_failure
#print axioms covWTyped_raw_true_guarded_control
#print axioms covWTyped_no_raw_step_antiReduction
#print axioms covWTyped_no_raw_red_antiReduction
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_TYPED_ANTI_REDUCTION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit
