import rcic.RcicNativeTypedModelCovWIrrelAligned
import rcic.RcicNativeTypedModelCovWEtaKGuardControl
import rcic.RcicNativeTypedModelCovWEtaHoControl

/-!
# Per-call K controls after proof-field erasure

The Eq, True and And supplies are direct derivations in the repaired
grammar. They retain the existing canon, index and common-typing
certificates. Old aligned observations are used only for the unchanged
computation-source premise of the K constructor. The And right-hand side
has a fresh raw derivation with empty demands.

The apart-index, blocked-index and ineligible higher-order exclusions are
transported through erasure from exclusions proved for the complete old
eta grammar. Both decorated and erased observations are classified.
There is no old-to-new observation embedding. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelKIndexFreeAudit TypedModelKGuardAudit TypedModelKControlAudit
open TypedModelKObstructionAudit TypedModelKTransportAudit TypedModelW6IotaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open ReadbackCK2IndexAudit ReadbackCK2ModelObstructionAudit ReadbackCK2InputsAudit
open PiProbeModelBoundaryAudit TypedModelCovTAudit TypedModelCovVAudit
open TypedModelCovWAudit TypedModelCovWEtaAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem k_empty_application {E : ResolvedEnv} {n : Nat}
    {ρ : EnvWIrrel} {f x : Expr Nat} {c : CptWIrrel}
    (h : ApproxTWIrrel E n ρ f (.lam [([], c)])) :
    ApproxTWIrrel E n ρ (.app f x) c :=
  .app h (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

private theorem k_empty_lambda {E : ResolvedEnv} {n : Nat}
    {ρ : EnvWIrrel} {A b : Expr Nat} {c : CptWIrrel} (hc : c ≠ .bot)
    (h : ApproxTWIrrel E n (EnvWIrrel.cons (demandWIrrel []) ρ) b c) :
    ApproxTWIrrel E n ρ (.lam A b) (.lam [([], c)]) := by
  refine .lam (.bot _ _) ?_ ⟨([], c), List.mem_singleton.mpr rfl, hc⟩ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact h

/-- A fresh saturated Eq call with its unchanged actual-call certificates. -/
theorem covWIrrel_K_eqGap_observed (n : Nat) (ρ : EnvWIrrel) :
    ApproxTKWIrrel eqEnvT n eqGapCtx ρ eqGapRedex .prop :=
  .recursorPropK eqGapW (.bvar 0) (Or.inl ⟨rfl, rfl, rfl⟩)
    not_isCtorSpine_bvar (kIndexGuardAt_eqGap n) (kCommonAt_eqGap n)
    (approxTKN_forgetN (covV_approxTK_of_native_heads covV_eq_native_heads
      (approxTK_eqGap_prop n (covWIrrelEnvErase ρ))))
    (.free (kFreeT_sort eqEnvT .zero) (.sort ρ .zero))

theorem covWIrrel_trueK_observed (n : Nat) (ρ : EnvWIrrel) :
    ApproxTKWIrrel trueEnvU n kVarCtx ρ (kRec (.bvar 0)) .prop :=
  .recursorPropK wTrueRecU (.bvar 0) (Or.inl ⟨rfl, rfl, rfl⟩)
    not_isCtorSpine_bvar (covW_trueK_index n) (covW_trueK_common n)
    (approxTKN_forgetN
      (covV_trueK_observed n kVarCtx (covWIrrelEnvErase ρ) (.bvar 0)))
    (.free (kFreeT_sort trueEnvU .zero) (.sort ρ .zero))

/-- The two proof projections receive empty demands in this fresh raw row. -/
theorem covWIrrel_andK_rhs_observed (ρ : EnvWIrrel) :
    ApproxTKWIrrel andEnvU 0 mixAndCtx ρ (iotaRhsOf covWAndCanonWitness)
      (.pi .bot []) := by
  apply ApproxTKWIrrel.free (kFreeT_andEnvU _)
  apply k_empty_application
  apply k_empty_application
  apply k_empty_lambda (by intro h; cases h)
  apply k_empty_lambda (by intro h; cases h)
  exact .pi (.bot _ _) (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim)

theorem covWIrrel_andK_observed (ρ : EnvWIrrel) :
    ApproxTKWIrrel andEnvU 0 mixAndCtx ρ mixAndRedex (.pi .bot []) :=
  .recursorPropK covWAndCanonWitness (.bvar 0) covW_andK_canon
    not_isCtorSpine_bvar covW_andK_index covW_andK_common
    (approxTKN_forgetN (covV_andK_observed 0 mixAndCtx (covWIrrelEnvErase ρ)))
    (covWIrrel_andK_rhs_observed ρ)

/-- All native premises are inhabited; the two displayed observations are new. -/
theorem covWIrrel_K_eqGap_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    Nonempty (HasTyT eqEnvT n eqGapCtx eqGapRedex (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n eqGapCtx eqGapRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KIndexGuardAt eqEnvT n eqGapCtx eqGapW ∧
    KCommonAt eqEnvT n eqGapCtx eqGapW (.bvar 0) ∧
    KCanonW eqGapW (.bvar 0) ∧
    KNativeHead eqEnvT n eqGapCtx eqGapRedex (.sort .zero) ∧
    ApproxTKWIrrel eqEnvT n eqGapCtx EnvWIrrel.bot eqGapRedex .prop ∧
    ApproxTKWIrrel eqEnvT n eqGapCtx EnvWIrrel.bot (.sort .zero) .prop := by
  obtain ⟨hW, hΓ, ht, hc, hi, hk, _, _⟩ := covW_K_eqGap_control n
  exact ⟨hW, hΓ, ht, hc, hi, kCommonAt_eqGap n, Or.inl ⟨rfl, rfl, rfl⟩,
    hk, covWIrrel_K_eqGap_observed n EnvWIrrel.bot,
    .free (kFreeT_sort eqEnvT .zero) (.sort _ .zero)⟩

theorem covWIrrel_trueK_control (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n kVarCtx) ∧
    Nonempty (NativeSpineHead.Step trueEnvU n kVarCtx
      (kRec (.bvar 0)) (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT trueEnvU n kVarCtx (.sort .zero)
      (kRec (.bvar 0)) (.sort (.succ .zero))) ∧
    KIndexGuardAt trueEnvU n kVarCtx wTrueRecU ∧
    KCommonAt trueEnvU n kVarCtx wTrueRecU (.bvar 0) ∧
    KCanonW wTrueRecU (.bvar 0) ∧
    ApproxTKWIrrel trueEnvU n kVarCtx EnvWIrrel.bot (kRec (.bvar 0)) .prop ∧
    RedR (WhStepCK2 trueEnvU n) kVarCtx (kRec (.bvar 0)) (.sort .zero) := by
  obtain ⟨hW, hΓ, hs, hc, hi, hcommon, _, hr⟩ := covW_trueK_control n
  exact ⟨hW, hΓ, hs, hc, hi, hcommon, Or.inl ⟨rfl, rfl, rfl⟩,
    covWIrrel_trueK_observed n EnvWIrrel.bot, hr⟩

theorem covWIrrel_andK_control :
    Nonempty (EnvWfT andEnvU) ∧ Nonempty (CtxWfT andEnvU 0 mixAndCtx) ∧
    Nonempty (NativeSpineHead.Step andEnvU 0 mixAndCtx mixAndRedex mixAndRhs
      (.app mixAndMot mixAndMkApp)) ∧
    Nonempty (ConvT andEnvU 0 mixAndCtx mixAndRedex mixPi
      (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
    KIndexGuardAt andEnvU 0 mixAndCtx covWAndCanonWitness ∧
    KCommonAt andEnvU 0 mixAndCtx covWAndCanonWitness (.bvar 0) ∧
    KCanonW covWAndCanonWitness (.bvar 0) ∧
    ApproxTKWIrrel andEnvU 0 mixAndCtx EnvWIrrel.bot mixAndRedex (.pi .bot []) ∧
    RedR (WhStepCK2 andEnvU 0) mixAndCtx mixAndRedex mixPi := by
  obtain ⟨hW, hΓ, hs, hc, hi, hcommon, _, hr⟩ := covW_andK_control
  exact ⟨hW, hΓ, hs, hc, hi, hcommon, covW_andK_canon,
    covWIrrel_andK_observed EnvWIrrel.bot, hr⟩

/-- The retained positive outputs are also observations in the old compact
codomain; their statement contains no universe-provenance information. -/
theorem covWIrrel_K_erased_positive_controls (n : Nat) :
    CovWIrrelObservation eqEnvT n eqGapCtx EnvWIrrel.bot eqGapRedex .prop ∧
    CovWIrrelObservation trueEnvU n kVarCtx EnvWIrrel.bot (kRec (.bvar 0)) .prop ∧
    CovWIrrelObservation andEnvU 0 mixAndCtx EnvWIrrel.bot mixAndRedex (.pi .bot []) :=
  ⟨covWIrrel_observation_of (covWIrrel_K_eqGap_observed n EnvWIrrel.bot),
    covWIrrel_observation_of (covWIrrel_trueK_observed n EnvWIrrel.bot),
    covWIrrel_observation_of (covWIrrel_andK_observed EnvWIrrel.bot)⟩

theorem covWIrrel_apart_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel} (h : ApproxTKWIrrel eqEnvT n Γ ρ apartRec c) : c = .bot :=
  (covWIrrel_erase_bot_iff c).mp
    (covWEta_apart_only_bot (covWIrrel_guarded_forget h))

theorem covWIrrel_etaIndex_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel} (h : ApproxTKWIrrel eqEnvT n Γ ρ etaIndexRedex c) : c = .bot :=
  (covWIrrel_erase_bot_iff c).mp
    (covWEta_etaIndex_only_bot (covWIrrel_guarded_forget h))

theorem covWIrrel_apart_observation_iff (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (c : CptT) :
    CovWIrrelObservation eqEnvT n Γ ρ apartRec c ↔ c = .bot := by
  constructor
  · intro h
    exact covWEta_apart_only_bot (covWIrrel_observation_forget h)
  · intro hc
    subst c
    exact ⟨.bot, rfl, .bot _ _ _⟩

theorem covWIrrel_etaIndex_observation_iff (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (c : CptT) :
    CovWIrrelObservation eqEnvT n Γ ρ etaIndexRedex c ↔ c = .bot := by
  constructor
  · intro h
    exact covWEta_etaIndex_only_bot (covWIrrel_observation_forget h)
  · intro hc
    subst c
    exact ⟨.bot, rfl, .bot _ _ _⟩

theorem covWIrrel_K_apart_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n apartCtx) ∧
    Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n apartCtx apartRec apartRec (.sort (.succ .zero))) ∧
    ApproxTKWIrrel eqEnvT n apartCtx EnvWIrrel.bot apartRec .bot ∧
    (∀ ρ c, ApproxTKWIrrel eqEnvT n apartCtx ρ apartRec c → c = .bot) ∧
    ¬ ApproxTKWIrrel eqEnvT n apartCtx EnvWIrrel.bot apartRec .prop := by
  obtain ⟨hW, hΓ, ht, hc, _, _, _⟩ := covWEta_K_apart_control n
  exact ⟨hW, hΓ, ht, hc, .bot _ _ _, fun _ _ h => covWIrrel_apart_only_bot h,
    fun h => CptWIrrel.noConfusion (covWIrrel_apart_only_bot h)⟩

/-- The native K step stays inhabited while its independent index guard
fails. Eta does not add a nonbottom observation at the blocked source. -/
theorem covWIrrel_K_eta_guard_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (HasTyT eqEnvT n etaEqCtx etaIndexRedex (.sort (.succ .zero))) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KNativeHead eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) ∧
    ApproxTKWIrrel eqEnvT n etaEqCtx EnvWIrrel.bot etaIndexRedex .bot ∧
    ApproxTKWIrrel eqEnvT n etaEqCtx EnvWIrrel.bot (.sort .zero) .prop ∧
    (∀ ρ c, ApproxTKWIrrel eqEnvT n etaEqCtx ρ etaIndexRedex c → c = .bot) ∧
    ¬ KIndexGuardAt eqEnvT n etaEqCtx
      (eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex etaIndexMot (.sort .zero)) := by
  obtain ⟨hW, hΓ, ht, hc, hk, _, _, _, hg⟩ := covWEta_K_eta_guard_control n
  exact ⟨hW, hΓ, ht, hc, hk, .bot _ _ _,
    .free (kFreeT_sort eqEnvT .zero) (.sort _ .zero),
    fun _ _ h => covWIrrel_etaIndex_only_bot h, hg⟩

theorem covWIrrel_ineligible_prop_head_only_bot {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    (hnF : ¬ KFreeRec E w.recRef) (hnP : ¬ KProjRec E w.recRef)
    (h : ApproxTKWIrrel E n Γ ρ e c)
    (hh : headConst e = some w.recRef) : c = .bot :=
  (covWIrrel_erase_bot_iff c).mp
    (covWEta_ineligible_prop_head_only_bot w hP hnF hnP
      (covWIrrel_guarded_forget h) hh)

theorem covWIrrel_ineligible_prop_spine {E : ResolvedEnv}
    (w : IotaWitnessS E) (hP : PropFamilyS w)
    (hnF : ¬ KFreeRec E w.recRef) (hnP : ¬ KProjRec E w.recRef)
    (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) (ls : List Level) (args : List (Expr Nat)) :
    ApproxTKWIrrel E n Γ ρ (foldApps (.const w.recRef ls) args) .bot ∧
    ∀ c, ApproxTKWIrrel E n Γ ρ (foldApps (.const w.recRef ls) args) c → c = .bot := by
  refine ⟨.bot _ _ _, ?_⟩
  intro c h
  exact covWIrrel_ineligible_prop_head_only_bot w hP hnF hnP h
    (by simp only [headConst_foldApps, headConst])

theorem covWIrrelHo_type_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel} (h : ApproxTKWIrrel covUHoEnv n Γ ρ covUHoType c) : c = .bot :=
  (covWIrrel_erase_bot_iff c).mp
    (covWEtaHo_type_only_bot (covWIrrel_guarded_forget h))

theorem covWIrrelHo_type_observation_iff (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (c : CptT) :
    CovWIrrelObservation covUHoEnv n Γ ρ covUHoType c ↔ c = .bot := by
  constructor
  · intro h
    exact covWEtaHo_type_only_bot (covWIrrel_observation_forget h)
  · intro hc
    subst c
    exact ⟨.bot, rfl, .bot _ _ _⟩

/-- The divergent higher-order fixture retains actual admission, native
typing, a new closing realizer and bottom supply, and no normal reduct. -/
theorem covWIrrelHo_repaired_instance (n : Nat) :
    Nonempty (EnvWfT covUHoEnv) ∧ Nonempty (CtxWfT covUHoEnv n []) ∧
    CovWIrrelRealized covUHoEnv n 1 [] EnvWIrrel.bot SubstT.id ∧
    Nonempty (HasTyT covUHoEnv n [] covUHoType (.sort (.succ .zero))) ∧
    ApproxTKWIrrelStage covUHoEnv n 1 [] EnvWIrrel.bot covUHoType .bot ∧
    (∀ c, ApproxTKWIrrel covUHoEnv n [] EnvWIrrel.bot covUHoType c → c = .bot) ∧
    ¬ ∃ N, RedR (WhStepCK2 covUHoEnv n) [] covUHoType N ∧
      NormalR (WhStepCK2 covUHoEnv n) [] N :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, covWIrrel_realized_nil covUHoEnv n 1,
    ⟨covUHoType_hasTy n []⟩,
    ⟨.bot _ _ _, by simp [covTObservationBudget, covWIrrelErase]⟩,
    (fun _ h => covWIrrelHo_type_only_bot h), covUHoType_no_normal_head n []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_K_CONTROLS_ROOTS
#print axioms covWIrrel_K_eqGap_observed
#print axioms covWIrrel_trueK_observed
#print axioms covWIrrel_andK_rhs_observed
#print axioms covWIrrel_andK_observed
#print axioms covWIrrel_K_eqGap_control
#print axioms covWIrrel_trueK_control
#print axioms covWIrrel_andK_control
#print axioms covWIrrel_K_erased_positive_controls
#print axioms covWIrrel_apart_only_bot
#print axioms covWIrrel_etaIndex_only_bot
#print axioms covWIrrel_apart_observation_iff
#print axioms covWIrrel_etaIndex_observation_iff
#print axioms covWIrrel_K_apart_control
#print axioms covWIrrel_K_eta_guard_control
#print axioms covWIrrel_ineligible_prop_head_only_bot
#print axioms covWIrrel_ineligible_prop_spine
#print axioms covWIrrelHo_type_only_bot
#print axioms covWIrrelHo_type_observation_iff
#print axioms covWIrrelHo_repaired_instance
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_K_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
