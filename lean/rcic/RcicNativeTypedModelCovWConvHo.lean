import rcic.RcicNativeTypedModelCovWConvForget

/-! Re-measure the W cells after legacy alignment. Every spine at its
recursor head is bottom-only; no absence of arbitrary ConvT derivations is
inferred from this fact. The existing native beta/zeta/eta/irr witnesses
are reused unchanged. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWAudit
open TypedModelCovWIrrelAudit TypedModelCovWMatrixAudit TypedModelW6IotaAudit
open TypedModelCovWNativeAudit
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The stronger invariant needs no condition on the W major. -/
theorem covWConv_Ho_head_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {e : Expr Nat} {c : CptWConvR} (h : ApproxTKWConv covUHoEnv n Γ ρ e c) :
    ∀ {ls k}, CovWIrrelHeadTerm 65 ls k e → c = .bot := by
  induction h with
  | bot => intro _ _ _; rfl
  | bvar => intro _ _ hh; cases hh
  | sort => intro _ _ hh; cases hh
  | const Γ ρ r ls hr hp =>
      intro _ _ hh
      have he : r = 65 := Option.some.inj hh.headConst
      subst r
      exact (not_rigidConst_of_recursor covUHoWitness hr).elim
  | recursor ls hi hnp hpre hfld h ih =>
      intro _ _ hh
      exact (hnp (covVHo_rec_family_prop _ (Option.some.inj hh.headConst))).elim
  | pi => intro _ _ hh; cases hh
  | lam => intro _ _ hh; cases hh
  | app hf hs ha ihf iha =>
      intro _ _ hh
      cases hh with
      | app hp => cases ihf hp
  | appSpine hf ha hslot hfield ihf iha =>
      intro _ _ hh
      cases hh with
      | app hp => cases ihf hp
  | @delta Γ ρ r ls m b c hd h ih =>
      intro _ _ hh
      have he : r = 65 := Option.some.inj hh.headConst
      subst r
      exact (not_deltaConst_of_recursor covUHoWitness hd).elim
  | letE => intro _ _ hh; cases hh
  | lit => intro _ _ hh; cases hh
  | iota w hl hr h ih =>
      intro _ _ hh
      have he := hh.headConst
      simp only [iotaLhsOf, recCall, headConst_foldApps, headConst] at he
      exact (covUHo_no_legacy_witness w (Option.some.inj he)).elim
  | recursorPropK w x hk h ih =>
      intro _ _ hh
      have he := hh.headConst
      simp only [recCall, headConst_foldApps, headConst] at he
      exact (covUHo_no_legacy_witness w (Option.some.inj he)).elim
  | eta he hD ht hne hb ihD ihb =>
      intro _ _ hh
      obtain ⟨s, hs, hn⟩ := hne
      exact (hn (ihb s hs (.app hh.lift_one))).elim

/-- I*: the constructor-major W call now has the correct bottom-only value. -/
theorem covWConv_Ho_ctor_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {c : CptWConvR} (h : ApproxTKWConv covUHoEnv n Γ ρ covWMatrixIotaSource c) : c = .bot :=
  covWConv_Ho_head_only_bot h (.app (.app (.app .head)))

theorem covWConv_Ho_divergent_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {c : CptWConvR} (h : ApproxTKWConv covUHoEnv n Γ ρ covUHoType c) : c = .bot :=
  covWConv_Ho_head_only_bot h (.app (.app (.app .head)))

theorem covWConv_Ho_beta_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {c : CptWConvR} (h : ApproxTKWConv covUHoEnv n Γ ρ covWNativeHoBetaSource c) : c = .bot :=
  (covWConvRaw_erase_bot_iff c).mp
    (covWNativeHo_beta_only_bot (covWConv_forget covUHoEnv_wf h))

theorem covWConv_Ho_let_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {c : CptWConvR} (h : ApproxTKWConv covUHoEnv n Γ ρ covWNativeHoLetSource c) : c = .bot :=
  (covWConvRaw_erase_bot_iff c).mp
    (covWNativeHo_let_only_bot (covWConv_forget covUHoEnv_wf h))

theorem covWConv_Ho_fn_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {c : CptWConvR} (h : ApproxTKWConv covUHoEnv n Γ ρ covWNativeHoBetaFn c) : c = .bot :=
  (covWConvRaw_erase_bot_iff c).mp
    (covWNativeHo_beta_fn_only_bot (covWConv_forget covUHoEnv_wf h))

theorem covWConv_Ho_prefix_only_bot {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {c : CptWConvR} (h : ApproxTKWConv covUHoEnv n Γ ρ covWNativeHoPrefix c) : c = .bot :=
  covWConv_Ho_head_only_bot h (.app (.app .head))

theorem covWConv_observation_bot_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {e : Expr Nat}
    (hb : ∀ d, ApproxTKWConv E n Γ ρ e d → d = .bot) (c : CptWConv) :
    CovWConvObservation E n Γ ρ e c ↔ c = .bot := by
  constructor
  · rintro ⟨d, hd, ho⟩
    rw [hb d ho] at hd
    exact hd.symm
  · rintro rfl
    exact ⟨.bot, rfl, .bot _ _ _⟩

theorem covWConv_bottom_observations_equal {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {e f : Expr Nat}
    (he : ∀ d, ApproxTKWConv E n Γ ρ e d → d = .bot)
    (hf : ∀ d, ApproxTKWConv E n Γ ρ f d → d = .bot) (c : CptWConv) :
    CovWConvObservation E n Γ ρ e c ↔ CovWConvObservation E n Γ ρ f c :=
  (covWConv_observation_bot_iff he c).trans (covWConv_observation_bot_iff hf c).symm

theorem covWConv_Ho_ctor_observation_iff (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) (c : CptWConv) :
    CovWConvObservation covUHoEnv n Γ ρ covWMatrixIotaSource c ↔ c = .bot :=
  covWConv_observation_bot_iff (fun _ => covWConv_Ho_ctor_only_bot) c

theorem covWConv_Ho_beta_all_observations (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) (c : CptWConv) :
    CovWConvObservation covUHoEnv n Γ ρ covWNativeHoBetaSource c ↔
    CovWConvObservation covUHoEnv n Γ ρ covWMatrixIotaSource c :=
  covWConv_bottom_observations_equal (fun _ => covWConv_Ho_beta_only_bot)
    (fun _ => covWConv_Ho_ctor_only_bot) c

theorem covWConv_Ho_zeta_all_observations (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) (c : CptWConv) :
    CovWConvObservation covUHoEnv n Γ ρ covWNativeHoLetSource c ↔
    CovWConvObservation covUHoEnv n Γ ρ covWMatrixIotaSource c :=
  covWConv_bottom_observations_equal (fun _ => covWConv_Ho_let_only_bot)
    (fun _ => covWConv_Ho_ctor_only_bot) c

theorem covWConv_Ho_eta_functions_equal (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) (c : CptWConv) :
    CovWConvObservation covUHoEnv n Γ ρ covWNativeHoBetaFn c ↔
    CovWConvObservation covUHoEnv n Γ ρ covWNativeHoPrefix c :=
  covWConv_bottom_observations_equal (fun _ => covWConv_Ho_fn_only_bot)
    (fun _ => covWConv_Ho_prefix_only_bot) c

/-- Filling [-] q is the already displayed beta-source/constructor pair. -/
theorem covWConv_Ho_eta_app_function_equal (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) (c : CptWConv) :
    CovWConvObservation covUHoEnv n Γ ρ (.app covWNativeHoBetaFn covWMatrixIotaMajor) c ↔
    CovWConvObservation covUHoEnv n Γ ρ (.app covWNativeHoPrefix covWMatrixIotaMajor) c :=
  covWConv_Ho_beta_all_observations n Γ ρ c

theorem covWConv_Ho_irr_calls_equal (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) (c : CptWConv) :
    CovWConvObservation covUHoEnv n Γ ρ covUHoType c ↔
    CovWConvObservation covUHoEnv n Γ ρ covWMatrixIotaSource c :=
  covWConv_bottom_observations_equal (fun _ => covWConv_Ho_divergent_only_bot)
    (fun _ => covWConv_Ho_ctor_only_bot) c

/-- Full observation equalities imply every displayed typed demand cell. -/
theorem covWConv_Ho_typed_cells (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) :
    CovWConvTypedInvariant covUHoEnv n Γ ρ (.sort (.succ .zero))
      covWNativeHoBetaSource covWMatrixIotaSource ∧
    CovWConvTypedInvariant covUHoEnv n Γ ρ (.sort (.succ .zero))
      covWNativeHoLetSource covWMatrixIotaSource ∧
    CovWConvTypedInvariant covUHoEnv n Γ ρ (.sort (.succ .zero))
      covUHoType covWMatrixIotaSource :=
  ⟨fun _ _ c _ => covWConv_Ho_beta_all_observations n Γ ρ c,
    fun _ _ c _ => covWConv_Ho_zeta_all_observations n Γ ρ c,
    fun _ _ c _ => covWConv_Ho_irr_calls_equal n Γ ρ c⟩

/-- Native admission and all comparison premises are supplied. -/
theorem covWConv_Ho_cells_inhabited (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covWNativeHoBetaSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    CovWMatrixNativePair covUHoEnv n covWNativeHoLetSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    CovWMatrixNativePair covUHoEnv n covUHoType covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    (∀ c, CovWConvObservation covUHoEnv n [] EnvWConvR.bot covWMatrixIotaSource c ↔ c = .bot) ∧
    (¬ ∃ N, RedR (WhStepCK2 covUHoEnv n) [] covUHoType N ∧
      NormalR (WhStepCK2 covUHoEnv n) [] N) :=
  ⟨covWNativeHo_beta_pair n, covWNativeHo_let_pair n, covWNativeHo_context_pair n,
    covWConv_Ho_ctor_observation_iff n [] EnvWConvR.bot, covUHoType_no_normal_head n []⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_HO_ROOTS
#print axioms covWConv_Ho_head_only_bot
#print axioms covWConv_Ho_ctor_only_bot
#print axioms covWConv_Ho_divergent_only_bot
#print axioms covWConv_Ho_beta_only_bot
#print axioms covWConv_Ho_let_only_bot
#print axioms covWConv_Ho_fn_only_bot
#print axioms covWConv_Ho_prefix_only_bot
#print axioms covWConv_observation_bot_iff
#print axioms covWConv_bottom_observations_equal
#print axioms covWConv_Ho_ctor_observation_iff
#print axioms covWConv_Ho_beta_all_observations
#print axioms covWConv_Ho_zeta_all_observations
#print axioms covWConv_Ho_eta_functions_equal
#print axioms covWConv_Ho_eta_app_function_equal
#print axioms covWConv_Ho_irr_calls_equal
#print axioms covWConv_Ho_typed_cells
#print axioms covWConv_Ho_cells_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_HO_ROOTS
end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
