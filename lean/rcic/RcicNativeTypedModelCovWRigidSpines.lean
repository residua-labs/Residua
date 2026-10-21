import rcic.RcicNativeTypedModelCovWRigidLocal

/-! A general supply of rigid spine observations, using the actual native
typing of every application. The W fixtures have nonbottom spine heads.
These facts do not assume, or prove, native nonconversion of the Boehm pair. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWAudit
open TypedModelCovWIrrelAudit TypedModelCovWMatrixAudit
open TypedModelCovWNativeAudit TypedModelCovWConvAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every well-typed application admits its bottom field with the native
function and argument types extracted from that occurrence. -/
theorem covWRigid_app_spine_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {f a T : Expr Nat} {r : Nat} {ls : List Level}
    {args : List CptWConvR}
    (ht : HasTyT E n Γ (.app f a) T)
    (hf : ApproxTKWRigid E n Γ ρ f (.spine r ls args)) :
    ApproxTKWRigid E n Γ ρ (.app f a) (.spine r ls (args ++ [.bot])) := by
  let hp := hasTyTInv_app ht rfl
  exact .appSpine hf (.bot _ _ _) (fun _ => rfl)
    (covWNative_field_bot hp.2.2.1 hp.2.2.2.1)

private theorem covWRigid_replicate_succ (k : Nat) :
    List.replicate (k + 1) (CptWConvR.bot) = List.replicate k CptWConvR.bot ++ [.bot] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons CptWConvR.bot) ih

/-- General supplier for an arbitrary finite, natively typed rigid-recursion
spine. It does not inspect or normalize a proof argument. -/
theorem covWRigid_typed_head_bot_fields {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {r k : Nat} {ls : List Level} {e T : Expr Nat}
    (hr : CovWRigidRecursor E r) (hh : CovWIrrelHeadTerm r ls k e)
    (ht : HasTyT E n Γ e T) :
    ApproxTKWRigid E n Γ ρ e (.spine r ls (List.replicate k .bot)) := by
  induction hh generalizing T with
  | head => exact .rigidRecursor _ _ _ _ hr
  | @app k f a hh ih =>
      let hp := hasTyTInv_app ht rfl
      have hf := ih hp.2.2.1
      have hs := covWRigid_app_spine_bot ht hf
      rw [covWRigid_replicate_succ k]
      exact hs

theorem covWRigid_Ho_recursor : CovWRigidRecursor covUHoEnv 65 :=
  ⟨covUHoRec, rfl, rfl, covUHo_no_legacy_witness⟩

def covWRigidHoDemandR : CptWConvR :=
  .spine 65 [.succ (.succ .zero)] [.bot, .bot, .bot]

def covWRigidHoDemand : CptWConv := covWConvCode covWRigidHoDemandR

theorem covWRigid_Ho_demand_nonbottom : covWRigidHoDemand ≠ .bot := by
  intro h
  cases h

theorem covWRigid_Ho_ctor_observed (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) :
    ApproxTKWRigid covUHoEnv n Γ ρ covWMatrixIotaSource covWRigidHoDemandR :=
  covWRigid_typed_head_bot_fields covWRigid_Ho_recursor
    (.app (.app (.app .head))) (covWMatrixIotaSource_ty n Γ)

theorem covWRigid_Ho_divergent_observed (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) :
    ApproxTKWRigid covUHoEnv n Γ ρ covUHoType covWRigidHoDemandR :=
  covWRigid_typed_head_bot_fields covWRigid_Ho_recursor
    (.app (.app (.app .head))) (covUHoType_hasTy n Γ)

theorem covWRigid_bohm_call_observed (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) :
    ApproxTKWRigid covUHoEnv n Γ ρ covWConvBohmCall covWRigidHoDemandR :=
  covWRigid_typed_head_bot_fields covWRigid_Ho_recursor
    (.app (.app (.app .head))) (covWConv_bohm_call_ty n Γ)

/-- Empty-demand constant rows are supplied directly in the new grammar. -/
theorem covWRigid_empty_lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {A b : Expr Nat} {c : CptWConvR}
    (hc : c ≠ .bot)
    (hb : ApproxTKWRigid E n (.assumption A :: Γ)
      (EnvWConvR.cons (demandWConvR []) ρ) b c) :
    ApproxTKWRigid E n Γ ρ (.lam A b) (.lam [([], c)]) := by
  apply ApproxTKWRigid.lam (.bot _ _ _)
  · intro s hs u hu
    simp only [List.mem_singleton] at hs
    subst s
    cases hu
  · exact ⟨([], c), by simp, hc⟩
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact hb

theorem covWRigid_empty_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {f a : Expr Nat} {c : CptWConvR}
    (hf : ApproxTKWRigid E n Γ ρ f (.lam [([], c)])) :
    ApproxTKWRigid E n Γ ρ (.app f a) c :=
  .app (s := ([], c)) hf (by simp) (by intro u hu; cases hu)

theorem covWRigid_Ho_beta_fn_observed (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) :
    ApproxTKWRigid covUHoEnv n Γ ρ covWNativeHoBetaFn
      (.lam [([], covWRigidHoDemandR)]) := by
  apply covWRigid_empty_lam (by intro h; cases h)
  apply covWRigid_typed_head_bot_fields covWRigid_Ho_recursor
    (.app (.app (.app .head)))
  exact .app _ _ _ _ _ (covWNativeHo_prefix_ty n _) (.bvar _ 0 _ rfl)

theorem covWRigid_Ho_beta_observed (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) :
    ApproxTKWRigid covUHoEnv n Γ ρ covWNativeHoBetaSource covWRigidHoDemandR :=
  covWRigid_empty_app (covWRigid_Ho_beta_fn_observed n Γ ρ)

theorem covWRigid_Ho_zeta_observed (n : Nat) (Γ : LCtx) (ρ : EnvWConvR) :
    ApproxTKWRigid covUHoEnv n Γ ρ covWNativeHoLetSource covWRigidHoDemandR :=
  .letE (covWRigid_Ho_beta_observed n Γ ρ)

/-- Nonbottom observations of the admitted comparison endpoints. The inherited
compact typing cannot supply strict universe typing for this dependent
recursor spine, as proved in the subsequent TypingBoundary module. -/
theorem covWRigid_Ho_cells_observed (n : Nat) :
    CovWMatrixNativePair covUHoEnv n covWNativeHoBetaSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    CovWMatrixNativePair covUHoEnv n covWNativeHoLetSource covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    CovWMatrixNativePair covUHoEnv n covUHoType covWMatrixIotaSource
      (.sort (.succ .zero)) (.succ (.succ .zero)) ∧
    covWRigidHoDemand ≠ .bot ∧
    CovWRigidObservation covUHoEnv n [] EnvWConvR.bot covWMatrixIotaSource covWRigidHoDemand ∧
    CovWRigidObservation covUHoEnv n [] EnvWConvR.bot covUHoType covWRigidHoDemand ∧
    CovWRigidObservation covUHoEnv n [] EnvWConvR.bot covWNativeHoBetaSource covWRigidHoDemand ∧
    CovWRigidObservation covUHoEnv n [] EnvWConvR.bot covWNativeHoLetSource covWRigidHoDemand :=
  ⟨covWNativeHo_beta_pair n, covWNativeHo_let_pair n, covWNativeHo_context_pair n,
    covWRigid_Ho_demand_nonbottom,
    covWRigid_observation_of (covWRigid_Ho_ctor_observed n [] EnvWConvR.bot),
    covWRigid_observation_of (covWRigid_Ho_divergent_observed n [] EnvWConvR.bot),
    covWRigid_observation_of (covWRigid_Ho_beta_observed n [] EnvWConvR.bot),
    covWRigid_observation_of (covWRigid_Ho_zeta_observed n [] EnvWConvR.bot)⟩

end Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

-- BEGIN COVWRIGID GENERATED MISSING AXIOM ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_app_spine_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_typed_head_bot_fields
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_recursor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidHoDemandR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidHoDemand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_demand_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_ctor_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_divergent_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_bohm_call_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_lam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_empty_app
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_beta_fn_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_beta_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_zeta_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_cells_observed
-- END COVWRIGID GENERATED MISSING AXIOM ROOTS
