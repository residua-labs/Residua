import rcic.RcicNativeTypedModelCovWIrrelAligned
import rcic.RcicNativeTypedModelCovWIrrelFunctionBoundary
import rcic.RcicNativeTypedModelCovWIrrelNativePositions

/-!
# The remaining function-field boundary after proof-field erasure

The actual admitted binder of `G : (Nat -> Nat) -> Prop` is natively not
a proof position. Consequently the repaired grammar retains the tagged
fine compact of `G succ`. Both successor and its eta expansion have an
actual strictly typed graph observation, but that graph does not replace
the atomic rigid compact retained inside the fine result spine.

The complete old-grammar exclusions transfer through structural erasure,
so native eta congruence and the displayed beta step still fail to
transport this fine observation. The finite valuation premise below is
stated explicitly for the erased valuation; the realizer and all tested
observations use the repaired grammar. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelAudit.TypingFin
open TypedModelCovTAudit TypedModelCovWAudit TypedModelCovWTypedAudit
open TypedModelCovWEtaAudit ReadbackCKAudit ReadbackCK2Audit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWFunctionAtomR : CptWIrrel := .spine 2 [] []
def covWFunctionFineR : CptWIrrel := .spine 4 [] [covWFunctionAtomR]
def covWFunctionArrowCodeR : CptWIrrel :=
  .pi (.spine 0 [] []) [([.bot], .spine 0 [] [])]
def covWFunctionGraphR : CptWIrrel := .lam [([.bot], .spine 2 [] [.bot])]
def covWFunctionLetSource : Expr Nat :=
  .letE covWFunctionArrow covWFunctionSucc covWFunctionBody

def covWFunction_let_body_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n (.letBinding covWFunctionArrow covWFunctionSucc :: Γ)
      covWFunctionBody (.sort .zero) :=
  .app _ _ _ covWFunctionArrow (.sort .zero) (covWFunction_g_ty n _)
    (.bvar _ 0 _ rfl)

def covWFunction_let_source_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWFunctionEnv n Γ covWFunctionLetSource (.sort .zero) :=
  .letE Γ covWFunctionArrow (.imax (.succ .zero) (.succ .zero)) covWFunctionSucc
    (.sort .zero) covWFunctionBody (covWFunction_arrow_ty n Γ)
    (covWFunction_succ_ty n Γ) (covWFunction_let_body_ty n Γ)

def covWFunction_let_conv (n : Nat) (Γ : LCtx) :
    ConvT covWFunctionEnv n Γ covWFunctionLetSource covWFunctionTarget (.sort .zero) :=
  .zeta Γ covWFunctionArrow covWFunctionSucc covWFunctionBody (.sort .zero)
    (.imax (.succ .zero) (.succ .zero)) (covWFunction_arrow_ty n Γ)
    (covWFunction_succ_ty n Γ) (covWFunction_let_body_ty n Γ)

theorem covWFunction_let_step (n : Nat) (Γ : LCtx) :
    WhStepCK2 covWFunctionEnv n Γ covWFunctionLetSource covWFunctionTarget :=
  .ctx (.zeta covWFunctionArrow covWFunctionSucc covWFunctionBody)

theorem covWFunction_let_kFree : KFreeT covWFunctionEnv covWFunctionLetSource :=
  (kFreeT_letE_iff _ _ _).mpr covWFunction_kFree.2.2

theorem covWFunction_fine_erases : covWIrrelErase covWFunctionFineR = covWFunctionFine := rfl

theorem covWFunctionEnv_inScope : covWFunctionEnv_wf.InScope := natEnvUWfT_inScope

theorem covWFunction_g_position (n : Nat) :
    CovWIrrelPosition covWFunctionEnv n 4 [] 0 [] covWFunctionArrow (.sort .zero) :=
  ⟨covWFunctionGMember, rfl, rfl, rfl, rfl⟩

theorem covWFunction_arrow_native_nonproof (n : Nat) :
    ¬ Nonempty (HasTyT covWFunctionEnv n [] covWFunctionArrow (.sort .zero)) :=
  covWIrrel_natArrow_notProp covWFunctionEnv_wf covWFunctionEnv_inScope .nil rfl

theorem covWFunction_g_nonproof_position (n : Nat) :
    ¬ CovWIrrelProofPosition covWFunctionEnv n 4 [] 0 :=
  covWIrrel_natArrowPosition_nonproof covWFunctionEnv_wf covWFunctionEnv_inScope rfl
    (covWFunction_g_position n)

theorem covWFunction_nat_observedR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ (.const 0 []) (.spine 0 [] []) :=
  .free (kFreeT_rigid_const covWFunction_nat_rigid [])
    (.const ρ 0 [] covWFunction_nat_rigid covWFunction_nat_not_propCtor)

theorem covWFunction_succ_observedR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionSucc covWFunctionAtomR :=
  .free (kFreeT_rigid_const covWFunction_succ_rigid [])
    (.const ρ 2 [] covWFunction_succ_rigid covWFunction_succ_not_propCtor)

theorem covWFunction_g_observedR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionG (.spine 4 [] []) :=
  .free (kFreeT_rigid_const covWFunction_g_rigid [])
    (.const ρ 4 [] covWFunction_g_rigid covWFunction_g_not_propCtor)

/-- Native nonproof evidence discharges the actual first position of `G`. -/
theorem covWFunction_target_observedR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionTarget covWFunctionFineR :=
  .appSpine (covWFunction_g_observedR n Γ ρ) (covWFunction_succ_observedR n Γ ρ)
    (fun hp => (covWFunction_g_nonproof_position n hp).elim)

theorem covWFunction_result_type_observedR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ (.sort .zero) .prop :=
  .free (kFreeT_sort covWFunctionEnv .zero) (.sort ρ .zero)

theorem covWFunction_arrow_observedR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionArrow covWFunctionArrowCodeR := by
  refine .pi (covWFunction_nat_observedR n Γ ρ) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact covWFunction_nat_observedR n _ _

theorem covWFunction_succ_graphR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionSucc covWFunctionGraphR := by
  refine .eta (covWFunction_succ_ty n Γ) (covWFunction_nat_observedR n Γ ρ) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨([.bot], .spine 2 [] [.bot]), List.mem_singleton.mpr rfl,
      fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .appSpine (covWFunction_succ_observedR n _ _) (.bot _ _ _)
      (fun _ => rfl)

theorem covWFunction_eta_graphR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionEta covWFunctionGraphR := by
  refine .lam (covWFunction_nat_observedR n Γ ρ) ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨([.bot], .spine 2 [] [.bot]), List.mem_singleton.mpr rfl,
      fun h => CptWIrrel.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .appSpine (covWFunction_succ_observedR n _ _) (.bot _ _ _)
      (fun _ => rfl)

theorem covWFunction_graph_typedR :
    CTyS covWFunctionEnv (covWIrrelErase covWFunctionGraphR)
      (covWIrrelErase covWFunctionArrowCodeR) := by
  change CTyS covWFunctionEnv (.lam [([.bot], .spine 2 [.bot])])
    (.pi (.spine 0 []) [([.bot], .spine 0 [])])
  rw [CTyS]
  refine Or.inr ⟨_, rfl, covWFunction_arrow_not_prop, ?_, ?_, ?_⟩
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs t ht _
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp ht
    rw [CTyS]
    exact Or.inr ⟨⟨2, [.bot], rfl⟩, covWFunction_nat_not_prop []⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact Or.inr ⟨([.bot], .spine 0 []), List.mem_singleton.mpr rfl,
      fun _ hu => hu⟩

theorem covWFunction_fine_typedR :
    CTyS covWFunctionEnv (covWIrrelErase covWFunctionFineR) (covWIrrelErase .prop) :=
  covWFunction_fine_typed

theorem covWFunction_fine_nonbottomR : covWFunctionFineR ≠ .bot :=
  fun h => CptWIrrel.noConfusion h

theorem covWFunction_eta_source_absentR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionEtaSource covWFunctionFineR :=
  fun h => covWFunction_eta_source_absent n Γ (covWIrrelEnvErase ρ)
    (covWIrrel_guarded_forget h)

theorem covWFunction_beta_source_absentR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionBetaSource covWFunctionFineR :=
  fun h => covWFunction_beta_source_absent n Γ (covWIrrelEnvErase ρ)
    (covWIrrel_guarded_forget h)

theorem covWFunction_let_source_absentR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionLetSource covWFunctionFineR := by
  intro h
  generalize he : covWFunctionLetSource = e at h
  generalize hc : covWFunctionFineR = c at h
  cases h with
  | bot => cases hc
  | free _ h =>
      rw [← he] at h
      cases h with
      | bot => cases hc
      | letE h =>
          apply covWFunction_beta_source_absentR n Γ ρ
          rw [hc]
          exact .free covWFunction_kFree.2.2 h
  | pi => cases hc
  | lam => cases hc
  | app => cases he
  | appSpine => cases he
  | delta => cases he
  | letE h =>
      cases he
      apply covWFunction_beta_source_absentR n Γ ρ
      rw [hc]
      exact h
  | lit => cases he
  | iota =>
      simp only [covWFunctionLetSource, iotaLhsOfS, recCall_eq_app] at he
      cases he
  | recursorPropK =>
      simp only [covWFunctionLetSource, recCall_eq_app] at he
      cases he
  | eta => cases hc

/-- No finite list works, even when its domain code is chosen from any
actual repaired observation of the native arrow. -/
theorem covWFunction_repaired_no_typed_factor (n : Nat) :
    ¬ ∃ (a : CptWIrrel) (us : List CptWIrrel),
      ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot covWFunctionArrow a ∧
      (∀ u ∈ us, CTyS covWFunctionEnv (covWIrrelErase u) (covWIrrelErase a)) ∧
      (∀ u ∈ us, ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot covWFunctionSucc u) ∧
      ApproxTKWIrrel covWFunctionEnv n [.assumption covWFunctionArrow]
        (EnvWIrrel.cons (demandWIrrel us) EnvWIrrel.bot) covWFunctionBody covWFunctionFineR := by
  rintro ⟨a, us, hA, ht, ha, hb⟩
  apply covWFunction_beta_source_absentR n [] EnvWIrrel.bot
  apply ApproxTKWIrrel.app (g := [(us, covWFunctionFineR)]) (s := (us, covWFunctionFineR))
  · refine .lam hA ?_ ?_ ?_
    · intro s hs u hu
      obtain rfl := List.mem_singleton.mp hs
      exact ht u hu
    · exact ⟨(us, covWFunctionFineR), List.mem_singleton.mpr rfl,
        covWFunction_fine_nonbottomR⟩
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      exact hb
  · exact List.mem_singleton.mpr rfl
  · exact ha

/-- All three terms retain the coarser nonbottom proposition observation. -/
theorem covWFunction_coarseR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionTarget (.spine 4 [] [.bot]) ∧
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionEtaSource (.spine 4 [] [.bot]) ∧
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionBetaSource (.spine 4 [] [.bot]) := by
  refine ⟨covWIrrel_guarded_appSpine_bot (covWFunction_g_observedR n Γ ρ),
    covWIrrel_guarded_appSpine_bot (covWFunction_g_observedR n Γ ρ), ?_⟩
  apply ApproxTKWIrrel.app (g := [([], .spine 4 [] [.bot])])
    (s := ([], .spine 4 [] [.bot]))
  · refine .lam (.bot Γ ρ covWFunctionArrow) ?_ ?_ ?_
    · intro s hs u hu
      obtain rfl := List.mem_singleton.mp hs
      cases hu
    · exact ⟨([], .spine 4 [] [.bot]), List.mem_singleton.mpr rfl,
        fun h => CptWIrrel.noConfusion h⟩
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      exact covWIrrel_guarded_appSpine_bot (covWFunction_g_observedR n _ _)
  · exact List.mem_singleton.mpr rfl
  · intro u hu
    cases hu

theorem covWFunction_let_coarseR (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionLetSource (.spine 4 [] [.bot]) :=
  .letE (covWFunction_coarseR n Γ ρ).2.2

/-- The native hypotheses are inherited from the proved old instance.
The repaired observation and realizer are supplied directly. -/
structure CovWFunctionRepairedFailureAt (n : Nat) : Prop where
  oldFailure : CovWFunctionOldFailureAt n
  letSourceTy : Nonempty (HasTyT covWFunctionEnv n [] covWFunctionLetSource (.sort .zero))
  letConversion : Nonempty
    (ConvT covWFunctionEnv n [] covWFunctionLetSource covWFunctionTarget (.sort .zero))
  letStep : WhStepCK2 covWFunctionEnv n [] covWFunctionLetSource covWFunctionTarget
  letReadback : RedR (WhStepCK2 covWFunctionEnv n) [] covWFunctionLetSource covWFunctionTarget
  nativeNonproof : ¬ CovWIrrelProofPosition covWFunctionEnv n 4 [] 0
  realized : CovWIrrelRealized covWFunctionEnv n 2 [] EnvWIrrel.bot SubstT.id
  erasedValuation : EnvTypedFinAtT
    (⟨ApproxTKWEta covWFunctionEnv n []⟩ : CtxModelT covWFunctionEnv) []
    (covWIrrelEnvErase EnvWIrrel.bot)
  erasedCoherence : CtxEnvM
    (⟨ApproxTKWEta covWFunctionEnv n []⟩ : CtxModelT covWFunctionEnv) []
    (covWIrrelEnvErase EnvWIrrel.bot)
  targetObservation : ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionTarget covWFunctionFineR
  typeObservation : ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot (.sort .zero) .prop
  arrowObservation : ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionArrow covWFunctionArrowCodeR
  successorGraph : ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionSucc covWFunctionGraphR
  expansionGraph : ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionEta covWFunctionGraphR
  graphDemand : CTyS covWFunctionEnv (covWIrrelErase covWFunctionGraphR)
    (covWIrrelErase covWFunctionArrowCodeR)
  demand : CTyS covWFunctionEnv (covWIrrelErase covWFunctionFineR) (covWIrrelErase .prop)
  nonbottom : covWFunctionFineR ≠ .bot
  etaNoFine : ¬ ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionEtaSource covWFunctionFineR
  betaNoFine : ¬ ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionBetaSource covWFunctionFineR
  letNoFine : ¬ ApproxTKWIrrel covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionLetSource covWFunctionFineR

theorem covWFunction_repaired_inhabited (n : Nat) : CovWFunctionRepairedFailureAt n where
  oldFailure := covWFunction_old_inhabited n
  letSourceTy := ⟨covWFunction_let_source_ty n []⟩
  letConversion := ⟨covWFunction_let_conv n []⟩
  letStep := covWFunction_let_step n []
  letReadback := redR_single (covWFunction_let_step n [])
  nativeNonproof := covWFunction_g_nonproof_position n
  realized := covWIrrel_realized_nil _ _ _
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  targetObservation := covWFunction_target_observedR n [] EnvWIrrel.bot
  typeObservation := covWFunction_result_type_observedR n [] EnvWIrrel.bot
  arrowObservation := covWFunction_arrow_observedR n [] EnvWIrrel.bot
  successorGraph := covWFunction_succ_graphR n [] EnvWIrrel.bot
  expansionGraph := covWFunction_eta_graphR n [] EnvWIrrel.bot
  graphDemand := covWFunction_graph_typedR
  demand := covWFunction_fine_typedR
  nonbottom := covWFunction_fine_nonbottomR
  etaNoFine := covWFunction_eta_source_absentR n [] EnvWIrrel.bot
  betaNoFine := covWFunction_beta_source_absentR n [] EnvWIrrel.bot
  letNoFine := covWFunction_let_source_absentR n [] EnvWIrrel.bot

/-- Transport of the repaired observations with actual native typing,
a repaired realizer, and the explicitly erased finite typed valuation. -/
def covWFunction_repaired_transportAt (n : Nat)
    (R : Expr Nat → Expr Nat → Prop) : Prop :=
  ∀ (ρ : EnvWIrrel) (σ : SubstT) (stage : Nat)
    (e e' T : Expr Nat) (l : Level) (c a : CptWIrrel),
    Nonempty (EnvWfT covWFunctionEnv) → Nonempty (CtxWfT covWFunctionEnv n []) →
    CovWIrrelRealized covWFunctionEnv n stage [] ρ σ →
    EnvTypedFinAtT (⟨ApproxTKWEta covWFunctionEnv n []⟩ : CtxModelT covWFunctionEnv)
      [] (covWIrrelEnvErase ρ) →
    Nonempty (HasTyT covWFunctionEnv n [] e T) →
    Nonempty (HasTyT covWFunctionEnv n [] e' T) →
    Nonempty (HasTyT covWFunctionEnv n [] T (.sort l)) →
    R e e' → ApproxTKWIrrel covWFunctionEnv n [] ρ e' c →
    ApproxTKWIrrel covWFunctionEnv n [] ρ T a →
    CTyS covWFunctionEnv (covWIrrelErase c) (covWIrrelErase a) → c ≠ .bot →
    ApproxTKWIrrel covWFunctionEnv n [] ρ e c

theorem covWFunction_repaired_no_conversion_transport (n : Nat) :
    ¬ covWFunction_repaired_transportAt n
      (fun e e' => Nonempty (ConvT covWFunctionEnv n [] e e' (.sort .zero))) := by
  intro h
  have hi := covWFunction_repaired_inhabited n
  exact hi.etaNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionEtaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFineR .prop
      hi.oldFailure.envWf hi.oldFailure.ctxWf hi.realized hi.erasedValuation
      hi.oldFailure.etaSourceTy hi.oldFailure.targetTy hi.oldFailure.typeTy
      hi.oldFailure.etaConversion hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_repaired_no_beta_transport (n : Nat) :
    ¬ covWFunction_repaired_transportAt n CovWTypedBetaHead := by
  intro h
  have hi := covWFunction_repaired_inhabited n
  exact hi.betaNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionBetaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFineR .prop
      hi.oldFailure.envWf hi.oldFailure.ctxWf hi.realized hi.erasedValuation
      hi.oldFailure.betaSourceTy hi.oldFailure.targetTy hi.oldFailure.typeTy
      ⟨covWFunctionArrow, covWFunctionBody, covWFunctionSucc, rfl, rfl⟩
      hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_repaired_no_step_transport (n : Nat) :
    ¬ covWFunction_repaired_transportAt n (WhStepCK2 covWFunctionEnv n []) := by
  intro h
  have hi := covWFunction_repaired_inhabited n
  exact hi.betaNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionBetaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFineR .prop
      hi.oldFailure.envWf hi.oldFailure.ctxWf hi.realized hi.erasedValuation
      hi.oldFailure.betaSourceTy hi.oldFailure.targetTy hi.oldFailure.typeTy
      hi.oldFailure.betaStep hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_repaired_no_let_transport (n : Nat) :
    ¬ covWFunction_repaired_transportAt n CovWTypedLetHead := by
  intro h
  have hi := covWFunction_repaired_inhabited n
  exact hi.letNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionLetSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFineR .prop
      hi.oldFailure.envWf hi.oldFailure.ctxWf hi.realized hi.erasedValuation
      hi.letSourceTy hi.oldFailure.targetTy hi.oldFailure.typeTy
      ⟨covWFunctionArrow, covWFunctionSucc, covWFunctionBody, rfl, rfl⟩
      hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_repaired_no_let_conversion_transport (n : Nat) :
    ¬ covWFunction_repaired_transportAt n
      (fun e e' => Nonempty (ConvT covWFunctionEnv n [] e e' (.sort .zero))) := by
  intro h
  have hi := covWFunction_repaired_inhabited n
  exact hi.letNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionLetSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFineR .prop
      hi.oldFailure.envWf hi.oldFailure.ctxWf hi.realized hi.erasedValuation
      hi.letSourceTy hi.oldFailure.targetTy hi.oldFailure.typeTy
      hi.letConversion hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

/-- Fully typed inverse substitution for repaired observations. Native
typing includes the substituted endpoint and its actual result type. -/
def covWFunction_repaired_inverseAt (n : Nat) : Prop :=
  ∀ (ρ : EnvWIrrel) (σ : SubstT) (stage : Nat)
    (D body arg B : Expr Nat) (lD lB : Level) (c b : CptWIrrel),
    Nonempty (EnvWfT covWFunctionEnv) → Nonempty (CtxWfT covWFunctionEnv n []) →
    CovWIrrelRealized covWFunctionEnv n stage [] ρ σ →
    EnvTypedFinAtT (⟨ApproxTKWEta covWFunctionEnv n []⟩ : CtxModelT covWFunctionEnv)
      [] (covWIrrelEnvErase ρ) →
    Nonempty (HasTyT covWFunctionEnv n [] D (.sort lD)) →
    Nonempty (HasTyT covWFunctionEnv n [] arg D) →
    Nonempty (HasTyT covWFunctionEnv n [.assumption D] B (.sort lB)) →
    Nonempty (HasTyT covWFunctionEnv n [.assumption D] body B) →
    Nonempty (HasTyT covWFunctionEnv n [] (instantiate0 arg body) (instantiate0 arg B)) →
    ApproxTKWIrrel covWFunctionEnv n [] ρ (instantiate0 arg body) c →
    ApproxTKWIrrel covWFunctionEnv n [] ρ (instantiate0 arg B) b →
    CTyS covWFunctionEnv (covWIrrelErase c) (covWIrrelErase b) → c ≠ .bot →
    ∃ (a : CptWIrrel) (us : List CptWIrrel),
      ApproxTKWIrrel covWFunctionEnv n [] ρ D a ∧
      (∀ u ∈ us, CTyS covWFunctionEnv (covWIrrelErase u) (covWIrrelErase a)) ∧
      (∀ u ∈ us, ApproxTKWIrrel covWFunctionEnv n [] ρ arg u) ∧
      ApproxTKWIrrel covWFunctionEnv n [.assumption D]
        (EnvWIrrel.cons (demandWIrrel us) ρ) body c

theorem covWFunction_repaired_no_typed_inverse (n : Nat) :
    ¬ covWFunction_repaired_inverseAt n := by
  intro h
  have hi := covWFunction_repaired_inhabited n
  apply covWFunction_repaired_no_typed_factor n
  exact h EnvWIrrel.bot SubstT.id 2 covWFunctionArrow covWFunctionBody
    covWFunctionSucc (.sort .zero) (.imax (.succ .zero) (.succ .zero)) (.succ .zero)
    covWFunctionFineR .prop hi.oldFailure.envWf hi.oldFailure.ctxWf hi.realized
    hi.erasedValuation hi.oldFailure.arrowTy hi.oldFailure.succTy
    ⟨.sort _ .zero⟩ ⟨covWFunction_body_ty n []⟩ hi.oldFailure.targetTy
    hi.targetObservation hi.typeObservation hi.demand hi.nonbottom

theorem covWFunction_repaired_same_stage (n : Nat) :
    CovWIrrelRealized covWFunctionEnv n 2 [] EnvWIrrel.bot SubstT.id ∧
    ApproxTKWIrrelStage covWFunctionEnv n 2 [] EnvWIrrel.bot
      covWFunctionTarget covWFunctionFineR ∧
    ApproxTKWIrrelStage covWFunctionEnv n 2 [] EnvWIrrel.bot (.sort .zero) .prop := by
  refine ⟨covWIrrel_realized_nil _ _ _,
    ⟨covWFunction_target_observedR n [] EnvWIrrel.bot, ?_⟩,
    ⟨covWFunction_result_type_observedR n [] EnvWIrrel.bot, ?_⟩⟩
  all_goals simp [covTObservationBudget, covWFunctionFineR, covWFunctionAtomR,
    covWIrrelErase, covWIrrelEraseArgs]

/-- The old complete grammar also excludes the let source. This statement
does not select any universe decoration of the observed compact. -/
theorem covWFunction_let_source_absent_old (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTKWEta covWFunctionEnv n Γ ρ covWFunctionLetSource covWFunctionFine := by
  intro h
  generalize he : covWFunctionLetSource = e at h
  generalize hc : covWFunctionFine = c at h
  cases h with
  | bot => cases hc
  | free _ h =>
      rw [← he] at h
      cases h with
      | bot => cases hc
      | letE h =>
          apply covWFunction_beta_source_absent n Γ ρ
          rw [hc]
          exact .free covWFunction_kFree.2.2 h
  | pi => cases hc
  | lam => cases hc
  | app => cases he
  | appSpine => cases he
  | delta => cases he
  | letE h =>
      cases he
      apply covWFunction_beta_source_absent n Γ ρ
      rw [hc]
      exact h
  | lit => cases he
  | iota =>
      simp only [covWFunctionLetSource, iotaLhsOfS, recCall_eq_app] at he
      cases he
  | recursorPropK =>
      simp only [covWFunctionLetSource, recCall_eq_app] at he
      cases he
  | eta => cases hc

theorem covWFunction_erased_target_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    CovWIrrelObservation covWFunctionEnv n Γ ρ covWFunctionTarget covWFunctionFine :=
  covWIrrel_observation_of (covWFunction_target_observedR n Γ ρ)

theorem covWFunction_erased_type_observed (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    CovWIrrelObservation covWFunctionEnv n Γ ρ (.sort .zero) .prop :=
  covWIrrel_observation_of (covWFunction_result_type_observedR n Γ ρ)

theorem covWFunction_erased_eta_absent (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ CovWIrrelObservation covWFunctionEnv n Γ ρ covWFunctionEtaSource covWFunctionFine :=
  fun h => covWFunction_eta_source_absent n Γ (covWIrrelEnvErase ρ)
    (covWIrrel_observation_forget h)

theorem covWFunction_erased_beta_absent (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ CovWIrrelObservation covWFunctionEnv n Γ ρ covWFunctionBetaSource covWFunctionFine :=
  fun h => covWFunction_beta_source_absent n Γ (covWIrrelEnvErase ρ)
    (covWIrrel_observation_forget h)

theorem covWFunction_erased_let_absent (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ¬ CovWIrrelObservation covWFunctionEnv n Γ ρ covWFunctionLetSource covWFunctionFine :=
  fun h => covWFunction_let_source_absent_old n Γ (covWIrrelEnvErase ρ)
    (covWIrrel_observation_forget h)

/-- Every decoration erasing to the original fine compact is excluded.
The boundary therefore concerns an original `CptT` observation, not a
distinction between universe-provenance labels. -/
theorem covWFunction_all_fine_decorations_absent (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel)
    (d : CptWIrrel) (hd : covWIrrelErase d = covWFunctionFine) :
    (¬ ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionEtaSource d) ∧
    (¬ ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionBetaSource d) ∧
    (¬ ApproxTKWIrrel covWFunctionEnv n Γ ρ covWFunctionLetSource d) :=
  ⟨fun h => covWFunction_erased_eta_absent n Γ ρ ⟨d, hd, h⟩,
   fun h => covWFunction_erased_beta_absent n Γ ρ ⟨d, hd, h⟩,
   fun h => covWFunction_erased_let_absent n Γ ρ ⟨d, hd, h⟩⟩

structure CovWFunctionErasedFailureAt (n : Nat) : Prop where
  native : CovWFunctionRepairedFailureAt n
  targetObservation : CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionTarget covWFunctionFine
  typeObservation : CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot
    (.sort .zero) .prop
  demand : CTyS covWFunctionEnv covWFunctionFine .prop
  nonbottom : covWFunctionFine ≠ .bot
  etaNoFine : ¬ CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionEtaSource covWFunctionFine
  betaNoFine : ¬ CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionBetaSource covWFunctionFine
  letNoFine : ¬ CovWIrrelObservation covWFunctionEnv n [] EnvWIrrel.bot
    covWFunctionLetSource covWFunctionFine

theorem covWFunction_erased_inhabited (n : Nat) : CovWFunctionErasedFailureAt n where
  native := covWFunction_repaired_inhabited n
  targetObservation := covWFunction_erased_target_observed n [] EnvWIrrel.bot
  typeObservation := covWFunction_erased_type_observed n [] EnvWIrrel.bot
  demand := covWFunction_fine_typed
  nonbottom := covWFunction_fine_nonbottom
  etaNoFine := covWFunction_erased_eta_absent n [] EnvWIrrel.bot
  betaNoFine := covWFunction_erased_beta_absent n [] EnvWIrrel.bot
  letNoFine := covWFunction_erased_let_absent n [] EnvWIrrel.bot

/-- Semantic transport tests only original finite compacts. Every native,
realizer, and finite-valuation premise is the same actual premise used in
the decorated internal formulation. -/
def covWFunction_erased_transportAt (n : Nat)
    (R : Expr Nat → Expr Nat → Prop) : Prop :=
  ∀ (ρ : EnvWIrrel) (σ : SubstT) (stage : Nat)
    (e e' T : Expr Nat) (l : Level) (c a : CptT),
    Nonempty (EnvWfT covWFunctionEnv) → Nonempty (CtxWfT covWFunctionEnv n []) →
    CovWIrrelRealized covWFunctionEnv n stage [] ρ σ →
    EnvTypedFinAtT (⟨ApproxTKWEta covWFunctionEnv n []⟩ : CtxModelT covWFunctionEnv)
      [] (covWIrrelEnvErase ρ) →
    Nonempty (HasTyT covWFunctionEnv n [] e T) →
    Nonempty (HasTyT covWFunctionEnv n [] e' T) →
    Nonempty (HasTyT covWFunctionEnv n [] T (.sort l)) →
    R e e' → CovWIrrelObservation covWFunctionEnv n [] ρ e' c →
    CovWIrrelObservation covWFunctionEnv n [] ρ T a →
    CTyS covWFunctionEnv c a → c ≠ .bot →
    CovWIrrelObservation covWFunctionEnv n [] ρ e c

theorem covWFunction_erased_no_conversion_transport (n : Nat) :
    ¬ covWFunction_erased_transportAt n
      (fun e e' => Nonempty (ConvT covWFunctionEnv n [] e e' (.sort .zero))) := by
  intro h
  have hi := covWFunction_erased_inhabited n
  exact hi.etaNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionEtaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop
      hi.native.oldFailure.envWf hi.native.oldFailure.ctxWf hi.native.realized hi.native.erasedValuation
      hi.native.oldFailure.etaSourceTy hi.native.oldFailure.targetTy hi.native.oldFailure.typeTy
      hi.native.oldFailure.etaConversion hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_erased_no_beta_transport (n : Nat) :
    ¬ covWFunction_erased_transportAt n CovWTypedBetaHead := by
  intro h
  have hi := covWFunction_erased_inhabited n
  exact hi.betaNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionBetaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop
      hi.native.oldFailure.envWf hi.native.oldFailure.ctxWf hi.native.realized hi.native.erasedValuation
      hi.native.oldFailure.betaSourceTy hi.native.oldFailure.targetTy hi.native.oldFailure.typeTy
      ⟨covWFunctionArrow, covWFunctionBody, covWFunctionSucc, rfl, rfl⟩
      hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_erased_no_step_transport (n : Nat) :
    ¬ covWFunction_erased_transportAt n (WhStepCK2 covWFunctionEnv n []) := by
  intro h
  have hi := covWFunction_erased_inhabited n
  exact hi.betaNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionBetaSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop
      hi.native.oldFailure.envWf hi.native.oldFailure.ctxWf hi.native.realized hi.native.erasedValuation
      hi.native.oldFailure.betaSourceTy hi.native.oldFailure.targetTy hi.native.oldFailure.typeTy
      hi.native.oldFailure.betaStep hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_erased_no_let_transport (n : Nat) :
    ¬ covWFunction_erased_transportAt n CovWTypedLetHead := by
  intro h
  have hi := covWFunction_erased_inhabited n
  exact hi.letNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionLetSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop
      hi.native.oldFailure.envWf hi.native.oldFailure.ctxWf hi.native.realized hi.native.erasedValuation
      hi.native.letSourceTy hi.native.oldFailure.targetTy hi.native.oldFailure.typeTy
      ⟨covWFunctionArrow, covWFunctionSucc, covWFunctionBody, rfl, rfl⟩
      hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

theorem covWFunction_erased_no_let_conversion_transport (n : Nat) :
    ¬ covWFunction_erased_transportAt n
      (fun e e' => Nonempty (ConvT covWFunctionEnv n [] e e' (.sort .zero))) := by
  intro h
  have hi := covWFunction_erased_inhabited n
  exact hi.letNoFine
    (h EnvWIrrel.bot SubstT.id 2 covWFunctionLetSource covWFunctionTarget
      (.sort .zero) (.succ .zero) covWFunctionFine .prop
      hi.native.oldFailure.envWf hi.native.oldFailure.ctxWf hi.native.realized hi.native.erasedValuation
      hi.native.letSourceTy hi.native.oldFailure.targetTy hi.native.oldFailure.typeTy
      hi.native.letConversion hi.targetObservation hi.typeObservation hi.demand hi.nonbottom)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FUNCTION_REPAIR_BOUNDARY_ROOTS
#print axioms covWFunctionAtomR
#print axioms covWFunctionFineR
#print axioms covWFunctionArrowCodeR
#print axioms covWFunctionGraphR
#print axioms covWFunctionLetSource
#print axioms covWFunction_let_body_ty
#print axioms covWFunction_let_source_ty
#print axioms covWFunction_let_conv
#print axioms covWFunction_let_step
#print axioms covWFunction_let_kFree
#print axioms covWFunction_fine_erases
#print axioms covWFunctionEnv_inScope
#print axioms covWFunction_g_position
#print axioms covWFunction_arrow_native_nonproof
#print axioms covWFunction_g_nonproof_position
#print axioms covWFunction_nat_observedR
#print axioms covWFunction_succ_observedR
#print axioms covWFunction_g_observedR
#print axioms covWFunction_target_observedR
#print axioms covWFunction_result_type_observedR
#print axioms covWFunction_arrow_observedR
#print axioms covWFunction_succ_graphR
#print axioms covWFunction_eta_graphR
#print axioms covWFunction_graph_typedR
#print axioms covWFunction_fine_typedR
#print axioms covWFunction_fine_nonbottomR
#print axioms covWFunction_eta_source_absentR
#print axioms covWFunction_beta_source_absentR
#print axioms covWFunction_let_source_absentR
#print axioms covWFunction_repaired_no_typed_factor
#print axioms covWFunction_coarseR
#print axioms covWFunction_let_coarseR
#print axioms CovWFunctionRepairedFailureAt
#print axioms covWFunction_repaired_inhabited
#print axioms covWFunction_repaired_transportAt
#print axioms covWFunction_repaired_no_conversion_transport
#print axioms covWFunction_repaired_no_beta_transport
#print axioms covWFunction_repaired_no_step_transport
#print axioms covWFunction_repaired_no_let_transport
#print axioms covWFunction_repaired_no_let_conversion_transport
#print axioms covWFunction_repaired_inverseAt
#print axioms covWFunction_repaired_no_typed_inverse
#print axioms covWFunction_repaired_same_stage
#print axioms covWFunction_let_source_absent_old
#print axioms covWFunction_erased_target_observed
#print axioms covWFunction_erased_type_observed
#print axioms covWFunction_erased_eta_absent
#print axioms covWFunction_erased_beta_absent
#print axioms covWFunction_erased_let_absent
#print axioms covWFunction_all_fine_decorations_absent
#print axioms CovWFunctionErasedFailureAt
#print axioms covWFunction_erased_inhabited
#print axioms covWFunction_erased_transportAt
#print axioms covWFunction_erased_no_conversion_transport
#print axioms covWFunction_erased_no_beta_transport
#print axioms covWFunction_erased_no_step_transport
#print axioms covWFunction_erased_no_let_transport
#print axioms covWFunction_erased_no_let_conversion_transport
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FUNCTION_REPAIR_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
