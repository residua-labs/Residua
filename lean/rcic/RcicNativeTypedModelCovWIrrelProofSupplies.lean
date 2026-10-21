import rcic.RcicNativeTypedModelCovWIrrelRepair
import rcic.RcicNativeTypedModelCovWEtaExpansionBoundary

/-!
# Concrete proof-binder supplies after proof-field erasure

In the exact original `covWRevEnv`, the beta and let sources now supply
every target observation strictly typed at the actual `Prop` code. The
nonbottom supply is raw: its lambda row has empty demand, its domain code
is bottom, and its body observes the rigid family with a bottom field.
The earlier proof-demand application also shares every strictly typed
result observation with the application to `True.intro`; its changed
bottom demand composes through the unchanged positive total candidate.
Public semantic statements erase universe provenance to the original
finite compact type. These are concrete supplies, not generic closure.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelAudit.TypingFin
open TypedModelCovXAudit TypedModelCovPAudit TypedModelCovRAudit TypedModelCovSAudit
open TypedModelCovUAudit TypedModelCovTAudit TypedModelCovWAudit TypedModelCovWEtaAudit
open ReadbackCKAudit ReadbackCK2Audit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem covWIrrel_inv_family_rigid : RigidConst covWRevEnv 5 :=
  rigidConst_of_inductiveM covWRevEnv_wf (m := covWRevFam) rfl rfl

theorem covWIrrel_inv_family_not_propCtor : ¬ PropCtorT covWRevEnv 5 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covWRevFam := Option.some.inj hm.symm
  subst m
  cases hk

theorem covWIrrel_inv_position (n : Nat) :
    CovWIrrelPosition covWRevEnv n 5 [] 0 [] covUProjP (.sort .zero) :=
  ⟨covWRevFam, rfl, rfl, rfl, rfl⟩

theorem covWIrrel_inv_proof_position (n : Nat) :
    CovWIrrelProofPosition covWRevEnv n 5 [] 0 :=
  ⟨[], covUProjP, .sort .zero, covWIrrel_inv_position n, ⟨covWRevP_ty n []⟩⟩

theorem covWIrrel_inv_family_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covWRevEnv n ρ (.const 5 []) (.spine 5 [] []) :=
  .const ρ 5 [] covWIrrel_inv_family_rigid covWIrrel_inv_family_not_propCtor

theorem covWIrrel_inv_body_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covWRevEnv n ρ covWEtaInvBody covWIrrelCoarse :=
  covWIrrel_raw_appSpine_bot (covWIrrel_inv_family_raw n ρ)

theorem covWIrrel_inv_source_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covWRevEnv n ρ covWEtaInvSource covWIrrelCoarse := by
  apply ApproxTWIrrel.app (g := [([], covWIrrelCoarse)]) (s := ([], covWIrrelCoarse))
  · refine .lam (.bot ρ covUProjP) ?_ ?_ ?_
    · intro s hs u hu
      obtain rfl := List.mem_singleton.mp hs
      cases hu
    · exact ⟨([], covWIrrelCoarse), List.mem_singleton.mpr rfl,
        fun h => CptWIrrel.noConfusion h⟩
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      exact covWIrrel_inv_body_raw n _
  · exact List.mem_singleton.mpr rfl
  · intro u hu
    cases hu

theorem covWIrrel_inv_let_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covWRevEnv n ρ covWEtaInvLet covWIrrelCoarse :=
  .letE (covWIrrel_inv_source_raw n ρ)

theorem covWIrrel_inv_target_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covWRevEnv n ρ covWEtaInvTarget covWIrrelCoarse :=
  covWIrrel_raw_appSpine_bot (covWIrrel_inv_family_raw n ρ)

theorem covWIrrel_inv_source_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWRevEnv n Γ ρ covWEtaInvSource covWIrrelCoarse :=
  .free covWEtaInv_kFree.1 (covWIrrel_inv_source_raw n ρ)

theorem covWIrrel_inv_let_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWRevEnv n Γ ρ covWEtaInvLet covWIrrelCoarse :=
  .free covWEtaInv_kFree.2.1 (covWIrrel_inv_let_raw n ρ)

theorem covWIrrel_inv_target_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWRevEnv n Γ ρ covWEtaInvTarget covWIrrelCoarse :=
  .free covWEtaInv_kFree.2.2 (covWIrrel_inv_target_raw n ρ)

theorem covWIrrel_inv_type_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWRevEnv n Γ ρ (.sort .zero) .prop :=
  .free (kFreeT_sort covWRevEnv .zero) (.sort ρ .zero)

theorem covWIrrel_inv_coarse_typed :
    CTyS covWRevEnv (covWIrrelErase covWIrrelCoarse) .prop := by
  rw [CTyS]
  exact Or.inr (.spine (m := covWRevFam) rfl rfl)

/-- The full guarded grammar, including every eta derivation, can emit
only bottom or the supplied coarse result at the actual Prop code. -/
theorem covWIrrel_inv_typed_sources {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel}
    (ho : ApproxTKWIrrel covWRevEnv n Γ ρ covWEtaInvTarget c)
    (ht : CTyS covWRevEnv (covWIrrelErase c) .prop) :
    ApproxTKWIrrel covWRevEnv n Γ ρ covWEtaInvSource c ∧
    ApproxTKWIrrel covWRevEnv n Γ ρ covWEtaInvLet c := by
  rcases covWIrrel_proof_field_shape covWIrrel_inv_family_rigid
      (covWIrrel_inv_proof_position n) ho ht with rfl | rfl
  · exact ⟨.bot _ _ _, .bot _ _ _⟩
  · exact ⟨covWIrrel_inv_source_new n Γ ρ, covWIrrel_inv_let_new n Γ ρ⟩

/-- The concrete inverse demand can be chosen empty for every such target
observation. Its domain code and argument demands are actually supplied. -/
theorem covWIrrel_inv_typed_factor {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel}
    (ho : ApproxTKWIrrel covWRevEnv n Γ ρ covWEtaInvTarget c)
    (ht : CTyS covWRevEnv (covWIrrelErase c) .prop) :
    ∃ (a : CptWIrrel) (us : List CptWIrrel),
      ApproxTKWIrrel covWRevEnv n Γ ρ covUProjP a ∧
      (∀ u ∈ us, CTyS covWRevEnv (covWIrrelErase u) (covWIrrelErase a)) ∧
      (∀ u ∈ us, ApproxTKWIrrel covWRevEnv n Γ ρ covUProjProof u) ∧
      ApproxTKWIrrel covWRevEnv n (.assumption covUProjP :: Γ)
        (EnvWIrrel.cons (demandWIrrel us) ρ) covWEtaInvBody c := by
  refine ⟨.bot, [], .bot _ _ _, (fun _ hu => nomatch hu),
    (fun _ hu => nomatch hu), ?_⟩
  rcases covWIrrel_proof_field_shape covWIrrel_inv_family_rigid
      (covWIrrel_inv_proof_position n) ho ht with rfl | rfl
  · exact .bot _ _ _
  · exact covWIrrel_guarded_appSpine_bot
      (.free (kFreeT_rigid_const covWIrrel_inv_family_rigid [])
        (covWIrrel_inv_family_raw n _))

theorem covWIrrel_inv_erased_sources {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptT} (ho : CovWIrrelObservation covWRevEnv n Γ ρ covWEtaInvTarget c)
    (ht : CTyS covWRevEnv c .prop) :
    CovWIrrelObservation covWRevEnv n Γ ρ covWEtaInvSource c ∧
    CovWIrrelObservation covWRevEnv n Γ ρ covWEtaInvLet c := by
  obtain ⟨d, rfl, hd⟩ := ho
  have hs := covWIrrel_inv_typed_sources hd ht
  exact ⟨⟨d, rfl, hs.1⟩, ⟨d, rfl, hs.2⟩⟩

structure CovWIrrelProofSuppliesAt (n : Nat) : Prop where
  envWf : Nonempty (EnvWfT covWRevEnv)
  ctxWf : Nonempty (CtxWfT covWRevEnv n [])
  realized : CovWIrrelRealized covWRevEnv n 2 [] EnvWIrrel.bot SubstT.id
  erasedValuation : EnvTypedFinAtT
    (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv) []
    (covWIrrelEnvErase EnvWIrrel.bot)
  erasedCoherence : CtxEnvM
    (⟨ApproxTKWEta covWRevEnv n []⟩ : CtxModelT covWRevEnv) []
    (covWIrrelEnvErase EnvWIrrel.bot)
  domainTy : Nonempty (HasTyT covWRevEnv n [] covUProjP (.sort .zero))
  argTy : Nonempty (HasTyT covWRevEnv n [] covUProjProof covUProjP)
  bodyTy : Nonempty (HasTyT covWRevEnv n [.assumption covUProjP]
    covWEtaInvBody (.sort .zero))
  letBodyTy : Nonempty (HasTyT covWRevEnv n [.letBinding covUProjP covUProjProof]
    covWEtaInvBody (.sort .zero))
  sourceTy : Nonempty (HasTyT covWRevEnv n [] covWEtaInvSource (.sort .zero))
  letTy : Nonempty (HasTyT covWRevEnv n [] covWEtaInvLet (.sort .zero))
  targetTy : Nonempty (HasTyT covWRevEnv n [] covWEtaInvTarget (.sort .zero))
  typeTy : Nonempty (HasTyT covWRevEnv n [] (.sort .zero) (.sort (.succ .zero)))
  betaConversion : Nonempty
    (ConvT covWRevEnv n [] covWEtaInvSource covWEtaInvTarget (.sort .zero))
  letConversion : Nonempty
    (ConvT covWRevEnv n [] covWEtaInvLet covWEtaInvTarget (.sort .zero))
  betaStep : WhStepCK2 covWRevEnv n [] covWEtaInvSource covWEtaInvTarget
  letStep : WhStepCK2 covWRevEnv n [] covWEtaInvLet covWEtaInvTarget
  betaReadback : RedR (WhStepCK2 covWRevEnv n) [] covWEtaInvSource covWEtaInvTarget
  letReadback : RedR (WhStepCK2 covWRevEnv n) [] covWEtaInvLet covWEtaInvTarget
  targetNormal : NormalR (WhStepCK2 covWRevEnv n) [] covWEtaInvTarget
  sourceRaw : ApproxTWIrrel covWRevEnv n EnvWIrrel.bot covWEtaInvSource covWIrrelCoarse
  letRaw : ApproxTWIrrel covWRevEnv n EnvWIrrel.bot covWEtaInvLet covWIrrelCoarse
  targetRaw : ApproxTWIrrel covWRevEnv n EnvWIrrel.bot covWEtaInvTarget covWIrrelCoarse
  sourceObservation : CovWIrrelObservation covWRevEnv n [] EnvWIrrel.bot
    covWEtaInvSource (.spine 5 [.bot])
  letObservation : CovWIrrelObservation covWRevEnv n [] EnvWIrrel.bot
    covWEtaInvLet (.spine 5 [.bot])
  targetObservation : CovWIrrelObservation covWRevEnv n [] EnvWIrrel.bot
    covWEtaInvTarget (.spine 5 [.bot])
  typeObservation : CovWIrrelObservation covWRevEnv n [] EnvWIrrel.bot (.sort .zero) .prop
  demand : CTyS covWRevEnv (.spine 5 [.bot]) .prop
  nonbottom : (.spine 5 [.bot] : CptT) ≠ .bot
  allTyped : ∀ c, CovWIrrelObservation covWRevEnv n [] EnvWIrrel.bot covWEtaInvTarget c →
    CTyS covWRevEnv c .prop →
    CovWIrrelObservation covWRevEnv n [] EnvWIrrel.bot covWEtaInvSource c ∧
    CovWIrrelObservation covWRevEnv n [] EnvWIrrel.bot covWEtaInvLet c

theorem covWIrrel_proof_supplies_inhabited (n : Nat) : CovWIrrelProofSuppliesAt n where
  envWf := ⟨covWRevEnv_wf⟩
  ctxWf := ⟨.nil⟩
  realized := covWIrrel_realized_nil _ _ _
  erasedValuation := envTypedFinAtT_nil _ _
  erasedCoherence := fun _ _ hv => Option.noConfusion hv
  domainTy := ⟨covWRevP_ty n []⟩
  argTy := ⟨covWRevIndex_ty n []⟩
  bodyTy := ⟨covWEtaInvBody_ty n⟩
  letBodyTy := ⟨covWEtaInvLetBody_ty n⟩
  sourceTy := ⟨covWEtaInvSource_ty n⟩
  letTy := ⟨covWEtaInvLet_ty n⟩
  targetTy := ⟨covWEtaInvTarget_ty n⟩
  typeTy := ⟨.sort [] .zero⟩
  betaConversion := ⟨covWEtaInv_beta_conv n⟩
  letConversion := ⟨covWEtaInv_let_conv n⟩
  betaStep := covWEtaInv_beta_step n
  letStep := covWEtaInv_let_step n
  betaReadback := redR_single (covWEtaInv_beta_step n)
  letReadback := redR_single (covWEtaInv_let_step n)
  targetNormal := covWEtaInv_normal n
  sourceRaw := covWIrrel_inv_source_raw n EnvWIrrel.bot
  letRaw := covWIrrel_inv_let_raw n EnvWIrrel.bot
  targetRaw := covWIrrel_inv_target_raw n EnvWIrrel.bot
  sourceObservation := covWIrrel_observation_of (covWIrrel_inv_source_new n [] EnvWIrrel.bot)
  letObservation := covWIrrel_observation_of (covWIrrel_inv_let_new n [] EnvWIrrel.bot)
  targetObservation := covWIrrel_observation_of (covWIrrel_inv_target_new n [] EnvWIrrel.bot)
  typeObservation := covWIrrel_observation_of (covWIrrel_inv_type_new n [] EnvWIrrel.bot)
  demand := covWIrrel_inv_coarse_typed
  nonbottom := fun h => CptT.noConfusion h
  allTyped := fun _ => covWIrrel_inv_erased_sources

def covWIrrelProofDemandCoarse : CptWIrrel := .spine 4 [] [.bot]

theorem covWIrrel_proofDemand_head_raw (n : Nat) (ρ : EnvWIrrel) :
    ApproxTWIrrel covSProofFnEnv n ρ (.const 4 []) (.spine 4 [] []) := by
  apply ApproxTWIrrel.const ρ 4 [] (neutralHeadP_rigid covSProofFn_neutral)
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  exact neutralHeadP_not_constructor covSProofFn_neutral hm hctor

theorem covWIrrel_proofDemand_head_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covSProofFnEnv n Γ ρ (.const 4 []) (.spine 4 [] []) :=
  .free (kFreeT_rigid_const (neutralHeadP_rigid covSProofFn_neutral) [])
    (covWIrrel_proofDemand_head_raw n ρ)

theorem covWIrrel_proofDemand_left_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 3 []))
      covWIrrelProofDemandCoarse :=
  covWIrrel_guarded_appSpine_bot (covWIrrel_proofDemand_head_new n Γ ρ)

theorem covWIrrel_proofDemand_right_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 1 []))
      covWIrrelProofDemandCoarse :=
  covWIrrel_guarded_appSpine_bot (covWIrrel_proofDemand_head_new n Γ ρ)

theorem covWIrrel_proofDemand_coarse_typed :
    CTyS covSProofFnEnv (covWIrrelErase covWIrrelProofDemandCoarse) .prop := by
  rw [CTyS]
  exact Or.inr (.spine (m := covSProofFnMember) rfl rfl)

theorem covWIrrel_proofDemand_typed_equal (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel)
    (c : CptWIrrel) (ht : CTyS covSProofFnEnv (covWIrrelErase c) .prop) :
    ApproxTKWIrrel covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 3 [])) c ↔
    ApproxTKWIrrel covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 1 [])) c := by
  constructor <;> intro h
  · rcases covWIrrel_proof_field_shape (neutralHeadP_rigid covSProofFn_neutral)
        (covWIrrel_proofDemand_proof_position n) h ht with rfl | rfl
    · exact .bot _ _ _
    · exact covWIrrel_proofDemand_right_new n Γ ρ
  · rcases covWIrrel_proof_field_shape (neutralHeadP_rigid covSProofFn_neutral)
        (covWIrrel_proofDemand_proof_position n) h ht with rfl | rfl
    · exact .bot _ _ _
    · exact covWIrrel_proofDemand_left_new n Γ ρ

theorem covWIrrel_proofDemand_erased_equal (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel)
    (c : CptT) (ht : CTyS covSProofFnEnv c .prop) :
    CovWIrrelObservation covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 3 [])) c ↔
    CovWIrrelObservation covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 1 [])) c := by
  constructor
  · rintro ⟨d, rfl, hd⟩
    exact ⟨d, rfl, (covWIrrel_proofDemand_typed_equal n Γ ρ d ht).mp hd⟩
  · rintro ⟨d, rfl, hd⟩
    exact ⟨d, rfl, (covWIrrel_proofDemand_typed_equal n Γ ρ d ht).mpr hd⟩

def covWIrrel_proofDemand_proofs_conv (n : Nat) (Γ : LCtx) :
    ConvT covSProofFnEnv n Γ (.const 3 []) (.const 1 []) (.const 0 []) :=
  .irr Γ (.const 0 []) (.const 3 []) (.const 1 []) (trueConstTyT rfl)
    (covSProofFn_argument_hasTy n Γ) (covSProofFn_intro_hasTy n Γ)

def covWIrrel_proofDemand_left_ty (n : Nat) (Γ : LCtx) :
    HasTyT covSProofFnEnv n Γ (.app (.const 4 []) (.const 3 [])) (.sort .zero) :=
  .app Γ _ _ (.const 0 []) (.sort .zero)
    (covSProofFn_hasTy n Γ) (covSProofFn_argument_hasTy n Γ)

def covWIrrel_proofDemand_right_ty (n : Nat) (Γ : LCtx) :
    HasTyT covSProofFnEnv n Γ (.app (.const 4 []) (.const 1 [])) (.sort .zero) :=
  .app Γ _ _ (.const 0 []) (.sort .zero)
    (covSProofFn_hasTy n Γ) (covSProofFn_intro_hasTy n Γ)

def covWIrrel_proofDemand_apps_conv (n : Nat) (Γ : LCtx) :
    ConvT covSProofFnEnv n Γ (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (.sort .zero) :=
  .app Γ _ _ _ _ (.const 0 []) (.sort .zero)
    (.refl Γ _ _ (covSProofFn_hasTy n Γ)) (covWIrrel_proofDemand_proofs_conv n Γ)

/-- The repaired application uses a bottom field and the corresponding
actual compact action; the old neutral arrow operator is unchanged. -/
theorem covWIrrel_proofDemand_action :
    CovXCompactAction covSProofFnEnv (.spine 4 []) [.bot]
      (covWIrrelErase covWIrrelProofDemandCoarse) :=
  AppCptT.appSpine (.bvar (List.mem_singleton_self _))

theorem covWIrrel_proofDemand_bottom_demand : BotDemandT [.bot] := by
  intro u hu
  exact List.mem_singleton.mp hu

theorem covWIrrel_proofDemand_composed (n : Nat) (Γ : LCtx) :
    covRCodeRel covSProofFnEnv .prop (.app (.const 4 []) (.const 3 []))
      (.app (.const 4 []) (.const 1 [])) (covWIrrelErase covWIrrelProofDemandCoarse) :=
  covS_positive_argument_action
    (covSTotal_isCandidate covSProofFnEnv (WhStepCK2 covSProofFnEnv n) Γ true)
    (covSProofFnArrow_member n Γ) covWIrrel_proofDemand_action
    (covSProofFn_argument_hasTy n Γ) (covSProofFn_intro_hasTy n Γ)
    ⟨covWIrrel_proofDemand_proofs_conv n Γ⟩

structure CovWIrrelProofDemandSupplyAt (n : Nat) : Prop where
  envWf : Nonempty (EnvWfT covSProofFnEnv)
  ctxWf : Nonempty (CtxWfT covSProofFnEnv n [])
  realized : CovWIrrelRealized covSProofFnEnv n 2 [] EnvWIrrel.bot SubstT.id
  erasedValuation : EnvTypedFinAtT
    (⟨ApproxTKWEta covSProofFnEnv n []⟩ : CtxModelT covSProofFnEnv) []
    (covWIrrelEnvErase EnvWIrrel.bot)
  proofTy : Nonempty (HasTyT covSProofFnEnv n [] (.const 0 []) (.sort .zero))
  functionTy : Nonempty (HasTyT covSProofFnEnv n [] (.const 4 []) covSProofFnTy)
  leftProofTy : Nonempty (HasTyT covSProofFnEnv n [] (.const 3 []) (.const 0 []))
  rightProofTy : Nonempty (HasTyT covSProofFnEnv n [] (.const 1 []) (.const 0 []))
  proofConversion : Nonempty
    (ConvT covSProofFnEnv n [] (.const 3 []) (.const 1 []) (.const 0 []))
  leftTy : Nonempty
    (HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 [])) (.sort .zero))
  rightTy : Nonempty
    (HasTyT covSProofFnEnv n [] (.app (.const 4 []) (.const 1 [])) (.sort .zero))
  conversion : Nonempty (ConvT covSProofFnEnv n [] (.app (.const 4 []) (.const 3 []))
    (.app (.const 4 []) (.const 1 [])) (.sort .zero))
  leftObservation : CovWIrrelObservation covSProofFnEnv n [] EnvWIrrel.bot
    (.app (.const 4 []) (.const 3 [])) (.spine 4 [.bot])
  rightObservation : CovWIrrelObservation covSProofFnEnv n [] EnvWIrrel.bot
    (.app (.const 4 []) (.const 1 [])) (.spine 4 [.bot])
  typeObservation : CovWIrrelObservation covSProofFnEnv n [] EnvWIrrel.bot
    (.sort .zero) .prop
  demand : CTyS covSProofFnEnv (.spine 4 [.bot]) .prop
  nonbottom : (.spine 4 [.bot] : CptT) ≠ .bot
  positiveCandidate : CandidateCovS covSProofFnEnv (WhStepCK2 covSProofFnEnv n) []
    true covSTotalRel
  arrowCandidate : CandidateCovS covSProofFnEnv (WhStepCK2 covSProofFnEnv n) []
    false (covSProofFnArrow n [])
  arrowMember : covSProofFnArrow n [] (.const 4 []) (.const 4 []) (.spine 4 [])
  action : CovXCompactAction covSProofFnEnv (.spine 4 []) [.bot] (.spine 4 [.bot])
  composed : covRCodeRel covSProofFnEnv .prop (.app (.const 4 []) (.const 3 []))
    (.app (.const 4 []) (.const 1 [])) (.spine 4 [.bot])
  allTyped : ∀ c, CTyS covSProofFnEnv c .prop →
    (CovWIrrelObservation covSProofFnEnv n [] EnvWIrrel.bot
      (.app (.const 4 []) (.const 3 [])) c ↔
    CovWIrrelObservation covSProofFnEnv n [] EnvWIrrel.bot
      (.app (.const 4 []) (.const 1 [])) c)

theorem covWIrrel_proofDemand_supply_inhabited (n : Nat) :
    CovWIrrelProofDemandSupplyAt n where
  envWf := ⟨covSProofFnEnvWfT⟩
  ctxWf := ⟨.nil⟩
  realized := covWIrrel_realized_nil _ _ _
  erasedValuation := envTypedFinAtT_nil _ _
  proofTy := ⟨trueConstTyT rfl⟩
  functionTy := ⟨covSProofFn_hasTy n []⟩
  leftProofTy := ⟨covSProofFn_argument_hasTy n []⟩
  rightProofTy := ⟨covSProofFn_intro_hasTy n []⟩
  proofConversion := ⟨covWIrrel_proofDemand_proofs_conv n []⟩
  leftTy := ⟨covWIrrel_proofDemand_left_ty n []⟩
  rightTy := ⟨covWIrrel_proofDemand_right_ty n []⟩
  conversion := ⟨covWIrrel_proofDemand_apps_conv n []⟩
  leftObservation := covWIrrel_observation_of
    (covWIrrel_proofDemand_left_new n [] EnvWIrrel.bot)
  rightObservation := covWIrrel_observation_of
    (covWIrrel_proofDemand_right_new n [] EnvWIrrel.bot)
  typeObservation := covWIrrel_observation_of
    (.free (kFreeT_sort covSProofFnEnv .zero) (.sort EnvWIrrel.bot .zero))
  demand := covWIrrel_proofDemand_coarse_typed
  nonbottom := fun h => CptT.noConfusion h
  positiveCandidate := covSTotal_isCandidate covSProofFnEnv _ [] true
  arrowCandidate := covSProofFnArrow_isCandidate n []
  arrowMember := covSProofFnArrow_member n []
  action := covWIrrel_proofDemand_action
  composed := covWIrrel_proofDemand_composed n []
  allTyped := covWIrrel_proofDemand_erased_equal n [] EnvWIrrel.bot

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_PROOF_SUPPLIES_ROOTS
#print axioms covWIrrel_inv_family_rigid
#print axioms covWIrrel_inv_family_not_propCtor
#print axioms covWIrrel_inv_position
#print axioms covWIrrel_inv_proof_position
#print axioms covWIrrel_inv_family_raw
#print axioms covWIrrel_inv_body_raw
#print axioms covWIrrel_inv_source_raw
#print axioms covWIrrel_inv_let_raw
#print axioms covWIrrel_inv_target_raw
#print axioms covWIrrel_inv_source_new
#print axioms covWIrrel_inv_let_new
#print axioms covWIrrel_inv_target_new
#print axioms covWIrrel_inv_type_new
#print axioms covWIrrel_inv_coarse_typed
#print axioms covWIrrel_inv_typed_sources
#print axioms covWIrrel_inv_typed_factor
#print axioms covWIrrel_inv_erased_sources
#print axioms CovWIrrelProofSuppliesAt
#print axioms covWIrrel_proof_supplies_inhabited
#print axioms covWIrrelProofDemandCoarse
#print axioms covWIrrel_proofDemand_head_raw
#print axioms covWIrrel_proofDemand_head_new
#print axioms covWIrrel_proofDemand_left_new
#print axioms covWIrrel_proofDemand_right_new
#print axioms covWIrrel_proofDemand_coarse_typed
#print axioms covWIrrel_proofDemand_typed_equal
#print axioms covWIrrel_proofDemand_erased_equal
#print axioms covWIrrel_proofDemand_proofs_conv
#print axioms covWIrrel_proofDemand_left_ty
#print axioms covWIrrel_proofDemand_right_ty
#print axioms covWIrrel_proofDemand_apps_conv
#print axioms covWIrrel_proofDemand_action
#print axioms covWIrrel_proofDemand_bottom_demand
#print axioms covWIrrel_proofDemand_composed
#print axioms CovWIrrelProofDemandSupplyAt
#print axioms covWIrrel_proofDemand_supply_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_PROOF_SUPPLIES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
