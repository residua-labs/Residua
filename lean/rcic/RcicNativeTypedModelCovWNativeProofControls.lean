import rcic.RcicNativeTypedModelCovWNativeFixtures
import rcic.RcicNativeTypedModelCovWIrrelFullProofEquality
import rcic.RcicNativeTypedModelCovWIrrelProofSupplies

/-! # Proof-field controls in the native-aligned guarded grammar
Every new observation is constructed directly. Native shape facts and
unchanged raw theorems are reused separately. `closure_claim = 0`. -/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKFragmentAudit TypedModelCovUAudit TypedModelCovWAudit
open TypedModelCovWEtaAudit TypedModelCovSAudit TypedModelCovWIrrelAudit
open TypedModelCovPAudit TypedModelCovRAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem headConst_fold (e : Expr Nat) (xs : List (Expr Nat)) :
    headConst (foldApps e xs) = headConst e := by
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih => exact ih (.app e x)

private theorem headShape_append {E : ResolvedEnv} {n r r' k : Nat}
    {ls ls' : List Level} {us : List CptWIrrel} {u : CptWIrrel}
    (h : CovWIrrelHeadShape E n r ls k (.spine r' ls' us))
    (hp : CovWIrrelProofPosition E n r' ls' us.length → u = .bot) :
    CovWIrrelHeadShape E n r ls (k + 1) (.spine r' ls' (us ++ [u])) := by
  rw [CovWIrrelHeadShape] at h ⊢
  obtain ⟨rfl, rfl, hk, hh⟩ := h
  refine ⟨rfl, rfl, by simp [hk], ?_⟩
  intro i hi hiP
  by_cases hl : i < us.length
  · simpa only [List.getElem_append_left hl] using hh i hl hiP
  · have he : i = us.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hp hiP

theorem covWNative_guarded_head_shape {E : ResolvedEnv} {n r k : Nat}
    {ls : List Level} {Γ : LCtx} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (hr : RigidConst E r) (h : ApproxTKWNative E n Γ ρ e c)
    (he : CovWIrrelHeadTerm r ls k e) : CovWIrrelHeadShape E n r ls k c := by
  induction h generalizing k with
  | bot => rw [CovWIrrelHeadShape]; trivial
  | bvar => cases he
  | sort => cases he
  | const => cases he; rw [CovWIrrelHeadShape]; exact ⟨rfl, rfl, rfl, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | recursor ls hp hpre hf h ih =>
      cases he
      exact ((hr _ ‹IotaWitnessS E›.hrec).2 ‹IotaWitnessS E›.hrecK).elim
  | pi => cases he
  | lam => cases he
  | app hf hs ha ihf iha =>
      cases he with
      | app hf =>
          have hh := ihf hf
          rw [CovWIrrelHeadShape] at hh
          exact hh _ hs
  | appSpine hf ha hp hfield ihf iha =>
      cases he with
      | app hf => exact headShape_append (ihf hf) hp
  | delta hd _ _ =>
      cases he
      exact (not_rigidConst_of_deltaConst hd hr).elim
  | letE => cases he
  | lit => cases he
  | iota w _ _ =>
      have heq := he.headConst
      rw [iotaLhsOfS, recCall, headConst_fold] at heq
      have heq : w.recRef = r := Option.some.inj heq
      subst r
      exact ((hr _ w.hrec).2 w.hrecK).elim
  | recursorPropK w x _ _ _ _ _ _ =>
      have heq := he.headConst
      rw [recCall, headConst_fold] at heq
      have heq : w.recRef = r := Option.some.inj heq
      subst r
      exact ((hr _ w.hrec).2 w.hrecK).elim
  | eta _ _ _ _ _ ihD ihb =>
      rw [CovWIrrelHeadShape]
      intro s hs
      exact ihb s hs (.app he.lift_one)

theorem covWNative_proof_field_shape {E : ResolvedEnv} {n r : Nat}
    {ls : List Level} {Γ : LCtx} {ρ : EnvWIrrel} {x : Expr Nat} {c : CptWIrrel}
    (hr : RigidConst E r) (hp : CovWIrrelProofPosition E n r ls 0)
    (h : ApproxTKWNative E n Γ ρ (.app (.const r ls) x) c)
    (ht : CTyS E (covWIrrelErase c) .prop) :
    c = .bot ∨ c = .spine r ls [.bot] := by
  have hs := covWNative_guarded_head_shape hr h (CovWIrrelHeadTerm.app .head)
  cases c with
  | bot => exact Or.inl rfl
  | prop => simp [CovWIrrelHeadShape] at hs
  | sort => simp [CovWIrrelHeadShape] at hs
  | pi => simp [CovWIrrelHeadShape] at hs
  | lam rows =>
      rcases ctyS_prop_inv ht with h | h
      · cases h
      · cases h
  | spine r' ls' us =>
      rw [CovWIrrelHeadShape] at hs
      obtain ⟨rfl, rfl, hl, hh⟩ := hs
      cases us with
      | nil => cases hl
      | cons u us =>
          have hlen : us = [] := List.length_eq_zero.mp (Nat.succ.inj hl)
          subst us
          have hu := hh 0 (by simp) hp
          have hu : u = .bot := hu
          subst u
          exact Or.inr rfl

theorem covWNative_family_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWIrrelEnv n Γ ρ covWIrrelFamily (.spine 5 [] []) :=
  .const Γ ρ 5 [] covWIrrel_family_rigid covWIrrel_family_not_propCtor

theorem covWNative_left_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWIrrelEnv n Γ ρ covWIrrelLeft covWIrrelCoarse :=
  covWNative_guarded_appSpine_bot (covWIrrel_family_ty n Γ) (covWIrrel_p_ty n Γ)
    (covWNative_family_new n Γ ρ)

theorem covWNative_right_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWIrrelEnv n Γ ρ covWIrrelRight covWIrrelCoarse :=
  covWNative_guarded_appSpine_bot (covWIrrel_family_ty n Γ) (covWIrrel_q_ty n Γ)
    (covWNative_family_new n Γ ρ)

private theorem source_headConst {n : Nat} {Γ : LCtx} {b : Bool} {e : Expr Nat}
    (hs : CovWIrrelFamilySource n Γ b e) : headConst e = some 5 := by
  cases hs <;> rfl

theorem covWNative_family_shape_of_native {n : Nat}
    (hScope : covWIrrelEnv_wf.InScope) (hstep : CovWIrrelFamilyEtaStep n)
    {Γ : LCtx} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWNative covWIrrelEnv n Γ ρ e c) :
    ∀ {b : Bool}, CtxWfT covWIrrelEnv n Γ →
      CovWIrrelFamilySource n Γ b e → CovWIrrelFamilyShape b c := by
  induction h with
  | bot =>
      intro b hΓ hs
      cases b <;> exact Or.inl rfl
  | bvar => intro b hΓ hs; cases hs
  | sort => intro b hΓ hs; cases hs
  | const => intro b hΓ hs; cases hs; exact Or.inr (Or.inl rfl)
  | recursor ls hp hpre hf h ih =>
      intro b hΓ hs
      have heq : (‹IotaWitnessS covWIrrelEnv›).recRef = 5 :=
        Option.some.inj (source_headConst hs)
      have hr : RigidConst covWIrrelEnv (‹IotaWitnessS covWIrrelEnv›).recRef := by
        rw [heq]
        exact covWIrrel_family_rigid
      exact ((hr _ ‹IotaWitnessS covWIrrelEnv›.hrec).2
        ‹IotaWitnessS covWIrrelEnv›.hrecK).elim
  | pi => intro b hΓ hs; cases hs
  | lam => intro b hΓ hs; cases hs
  | app hf hs ha ihf iha =>
      intro b hΓ he
      cases he with
      | applied _ =>
          have hh := ihf hΓ CovWIrrelFamilySource.head
          rcases hh with h | h | ⟨rows, h, hrows⟩
          · cases h
          · cases h
          · cases h
            exact hrows _ hs
  | appSpine hf ha hp hfield ihf iha =>
      intro b hΓ he
      cases he with
      | applied _ =>
          have hh := ihf hΓ CovWIrrelFamilySource.head
          rcases hh with h | h | ⟨rows, h, hrows⟩
          · cases h
          · cases h
            have hu := hp (covWIrrel_family_proof_position n)
            rw [hu]
            exact Or.inr rfl
          · cases h
  | delta hd _ _ =>
      intro b hΓ he
      cases he
      exact (not_rigidConst_of_deltaConst hd covWIrrel_family_rigid).elim
  | letE => intro b hΓ hs; cases hs
  | lit => intro b hΓ hs; cases hs
  | iota w _ _ =>
      intro b hΓ hs
      have heq := source_headConst hs
      rw [iotaLhsOfS, recCall, headConst_fold] at heq
      have heq : w.recRef = 5 := Option.some.inj heq
      have hr : RigidConst covWIrrelEnv w.recRef := by
        rw [heq]
        exact covWIrrel_family_rigid
      exact ((hr _ w.hrec).2 w.hrecK).elim
  | recursorPropK w x _ _ _ _ _ _ =>
      intro b hΓ hs
      have heq := source_headConst hs
      rw [recCall, headConst_fold] at heq
      have heq : w.recRef = 5 := Option.some.inj heq
      have hr : RigidConst covWIrrelEnv w.recRef := by
        rw [heq]
        exact covWIrrel_family_rigid
      exact ((hr _ w.hrec).2 w.hrecK).elim
  | eta he hD ht hn hb ihD ihb =>
      intro b hΓ hs
      cases hs with
      | head =>
          obtain ⟨⟨hΓ', hbody⟩⟩ := hstep hΓ he
          refine Or.inr (Or.inr ⟨_, rfl, ?_⟩)
          intro s hs
          exact ihb s hs hΓ' (.applied ⟨hbody⟩)
      | applied hsort =>
          obtain ⟨hsort⟩ := hsort
          exact (covWIrrel_native_not_sort_and_pi covWIrrelEnv_wf
            hScope hΓ hsort he).elim

theorem covWNative_family_applied_all_shape_of_native {n : Nat}
    (hScope : covWIrrelEnv_wf.InScope) (hstep : CovWIrrelFamilyEtaStep n)
    {Γ : LCtx} (hΓ : CtxWfT covWIrrelEnv n Γ) {ρ : EnvWIrrel}
    {x : Expr Nat} {c : CptWIrrel}
    (ht : HasTyT covWIrrelEnv n Γ (.app covWIrrelFamily x) (.sort .zero))
    (h : ApproxTKWNative covWIrrelEnv n Γ ρ (.app covWIrrelFamily x) c) :
    c = .bot ∨ c = covWIrrelCoarse :=
  covWNative_family_shape_of_native hScope hstep h hΓ (.applied ⟨ht⟩)

theorem covWNative_family_all_observations_equal_of_native (n : Nat)
    (hScope : covWIrrelEnv_wf.InScope) (hstep : CovWIrrelFamilyEtaStep n)
    (Γ : LCtx) (hΓ : CtxWfT covWIrrelEnv n Γ) (ρ : EnvWIrrel)
    (c : CptWIrrel) :
    ApproxTKWNative covWIrrelEnv n Γ ρ covWIrrelLeft c ↔
      ApproxTKWNative covWIrrelEnv n Γ ρ covWIrrelRight c := by
  constructor <;> intro h
  · rcases covWNative_family_applied_all_shape_of_native hScope hstep hΓ
        (covWIrrel_left_ty n Γ) h with rfl | rfl
    · exact .bot _ _ _
    · exact covWNative_right_new n Γ ρ
  · rcases covWNative_family_applied_all_shape_of_native hScope hstep hΓ
        (covWIrrel_right_ty n Γ) h with rfl | rfl
    · exact .bot _ _ _
    · exact covWNative_left_new n Γ ρ

theorem covWNative_family_all_public_observations_equal_of_native (n : Nat)
    (hScope : covWIrrelEnv_wf.InScope) (hstep : CovWIrrelFamilyEtaStep n)
    (Γ : LCtx) (hΓ : CtxWfT covWIrrelEnv n Γ) (ρ : EnvWIrrel)
    (c : CptT) :
    CovWNativeObservation covWIrrelEnv n Γ ρ covWIrrelLeft c ↔
      CovWNativeObservation covWIrrelEnv n Γ ρ covWIrrelRight c := by
  constructor <;> rintro ⟨d, hd, h⟩
  · exact ⟨d, hd,
      (covWNative_family_all_observations_equal_of_native n hScope hstep Γ hΓ ρ d).mp h⟩
  · exact ⟨d, hd,
      (covWNative_family_all_observations_equal_of_native n hScope hstep Γ hΓ ρ d).mpr h⟩

/-- Every observation of a well-typed application of this family is one
of its two exact compacts. There is no semantic typing restriction on c. -/
theorem covWNative_family_applied_all_shape {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT covWIrrelEnv n Γ) {ρ : EnvWIrrel}
    {x : Expr Nat} {c : CptWIrrel}
    (ht : HasTyT covWIrrelEnv n Γ (.app covWIrrelFamily x) (.sort .zero))
    (h : ApproxTKWNative covWIrrelEnv n Γ ρ (.app covWIrrelFamily x) c) :
    c = .bot ∨ c = covWIrrelCoarse :=
  covWNative_family_applied_all_shape_of_native covWIrrelEnv_inScope
    (covWIrrel_family_eta_step n) hΓ ht h

/-- The supplied proof pair shares every decorated observation, including
all finite graph and eta alternatives, in each well-formed context. -/
theorem covWNative_family_all_observations_equal (n : Nat)
    (Γ : LCtx) (hΓ : CtxWfT covWIrrelEnv n Γ) (ρ : EnvWIrrel)
    (c : CptWIrrel) :
    ApproxTKWNative covWIrrelEnv n Γ ρ covWIrrelLeft c ↔
      ApproxTKWNative covWIrrelEnv n Γ ρ covWIrrelRight c :=
  covWNative_family_all_observations_equal_of_native n covWIrrelEnv_inScope
    (covWIrrel_family_eta_step n) Γ hΓ ρ c

/-- The same equality is stated at the public, recursively erased compact. -/
theorem covWNative_family_all_public_observations_equal (n : Nat)
    (Γ : LCtx) (hΓ : CtxWfT covWIrrelEnv n Γ) (ρ : EnvWIrrel)
    (c : CptT) :
    CovWNativeObservation covWIrrelEnv n Γ ρ covWIrrelLeft c ↔
      CovWNativeObservation covWIrrelEnv n Γ ρ covWIrrelRight c :=
  covWNative_family_all_public_observations_equal_of_native n covWIrrelEnv_inScope
    (covWIrrel_family_eta_step n) Γ hΓ ρ c

theorem covWNative_family_closed_observations_equal (n : Nat) (c : CptWIrrel) :
    ApproxTKWNative covWIrrelEnv n [] EnvWIrrel.bot covWIrrelLeft c ↔
      ApproxTKWNative covWIrrelEnv n [] EnvWIrrel.bot covWIrrelRight c :=
  covWNative_family_all_observations_equal n [] .nil EnvWIrrel.bot c

theorem covWNative_family_closed_public_observations_equal (n : Nat) (c : CptT) :
    CovWNativeObservation covWIrrelEnv n [] EnvWIrrel.bot covWIrrelLeft c ↔
      CovWNativeObservation covWIrrelEnv n [] EnvWIrrel.bot covWIrrelRight c :=
  covWNative_family_all_public_observations_equal n [] .nil EnvWIrrel.bot c

theorem covWNative_proofDemand_head (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covSProofFnEnv n Γ ρ (.const 4 []) (.spine 4 [] []) :=
  covWNative_neutral_observed covSProofFn_neutral n Γ ρ

theorem covWNative_proofDemand_left (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 3 []))
      covWIrrelProofDemandCoarse :=
  covWNative_guarded_appSpine_bot (covSProofFn_hasTy n Γ)
    (covSProofFn_argument_hasTy n Γ) (covWNative_proofDemand_head n Γ ρ)

theorem covWNative_proofDemand_right (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 1 []))
      covWIrrelProofDemandCoarse :=
  covWNative_guarded_appSpine_bot (covSProofFn_hasTy n Γ)
    (covSProofFn_intro_hasTy n Γ) (covWNative_proofDemand_head n Γ ρ)

theorem covWNative_proofDemand_typed_equal (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel)
    (c : CptWIrrel) (ht : CTyS covSProofFnEnv (covWIrrelErase c) .prop) :
    ApproxTKWNative covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 3 [])) c ↔
      ApproxTKWNative covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 1 [])) c := by
  constructor <;> intro h
  · rcases covWNative_proof_field_shape (neutralHeadP_rigid covSProofFn_neutral)
        (covWIrrel_proofDemand_proof_position n) h ht with rfl | rfl
    · exact .bot _ _ _
    · exact covWNative_proofDemand_right n Γ ρ
  · rcases covWNative_proof_field_shape (neutralHeadP_rigid covSProofFn_neutral)
        (covWIrrel_proofDemand_proof_position n) h ht with rfl | rfl
    · exact .bot _ _ _
    · exact covWNative_proofDemand_left n Γ ρ

theorem covWNative_proofDemand_erased_equal (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel)
    (c : CptT) (ht : CTyS covSProofFnEnv c .prop) :
    CovWNativeObservation covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 3 [])) c ↔
      CovWNativeObservation covSProofFnEnv n Γ ρ (.app (.const 4 []) (.const 1 [])) c := by
  constructor
  · rintro ⟨d, rfl, hd⟩
    exact ⟨d, rfl, (covWNative_proofDemand_typed_equal n Γ ρ d ht).mp hd⟩
  · rintro ⟨d, rfl, hd⟩
    exact ⟨d, rfl, (covWNative_proofDemand_typed_equal n Γ ρ d ht).mpr hd⟩

/-- The old native/action payload remains explicitly old. The observations
and realizer conjuncts below are fresh supplies in the aligned grammar. -/
theorem covWNative_proofDemand_control (n : Nat) :
    CovWIrrelProofDemandSupplyAt n ∧
    CovWNativeRealized covSProofFnEnv n 2 [] EnvWIrrel.bot SubstT.id ∧
    CovWNativeObservation covSProofFnEnv n [] EnvWIrrel.bot
      (.sort .zero) .prop ∧
    CovWNativeObservation covSProofFnEnv n [] EnvWIrrel.bot
      (.app (.const 4 []) (.const 3 [])) (.spine 4 [.bot]) ∧
    CovWNativeObservation covSProofFnEnv n [] EnvWIrrel.bot
      (.app (.const 4 []) (.const 1 [])) (.spine 4 [.bot]) ∧
    ∀ c, CTyS covSProofFnEnv c .prop →
      (CovWNativeObservation covSProofFnEnv n [] EnvWIrrel.bot
        (.app (.const 4 []) (.const 3 [])) c ↔
      CovWNativeObservation covSProofFnEnv n [] EnvWIrrel.bot
        (.app (.const 4 []) (.const 1 [])) c) :=
  ⟨covWIrrel_proofDemand_supply_inhabited n, covWNative_realized_nil _ _ _,
    covWNative_observation_of (.sort _ _ .zero),
    covWNative_observation_of (covWNative_proofDemand_left n _ _),
    covWNative_observation_of (covWNative_proofDemand_right n _ _),
    covWNative_proofDemand_erased_equal n [] EnvWIrrel.bot⟩

theorem covWNative_inv_family (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWRevEnv n Γ ρ (.const 5 []) (.spine 5 [] []) :=
  .const Γ ρ 5 [] covWIrrel_inv_family_rigid covWIrrel_inv_family_not_propCtor

theorem covWNative_inv_body (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWRevEnv n (.assumption covUProjP :: Γ) ρ
      covWEtaInvBody covWIrrelCoarse :=
  covWNative_guarded_appSpine_bot (.const (.assumption covUProjP :: Γ) 5 [] covWRevFam rfl rfl rfl)
    (.bvar _ 0 _ rfl) (covWNative_inv_family n _ _)

theorem covWNative_inv_source (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWRevEnv n Γ ρ covWEtaInvSource covWIrrelCoarse := by
  apply covWNative_empty_app
  apply covWNative_empty_lam (by intro h; cases h)
  exact covWNative_inv_body n Γ _

theorem covWNative_inv_let (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWRevEnv n Γ ρ covWEtaInvLet covWIrrelCoarse :=
  .letE (covWNative_inv_source n Γ ρ)

theorem covWNative_inv_target (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWNative covWRevEnv n Γ ρ covWEtaInvTarget covWIrrelCoarse :=
  covWNative_guarded_appSpine_bot (.const _ 5 [] covWRevFam rfl rfl rfl)
    (covWRevIndex_ty n Γ) (covWNative_inv_family n Γ ρ)

theorem covWNative_inv_typed_sources {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptWIrrel} (ho : ApproxTKWNative covWRevEnv n Γ ρ covWEtaInvTarget c)
    (ht : CTyS covWRevEnv (covWIrrelErase c) .prop) :
    ApproxTKWNative covWRevEnv n Γ ρ covWEtaInvSource c ∧
    ApproxTKWNative covWRevEnv n Γ ρ covWEtaInvLet c := by
  rcases covWNative_proof_field_shape covWIrrel_inv_family_rigid
      (covWIrrel_inv_proof_position n) ho ht with rfl | rfl
  · exact ⟨.bot _ _ _, .bot _ _ _⟩
  · exact ⟨covWNative_inv_source n Γ ρ, covWNative_inv_let n Γ ρ⟩

theorem covWNative_inv_erased_sources {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel}
    {c : CptT} (ho : CovWNativeObservation covWRevEnv n Γ ρ covWEtaInvTarget c)
    (ht : CTyS covWRevEnv c .prop) :
    CovWNativeObservation covWRevEnv n Γ ρ covWEtaInvSource c ∧
    CovWNativeObservation covWRevEnv n Γ ρ covWEtaInvLet c := by
  obtain ⟨d, rfl, hd⟩ := ho
  have hs := covWNative_inv_typed_sources hd ht
  exact ⟨⟨d, rfl, hs.1⟩, ⟨d, rfl, hs.2⟩⟩

/-- Local beta/let supplies include the old native fixture explicitly and
fresh native-aligned observations; this is not general subject expansion. -/
theorem covWNative_inv_control (n : Nat) :
    CovWIrrelProofSuppliesAt n ∧
    CovWNativeRealized covWRevEnv n 2 [] EnvWIrrel.bot SubstT.id ∧
    CovWNativeObservation covWRevEnv n [] EnvWIrrel.bot (.sort .zero) .prop ∧
    CovWNativeObservation covWRevEnv n [] EnvWIrrel.bot covWEtaInvSource (.spine 5 [.bot]) ∧
    CovWNativeObservation covWRevEnv n [] EnvWIrrel.bot covWEtaInvLet (.spine 5 [.bot]) ∧
    CovWNativeObservation covWRevEnv n [] EnvWIrrel.bot covWEtaInvTarget (.spine 5 [.bot]) ∧
    ∀ c, CovWNativeObservation covWRevEnv n [] EnvWIrrel.bot covWEtaInvTarget c →
      CTyS covWRevEnv c .prop →
      CovWNativeObservation covWRevEnv n [] EnvWIrrel.bot covWEtaInvSource c ∧
      CovWNativeObservation covWRevEnv n [] EnvWIrrel.bot covWEtaInvLet c :=
  ⟨covWIrrel_proof_supplies_inhabited n, covWNative_realized_nil _ _ _,
    covWNative_observation_of (.sort _ _ .zero),
    covWNative_observation_of (covWNative_inv_source n _ _),
    covWNative_observation_of (covWNative_inv_let n _ _),
    covWNative_observation_of (covWNative_inv_target n _ _),
    fun _ => covWNative_inv_erased_sources⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_PROOF_CONTROLS_ROOTS
#print axioms covWNative_guarded_head_shape
#print axioms covWNative_proof_field_shape
#print axioms covWNative_family_new
#print axioms covWNative_left_new
#print axioms covWNative_right_new
#print axioms covWNative_family_shape_of_native
#print axioms covWNative_family_applied_all_shape_of_native
#print axioms covWNative_family_all_observations_equal_of_native
#print axioms covWNative_family_all_public_observations_equal_of_native
#print axioms covWNative_family_applied_all_shape
#print axioms covWNative_family_all_observations_equal
#print axioms covWNative_family_all_public_observations_equal
#print axioms covWNative_family_closed_observations_equal
#print axioms covWNative_family_closed_public_observations_equal
#print axioms covWNative_proofDemand_head
#print axioms covWNative_proofDemand_left
#print axioms covWNative_proofDemand_right
#print axioms covWNative_proofDemand_typed_equal
#print axioms covWNative_proofDemand_erased_equal
#print axioms covWNative_proofDemand_control
#print axioms covWNative_inv_family
#print axioms covWNative_inv_body
#print axioms covWNative_inv_source
#print axioms covWNative_inv_let
#print axioms covWNative_inv_target
#print axioms covWNative_inv_typed_sources
#print axioms covWNative_inv_erased_sources
#print axioms covWNative_inv_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_PROOF_CONTROLS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
