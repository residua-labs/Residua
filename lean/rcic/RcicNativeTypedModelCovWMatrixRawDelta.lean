import rcic.RcicNativeTypedModelCovWMatrixRawCongruence

/-!
# Admitted delta bodies preserve all raw observations in every context

Raw observations of a definition are observations of its instantiated
body at the bottom valuation. The structural closed-term lemma below
moves those observations to any valuation. The final delta theorem
obtains body closure from the actual environment admission and lookup;
it has no extra body-closure or semantic-equivalence premise.

Raw context congruence transports this equality through every displayed
syntax context. This module makes no guarded-delta claim. The admitted
transparent definition of `Sort 0` provides an explicit native and
nonbottom semantic instance. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovWIrrelAudit

theorem covWMatrix_raw_closedAt_env {E : ResolvedEnv} {n : Nat}
    {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTWIrrel E n ρ e c) :
    ∀ {k : Nat} {ρ' : EnvWIrrel}, exprClosedAt k e = true →
      (∀ i < k, ρ i = ρ' i) → ApproxTWIrrel E n ρ' e c := by
  induction h with
  | bot => intro _ _ _ _; exact .bot _ _
  | @bvar ρ i c h =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, decide_eq_true_eq] at hcl
      exact .bvar (heq i hcl ▸ h)
  | sort => intro _ _ _ _; exact .sort _ _
  | pi _ ht _ ihA ihB =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .pi (ihA hcl.1 heq) ht (fun s hs => ihB s hs hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | lam _ ht hne _ ihA ihB =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      refine .lam (ihA hcl.1 heq) ht hne (fun s hs => ihB s hs hcl.2 (fun i hi => ?_))
      cases i with
      | zero => rfl
      | succ i => exact heq i (Nat.lt_of_succ_lt_succ hi)
  | app _ hs _ ihf iha =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      exact .app (ihf hcl.1 heq) hs (fun u hu => iha u hu hcl.2 heq)
  | const _ _ _ hr hp => intro _ _ _ _; exact .const _ _ _ hr hp
  | delta hd h _ => intro _ _ _ _; exact .delta hd h
  | recursor ls hp hpre hflds h _ =>
      intro _ _ _ _
      exact .recursor ls hp hpre hflds h
  | appSpine _ _ hslot ihf iha =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      exact .appSpine (ihf hcl.1 heq) (iha hcl.2 heq) hslot
  | @letE _ A v b _ _ ih =>
      intro k ρ' hcl heq
      simp only [exprClosedAt, Bool.and_eq_true] at hcl
      have hcl' : exprClosedAt k (.app (.lam A b) v) = true := by
        simp only [exprClosedAt, Bool.and_eq_true]
        exact ⟨⟨hcl.1.1, hcl.2⟩, hcl.1.2⟩
      exact .letE (ih hcl' heq)
  | @lit _ t _ _ ih =>
      intro k ρ' _ heq
      exact .lit (ih (exprClosedAt_natExpand k t) heq)

theorem covWMatrix_raw_closed_env {E : ResolvedEnv} {n : Nat}
    (ρ ρ' : EnvWIrrel) {e : Expr Nat} (hcl : exprClosedAt 0 e = true)
    {c : CptWIrrel} (h : ApproxTWIrrel E n ρ e c) : ApproxTWIrrel E n ρ' e c :=
  covWMatrix_raw_closedAt_env h hcl (fun _ hi => (Nat.not_lt_zero _ hi).elim)

theorem covWMatrix_raw_delta_const_inv {E : ResolvedEnv} {n : Nat}
    {ρ : EnvWIrrel} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hd : DeltaConst E r m b) {c : CptWIrrel}
    (h : ApproxTWIrrel E n ρ (.const r ls) c) :
    ApproxTWIrrel E n EnvWIrrel.bot (instantiateLevels ls b) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hr _ => exact (not_rigidConst_of_deltaConst hd hr).elim
  | delta hd' h' =>
      have hm : m = _ := Option.some.inj (hd.1.symm.trans hd'.1)
      subst hm
      have hb : b = _ := Option.some.inj (hd.2.1.symm.trans hd'.2.1)
      subst hb
      exact h'
  | @recursor _ w => exact (not_deltaConst_of_recursor w hd).elim

/-- Admission supplies the body-closure premise used internally. -/
theorem covWMatrix_raw_delta_eq {E : ResolvedEnv} (hW : EnvWfT E) (n : Nat)
    {r : Nat} (ls : List Level) {m : CheckedMember} {b : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some b) :
    CovWMatrixRawEq E n (.const r ls) (instantiateLevels ls b) := by
  obtain ⟨hd, hcl⟩ := envWfT_member_body_closed hW r m b hm hb
  have hcli : exprClosedAt 0 (instantiateLevels ls b) = true := by
    rw [exprClosedAt_instantiateLevels]
    exact hcl
  intro ρ c
  constructor
  · intro h
    exact covWMatrix_raw_closed_env EnvWIrrel.bot ρ hcli (covWMatrix_raw_delta_const_inv hd h)
  · intro h
    exact .delta hd (covWMatrix_raw_closed_env ρ EnvWIrrel.bot hcli h)

theorem covWMatrix_raw_delta_context_eq {E : ResolvedEnv} (hW : EnvWfT E) (n : Nat)
    {r : Nat} (ls : List Level) {m : CheckedMember} {b : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some b) (C : CovWMatrixRawContext) :
    CovWMatrixRawEq E n (covWMatrixRawFill C (.const r ls))
      (covWMatrixRawFill C (instantiateLevels ls b)) :=
  covWMatrix_raw_context_congr C (covWMatrix_raw_delta_eq hW n ls hm hb)

theorem covWMatrix_raw_delta_context_invariant {E : ResolvedEnv}
    (hW : EnvWfT E) (n : Nat) {r : Nat} (ls : List Level)
    {m : CheckedMember} {b : Expr Nat} (hm : E.members r = some m) (hb : m.body = some b)
    (C : CovWMatrixRawContext) (ρ : EnvWIrrel) (A : Expr Nat) :
    CovWMatrixRawTypedInvariant E n ρ A (covWMatrixRawFill C (.const r ls))
      (covWMatrixRawFill C (instantiateLevels ls b)) :=
  covWMatrix_raw_eq_typed_invariant (covWMatrix_raw_delta_context_eq hW n ls hm hb C) ρ A

theorem covWMatrix_raw_delta_native_pin (n : Nat) :
    CovWMatrixNativePair defSortEnv n (.const 0 []) (.sort .zero)
      (.sort (.succ .zero)) (.succ (.succ .zero)) where
  envWf := ⟨defSortEnvWfT⟩
  ctxWf := ⟨.nil⟩
  leftTy := ⟨.const [] 0 []
    ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ rfl rfl rfl⟩
  rightTy := ⟨.sort [] .zero⟩
  typeTy := ⟨.sort [] (.succ .zero)⟩
  conversion := ⟨.delta [] 0 []
    ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ (.sort .zero)
    rfl rfl rfl rfl rfl (.sort [] .zero)⟩

theorem covWMatrix_raw_delta_eq_pin (n : Nat) :
    CovWMatrixRawEq defSortEnv n (.const 0 []) (.sort .zero) :=
  covWMatrix_raw_delta_eq (r := 0)
    (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩)
    (b := .sort .zero) defSortEnvWfT n [] rfl rfl

/-- An actual shared nonbottom observation at an actually observed type code. -/
theorem covWMatrix_raw_delta_nonbottom_pin (n : Nat) :
    CovWIrrelRawObservation defSortEnv n EnvWIrrel.bot (.const 0 []) .prop ∧
    CovWIrrelRawObservation defSortEnv n EnvWIrrel.bot (.sort .zero) .prop ∧
    CovWIrrelRawObservation defSortEnv n EnvWIrrel.bot (.sort (.succ .zero)) .sort ∧
    CTyS defSortEnv .prop .sort ∧ (CptT.prop ≠ .bot) := by
  have hprop : ApproxTWIrrel defSortEnv n EnvWIrrel.bot (.sort .zero) .prop :=
    .sort _ .zero
  refine ⟨⟨.prop, rfl, ((covWMatrix_raw_delta_eq_pin n) _ _).mpr hprop⟩,
    ⟨.prop, rfl, hprop⟩, ⟨.sort, rfl, .sort _ (.succ .zero)⟩, ?_, ?_⟩
  · rw [CTyS]
    exact Or.inr .prop
  · intro h
    cases h

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_RAW_DELTA_ROOTS
#print axioms covWMatrix_raw_closedAt_env
#print axioms covWMatrix_raw_closed_env
#print axioms covWMatrix_raw_delta_const_inv
#print axioms covWMatrix_raw_delta_eq
#print axioms covWMatrix_raw_delta_context_eq
#print axioms covWMatrix_raw_delta_context_invariant
#print axioms covWMatrix_raw_delta_native_pin
#print axioms covWMatrix_raw_delta_eq_pin
#print axioms covWMatrix_raw_delta_nonbottom_pin
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_RAW_DELTA_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit
