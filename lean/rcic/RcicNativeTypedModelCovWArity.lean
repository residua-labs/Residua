import rcic.RcicNativeTypedModelCovVHeadActions
import rcic.RcicIotaWitnessTypedClosed

/-!
# Native constant arities for observation induction

The condition below records only declared constant instances and their
universe-list lengths. Native typing supplies it directly. Stored bodies and
admitted recursor schemas supply it from `EnvWfT`, including opaque bodies.
This avoids assuming typing of arbitrary action arguments while retaining
the exact universe-arity premise needed by native schema iota.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit PiModelDeltaIotaAudit

def CovWMemberArity (E : ResolvedEnv) (r k : Nat) : Prop :=
  ∃ m : CheckedMember, E.members r = some m ∧ k = m.arity

def CovWConstsArity (E : ResolvedEnv) : Expr Nat → Prop
  | .bvar _ | .sort _ => True
  | .const r ls => CovWMemberArity E r ls.length
  | .app f a => CovWConstsArity E f ∧ CovWConstsArity E a
  | .lam A b | .pi A b => CovWConstsArity E A ∧ CovWConstsArity E b
  | .letE A v b => CovWConstsArity E A ∧ CovWConstsArity E v ∧ CovWConstsArity E b
  | .lit 0 => CovWMemberArity E 1 0
  | .lit (_ + 1) => CovWMemberArity E 1 0 ∧ CovWMemberArity E 2 0

theorem covW_consts_arity_natExpand_iff (E : ResolvedEnv) : ∀ t : Nat,
    CovWConstsArity E (natExpand t) ↔ CovWConstsArity E (.lit t)
  | 0 => Iff.rfl
  | 1 => by
      change (CovWMemberArity E 2 0 ∧ CovWMemberArity E 1 0) ↔
        (CovWMemberArity E 1 0 ∧ CovWMemberArity E 2 0)
      exact and_comm
  | t + 2 => by
      change (CovWMemberArity E 2 0 ∧ CovWConstsArity E (natExpand (t + 1))) ↔
        (CovWMemberArity E 1 0 ∧ CovWMemberArity E 2 0)
      rw [covW_consts_arity_natExpand_iff E (t + 1)]
      change (CovWMemberArity E 2 0 ∧
        (CovWMemberArity E 1 0 ∧ CovWMemberArity E 2 0)) ↔
        (CovWMemberArity E 1 0 ∧ CovWMemberArity E 2 0)
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h⟩⟩

/-- Every term constructor reads its actual native typing premises. -/
theorem covW_hasTy_consts_arity {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T → CovWConstsArity E e
  | _, _, _, .sort _ _ => trivial
  | _, _, _, .bvar _ _ _ _ => trivial
  | _, _, _, .const _ _ _ m hm hlen _ => ⟨m, hm, hlen⟩
  | _, _, _, .pi _ _ _ _ _ hA hB =>
      ⟨covW_hasTy_consts_arity hA, covW_hasTy_consts_arity hB⟩
  | _, _, _, .lam _ _ _ _ _ hA hb =>
      ⟨covW_hasTy_consts_arity hA, covW_hasTy_consts_arity hb⟩
  | _, _, _, .app _ _ _ _ _ hf ha =>
      ⟨covW_hasTy_consts_arity hf, covW_hasTy_consts_arity ha⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb =>
      ⟨covW_hasTy_consts_arity hA, covW_hasTy_consts_arity hv, covW_hasTy_consts_arity hb⟩
  | _, _, _, .lit _ t _ h =>
      (covW_consts_arity_natExpand_iff E t).mp (covW_hasTy_consts_arity h)
  | _, _, _, .conv _ _ _ _ _ h _ => covW_hasTy_consts_arity h

theorem CovWMemberArity.mono {E E' : ResolvedEnv}
    (he : ∀ r m, E.members r = some m → E'.members r = some m)
    {r k : Nat} (h : CovWMemberArity E r k) : CovWMemberArity E' r k := by
  obtain ⟨m, hm, hk⟩ := h
  exact ⟨m, he r m hm, hk⟩

theorem covW_consts_arity_mono {E E' : ResolvedEnv}
    (he : ∀ r m, E.members r = some m → E'.members r = some m)
    {e : Expr Nat} (h : CovWConstsArity E e) : CovWConstsArity E' e := by
  induction e with
  | bvar => trivial
  | sort => trivial
  | const => exact h.mono he
  | app f a ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam A b ihA ihb => exact ⟨ihA h.1, ihb h.2⟩
  | pi A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | letE A v b ihA ihv ihb => exact ⟨ihA h.1, ihv h.2.1, ihb h.2.2⟩
  | lit t =>
      cases t with
      | zero => exact h.mono he
      | succ t => exact ⟨h.1.mono he, h.2.mono he⟩

/-- Universe substitution preserves the length of every constant instance. -/
theorem covW_consts_arity_levels {E : ResolvedEnv} (ls : List Level)
    {e : Expr Nat} (h : CovWConstsArity E e) :
    CovWConstsArity E (instantiateLevels ls e) := by
  induction e with
  | bvar => trivial
  | sort => trivial
  | const r us =>
      simpa only [instantiateLevels, CovWConstsArity, List.length_map] using h
  | app f a ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam A b ihA ihb => exact ⟨ihA h.1, ihb h.2⟩
  | pi A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | letE A v b ihA ihv ihb => exact ⟨ihA h.1, ihv h.2.1, ihb h.2.2⟩
  | lit => exact h

theorem covW_group_body_arities {S E E' : ResolvedEnv}
    {members : List (Nat × CheckedMember)} (hmembers : GroupMembersT S E members E')
    (hE : ∀ r m b, E.members r = some m → m.body = some b → CovWConstsArity E b) :
    ∀ r m b, E'.members r = some m → m.body = some b → CovWConstsArity E' b := by
  induction hmembers with
  | nil _ => exact hE
  | @cons E₀ r₀ m₀ _ _ hfresh hnobody _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      refine ih (fun r m b hm hb => ?_)
      by_cases hrr : r = r₀
      · subst hrr
        rw [members_extend_eq] at hm
        cases hm
        rw [hnobody] at hb
        cases hb
      · rw [members_extend_ne E₀ r₀ m₀ r hrr] at hm
        exact covW_consts_arity_mono (members_extend_preserved hfresh) (hE r m b hm hb)

/-- Stored definition, theorem and opaque bodies inherit the arities of
their actual admission derivations. Group steps add no new bodies. -/
theorem covW_body_consts_arity {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ r m b, E.members r = some m → m.body = some b → CovWConstsArity E b := by
  induction hW with
  | empty => intro _ _ _ hm _; exact Option.noConfusion hm
  | @«axiom» E₀ r₀ A _ _ hfresh _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr
        rw [members_extend_eq] at hm
        cases hm
        cases hb
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm
        exact covW_consts_arity_mono (members_extend_preserved hfresh) (ih r m b hm hb)
  | @definition E₀ r₀ A v _ _ hfresh _ hv _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr
        rw [members_extend_eq] at hm
        cases hm
        cases hb
        exact covW_consts_arity_mono (members_extend_preserved hfresh)
          (covW_hasTy_consts_arity hv)
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm
        exact covW_consts_arity_mono (members_extend_preserved hfresh) (ih r m b hm hb)
  | @thm E₀ r₀ A p _ hfresh _ hp _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr
        rw [members_extend_eq] at hm
        cases hm
        cases hb
        exact covW_consts_arity_mono (members_extend_preserved hfresh)
          (covW_hasTy_consts_arity hp)
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm
        exact covW_consts_arity_mono (members_extend_preserved hfresh) (ih r m b hm hb)
  | @«opaque» E₀ r₀ A v _ _ hfresh _ hv _ _ _ _ ih =>
      intro r m b hm hb
      by_cases hrr : r = r₀
      · subst hrr
        rw [members_extend_eq] at hm
        cases hm
        cases hb
        exact covW_consts_arity_mono (members_extend_preserved hfresh)
          (covW_hasTy_consts_arity hv)
      · rw [members_extend_ne E₀ r₀ _ r hrr] at hm
        exact covW_consts_arity_mono (members_extend_preserved hfresh) (ih r m b hm hb)
  | group _ _ _ _ _ _ _ _ _ _ _ hmembers ih =>
      exact covW_group_body_arities hmembers ih

/-- Admission's typed schema supplies all hidden constant arities. The
schema's native variables need no inhabitants for this syntactic conclusion. -/
theorem covW_schema_consts_arity {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitnessS E) (ls : List Level) :
    CovWConstsArity E (instantiateLevels ls w.schema) := by
  let cell := envWfT_cellHT hW w.hrec w.hrecK
  obtain ⟨i, _, doms, _, ⟨ht⟩⟩ := iotaWitnessS_schema_typed_cellHT w cell
  exact covW_consts_arity_levels ls (covW_hasTy_consts_arity ht)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ARITY_ROOTS
#print axioms CovWMemberArity
#print axioms CovWConstsArity
#print axioms covW_consts_arity_natExpand_iff
#print axioms covW_hasTy_consts_arity
#print axioms CovWMemberArity.mono
#print axioms covW_consts_arity_mono
#print axioms covW_consts_arity_levels
#print axioms covW_group_body_arities
#print axioms covW_body_consts_arity
#print axioms covW_schema_consts_arity
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ARITY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWAudit
