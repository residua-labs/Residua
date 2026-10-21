import rcic.RcicNativeTypedModelK
import rcic.RcicNativeTypedModelCovSTemplate

/-!
# An explicit finite-information stage for ApproxTK

The existing ApproxTK index is the universe-parameter arity. This additive
wrapper introduces a separate compact-node budget. It bounds information
stored in the observation, not native reduction steps or derivation height.
It neither changes an ApproxTK rule nor makes observations deterministic.
In particular any two existing finite observations can be put at a common
stage; that fact alone is not a semantic coupling theorem.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit
open TypedModelCovSAudit

/-- Count observed type nodes. Demands and rigid arguments are values;
their internal tables are not recursively interpreted as native types. -/
def covTObservationBudget (c : CptT) : Nat :=
  match c with
  | .bot => 0
  | .prop => 1
  | .sort => 1
  | .spine _ _ => 1
  | .pi d rows => 1 + covTObservationBudget d +
      (rows.attach.map fun s => covTObservationBudget s.val.2).sum
  | .lam rows => 1 +
      (rows.attach.map fun s => covTObservationBudget s.val.2).sum
termination_by sizeOf c
decreasing_by
  · exact covS_pi_domain_size_lt _ _
  · exact covS_pi_output_size_lt _ _ _ s.property
  · have h₁ := List.sizeOf_lt_of_mem s.property
    have h₂ := sizeOfT_snd_lt s.val
    simp only [CptT.lam.sizeOf_spec]
    omega

theorem covTObservationBudget_zero_iff (c : CptT) :
    covTObservationBudget c = 0 ↔ c = .bot := by
  cases c <;> simp [covTObservationBudget] <;> omega

/-- Both indices are explicit: native universe-parameter arity, then a
finite observation-information budget. -/
def ApproxTKStage (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvT) (e : Expr Nat) (c : CptT) : Prop :=
  ApproxTK E arity Γ ρ e c ∧ covTObservationBudget c ≤ stage

theorem ApproxTKStage.forget {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTKStage E arity stage Γ ρ e c) :
    ApproxTK E arity Γ ρ e c := h.1

theorem ApproxTKStage.mono {E : ResolvedEnv} {arity k l : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTKStage E arity k Γ ρ e c) (hkl : k ≤ l) :
    ApproxTKStage E arity l Γ ρ e c := ⟨h.1, Nat.le_trans h.2 hkl⟩

theorem approxTKStage_bot (E : ResolvedEnv) (arity stage : Nat)
    (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) :
    ApproxTKStage E arity stage Γ ρ e .bot := by
  exact ⟨.bot _ _ _, by simp [covTObservationBudget]⟩

theorem approxTKStage_zero {E : ResolvedEnv} {arity : Nat} {Γ : LCtx}
    {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTKStage E arity 0 Γ ρ e c) : c = .bot :=
  (covTObservationBudget_zero_iff c).mp (Nat.eq_zero_of_le_zero h.2)

/-- Every actual finite observation supplies its own stage, constructively. -/
theorem approxTKStage_at_budget {E : ResolvedEnv} {arity : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTK E arity Γ ρ e c) :
    ApproxTKStage E arity (covTObservationBudget c) Γ ρ e c :=
  ⟨h, Nat.le_refl _⟩

theorem approxTK_iff_exists_stage {E : ResolvedEnv} {arity : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT} :
    ApproxTK E arity Γ ρ e c ↔ ∃ k, ApproxTKStage E arity k Γ ρ e c :=
  ⟨fun h => ⟨_, approxTKStage_at_budget h⟩, fun ⟨_, h⟩ => h.1⟩

/-- A common information budget does not identify the two approximation
derivations or make their semantic information compatible. -/
theorem approxTKStage_common {E : ResolvedEnv} {arity : Nat}
    {Γ : LCtx} {ρ : EnvT} {A t : Expr Nat} {a c : CptT}
    (hA : ApproxTK E arity Γ ρ A a) (ht : ApproxTK E arity Γ ρ t c) :
    ∃ k, ApproxTKStage E arity k Γ ρ A a ∧
      ApproxTKStage E arity k Γ ρ t c :=
  ⟨max (covTObservationBudget a) (covTObservationBudget c),
    ⟨hA, Nat.le_max_left _ _⟩, ⟨ht, Nat.le_max_right _ _⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_T_STAGE_ROOTS
#print axioms covTObservationBudget
#print axioms covTObservationBudget_zero_iff
#print axioms ApproxTKStage
#print axioms ApproxTKStage.forget
#print axioms ApproxTKStage.mono
#print axioms approxTKStage_bot
#print axioms approxTKStage_zero
#print axioms approxTKStage_at_budget
#print axioms approxTK_iff_exists_stage
#print axioms approxTKStage_common
-- END RCIC_NATIVE_TYPED_MODEL_COV_T_STAGE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit
