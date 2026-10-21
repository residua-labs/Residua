import rcic.RcicNativeTypedModelCovWConvCore

/-!
A concrete local-definition gap in the current observation grammar.

In the well-formed context `[let X : Sort 2 := Sort 1]`, native zetaLocal
converts `bvar 0` to `Sort 1`.  The value has a nonbottom, strictly typed sort
observation that the variable lacks at the bottom observation environment.

This refutes the displayed open-context CovWConvTypedInvariant for this pair.
It does not refute the closed-context CovWConvCodesDetermineTypes obligation.
The new grammar has no full environment-realization predicate yet; the
single-slot demand-realization fact below is stated explicitly and is not
claimed to constitute such a predicate.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovWAudit TypedModelCovTAudit TypedModelCovWIrrelAudit
open TypedModelCovWNativeAudit

def covWConvLocalType : Expr Nat := .sort levelTwo
def covWConvLocalValue : Expr Nat := .sort levelOne

def covWConvLocalCtx : LCtx :=
  [.letBinding covWConvLocalType covWConvLocalValue]

def covWConvLocalTypeCode : CptWConv :=
  .sort (LevelCode.ofLevel levelTwo)

def covWConvLocalDemand : CptWConv :=
  .sort (LevelCode.ofLevel levelOne)

def covWConvLocal_ctx_wf (n : Nat) :
    CtxWfT emptyEnv n covWConvLocalCtx :=
  .letBinding [] covWConvLocalType levelThree covWConvLocalValue
    .nil (.sort [] levelTwo) (.sort [] levelOne)

def covWConvLocal_type_typed (n : Nat) :
    HasTyT emptyEnv n covWConvLocalCtx covWConvLocalType
      (.sort levelThree) :=
  .sort covWConvLocalCtx levelTwo

def covWConvLocal_variable_typed (n : Nat) :
    HasTyT emptyEnv n covWConvLocalCtx (.bvar 0) covWConvLocalType :=
  .bvar covWConvLocalCtx 0 covWConvLocalType rfl

def covWConvLocal_value_typed (n : Nat) :
    HasTyT emptyEnv n covWConvLocalCtx covWConvLocalValue covWConvLocalType :=
  .sort covWConvLocalCtx levelOne

def covWConvLocal_native_conv (n : Nat) :
    ConvT emptyEnv n covWConvLocalCtx (.bvar 0)
      covWConvLocalValue covWConvLocalType :=
  .zetaLocal covWConvLocalCtx 0 covWConvLocalType covWConvLocalValue
    rfl rfl (covWConvLocal_value_typed n)

theorem covWConvLocal_native_step (n : Nat) :
    WhStepCK2 emptyEnv n covWConvLocalCtx (.bvar 0) covWConvLocalValue :=
  .ctx (.zetaLocal rfl)

theorem covWConvLocal_type_observed (n : Nat) :
    CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
      covWConvLocalType covWConvLocalTypeCode :=
  ⟨.sort levelTwo, rfl, .sort covWConvLocalCtx EnvWConvR.bot levelTwo⟩

theorem covWConvLocal_value_observed (n : Nat) :
    CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
      covWConvLocalValue covWConvLocalDemand :=
  ⟨.sort levelOne, rfl, .sort covWConvLocalCtx EnvWConvR.bot levelOne⟩

theorem covWConvLocal_demand_typed :
    CTySConv emptyEnv covWConvLocalDemand covWConvLocalTypeCode := by
  refine ⟨.sort levelOne, .sort levelTwo, rfl, rfl, ?_⟩
  refine .sortTy (.sort levelOne levelTwo (fun _ => rfl)) ?_
  change CTyS emptyEnv .sort .sort
  rw [CTyS]
  exact Or.inr .sort

theorem covWConvLocal_demand_nonbottom : covWConvLocalDemand ≠ .bot := by
  intro h
  cases h

/-- All observations demanded by this bottom slot are realized by its value. -/
theorem covWConvLocal_slot_demands_realized (n : Nat) :
    ∀ c, EnvWConvR.bot 0 c →
      ApproxTKWConv emptyEnv n [] EnvWConvR.bot covWConvLocalValue c := by
  intro c hc
  change c = .bot at hc
  cases hc
  exact .bot [] EnvWConvR.bot covWConvLocalValue

/--
The full current grammar cannot derive a sort-shaped observation for a
variable at the bottom environment.  Eta has a lambda-shaped result, and
emptyEnv has no legacy iota witness.
-/
theorem covWConv_bvar_bot_lacks_sort {n : Nat} {Γ : LCtx}
    (i : Nat) (u : Level) :
    ¬ CovWConvObservation emptyEnv n Γ EnvWConvR.bot (.bvar i)
      (.sort (LevelCode.ofLevel u)) := by
  rintro ⟨c, hc, ho⟩
  generalize heq : (Expr.bvar i : Expr Nat) = e at ho
  cases ho with
  | bot => cases hc
  | bvar h =>
      change _ = CptWConvR.bot at h
      cases h
      cases hc
  | sort => cases heq
  | const => cases heq
  | recursor => cases heq
  | pi => cases heq
  | lam => cases heq
  | app => cases heq
  | appSpine => cases heq
  | delta => cases heq
  | letE => cases heq
  | lit => cases heq
  | iota w hl hr h => cases w.hrec
  | recursorPropK w x hk h => cases w.hrec
  | eta he hD ht hn hb => cases hc

theorem covWConvLocal_variable_lacks_demand (n : Nat) :
    ¬ CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
      (.bvar 0) covWConvLocalDemand :=
  covWConv_bvar_bot_lacks_sort 0 levelOne

/-- A concrete failure of the currently defined typed invariant. -/
theorem covWConvLocal_not_typed_invariant (n : Nat) :
    ¬ CovWConvTypedInvariant emptyEnv n covWConvLocalCtx EnvWConvR.bot
      covWConvLocalType (.bvar 0) covWConvLocalValue := by
  intro h
  have he := h covWConvLocalTypeCode (covWConvLocal_type_observed n)
    covWConvLocalDemand covWConvLocal_demand_typed
  exact covWConvLocal_variable_lacks_demand n
    (he.mpr (covWConvLocal_value_observed n))

/-- The missing direction is observation expansion across local zeta. -/
theorem covWConvLocal_not_observation_expansion (n : Nat) :
    ¬ (∀ c, CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
        covWConvLocalValue c →
      CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
        (.bvar 0) c) := by
  intro h
  exact covWConvLocal_variable_lacks_demand n
    (h covWConvLocalDemand (covWConvLocal_value_observed n))

/--
All native well-formedness, common typing, conversion, type-observation, and
strict-demand premises are supplied.  The claim is about this open-context
cell in the present grammar, not about a closed completeness theorem.
-/
theorem covWConvLocal_cell_inhabited (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧
    Nonempty (CtxWfT emptyEnv n covWConvLocalCtx) ∧
    Nonempty (HasTyT emptyEnv n covWConvLocalCtx covWConvLocalType
      (.sort levelThree)) ∧
    Nonempty (HasTyT emptyEnv n covWConvLocalCtx (.bvar 0) covWConvLocalType) ∧
    Nonempty (HasTyT emptyEnv n covWConvLocalCtx covWConvLocalValue
      covWConvLocalType) ∧
    Nonempty (ConvT emptyEnv n covWConvLocalCtx (.bvar 0)
      covWConvLocalValue covWConvLocalType) ∧
    WhStepCK2 emptyEnv n covWConvLocalCtx (.bvar 0) covWConvLocalValue ∧
    CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
      covWConvLocalType covWConvLocalTypeCode ∧
    CTySConv emptyEnv covWConvLocalDemand covWConvLocalTypeCode ∧
    covWConvLocalDemand ≠ .bot ∧
    CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
      covWConvLocalValue covWConvLocalDemand ∧
    (¬ CovWConvObservation emptyEnv n covWConvLocalCtx EnvWConvR.bot
      (.bvar 0) covWConvLocalDemand) ∧
    ¬ CovWConvTypedInvariant emptyEnv n covWConvLocalCtx EnvWConvR.bot
      covWConvLocalType (.bvar 0) covWConvLocalValue := by
  exact ⟨⟨.empty⟩, ⟨covWConvLocal_ctx_wf n⟩,
    ⟨covWConvLocal_type_typed n⟩, ⟨covWConvLocal_variable_typed n⟩,
    ⟨covWConvLocal_value_typed n⟩, ⟨covWConvLocal_native_conv n⟩,
    covWConvLocal_native_step n, covWConvLocal_type_observed n,
    covWConvLocal_demand_typed, covWConvLocal_demand_nonbottom,
    covWConvLocal_value_observed n, covWConvLocal_variable_lacks_demand n,
    covWConvLocal_not_typed_invariant n⟩

#print axioms covWConvLocal_ctx_wf
#print axioms covWConvLocal_type_typed
#print axioms covWConvLocal_variable_typed
#print axioms covWConvLocal_value_typed
#print axioms covWConvLocal_native_conv
#print axioms covWConvLocal_native_step
#print axioms covWConvLocal_type_observed
#print axioms covWConvLocal_value_observed
#print axioms covWConvLocal_demand_typed
#print axioms covWConvLocal_demand_nonbottom
#print axioms covWConvLocal_slot_demands_realized
#print axioms covWConv_bvar_bot_lacks_sort
#print axioms covWConvLocal_variable_lacks_demand
#print axioms covWConvLocal_not_typed_invariant
#print axioms covWConvLocal_not_observation_expansion
#print axioms covWConvLocal_cell_inhabited

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
