import rcic.RcicNativeTypedModelCovWRigidCore

/-! Local definitions determine the variable's entire observation set.
No valuation-realization or closing-substitution hypothesis is used. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovWNativeAudit TypedModelCovWConvAudit

/-- The recursive head rule admits every observation of the lifted value. -/
theorem covWRigid_zetaLocal_expand {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {i : Nat} {v : Expr Nat} {c : CptWConvR}
    (hv : lookupValue Γ i = some v)
    (h : ApproxTKWRigid E n Γ ρ v c) :
    ApproxTKWRigid E n Γ ρ (.bvar i) c := .zetaLocal hv h

/-- No other nonbottom observation constructor bypasses local resolution. -/
theorem covWRigid_zetaLocal_contract {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {i : Nat} {v : Expr Nat} {c : CptWConvR}
    (hv : lookupValue Γ i = some v)
    (h : ApproxTKWRigid E n Γ ρ (.bvar i) c) :
    ApproxTKWRigid E n Γ ρ v c := by
  generalize hs : (Expr.bvar i : Expr Nat) = e at h
  cases h with
  | bot => exact .bot _ _ _
  | bvar hn hρ =>
      cases hs
      rw [hv] at hn
      cases hn
  | zetaLocal hv' h =>
      cases hs
      have he := Option.some.inj (hv.symm.trans hv')
      cases he
      exact h
  | sort => cases hs
  | const => cases hs
  | rigidRecursor => cases hs
  | recursor => cases hs
  | pi => cases hs
  | lam => cases hs
  | app => cases hs
  | appSpine => cases hs
  | delta => cases hs
  | letE => cases hs
  | lit => cases hs
  | iota w hl hr ho =>
      simp only [iotaLhsOf, recCall_eq_app] at hs
      cases hs
  | recursorPropK w x hk ho =>
      simp only [recCall_eq_app] at hs
      cases hs
  | eta hh he hd ht hn hb =>
      cases hs
      have hn := hh i rfl
      rw [hv] at hn
      cases hn

theorem covWRigid_zetaLocal_raw_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} {i : Nat} {v : Expr Nat} {c : CptWConvR}
    (hv : lookupValue Γ i = some v) :
    ApproxTKWRigid E n Γ ρ (.bvar i) c ↔ ApproxTKWRigid E n Γ ρ v c :=
  ⟨covWRigid_zetaLocal_contract hv, covWRigid_zetaLocal_expand hv⟩

theorem covWRigid_zetaLocal_observations {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ρ : EnvWConvR) {i : Nat} {v : Expr Nat}
    (hv : lookupValue Γ i = some v) (c : CptWConv) :
    CovWRigidObservation E n Γ ρ (.bvar i) c ↔
      CovWRigidObservation E n Γ ρ v c := by
  constructor
  · rintro ⟨d, hd, ho⟩
    exact ⟨d, hd, covWRigid_zetaLocal_contract hv ho⟩
  · rintro ⟨d, hd, ho⟩
    exact ⟨d, hd, covWRigid_zetaLocal_expand hv ho⟩

/-- A general head supplier, at every observed type and every strict demand. -/
theorem covWRigid_zetaLocal_typed_invariant {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (ρ : EnvWConvR) (A : Expr Nat) {i : Nat} {v : Expr Nat}
    (hv : lookupValue Γ i = some v) :
    CovWRigidTypedInvariant E n Γ ρ A (.bvar i) v := by
  intro a ha c hc
  exact covWRigid_zetaLocal_observations ρ hv c

/-- The native conversion uses exactly the native local-zeta premises. -/
def covWRigid_zetaLocal_native {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat} (hv : lookupValue Γ i = some v)
    (hA : lookupType Γ i = some A) (ht : HasTyT E n Γ v A) :
    ConvT E n Γ (.bvar i) v A := .zetaLocal Γ i A v hv hA ht

/-- The prior fully inhabited LocalRealized source now has its strict demand,
for an arbitrary valuation. No closing substitution is used to obtain it. -/
theorem covWRigidLocal_variable_observed (n : Nat) (ρ : EnvWConvR) :
    CovWRigidObservation emptyEnv n covWConvLocalCtx ρ (.bvar 0)
      covWConvLocalDemand := by
  exact covWRigid_observation_of
    (.zetaLocal (show lookupValue covWConvLocalCtx 0 = some covWConvLocalValue from rfl)
      (.sort _ _ _))

theorem covWRigidLocal_all_observations (n : Nat) (ρ : EnvWConvR) (c : CptWConv) :
    CovWRigidObservation emptyEnv n covWConvLocalCtx ρ (.bvar 0) c ↔
      CovWRigidObservation emptyEnv n covWConvLocalCtx ρ covWConvLocalValue c :=
  covWRigid_zetaLocal_observations (E := emptyEnv) (n := n) ρ
    (show lookupValue covWConvLocalCtx 0 = some covWConvLocalValue from rfl) c

theorem covWRigidLocal_cell_inhabited (n : Nat) (ρ : EnvWConvR) :
    Nonempty (EnvWfT emptyEnv) ∧
    Nonempty (CtxWfT emptyEnv n covWConvLocalCtx) ∧
    Nonempty (HasTyT emptyEnv n covWConvLocalCtx (.bvar 0) covWConvLocalType) ∧
    Nonempty (HasTyT emptyEnv n covWConvLocalCtx covWConvLocalValue covWConvLocalType) ∧
    Nonempty (ConvT emptyEnv n covWConvLocalCtx (.bvar 0)
      covWConvLocalValue covWConvLocalType) ∧
    CovWRigidObservation emptyEnv n covWConvLocalCtx ρ covWConvLocalType
      covWConvLocalTypeCode ∧
    CTySConv emptyEnv covWConvLocalDemand covWConvLocalTypeCode ∧
    covWConvLocalDemand ≠ .bot ∧
    CovWRigidObservation emptyEnv n covWConvLocalCtx ρ (.bvar 0)
      covWConvLocalDemand ∧
    CovWRigidObservation emptyEnv n covWConvLocalCtx ρ covWConvLocalValue
      covWConvLocalDemand ∧
    CovWRigidTypedInvariant emptyEnv n covWConvLocalCtx ρ covWConvLocalType
      (.bvar 0) covWConvLocalValue :=
  ⟨⟨.empty⟩, ⟨covWConvLocal_ctx_wf n⟩,
    ⟨covWConvLocal_variable_typed n⟩, ⟨covWConvLocal_value_typed n⟩,
    ⟨covWConvLocal_native_conv n⟩,
    covWRigid_observation_of (.sort _ _ _), covWConvLocal_demand_typed,
    covWConvLocal_demand_nonbottom, covWRigidLocal_variable_observed n ρ,
    covWRigid_observation_of (.sort _ _ _), covWRigid_zetaLocal_typed_invariant ρ _ rfl⟩

/-- In a well-formed context the resolved value was typed in a strictly
shorter tail. The observation rule uses its native lifted lookup value. -/
theorem covWRigid_local_value_from_earlier_tail {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {i : Nat} {v : Expr Nat}
    (hv : lookupValue Γ i = some v) :
    ∃ A v₀, Γ.get? i = some (.letBinding A v₀) ∧ v = lift 0 (i + 1) v₀ ∧
      Nonempty (HasTyT E n (Γ.drop (i + 1)) v₀ A) ∧
      (Γ.drop (i + 1)).length < Γ.length := by
  obtain ⟨A, v₀, hg, he⟩ := lookupValue_inv hv
  refine ⟨A, v₀, hg, he, ⟨ctxWfTLookupValueAtDrop hΓ i hg⟩, ?_⟩
  cases Γ with
  | nil => cases hg
  | cons d Γ =>
    simp only [List.length_drop, List.length_cons]
    omega

end Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

-- BEGIN COVWRIGID GENERATED MISSING AXIOM ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_expand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_contract
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_raw_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_typed_invariant
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_zetaLocal_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidLocal_variable_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidLocal_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigidLocal_cell_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_local_value_from_earlier_tail
-- END COVWRIGID GENERATED MISSING AXIOM ROOTS
