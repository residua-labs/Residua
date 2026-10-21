import rcic.RcicNativeTypedModelCovWIrrelAligned

/-!
# Typed observation invariance and concrete failure evidence

The invariant compares the original erased `CptT` observations at each
shared observed type code. Universe provenance is not an observable.
The raw and guarded relations refer to the unchanged landed grammars.

The failure records require actual native typing and conversion, a
realized closed valuation, an explicitly erased finite typed valuation,
and a nonbottom observation supplied on only one side. No record assigns
a status to an unproved matrix cell. The equivalence lemmas below compose
observation equalities only; they do not assert term-context congruence.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelAudit.TypingFin TypedModelCovWAudit TypedModelCovTAudit
open TypedModelCovWEtaAudit TypedModelCovWIrrelAudit

def CovWMatrixTypedInvariant (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (A left right : Expr Nat) : Prop :=
  ∀ a c, CovWIrrelObservation E n Γ ρ A a → CTyS E c a →
    (CovWIrrelObservation E n Γ ρ left c ↔
      CovWIrrelObservation E n Γ ρ right c)

def CovWMatrixRawTypedInvariant (E : ResolvedEnv) (n : Nat)
    (ρ : EnvWIrrel) (A left right : Expr Nat) : Prop :=
  ∀ a c, CovWIrrelRawObservation E n ρ A a → CTyS E c a →
    (CovWIrrelRawObservation E n ρ left c ↔
      CovWIrrelRawObservation E n ρ right c)

/-- A filtered observation is useful independently of the shared-code relation. -/
def CovWMatrixTypedObservation (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (e A : Expr Nat) (c : CptT) : Prop :=
  ∃ a, CovWIrrelObservation E n Γ ρ A a ∧ CTyS E c a ∧
    CovWIrrelObservation E n Γ ρ e c

theorem covWMatrix_invariant_iff_typed_observations {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel} {A left right : Expr Nat} :
    CovWMatrixTypedInvariant E n Γ ρ A left right ↔
      ∀ c, CovWMatrixTypedObservation E n Γ ρ left A c ↔
        CovWMatrixTypedObservation E n Γ ρ right A c := by
  constructor
  · intro h c
    constructor
    · rintro ⟨a, ha, hc, he⟩
      exact ⟨a, ha, hc, (h a c ha hc).mp he⟩
    · rintro ⟨a, ha, hc, he⟩
      exact ⟨a, ha, hc, (h a c ha hc).mpr he⟩
  · intro h a c ha hc
    constructor
    · intro he
      obtain ⟨_, _, _, hr⟩ := (h c).mp ⟨a, ha, hc, he⟩
      exact hr
    · intro he
      obtain ⟨_, _, _, hl⟩ := (h c).mpr ⟨a, ha, hc, he⟩
      exact hl

theorem covWMatrix_invariant_of_observation_equality {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {ρ : EnvWIrrel} {A left right : Expr Nat}
    (h : ∀ c, CovWIrrelObservation E n Γ ρ left c ↔
      CovWIrrelObservation E n Γ ρ right c) :
    CovWMatrixTypedInvariant E n Γ ρ A left right :=
  fun _ c _ _ => h c

theorem covWMatrix_invariant_refl (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (A e : Expr Nat) :
    CovWMatrixTypedInvariant E n Γ ρ A e e :=
  fun _ _ _ _ => Iff.rfl

theorem covWMatrix_invariant_symm {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {A left right : Expr Nat}
    (h : CovWMatrixTypedInvariant E n Γ ρ A left right) :
    CovWMatrixTypedInvariant E n Γ ρ A right left :=
  fun a c ha hc => (h a c ha hc).symm

theorem covWMatrix_invariant_trans {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ρ : EnvWIrrel} {A left middle right : Expr Nat}
    (h₁ : CovWMatrixTypedInvariant E n Γ ρ A left middle)
    (h₂ : CovWMatrixTypedInvariant E n Γ ρ A middle right) :
    CovWMatrixTypedInvariant E n Γ ρ A left right :=
  fun a c ha hc => (h₁ a c ha hc).trans (h₂ a c ha hc)

structure CovWMatrixNativePair (E : ResolvedEnv) (n : Nat)
    (left right A : Expr Nat) (u : Level) : Prop where
  envWf : Nonempty (EnvWfT E)
  ctxWf : Nonempty (CtxWfT E n [])
  leftTy : Nonempty (HasTyT E n [] left A)
  rightTy : Nonempty (HasTyT E n [] right A)
  typeTy : Nonempty (HasTyT E n [] A (.sort u))
  conversion : Nonempty (ConvT E n [] left right A)

structure CovWMatrixClosedFailure (E : ResolvedEnv) (n stage : Nat)
    (left right A : Expr Nat) (u : Level) (c a : CptT) : Prop where
  native : CovWMatrixNativePair E n left right A u
  realized : CovWIrrelRealized E n stage [] EnvWIrrel.bot SubstT.id
  erasedValuation : EnvTypedFinAtT
    (⟨ApproxTKWEta E n []⟩ : CtxModelT E) [] (covWIrrelEnvErase EnvWIrrel.bot)
  erasedCoherence : CtxEnvM
    (⟨ApproxTKWEta E n []⟩ : CtxModelT E) [] (covWIrrelEnvErase EnvWIrrel.bot)
  typeObserved : CovWIrrelObservation E n [] EnvWIrrel.bot A a
  demand : CTyS E c a
  nonbottom : c ≠ .bot
  rightObserved : CovWIrrelObservation E n [] EnvWIrrel.bot right c
  leftAbsent : ¬ CovWIrrelObservation E n [] EnvWIrrel.bot left c

structure CovWMatrixRawClosedFailure (E : ResolvedEnv) (n stage : Nat)
    (left right A : Expr Nat) (u : Level) (c a : CptT) : Prop where
  native : CovWMatrixNativePair E n left right A u
  typedSubst : TypedSubstT E n [] SubstT.id []
  realized : ∀ i d, EnvWIrrel.bot i d →
    ApproxTWIrrel E n EnvWIrrel.bot (SubstT.id i) d ∧
      covTObservationBudget (covWIrrelErase d) ≤ stage
  erasedValuation : EnvTypedFinAtT
    (⟨ApproxTW E⟩ : CtxModelT E) [] (covWIrrelEnvErase EnvWIrrel.bot)
  erasedCoherence : CtxEnvM
    (⟨ApproxTW E⟩ : CtxModelT E) [] (covWIrrelEnvErase EnvWIrrel.bot)
  typeObserved : CovWIrrelRawObservation E n EnvWIrrel.bot A a
  demand : CTyS E c a
  nonbottom : c ≠ .bot
  rightObserved : CovWIrrelRawObservation E n EnvWIrrel.bot right c
  leftAbsent : ¬ CovWIrrelRawObservation E n EnvWIrrel.bot left c

theorem covWMatrix_closedFailure_refutes {E : ResolvedEnv} {n stage : Nat}
    {left right A : Expr Nat} {u : Level} {c a : CptT}
    (h : CovWMatrixClosedFailure E n stage left right A u c a) :
    ¬ CovWMatrixTypedInvariant E n [] EnvWIrrel.bot A left right := by
  intro hi
  exact h.leftAbsent ((hi a c h.typeObserved h.demand).mpr h.rightObserved)

theorem covWMatrix_rawClosedFailure_refutes {E : ResolvedEnv} {n stage : Nat}
    {left right A : Expr Nat} {u : Level} {c a : CptT}
    (h : CovWMatrixRawClosedFailure E n stage left right A u c a) :
    ¬ CovWMatrixRawTypedInvariant E n EnvWIrrel.bot A left right := by
  intro hi
  exact h.leftAbsent ((hi a c h.typeObserved h.demand).mpr h.rightObserved)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_CORE_ROOTS
#print axioms CovWMatrixTypedInvariant
#print axioms CovWMatrixRawTypedInvariant
#print axioms CovWMatrixTypedObservation
#print axioms covWMatrix_invariant_iff_typed_observations
#print axioms covWMatrix_invariant_of_observation_equality
#print axioms covWMatrix_invariant_refl
#print axioms covWMatrix_invariant_symm
#print axioms covWMatrix_invariant_trans
#print axioms CovWMatrixNativePair
#print axioms CovWMatrixClosedFailure
#print axioms CovWMatrixRawClosedFailure
#print axioms covWMatrix_closedFailure_refutes
#print axioms covWMatrix_rawClosedFailure_refutes
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_CORE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit
