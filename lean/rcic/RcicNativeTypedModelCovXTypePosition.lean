import rcic.RcicNativeTypedModelCovNormBoundary

/-!
# Measuring type-position readback observations without changing K

The auxiliary observation reads the normal reduct of a type position. It
does not add a constructor to `ApproxTK`, nor alter any native or independent
K guard. Reflection of this observation to the original source syntax is a
different property, and the actual typed Eq alias refutes that property.

The apart fixture measures the boundary of promoting this auxiliary type
observation into a term observation: its new `.prop` observation is exactly
readback to `Sort 0`. Native exclusion of that readback belongs to the
independent shape-disjointness lane and is not assumed here.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit PiModelDeltaIotaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open ReadbackCK2ModelObstructionAudit TypedModelKAudit TypedModelKControlAudit
open TypedModelKGuardAudit TypedModelKTypedBetaAudit TypedModelCovPropagationAudit
open TypedModelCovRelAudit TypedModelCovRelEscapeAudit
open TypedModelCovRelRealizationAudit TypedModelCovNormEscapeAudit

/-- Observe the readback of a type position, retaining the same native
context and valuation. This is an auxiliary typing observation. -/
def TypeReadbackObservationTK (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvT) (A : Expr Nat) (c : CptT) : Prop :=
  ∃ A₀, RedR (WhStepCK2 E n) Γ A A₀ ∧
    NormalR (WhStepCK2 E n) Γ A₀ ∧ ApproxTK E n Γ ρ A₀ c

/-- The exact stronger source-reflection input. The source remains `A`;
this is not silently identified with observing its reduct. -/
def TypePositionReadbackAtTK (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A : Expr Nat) : Prop :=
  ∀ (ρ : EnvT) (c : CptT), TypeReadbackObservationTK E n Γ ρ A c →
    ApproxTK E n Γ ρ A c

/-- At an already normal source the auxiliary observation is exact. -/
theorem typeReadbackObservationTK_iff_at_normal
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {A : Expr Nat} {c : CptT} (hA : NormalR (WhStepCK2 E n) Γ A) :
    TypeReadbackObservationTK E n Γ ρ A c ↔ ApproxTK E n Γ ρ A c := by
  constructor
  · rintro ⟨A₀, hr, _, ha⟩
    have he := redR_of_normal hA hr
    subst A₀
    exact ha
  · intro ha
    exact ⟨A, .refl _, hA, ha⟩

theorem typePositionReadbackAtTK_of_normal
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat}
    (hA : NormalR (WhStepCK2 E n) Γ A) :
    TypePositionReadbackAtTK E n Γ A :=
  fun _ _ h => (typeReadbackObservationTK_iff_at_normal hA).mp h

/-- A complete, non-bottom sort instance of the source-reflection port. -/
theorem typePositionReadbackAtTK_sort_control (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    TypePositionReadbackAtTK E n Γ (.sort .zero) ∧
    TypeReadbackObservationTK E n Γ ρ (.sort .zero) .prop ∧
    ApproxTK E n Γ ρ (.sort .zero) .prop ∧ (.prop : CptT) ≠ .bot := by
  have hm : ApproxTK E n Γ ρ (.sort .zero) .prop := by
    simpa only [sortCode_zero] using approxTK_sort_code E n Γ ρ .zero
  exact ⟨typePositionReadbackAtTK_of_normal (normalR_sortCK2 Γ .zero),
    ⟨.sort .zero, .refl _, normalR_sortCK2 Γ .zero, hm⟩, hm,
    fun h => CptT.noConfusion h⟩

/-- The alias has a non-bottom type-position observation at its actual
readback, for every valuation. No raw expansion law is used. -/
theorem typeReadbackObservationTK_eqGapAlias (n : Nat) (ρ : EnvT)
    (A B : Expr Nat) :
    TypeReadbackObservationTK eqEnvT n eqGapCtx ρ (eqGapDirectAlias A B) .prop := by
  refine ⟨.sort .zero, eqGapAlias_type_read n A B,
    normalR_sortCK2 eqGapCtx .zero, ?_⟩
  simpa only [sortCode_zero] using approxTK_sort_code eqEnvT n eqGapCtx ρ .zero

/-- Raw source reflection is false even though its readback observation
is positively inhabited. -/
theorem not_typePositionReadbackAtTK_eqGapAlias (n : Nat) (A B : Expr Nat) :
    ¬ TypePositionReadbackAtTK eqEnvT n eqGapCtx (eqGapDirectAlias A B) := by
  intro h
  exact CptT.noConfusion (approxTK_eqGapDirectAlias_bot A B
    (h EnvT.bot .prop (typeReadbackObservationTK_eqGapAlias n EnvT.bot A B)))

/-- The source-reflection refutation retains admission, native type
typing, the coherent covariant environment, and its positive readback. -/
theorem typePositionReadback_alias_native_control (C : CovTyping eqEnvT) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B)
        (.sort (.succ .zero))) ∧
      TypeReadbackObservationTK eqEnvT n eqGapCtx EnvT.bot
        (eqGapDirectAlias A B) .prop ∧
      (¬ TypePositionReadbackAtTK eqEnvT n eqGapCtx (eqGapDirectAlias A B)) ∧
      (.prop : CptT) ≠ .bot := by
  obtain ⟨A, B, ht, _⟩ := covNormAliasIdentity_native n
  exact ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, envTypedCovAtP_eqGap_bot C n,
    A, B, ht, typeReadbackObservationTK_eqGapAlias n EnvT.bot A B,
    not_typePositionReadbackAtTK_eqGapAlias n A B,
    fun h => CptT.noConfusion h⟩

/-- The auxiliary type observation coexists with the original model's
apart exclusion and its unchanged native-plus-DI guard exclusion. The
canonical witness is the actual apart call; no impossible witness is used. -/
theorem typeReadback_alias_and_apart_guard (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    TypeReadbackObservationTK eqEnvT n eqGapCtx ρ (eqGapDirectAlias A B) .prop ∧
    (¬ ApproxTK eqEnvT n apartCtx ρ apartRec .prop) ∧
    ¬ KIndexGuardAt eqEnvT n apartCtx
      (eqConvW (fun _ _ h => h) (.sort .zero) idPiProp apartRight apartMot
        (.sort .zero)) := by
  refine ⟨typeReadbackObservationTK_eqGapAlias n ρ A B,
    not_approxTK_apartRec_prop, ?_⟩
  exact not_kIndexGuardAt_apart (x := .bvar 0) rfl rfl
    (Or.inl ⟨rfl, rfl, rfl⟩)

/-- Exact measurement if the auxiliary observation is also used at the
apart call: observing `.prop` is equivalent to native readback to `Sort 0`.
This equivalence supplies neither side and does not assert native separation. -/
theorem typeReadbackObservationTK_apart_prop_iff (n : Nat) (ρ : EnvT) :
    TypeReadbackObservationTK eqEnvT n apartCtx ρ apartRec .prop ↔
      RedR (WhStepCK2 eqEnvT n) apartCtx apartRec (.sort .zero) := by
  constructor
  · rintro ⟨A₀, hr, _, ha⟩
    rcases redR_whStepCK2_apartRec_cases hr with he | he
    · subst A₀
      exact (not_approxTK_apartRec_prop ha).elim
    · exact he ▸ hr
  · intro hr
    refine ⟨.sort .zero, hr, normalR_sortCK2 apartCtx .zero, ?_⟩
    simpa only [sortCode_zero] using approxTK_sort_code eqEnvT n apartCtx ρ .zero

/-- The full auxiliary-observation exclusion needs exactly the independent
native readback exclusion displayed here. This is a conditional consumer. -/
theorem typeReadbackObservationTK_apart_bot_of_no_sort (n : Nat) (ρ : EnvT)
    (hno : ¬ RedR (WhStepCK2 eqEnvT n) apartCtx apartRec (.sort .zero))
    {c : CptT} (h : TypeReadbackObservationTK eqEnvT n apartCtx ρ apartRec c) :
    c = .bot := by
  obtain ⟨A₀, hr, _, ha⟩ := h
  rcases redR_whStepCK2_apartRec_cases hr with he | he
  · subst A₀
    exact approxTK_apartRec_bot ha
  · exact (hno (he ▸ hr)).elim

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_TYPE_POSITION_ROOTS
#print axioms TypeReadbackObservationTK
#print axioms TypePositionReadbackAtTK
#print axioms typeReadbackObservationTK_iff_at_normal
#print axioms typePositionReadbackAtTK_of_normal
#print axioms typePositionReadbackAtTK_sort_control
#print axioms typeReadbackObservationTK_eqGapAlias
#print axioms not_typePositionReadbackAtTK_eqGapAlias
#print axioms typePositionReadback_alias_native_control
#print axioms typeReadback_alias_and_apart_guard
#print axioms typeReadbackObservationTK_apart_prop_iff
#print axioms typeReadbackObservationTK_apart_bot_of_no_sort
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_TYPE_POSITION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXTypePositionAudit
