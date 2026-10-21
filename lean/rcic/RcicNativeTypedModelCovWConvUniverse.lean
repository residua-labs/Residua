import rcic.RcicNativeTypedModelCovWConvForget

/-! Universe observations in the full guarded grammar.  The two Pi fixtures
have native typing at Sort 3 and a typed separating observation.  Completeness
below is restricted to bare sort rows; no general completeness is asserted. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open TypedModelAudit TypedModelCovTAudit TypedModelCovWIrrelAudit
open TypedModelCovWNativeAudit

/-- A sort-shaped public observation retains exactly the source level class.
The eta constructor has a lambda-shaped code, so it cannot enter this row. -/
theorem covWConv_sort_observation_exact {n : Nat} {Γ : LCtx}
    {ρ : EnvWConvR} (u v : Level) :
    CovWConvObservation emptyEnv n Γ ρ (.sort u)
      (.sort (LevelCode.ofLevel v)) ↔ eqN u v := by
  constructor
  · rintro ⟨c, hc, ho⟩
    generalize heq : (Expr.sort u : Expr Nat) = e at ho
    cases ho with
    | bot => cases hc
    | bvar => cases heq
    | sort =>
      cases heq
      exact (sort_code_exact _ _).mp hc
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
    | eta he hD ht hn hb =>
      cases heq
      cases hc
  · intro h
    exact ⟨.sort u, (sort_code_exact u v).mpr h, .sort Γ ρ u⟩

/-- Equality of all full observations implies native conversion on sort rows. -/
def covWConv_sort_complete {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {u v : Level}
    (h : ∀ c, CovWConvObservation emptyEnv n Γ ρ (.sort u) c ↔
      CovWConvObservation emptyEnv n Γ ρ (.sort v) c) :
    ConvT emptyEnv n Γ (.sort u) (.sort v) (.sort (.succ u)) :=
  .sorts Γ u v ((covWConv_sort_observation_exact u v).mp
    ((h (.sort (LevelCode.ofLevel v))).mpr ⟨.sort v, rfl, .sort Γ ρ v⟩))

def universePiARaw : CptWConvR :=
  .pi (.sort levelOne) [([], .sort levelTwo)]

def universePiBRaw : CptWConvR :=
  .pi (.sort levelTwo) [([], .sort levelTwo)]

@[simp] theorem universePiARaw_code : covWConvCode universePiARaw = universePiACode := rfl
@[simp] theorem universePiBRaw_code : covWConvCode universePiBRaw = universePiBCode := rfl

private theorem universe_pi_const {E : ResolvedEnv} {a b : CptWConvR}
    {u v l : Level} (ha : UniverseWConv E a u) (hb : UniverseWConv E b v)
    (hl : eqN (.imax u v) l) :
    UniverseWConv E (.pi a [([], b)]) l := by
  refine .pi ha ?_ ?_ hl
  · intro s hs c hc
    obtain rfl := List.mem_singleton.mp hs
    cases hc
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact hb

theorem covWConv_universeA_formation (E : ResolvedEnv) :
    UniverseWConv E universePiARaw levelThree := by
  exact universe_pi_const
    (.sort levelOne levelTwo (fun _ => rfl))
    (.sort levelTwo levelThree (fun _ => rfl))
    ((LevelCode.ofLevel_eq_iff (.imax levelTwo levelThree) levelThree).mp
      imax_two_three)

theorem covWConv_universeB_formation (E : ResolvedEnv) :
    UniverseWConv E universePiBRaw levelThree := by
  exact universe_pi_const
    (.sort levelTwo levelThree (fun _ => rfl))
    (.sort levelTwo levelThree (fun _ => rfl))
    ((LevelCode.ofLevel_eq_iff (.imax levelThree levelThree) levelThree).mp
      imax_three_three)

private theorem coarse_universe_pi_typed (E : ResolvedEnv) :
    CTyS E (.pi .sort [([], .sort)]) .sort := by
  rw [CTyS]
  refine Or.inr (.pi .sort ?_)
  intro s hs
  obtain rfl := List.mem_singleton.mp hs
  exact .sort

theorem covWConv_universeA_raw_typed (E : ResolvedEnv) :
    CTyWConvR E universePiARaw (.sort levelThree) := by
  refine .sortTy (covWConv_universeA_formation E) ?_
  exact coarse_universe_pi_typed E

theorem covWConv_universeB_raw_typed (E : ResolvedEnv) :
    CTyWConvR E universePiBRaw (.sort levelThree) := by
  refine .sortTy (covWConv_universeB_formation E) ?_
  exact coarse_universe_pi_typed E

theorem covWConv_universeA_code_typed (E : ResolvedEnv) :
    CTySConv E universePiACode (.sort (LevelCode.ofLevel levelThree)) :=
  ⟨universePiARaw, .sort levelThree, rfl, rfl, covWConv_universeA_raw_typed E⟩

theorem covWConv_universeB_code_typed (E : ResolvedEnv) :
    CTySConv E universePiBCode (.sort (LevelCode.ofLevel levelThree)) :=
  ⟨universePiBRaw, .sort levelThree, rfl, rfl, covWConv_universeB_raw_typed E⟩

private theorem pi_sort_raw_observation (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWConvR) (u v : Level) :
    ApproxTKWConv E n Γ ρ (.pi (.sort u) (.sort v))
      (.pi (.sort u) [([], .sort v)]) := by
  refine .pi (.sort Γ ρ u) ?_ ?_
  · intro s hs c hc
    obtain rfl := List.mem_singleton.mp hs
    cases hc
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .sort _ _ v

theorem covWConv_universeA_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWConvR) :
    CovWConvObservation E n Γ ρ universePiA universePiACode :=
  ⟨universePiARaw, rfl, pi_sort_raw_observation E n Γ ρ levelOne levelTwo⟩

theorem covWConv_universeB_observed (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWConvR) :
    CovWConvObservation E n Γ ρ universePiB universePiBCode :=
  ⟨universePiBRaw, rfl, pi_sort_raw_observation E n Γ ρ levelTwo levelTwo⟩

/-- This excludes the separating code from B in the full grammar, rather than
merely comparing the two chosen codes from the structural fragment. -/
theorem covWConv_universeB_lacks_A {n : Nat} {Γ : LCtx} {ρ : EnvWConvR} :
    ¬ CovWConvObservation emptyEnv n Γ ρ universePiB universePiACode := by
  rintro ⟨c, hc, ho⟩
  generalize heq : (universePiB : Expr Nat) = e at ho
  cases ho with
  | bot => cases hc
  | bvar => cases heq
  | sort => cases heq
  | const => cases heq
  | recursor => cases heq
  | pi hA ht hb =>
    cases heq
    have hd := (CptWConv.pi.inj hc).1
    have he : eqN levelTwo levelOne :=
      (covWConv_sort_observation_exact levelTwo levelOne).mp ⟨_, hd, hA⟩
    exact levelOne_code_ne_levelTwo
      ((LevelCode.ofLevel_eq_iff levelTwo levelOne).mpr he).symm
  | lam => cases heq
  | app => cases heq
  | appSpine => cases heq
  | delta => cases heq
  | letE => cases heq
  | lit => cases heq
  | iota w hl hr h => cases w.hrec
  | recursorPropK w x hk h => cases w.hrec
  | eta he hD ht hn hb =>
    cases heq
    cases hc

theorem covWConv_universe_observations_differ (n : Nat) :
    ¬ (∀ c, CovWConvObservation emptyEnv n [] EnvWConvR.bot universePiA c ↔
      CovWConvObservation emptyEnv n [] EnvWConvR.bot universePiB c) := by
  intro h
  exact covWConv_universeB_lacks_A
    ((h universePiACode).mp (covWConv_universeA_observed emptyEnv n [] EnvWConvR.bot))

/-- These native derivations reuse the landed common-universe fixture. -/
def covWConv_universeA_native_typed (n : Nat) (Γ : LCtx) :
    HasTyT emptyEnv n Γ universePiA (.sort levelThree) :=
  covWNativeUniverseA_ty n Γ

def covWConv_universeB_native_typed (n : Nat) (Γ : LCtx) :
    HasTyT emptyEnv n Γ universePiB (.sort levelThree) :=
  covWNativeUniverseB_ty n Γ

theorem covWConv_universe_native_not_conv (n : Nat) (u : Level) :
    ¬ Nonempty (ConvT emptyEnv n [] universePiA universePiB (.sort u)) :=
  covWNativeUniverse_not_conv n u

/-- An inhabited, typed separator at the common universe, in the full model. -/
theorem covWConv_universe_typed_separator (n : Nat) :
    Nonempty (HasTyT emptyEnv n [] universePiA (.sort levelThree)) ∧
    Nonempty (HasTyT emptyEnv n [] universePiB (.sort levelThree)) ∧
    ∃ c, CTySConv emptyEnv c (.sort (LevelCode.ofLevel levelThree)) ∧
      CovWConvObservation emptyEnv n [] EnvWConvR.bot universePiA c ∧
      ¬ CovWConvObservation emptyEnv n [] EnvWConvR.bot universePiB c :=
  ⟨⟨covWConv_universeA_native_typed n []⟩,
    ⟨covWConv_universeB_native_typed n []⟩,
    universePiACode, covWConv_universeA_code_typed emptyEnv,
    covWConv_universeA_observed emptyEnv n [] EnvWConvR.bot,
    covWConv_universeB_lacks_A⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_UNIVERSE_ROOTS
#print axioms covWConv_sort_observation_exact
#print axioms covWConv_sort_complete
#print axioms covWConv_universeA_formation
#print axioms covWConv_universeB_formation
#print axioms covWConv_universeA_code_typed
#print axioms covWConv_universeB_code_typed
#print axioms covWConv_universeA_observed
#print axioms covWConv_universeB_lacks_A
#print axioms covWConv_universe_observations_differ
#print axioms covWConv_universe_native_not_conv
#print axioms covWConv_universe_typed_separator
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_UNIVERSE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
