import rcic.RcicNativeReadbackCK2Inputs
import rcic.RcicNativeReadbackCK2
import rcic.RcicNativeReadbackCK2Index

/-!
# The original Eq gap at every related substitution

The full local `FundConvAt` is reduced to the exact remaining constructor
arity obligation.  Non-constructor majors compute by the repaired K rule.
An Eq.refl major with exactly two arguments computes by existing iota,
without any syntactic agreement between its parameters and the recursor's.

The converse uses inversion of the complete candidate grammars.  It does
not infer native nonconvertibility from distinct syntax, and it does not
assume that a typed constructor spine is saturated.  Every quantified
port retains the original related-substitution package and native context.
Composition only; `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.PiProbeRelIotaAudit

variable {n : Nat} {Γ Δ : LCtx} {R : Readback}

/-- The exact actual index after substituting the original gap. -/
def gapBetaIndex (A a : Expr Nat) : Expr Nat :=
  .app (.lam A (.bvar 0)) a

/-- A constant-minor Eq call, with its arbitrary substituted proof major. -/
def gapCall (A a mot b x : Expr Nat) : Expr Nat :=
  recCall (.const 65 [.succ (.succ .zero)]) [A, a, mot, .sort .zero, b] x

/-- Simultaneous substitution leaves precisely this recursor shape. -/
theorem substT_eqGapRedex (σ : SubstT) :
    substT σ eqGapRedex =
      gapCall (σ 2) (σ 1) (substT σ eqGapMot)
        (gapBetaIndex (σ 2) (σ 1)) (σ 0) := rfl

/-- Native typing of the substituted identity application. -/
def gapBetaIndexTy {A a : Expr Nat}
    (hA : HasTyT eqEnvT n Γ A (.sort (.succ .zero)))
    (ha : HasTyT eqEnvT n Γ a A) :
    HasTyT eqEnvT n Γ (gapBetaIndex A a) A := by
  have h := HasTyT.app Γ (.lam A (.bvar 0)) a A (lift 0 1 A)
    (.lam Γ A (.succ .zero) (.bvar 0) (lift 0 1 A) hA
      (.bvar (.assumption A :: Γ) 0 (lift 0 1 A) rfl)) ha
  simpa only [instantiate0, instantiate_lift_id] using h

/-- The native beta certificate is uniform in the substituted type and term. -/
def gapBetaIndexConv {A a : Expr Nat}
    (hA : HasTyT eqEnvT n Γ A (.sort (.succ .zero)))
    (ha : HasTyT eqEnvT n Γ a A) :
    ConvT eqEnvT n Γ (gapBetaIndex A a) a A := by
  have h := ConvT.beta Γ A (.bvar 0) a (lift 0 1 A) (.succ .zero) hA
    (.bvar (.assumption A :: Γ) 0 (lift 0 1 A) rfl) ha
  simpa only [instantiate0, instantiate_lift_id] using h

/-- The right typed-substitution component supplies exactly the native K inputs. -/
theorem eqGap_typedSubst_data {σ : SubstT}
    (hT : TypedSubstT eqEnvT n Δ σ eqGapCtx) :
    Nonempty (HasTyT eqEnvT n Δ (σ 2) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT eqEnvT n Δ (σ 1) (σ 2)) ∧
    Nonempty (HasTyT eqEnvT n Δ (σ 0)
      (foldApps (.const 63 []) [σ 2, σ 1, gapBetaIndex (σ 2) (σ 1)])) :=
  ⟨hT.1 2 _ rfl, hT.1 1 _ rfl, hT.1 0 _ rfl⟩

/-- Every non-constructor substituted proof computes in candidate (a). -/
theorem redR_eqGap_subst_nonCtor_native {σ : SubstT}
    (hT : TypedSubstT eqEnvT n Δ σ eqGapCtx)
    (hnc : ¬ IsCtorSpine eqEnvT (σ 0)) :
    RedR (WhStepCK2 eqEnvT n) Δ (substT σ eqGapRedex) (.sort .zero) := by
  obtain ⟨⟨hA⟩, ⟨ha⟩, ⟨hx⟩⟩ := eqGap_typedSubst_data hT
  rw [substT_eqGapRedex]
  exact .step (.native (kNativeHead_eq_of_indexConv (fun _ _ h => h)
    (substT σ eqGapMot) (.sort .zero) hA ha (gapBetaIndexTy hA ha) hx
    (gapBetaIndexConv hA ha) hnc)) (.refl _)

/-- Candidate (b) handles every non-constructor major by actual-index beta then K.
The syntactically-agreeing branch is included explicitly, so no occurs-check
or classical case split is needed. -/
theorem redR_gapCall_nonCtor_index (A a mot x : Expr Nat)
    (hnc : ¬ IsCtorSpine eqEnvT x) :
    RedR (WhStepIndexCK2 eqEnvT) Γ
      (gapCall A a mot (gapBetaIndex A a) x) (.sort .zero) := by
  let w := eqConvW (fun _ _ h => h) A a (gapBetaIndex A a) mot (.sort .zero)
  by_cases hidx : gapBetaIndex A a = a
  · exact .step (.ck (.kStar (w := w) ⟨rfl, rfl, rfl⟩ hnc
      (by change [gapBetaIndex A a] = [a]; rw [hidx]))) (.refl _)
  · let wa := eqConvW (fun _ _ h => h) A a a mot (.sort .zero)
    exact .step (.index (w := w) (.inl ⟨rfl, rfl, rfl⟩) hnc
      (.here hidx (.ctx (.beta A (.bvar 0) a))))
      (.step (.ck (.kStar (w := wa) ⟨rfl, rfl, rfl⟩ hnc rfl)) (.refl _))

/-- The original gap after any non-constructor substitution computes in candidate (b). -/
theorem redR_eqGap_subst_nonCtor_index (σ : SubstT)
    (hnc : ¬ IsCtorSpine eqEnvT (σ 0)) :
    RedR (WhStepIndexCK2 eqEnvT) Γ (substT σ eqGapRedex) (.sort .zero) := by
  rw [substT_eqGapRedex]
  exact redR_gapCall_nonCtor_index _ _ _ _ hnc

/-- The checked Eq environment has exactly one constructor member. -/
theorem eqEnv_ctorMember {r : Nat} {m : CheckedMember}
    (hm : eqEnvT.members r = some m) (hk : m.mclass = .constructorM) :
    r = 64 ∧ m = eqReflT := by
  rw [eqEnvT_mem] at hm
  by_cases h65 : r = 65
  · simp only [h65, ↓reduceIte, Option.some.injEq] at hm
    subst m
    cases hk
  · simp only [h65, ↓reduceIte] at hm
    by_cases h64 : r = 64
    · simp only [h64, ↓reduceIte, Option.some.injEq] at hm
      exact ⟨h64, hm.symm⟩
    · simp only [h64, ↓reduceIte] at hm
      by_cases h63 : r = 63
      · simp only [h63, ↓reduceIte, Option.some.injEq] at hm
        subst m
        cases hk
      · simp only [h63, ↓reduceIte] at hm
        cases hm

/-- Constructor classification fixes its head, but does not infer its term arity. -/
theorem isCtorSpine_eq_iff (x : Expr Nat) :
    IsCtorSpine eqEnvT x ↔
      ∃ us args, x = foldApps (.const 64 us) args := by
  constructor
  · rintro ⟨r, us, args, m, he, hm, hk⟩
    obtain ⟨rfl, rfl⟩ := eqEnv_ctorMember hm hk
    exact ⟨us, args, he⟩
  · rintro ⟨us, args, rfl⟩
    exact ⟨64, us, args, eqReflT, rfl, rfl, rfl⟩

/-- Constructive classification avoids any classical decidability of the existential predicate. -/
theorem eqMajor_cases (x : Expr Nat) :
    (∃ us args, x = foldApps (.const 64 us) args) ∨ ¬ IsCtorSpine eqEnvT x := by
  cases hh : (appsSpine x).1
  case const r us =>
    by_cases hr : r = 64
    · subst r
      left
      refine ⟨us, (appsSpine x).2, ?_⟩
      have he := (foldApps_appsSpine x).symm
      rwa [hh] at he
    · right
      intro hc
      obtain ⟨vs, args, he⟩ := (isCtorSpine_eq_iff x).mp hc
      have hk := congrArg (fun e => (appsSpine e).1) he
      simp only [appsSpine_foldApps_const] at hk
      rw [hh] at hk
      exact hr (Expr.const.inj hk).1
  all_goals
    right
    intro hc
    obtain ⟨vs, args, he⟩ := (isCtorSpine_eq_iff x).mp hc
    have hk := congrArg (fun e => (appsSpine e).1) he
    simp only [appsSpine_foldApps_const] at hk
    rw [hh] at hk
    exact Expr.noConfusion hk

/-- The ordinary iota witness permits independent constructor-side parameters. -/
def gapCtorW (A a mot b C c : Expr Nat) (us : List Level) : IotaWitness eqEnvT :=
  { eqConvW (fun _ _ h => h) A a b mot (.sort .zero) with
    lsC := us
    ctorParams := [C, c]
    hctorParams := rfl }

/-- A two-argument Eq.refl major computes by existing iota, at every index. -/
theorem whStepCtx_gapCall_refl (A a mot b C c : Expr Nat) (us : List Level) :
    WhStepCtx eqEnvT Γ
      (gapCall A a mot b (foldApps (.const 64 us) [C, c])) (.sort .zero) :=
  .iota (.ofU (gapCtorW A a mot b C c us))

/-- The constructor arity condition alone suffices for the old context step. -/
theorem whStepCtx_gapCall_ctor_two {A a mot b x : Expr Nat}
    (hc : IsCtorSpine eqEnvT x) (hl : (appsSpine x).2.length = 2) :
    WhStepCtx eqEnvT Γ (gapCall A a mot b x) (.sort .zero) := by
  obtain ⟨us, args, rfl⟩ := (isCtorSpine_eq_iff x).mp hc
  rw [appsSpine_foldApps_const] at hl
  cases args with
  | nil => cases hl
  | cons C args =>
      cases args with
      | nil => cases hl
      | cons c args =>
          have hz : args.length = 0 := by
            simp only [List.length_cons] at hl
            omega
          obtain rfl := List.eq_nil_of_length_eq_zero hz
          exact whStepCtx_gapCall_refl A a mot b C c us

/-- Every legacy or structured iota landing at Eq.rec has exactly two major arguments. -/
theorem gapCall_iota_arity {A a mot b x y : Expr Nat}
    (hi : DerivedIotaU eqEnvT (gapCall A a mot b x) y) :
    (appsSpine x).2.length = 2 := by
  generalize he : gapCall A a mot b x = src at hi
  cases hi with
  | ofU w =>
      have he' : recCall (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b] x =
          recCall (.const w.recRef w.ls) w.preMajor (ctorMajor w) := he
      obtain ⟨hr, _, _, hx⟩ := recCall_const_inj he'
      obtain ⟨hnp, _, _⟩ := eqWitnessIndexCut w hr.symm
      have hf := (eqWitnessCtorData w hr.symm).2
      rw [hx]
      change (appsSpine (foldApps (.const w.ctorRef w.lsC)
        (w.ctorParams ++ w.fields))).2.length = 2
      rw [appsSpine_foldApps_const]
      simp only [List.length_append, hf, List.length_nil, Nat.add_zero,
        w.hctorParams, hnp]
  | ofUS w =>
      have he' : recCall (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b] x =
          recCall (.const w.recRef w.ls) w.preMajor
            (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)) := he
      obtain ⟨hr, _, _, hx⟩ := recCall_const_inj he'
      have hm : w.recMember = eqRecT := by
        have h := w.hrec
        rw [← hr] at h
        exact (Option.some.inj h).symm
      have hd := IotaWitnessS.recData_admitted eqGroupAdm
        (fun _ _ h => h) w hr.symm hm
      change w.familyRef = 63 ∧ w.famMember = eqFamT ∧
        w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 at hd
      have hf := (eqRec_model_schema w hr.symm).2.2.1
      rw [hx, appsSpine_foldApps_const]
      simp only [List.length_append, hf, List.length_nil, Nat.add_zero,
        w.hctorParams, hd.2.2.1]

/-- A context step at this saturated Eq call must be the existing iota case. -/
theorem whStepCtx_gapCall_arity {A a mot b x y : Expr Nat}
    (hs : WhStepCtx eqEnvT Γ (gapCall A a mot b x) y) :
    (appsSpine x).2.length = 2 := by
  have happ : WhStepCtx eqEnvT Γ
      (.app (foldApps (.const 65 [.succ (.succ .zero)])
        [A, a, mot, .sort .zero, b]) x) y := hs
  rcases whStepCtx_app_cases happ with ⟨D, body, hf, _⟩ | hi | ⟨f', hf, _⟩
  · exact (F8EtaK.foldApps_const_ne_lam_any hf).elim
  · obtain ⟨hi⟩ := hi
    exact gapCall_iota_arity hi
  · exact (whStepCtx_recPrefix_false_aux pinEqGroupWfT
      (rfl : eqEnvT.members 65 = some eqRecT) rfl hf rfl
      (by change 6 ≤ 6; omega)).elim

/-- At a constructor major, every old CK step forces the same exact arity. -/
theorem whStepCK_gapCall_ctor_arity {A a mot b x y : Expr Nat}
    (hc : IsCtorSpine eqEnvT x) (hs : WhStepCK eqEnvT Γ (gapCall A a mot b x) y) :
    (appsSpine x).2.length = 2 := by
  generalize he : gapCall A a mot b x = src at hs
  cases hs with
  | ctx hs => exact whStepCtx_gapCall_arity (he.symm ▸ hs)
  | kStar hK hnc hidx =>
      rename_i w z
      have he' : recCall (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b] x =
          recCall (.const w.recRef w.ls) w.preMajor z := he
      exact (hnc ((recCall_const_inj he').2.2.2 ▸ hc)).elim
  | kProj hK hnc hf hidx =>
      rename_i w z
      have he' : recCall (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b] x =
          recCall (.const w.recRef w.ls) w.preMajor z := he
      exact (hnc ((recCall_const_inj he').2.2.2 ▸ hc)).elim
  | @recMajor r m ls pre z z' hm hr hl hnK hnP hs =>
      have he' : recCall (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b] x = recCall (.const r ls) pre z := he
      exact (hnK ⟨eqGapW, (recCall_const_inj he').1, rfl, rfl, rfl⟩).elim
  | @appHead f f' z hs =>
      have he' : Expr.app (foldApps (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b]) x = .app f z := he
      exact (whStepCK_recPrefix_false_aux pinEqGroupWfT
        (rfl : eqEnvT.members 65 = some eqRecT) rfl hs
        (Expr.app.inj he').1.symm (by change 6 ≤ 6; omega)).elim

/-- The entire native-gated grammar has the same constructor-major arity restriction. -/
theorem whStepCK2_gapCall_ctor_arity {A a mot b x y : Expr Nat}
    (hc : IsCtorSpine eqEnvT x)
    (hs : WhStepCK2 eqEnvT n Γ (gapCall A a mot b x) y) :
    (appsSpine x).2.length = 2 := by
  generalize he : gapCall A a mot b x = src at hs
  cases hs with
  | ctx hs => exact whStepCtx_gapCall_arity (he.symm ▸ hs)
  | native hs =>
      cases hs with
      | intro hK hnc hi ht =>
          rename_i w z
          have he' : recCall (.const 65 [.succ (.succ .zero)])
              [A, a, mot, .sort .zero, b] x =
              recCall (.const w.recRef w.ls) w.preMajor z := he
          exact (hnc ((recCall_const_inj he').2.2.2 ▸ hc)).elim
  | @recMajor r m ls pre z z' hm hr hl hnK hnP hs =>
      have he' : recCall (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b] x = recCall (.const r ls) pre z := he
      exact (hnK ⟨eqGapW, (recCall_const_inj he').1, rfl, rfl, rfl⟩).elim
  | @appHead f f' z hs =>
      have he' : Expr.app (foldApps (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b]) x = .app f z := he
      exact (normalR_recPrefixCK2 pinEqGroupWfT
        (rfl : eqEnvT.members 65 = some eqRecT) rfl Γ _
        [A, a, mot, .sort .zero, b] (by change 6 ≤ 6; omega) _
        ((Expr.app.inj he').1.symm ▸ hs)).elim

/-- The complete index-scheduled grammar retains that exact constructor-major restriction. -/
theorem whStepIndexCK2_gapCall_ctor_arity {A a mot b x y : Expr Nat}
    (hc : IsCtorSpine eqEnvT x)
    (hs : WhStepIndexCK2 eqEnvT Γ (gapCall A a mot b x) y) :
    (appsSpine x).2.length = 2 := by
  generalize he : gapCall A a mot b x = src at hs
  cases hs with
  | ck hs => exact whStepCK_gapCall_ctor_arity hc (he.symm ▸ hs)
  | index hK hnc hi =>
      rename_i w z idxs
      have he' : recCall (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b] x =
          recCall (.const w.recRef w.ls) w.preMajor z := he
      exact (hnc ((recCall_const_inj he').2.2.2 ▸ hc)).elim
  | @recMajor r m ls pre z z' hm hr hl hnK hnP hs =>
      have he' : recCall (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b] x = recCall (.const r ls) pre z := he
      exact (hnK ⟨eqGapW, (recCall_const_inj he').1, rfl, rfl, rfl⟩).elim
  | @appHead f f' z hs =>
      have he' : Expr.app (foldApps (.const 65 [.succ (.succ .zero)])
          [A, a, mot, .sort .zero, b]) x = .app f z := he
      exact (whStepIndexCK2_recPrefix_false_aux pinEqGroupWfT
        (rfl : eqEnvT.members 65 = some eqRecT) rfl hs
        (Expr.app.inj he').1.symm (by change 6 ≤ 6; omega)).elim

/-- A constructor-major read to any sort has a first step, hence the exact two-argument arity. -/
theorem redR_gapCall_ctor_arity_native {A a mot b x : Expr Nat} {u : Level}
    (hc : IsCtorSpine eqEnvT x)
    (hr : RedR (WhStepCK2 eqEnvT n) Γ (gapCall A a mot b x) (.sort u)) :
    (appsSpine x).2.length = 2 := by
  generalize he : gapCall A a mot b x = src at hr
  cases hr with
  | refl => exact Expr.noConfusion he
  | step hs _ => exact whStepCK2_gapCall_ctor_arity hc (he.symm ▸ hs)

/-- The same necessity holds for any finite read of the index-scheduled candidate. -/
theorem redR_gapCall_ctor_arity_index {A a mot b x : Expr Nat} {u : Level}
    (hc : IsCtorSpine eqEnvT x)
    (hr : RedR (WhStepIndexCK2 eqEnvT) Γ (gapCall A a mot b x) (.sort u)) :
    (appsSpine x).2.length = 2 := by
  generalize he : gapCall A a mot b x = src at hr
  cases hr with
  | refl => exact Expr.noConfusion he
  | step hs _ => exact whStepIndexCK2_gapCall_ctor_arity hc (he.symm ▸ hs)

/-- A wrong-arity constructor major is normal for the entire native-gated candidate. -/
theorem normalR_gapCall_ctor_badarity_native {A a mot b x : Expr Nat}
    (hc : IsCtorSpine eqEnvT x) (hl : (appsSpine x).2.length ≠ 2) :
    NormalR (WhStepCK2 eqEnvT n) Γ (gapCall A a mot b x) :=
  fun _ hs => hl (whStepCK2_gapCall_ctor_arity hc hs)

/-- It is also normal for the entire index-scheduled candidate. -/
theorem normalR_gapCall_ctor_badarity_index {A a mot b x : Expr Nat}
    (hc : IsCtorSpine eqEnvT x) (hl : (appsSpine x).2.length ≠ 2) :
    NormalR (WhStepIndexCK2 eqEnvT) Γ (gapCall A a mot b x) :=
  fun _ hs => hl (whStepIndexCK2_gapCall_ctor_arity hc hs)

/-- The exact remaining port over every original related substitution. -/
def EqGapRelatedCtorArity (R : Readback) (n : Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
    CtxWfT eqEnvT n Δ →
    RelSubstAtT (ctxModelT_approxT eqEnvT) R n Δ ρ ρ' σ σ' eqGapCtx →
    IsCtorSpine eqEnvT (σ' 0) → (appsSpine (σ' 0)).2.length = 2

/-- An equivalent native-only port: a typed substitution may not put a
constructor of the wrong arity at the original proof variable. -/
def EqGapTypedCtorArity (n : Nat) : Prop :=
  ∀ {Δ : LCtx} {σ : SubstT}, CtxWfT eqEnvT n Δ →
    TypedSubstT eqEnvT n Δ σ eqGapCtx →
    IsCtorSpine eqEnvT (σ 0) → (appsSpine (σ 0)).2.length = 2

/-- Every typed substitution into this let-free source context gives a
diagonal related substitution at bottom, uniformly in model and readback. -/
theorem relSubstAtT_eqGap_bot_diagonal (M : CtxModelT eqEnvT) (R : Readback)
    {σ : SubstT} (hT : TypedSubstT eqEnvT n Δ σ eqGapCtx) :
    RelSubstAtT M R n Δ EnvT.bot EnvT.bot σ σ eqGapCtx := by
  refine ⟨hT, hT, ?_, ?_, ?_⟩
  · intro i A hA
    obtain ⟨hi⟩ := hT.1 i A hA
    exact ⟨.refl Δ (σ i) (substT σ A) hi⟩
  · intro i A _ c hc
    have hc' : c = .bot := hc.elim id id
    subst c
    exact ⟨lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _,
      lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _⟩
  · intro i v A hv _
    rw [lookupValue_eqGapCtx_none] at hv
    exact Option.noConfusion hv

/-- The related port is precisely a native typed-substitution arity question.
The reverse direction explicitly constructs the required related package;
it does not identify packages belonging to different readbacks. -/
theorem eqGapRelatedCtorArity_iff_typed :
    EqGapRelatedCtorArity R n ↔ EqGapTypedCtorArity n := by
  constructor
  · intro h Δ σ hΔ hT hc
    exact h hΔ (relSubstAtT_eqGap_bot_diagonal (ctxModelT_approxT eqEnvT) R hT) hc
  · intro h Δ ρ ρ' σ σ' hΔ hS hc
    exact h hΔ hS.2.1 hc

/-- Candidate (a)'s quantified original-gap readback is equivalent to the exact arity port. -/
theorem eqGapUniformRead_native_iff_relatedCtorArity :
    EqGapUniformReadCK2 (WhStepCK2 eqEnvT n) n ↔
      EqGapRelatedCtorArity (WhStepCK2 eqEnvT n) n := by
  constructor
  · intro h Δ ρ ρ' σ σ' hΔ hS hc
    obtain ⟨u, hr⟩ := h hΔ hS
    rw [substT_eqGapRedex] at hr
    exact redR_gapCall_ctor_arity_native hc hr
  · intro h Δ ρ ρ' σ σ' hΔ hS
    rcases eqMajor_cases (σ' 0) with ⟨us, args, he⟩ | hnc
    · have hc := (isCtorSpine_eq_iff (σ' 0)).mpr ⟨us, args, he⟩
      have hl := h hΔ hS hc
      refine ⟨.zero, ?_⟩
      rw [substT_eqGapRedex]
      exact .step (.ctx (whStepCtx_gapCall_ctor_two hc hl)) (.refl _)
    · exact ⟨.zero, redR_eqGap_subst_nonCtor_native hS.2.1 hnc⟩

/-- Candidate (b)'s full quantified readback has the same constructor branch. -/
theorem eqGapUniformRead_index_iff_relatedCtorArity :
    EqGapUniformReadCK2 (WhStepIndexCK2 eqEnvT) n ↔
      EqGapRelatedCtorArity (WhStepIndexCK2 eqEnvT) n := by
  constructor
  · intro h Δ ρ ρ' σ σ' hΔ hS hc
    obtain ⟨u, hr⟩ := h hΔ hS
    rw [substT_eqGapRedex] at hr
    exact redR_gapCall_ctor_arity_index hc hr
  · intro h Δ ρ ρ' σ σ' hΔ hS
    rcases eqMajor_cases (σ' 0) with ⟨us, args, he⟩ | hnc
    · have hc := (isCtorSpine_eq_iff (σ' 0)).mpr ⟨us, args, he⟩
      have hl := h hΔ hS hc
      refine ⟨.zero, ?_⟩
      rw [substT_eqGapRedex]
      exact .step (.ck (.ctx (whStepCtx_gapCall_ctor_two hc hl))) (.refl _)
    · exact ⟨.zero, redR_eqGap_subst_nonCtor_index σ' hnc⟩

/-- Exact restatement of candidate (a)'s full local supplier, with all substitutions retained. -/
theorem eqGapFundConvAt_native_iff_typedCtorArity (n : Nat) :
    FundConvAt (ctxModelT_approxT eqEnvT) (WhStepCK2 eqEnvT n) n eqGapCtx
      (.sort .zero) eqGapRedex (.sort (.succ .zero)) ↔ EqGapTypedCtorArity n :=
  eqGapFundConvAt_iff_uniformRead.trans
    (eqGapUniformRead_native_iff_relatedCtorArity.trans eqGapRelatedCtorArity_iff_typed)

/-- Exact restatement of candidate (b)'s full local supplier at the same native arity port. -/
theorem eqGapFundConvAt_index_iff_typedCtorArity (n : Nat) :
    FundConvAt (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT) n eqGapCtx
      (.sort .zero) eqGapRedex (.sort (.succ .zero)) ↔ EqGapTypedCtorArity n :=
  eqGapFundConvAt_iff_uniformRead.trans
    (eqGapUniformRead_index_iff_relatedCtorArity.trans eqGapRelatedCtorArity_iff_typed)

/-- For this original local gap, the two full suppliers have exactly the same truth value.
This follows through the explicit native port, not by equating their related packages. -/
theorem eqGapFundConvAt_native_iff_index (n : Nat) :
    FundConvAt (ctxModelT_approxT eqEnvT) (WhStepCK2 eqEnvT n) n eqGapCtx
      (.sort .zero) eqGapRedex (.sort (.succ .zero)) ↔
    FundConvAt (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT) n eqGapCtx
      (.sort .zero) eqGapRedex (.sort (.succ .zero)) :=
  (eqGapFundConvAt_native_iff_typedCtorArity n).trans
    (eqGapFundConvAt_index_iff_typedCtorArity n).symm

/-- A closed canonical proof for a concrete substituted Eq type. -/
def gapCanonicalMajor : Expr Nat :=
  foldApps (.const 64 []) [indexFn, indexId]

/-- Replace alpha by the function type, a by its identity, and h by Eq.refl. -/
def gapCanonicalSubst : SubstT :=
  SubstT.cons gapCanonicalMajor
    (SubstT.cons indexId (SubstT.cons indexFn SubstT.id))

/-- Native conversion types the constructor at the original beta-indexed proposition. -/
def gapCanonicalMajorTy (n : Nat) :
    HasTyT eqEnvT n [] gapCanonicalMajor
      (foldApps (.const 63 []) [indexFn, indexId, gapBetaIndex indexFn indexId]) := by
  have hA := indexFnTy eqEnvT n []
  have ha := indexIdTy eqEnvT n []
  have cp : ConvT eqEnvT n []
      (foldApps (.const 63 []) [indexFn, indexId, indexId])
      (foldApps (.const 63 []) [indexFn, indexId, gapBetaIndex indexFn indexId])
      (.sort .zero) :=
    .app _ _ _ _ _ _ _ (.refl _ _ _ (eqFamilyPartialTy (fun _ _ h => h) hA ha))
      (.symm _ _ _ _ (gapBetaIndexConv hA ha))
  exact .conv [] _ _ _ .zero (eqReflApplyTy (fun _ _ h => h) hA ha) cp

/-- This constructor-headed replacement is a real native typed substitution. -/
theorem gapCanonicalSubst_typed (n : Nat) :
    TypedSubstT eqEnvT n [] gapCanonicalSubst eqGapCtx := by
  constructor
  · intro i A hi
    cases i with
    | zero =>
        have hA : A = foldApps (.const 63 [])
            [.bvar 2, .bvar 1, gapBetaIndex (.bvar 2) (.bvar 1)] :=
          (Option.some.inj hi).symm
        subst A
        exact ⟨gapCanonicalMajorTy n⟩
    | succ i =>
        cases i with
        | zero =>
            have hA : A = .bvar 2 := (Option.some.inj hi).symm
            subst A
            exact ⟨indexIdTy eqEnvT n []⟩
        | succ i =>
            cases i with
            | zero =>
                have hA : A = .sort (.succ .zero) := (Option.some.inj hi).symm
                subst A
                exact ⟨indexFnTy eqEnvT n []⟩
            | succ i => simp [eqGapCtx, lookupType] at hi
  · intro i v hv
    rw [lookupValue_eqGapCtx_none] at hv
    exact Option.noConfusion hv

/-- The explicit canonical replacement meets the complete related-substitution interface. -/
theorem gapCanonicalSubst_related (R : Readback) (n : Nat) :
    RelSubstAtT (ctxModelT_approxT eqEnvT) R n [] EnvT.bot EnvT.bot
      gapCanonicalSubst gapCanonicalSubst eqGapCtx :=
  relSubstAtT_eqGap_bot_diagonal (ctxModelT_approxT eqEnvT) R (gapCanonicalSubst_typed n)

/-- The constructor branch is inhabited at the admitted environment and empty native context. -/
theorem gapCanonical_control (R : Readback) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n []) ∧
    TypedSubstT eqEnvT n [] gapCanonicalSubst eqGapCtx ∧
    RelSubstAtT (ctxModelT_approxT eqEnvT) R n [] EnvT.bot EnvT.bot
      gapCanonicalSubst gapCanonicalSubst eqGapCtx ∧
    IsCtorSpine eqEnvT (gapCanonicalSubst 0) ∧
    (appsSpine (gapCanonicalSubst 0)).2.length = 2 :=
  ⟨⟨pinEqGroupWfT⟩, ⟨.nil⟩, gapCanonicalSubst_typed n, gapCanonicalSubst_related R n,
    ⟨64, [], [indexFn, indexId], eqReflT, rfl, rfl, rfl⟩, rfl⟩

/-- Both complete candidates compute the explicit constructor substitution. -/
theorem gapCanonical_readbacks (n : Nat) :
    RedR (WhStepCK2 eqEnvT n) [] (substT gapCanonicalSubst eqGapRedex) (.sort .zero) ∧
    RedR (WhStepIndexCK2 eqEnvT) [] (substT gapCanonicalSubst eqGapRedex) (.sort .zero) := by
  have hs : WhStepCtx eqEnvT []
      (substT gapCanonicalSubst eqGapRedex) (.sort .zero) := by
    rw [substT_eqGapRedex]
    exact whStepCtx_gapCall_ctor_two
      (show IsCtorSpine eqEnvT (gapCanonicalSubst 0) from
        ⟨64, [], [indexFn, indexId], eqReflT, rfl, rfl, rfl⟩) rfl
  exact ⟨.step (.ctx hs) (.refl _), .step (.ck (.ctx hs)) (.refl _)⟩

/-- The non-constructor branch is independently inhabited by the original identity package. -/
theorem gapIdentity_control (R : Readback) (n : Nat) :
    Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    RelSubstAtT (ctxModelT_approxT eqEnvT) R n eqGapCtx EnvT.bot EnvT.bot
      SubstT.id SubstT.id eqGapCtx ∧
    ¬ IsCtorSpine eqEnvT (SubstT.id 0) :=
  ⟨eqGapCtx_wf n, relSubstIdT_eqGap_bot (ctxModelT_approxT eqEnvT) R n,
    not_isCtorSpine_bvar⟩

-- BEGIN CK2 GAP AUDIT ROOTS
#print axioms gapBetaIndex
#print axioms gapCall
#print axioms substT_eqGapRedex
#print axioms gapBetaIndexTy
#print axioms gapBetaIndexConv
#print axioms eqGap_typedSubst_data
#print axioms redR_eqGap_subst_nonCtor_native
#print axioms redR_gapCall_nonCtor_index
#print axioms redR_eqGap_subst_nonCtor_index
#print axioms eqEnv_ctorMember
#print axioms isCtorSpine_eq_iff
#print axioms eqMajor_cases
#print axioms gapCtorW
#print axioms whStepCtx_gapCall_refl
#print axioms whStepCtx_gapCall_ctor_two
#print axioms gapCall_iota_arity
#print axioms whStepCtx_gapCall_arity
#print axioms whStepCK_gapCall_ctor_arity
#print axioms whStepCK2_gapCall_ctor_arity
#print axioms whStepIndexCK2_gapCall_ctor_arity
#print axioms redR_gapCall_ctor_arity_native
#print axioms redR_gapCall_ctor_arity_index
#print axioms normalR_gapCall_ctor_badarity_native
#print axioms normalR_gapCall_ctor_badarity_index
#print axioms EqGapRelatedCtorArity
#print axioms EqGapTypedCtorArity
#print axioms relSubstAtT_eqGap_bot_diagonal
#print axioms eqGapRelatedCtorArity_iff_typed
#print axioms eqGapUniformRead_native_iff_relatedCtorArity
#print axioms eqGapUniformRead_index_iff_relatedCtorArity
#print axioms eqGapFundConvAt_native_iff_typedCtorArity
#print axioms eqGapFundConvAt_index_iff_typedCtorArity
#print axioms eqGapFundConvAt_native_iff_index
#print axioms gapCanonicalMajor
#print axioms gapCanonicalSubst
#print axioms gapCanonicalMajorTy
#print axioms gapCanonicalSubst_typed
#print axioms gapCanonicalSubst_related
#print axioms gapCanonical_control
#print axioms gapCanonical_readbacks
#print axioms gapIdentity_control
-- END CK2 GAP AUDIT ROOTS

end Rcic.Declarative.NativeValleys.ReadbackCK2GapAudit
