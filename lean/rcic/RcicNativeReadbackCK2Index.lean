import rcic.RcicNativeReadbackCK
import rcic.RcicIotaLegacyAdm
import rcic.RcicNativePiProbeRelIota

/-!
# CK2 index-normalization measurement

This file defines the index-list scheduler and the complete standalone
candidate-(b) comparator `WhStepIndexCK2`.  The scheduler's index step is
exactly the landed `WhStepCK`.  Consequently its word "normal" means
weak-head normal.  A lambda body, Pi body, argument, and binder annotation
are not inspected by this scheduler.

The actual list is scanned left to right.  An entry is skipped exactly when
it already agrees syntactically with the corresponding computed index, or
when it is weak-head normal.  The first remaining entry takes one CK step.
The computed constructor indices do not themselves step here.  Every new
recursor-level scheduler using this relation must recompute them after the
actual index list changes.  The parameter/index cut of a legacy Eq witness
is pinned below by the admitted recursor descriptor; the apparent extra
cuts permitted by its arithmetic fields alone are not actual witnesses.

All controls carry native typed conversion witnesses.  Binder and eta
controls use the admitted `eqEnvT`; the delta control extends that exact
environment by one checked transparent definition.

Composition only.  No change to `WhStepCK`, native conversion, or model
interfaces.  No normalization or fundamental theorem is assumed.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- One step at the first non-normal mismatching actual index. -/
inductive FirstWhnfMismatch (E : ResolvedEnv) (Γ : LCtx) :
    List (Expr Nat) → List (Expr Nat) → List (Expr Nat) → Prop
  | here {x y x' : Expr Nat} {xs ys : List (Expr Nat)}
      (hne : x ≠ y) (hs : WhStepCK E Γ x x') :
      FirstWhnfMismatch E Γ (x :: xs) (y :: ys) (x' :: xs)
  | there {x y : Expr Nat} {xs ys xs' : List (Expr Nat)}
      (hskip : x = y ∨ NormalR (WhStepCK E) Γ x)
      (hs : FirstWhnfMismatch E Γ xs ys xs') :
      FirstWhnfMismatch E Γ (x :: xs) (y :: ys) (x :: xs')

/-- The selected position and its reduct are deterministic. -/
theorem firstWhnfMismatch_det (hW : EnvWfT E)
    {xs target ys zs : List (Expr Nat)}
    (hy : FirstWhnfMismatch E Γ xs target ys)
    (hz : FirstWhnfMismatch E Γ xs target zs) : ys = zs := by
  induction hy generalizing zs with
  | @here x y x' xs target hne hs =>
      cases hz with
      | here _ hs' =>
          exact congrArg (fun z => z :: xs) (detR_whStepCK hW Γ hs hs')
      | there hskip _ =>
          rcases hskip with heq | hnormal
          · exact (hne heq).elim
          · exact (hnormal _ hs).elim
  | @there x y xs target xs' hskip hs ih =>
      cases hz with
      | here hne hs' =>
          rcases hskip with heq | hnormal
          · exact (hne heq).elim
          · exact (hnormal _ hs').elim
      | there _ hs' => exact congrArg (fun zs => x :: zs) (ih hs')

/-- Weak-head-normal actual indices leave no scheduled index step. -/
theorem firstWhnfMismatch_false_of_normal
    {xs target ys : List (Expr Nat)}
    (hnormal : ∀ x, x ∈ xs → NormalR (WhStepCK E) Γ x) :
    ¬ FirstWhnfMismatch E Γ xs target ys := by
  intro h
  revert hnormal
  induction h with
  | here _ hs =>
      intro hnormal
      exact hnormal _ (by simp) _ hs
  | @there x y xs target xs' _ hs ih =>
      intro hnormal
      apply ih
      intro z hz
      exact hnormal z (List.mem_cons_of_mem x hz)

/-- Iteration of the selected index schedule, with a fixed computed target. -/
inductive FirstWhnfMismatchStar (E : ResolvedEnv) (Γ : LCtx)
    (target : List (Expr Nat)) : List (Expr Nat) → List (Expr Nat) → Prop
  | refl (xs : List (Expr Nat)) : FirstWhnfMismatchStar E Γ target xs xs
  | step {xs ys zs : List (Expr Nat)}
      (hs : FirstWhnfMismatch E Γ xs target ys)
      (hr : FirstWhnfMismatchStar E Γ target ys zs) :
      FirstWhnfMismatchStar E Γ target xs zs

/-- Iteration cannot escape a weak-head-normal actual index list. -/
theorem firstWhnfMismatchStar_eq_of_normal
    {xs target ys : List (Expr Nat)}
    (hnormal : ∀ x, x ∈ xs → NormalR (WhStepCK E) Γ x)
    (hr : FirstWhnfMismatchStar E Γ target xs ys) : ys = xs := by
  cases hr with
  | refl => rfl
  | step hs _ => exact (firstWhnfMismatch_false_of_normal hnormal hs).elim

/-- The existing beta-gap index is selected and contracts to the canon index. -/
theorem firstWhnfMismatch_eqGap :
    FirstWhnfMismatch eqEnvT eqGapCtx
      [.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)] [.bvar 1] [.bvar 1] :=
  .here (by decide) (.ctx (.beta _ _ _))

/-- The beta-gap index conversion is native and typed in the existing Eq context. -/
def eqGap_indexConv (n : Nat) :
    ConvT eqEnvT n eqGapCtx
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) (.bvar 1) (.bvar 2) :=
  .beta _ _ _ _ _ _
    (.bvar eqGapCtx 2 _ rfl)
    (.bvar (.assumption (.bvar 2) :: eqGapCtx) 0 _ rfl)
    (.bvar eqGapCtx 1 _ rfl)

/-- The admitted Eq descriptor fixes the index cut of every legacy witness. -/
theorem eqWitnessIndexCut (w : IotaWitness eqEnvT) (hr : w.recRef = 65) :
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 := by
  have hm : w.recMember = eqRecT := by
    have h := w.hrec
    rw [hr] at h
    exact (Option.some.inj h).symm
  have hd := IotaWitness.recData_admitted eqGroupAdm
    (fun _ _ h => h) w hr hm
  change w.familyRef = 63 ∧ w.famMember = eqFamT ∧
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 at hd
  exact hd.2.2

/-- A small closed function type in `Sort 1`, usable as Eq's type parameter. -/
def indexFn : Expr Nat := .pi (.sort .zero) (.sort .zero)

/-- The identity on propositions, used as the computed constructor index. -/
def indexId : Expr Nat := .lam (.sort .zero) (.bvar 0)

/-- A beta redex strictly below a lambda. -/
def indexBinderBeta : Expr Nat :=
  .lam (.sort .zero) (.app indexId (.bvar 0))

/-- Native sort typing of the function index type. -/
def indexFnTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ indexFn (.sort (.succ .zero)) :=
  .conv _ _ _ _ _
    (.pi _ _ _ _ _ (.sort _ _) (.sort _ _))
    (.sorts _ _ _ (fun _ => rfl))

/-- Native typing of the constructor index. -/
def indexIdTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ indexId indexFn :=
  .lam _ _ _ _ _ (.sort _ _) (.bvar _ 0 _ rfl)

/-- Native typing of the index containing an internal beta redex. -/
def indexBinderBetaTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ indexBinderBeta indexFn :=
  .lam _ _ _ _ _ (.sort _ _)
    (.app _ _ _ _ _ (indexIdTy E n _) (.bvar _ 0 _ rfl))

/-- Native conversion does inspect the lambda body. -/
def indexBinderBetaConv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ConvT E n Γ indexBinderBeta indexId indexFn :=
  .lam _ _ _ _ _ _ _ (.refl _ _ _ (.sort _ _))
    (.beta _ _ _ _ _ _ (.sort _ _) (.bvar _ 0 _ rfl) (.bvar _ 0 _ rfl))

/-- An actual Eq proof assumption with the internal-beta mismatch. -/
def binderEqCtx : LCtx :=
  [.assumption (foldApps (.const 63 []) [indexFn, indexId, indexBinderBeta])]

/-- This is a well-formed native context over the admitted Eq environment. -/
def binderEqCtxWf (n : Nat) : CtxWfT eqEnvT n binderEqCtx :=
  .assumption _ _ _ .nil
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl)
          (indexFnTy eqEnvT n [])) (indexIdTy eqEnvT n []))
      (indexBinderBetaTy eqEnvT n []))

/-- Both binder indices are weak-head normal, even though they are natively convertible. -/
theorem binder_indices_normal (Γ : LCtx) :
    NormalR (WhStepCK eqEnvT) Γ indexBinderBeta ∧
    NormalR (WhStepCK eqEnvT) Γ indexId :=
  ⟨fun _ h => whStepCK_lam_false_aux h rfl,
   fun _ h => whStepCK_lam_false_aux h rfl⟩

/-- The first-non-normal schedule cannot cross this typed binder mismatch. -/
theorem binder_index_schedule_stuck (ys : List (Expr Nat)) :
    ¬ FirstWhnfMismatch eqEnvT binderEqCtx [indexBinderBeta] [indexId] ys := by
  apply firstWhnfMismatch_false_of_normal
  intro x hx
  have heq : x = indexBinderBeta := by simpa using hx
  subst x
  exact (binder_indices_normal binderEqCtx).1

/-- A native, well-formed, convertible but syntactically unequal binder control. -/
theorem binder_index_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n binderEqCtx) ∧
    Nonempty (ConvT eqEnvT n binderEqCtx indexBinderBeta indexId indexFn) ∧
    indexBinderBeta ≠ indexId ∧
    ∀ ys, ¬ FirstWhnfMismatch eqEnvT binderEqCtx [indexBinderBeta] [indexId] ys :=
  ⟨⟨pinEqGroupWfT⟩, ⟨binderEqCtxWf n⟩,
    ⟨indexBinderBetaConv eqEnvT n binderEqCtx⟩, by decide,
    binder_index_schedule_stuck⟩

/-- `f : Prop → Prop`, followed by an Eq assumption comparing `f` with its eta expansion. -/
def etaEqCtx : LCtx :=
  [.assumption (foldApps (.const 63 [])
      [indexFn, .bvar 0, .lam (.sort .zero) (.app (.bvar 1) (.bvar 0))]),
   .assumption indexFn]

/-- The actual eta-expanded index in `etaEqCtx`. -/
def etaIndex : Expr Nat :=
  .lam (.sort .zero) (.app (.bvar 2) (.bvar 0))

/-- Native well-formedness of the eta control's context. -/
def etaEqCtxWf (n : Nat) : CtxWfT eqEnvT n etaEqCtx := by
  have hf : HasTyT eqEnvT n [.assumption indexFn] (.bvar 0) indexFn :=
    .bvar [.assumption indexFn] 0 indexFn rfl
  have hfl : HasTyT eqEnvT n [.assumption (.sort .zero), .assumption indexFn]
      (.bvar 1) indexFn :=
    .bvar [.assumption (.sort .zero), .assumption indexFn] 1 indexFn rfl
  have hx : HasTyT eqEnvT n [.assumption (.sort .zero), .assumption indexFn]
      (.bvar 0) (.sort .zero) :=
    .bvar [.assumption (.sort .zero), .assumption indexFn] 0 (.sort .zero) rfl
  have hη : HasTyT eqEnvT n [.assumption indexFn]
      (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))) indexFn :=
    .lam _ _ _ _ _ (.sort _ _) (.app _ _ _ _ _ hfl hx)
  exact .assumption _ _ _
    (.assumption _ _ _ .nil (indexFnTy eqEnvT n []))
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl)
          (indexFnTy eqEnvT n [.assumption indexFn])) hf) hη)

/-- The mismatch is exactly native eta, with a genuinely neutral function. -/
def etaIndexConv (n : Nat) :
    ConvT eqEnvT n etaEqCtx etaIndex (.bvar 1) indexFn :=
  .eta etaEqCtx (.bvar 1) (.sort .zero) (.sort .zero)
    (.bvar etaEqCtx 1 indexFn rfl)

/-- Neither endpoint has a weak-head step. -/
theorem eta_indices_normal :
    NormalR (WhStepCK eqEnvT) etaEqCtx etaIndex ∧
    NormalR (WhStepCK eqEnvT) etaEqCtx (.bvar 1) :=
  ⟨fun _ h => whStepCK_lam_false_aux h rfl,
   fun _ h => whStepCK_bvar_none_false (Γ := etaEqCtx) (i := 1) rfl h rfl⟩

/-- Weak-head index normalization cannot remove this native eta mismatch. -/
theorem eta_index_schedule_stuck (ys : List (Expr Nat)) :
    ¬ FirstWhnfMismatch eqEnvT etaEqCtx [etaIndex] [.bvar 1] ys := by
  apply firstWhnfMismatch_false_of_normal
  intro x hx
  have heq : x = etaIndex := by simpa using hx
  subst x
  exact eta_indices_normal.1

/-- The eta obstruction carries both native environment and context witnesses. -/
theorem eta_index_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndex (.bvar 1) indexFn) ∧
    etaIndex ≠ .bvar 1 ∧
    ∀ ys, ¬ FirstWhnfMismatch eqEnvT etaEqCtx [etaIndex] [.bvar 1] ys :=
  ⟨⟨pinEqGroupWfT⟩, ⟨etaEqCtxWf n⟩, ⟨etaIndexConv n⟩, by decide,
    eta_index_schedule_stuck⟩

/-- One admitted transparent definition, extending the actual Eq fixture. -/
def deltaEqMember : CheckedMember :=
  ⟨.definitionM, 0, indexFn, some indexId⟩

/-- Eq plus a transparent identity function at reference 66. -/
def deltaEqEnv : ResolvedEnv := extendEnv eqEnvT 66 deltaEqMember

/-- The extension is accepted by the native environment judgment. -/
def deltaEqEnvWf : EnvWfT deltaEqEnv :=
  .definition eqEnvT 66 indexFn indexId (.succ .zero)
    pinEqGroupWfT rfl (indexFnTy eqEnvT 0 []) (indexIdTy eqEnvT 0 [])
    (fun _ => rfl)
    (by intro k; simp [indexId, lift]) rfl rfl

/-- The delta index itself has a checked native conversion to the canon. -/
def deltaIndexConv (n : Nat) (Γ : LCtx) :
    ConvT deltaEqEnv n Γ (.const 66 []) indexId indexFn :=
  .delta Γ 66 [] deltaEqMember indexId rfl rfl rfl rfl rfl
    (indexIdTy deltaEqEnv n Γ)

/-- Delta at an index head is seen by the scheduler. -/
theorem delta_index_schedule (Γ : LCtx) :
    FirstWhnfMismatch deltaEqEnv Γ [.const 66 []] [indexId] [indexId] :=
  .here (by decide) (.ctx (.delta (m := deltaEqMember) (b := indexId) rfl rfl))

/-- A transparent constant placed strictly below a lambda. -/
def deltaBinderIndex : Expr Nat :=
  .lam (.sort .zero) (.app (.const 66 []) (.bvar 0))

/-- The below-binder delta is followed by beta in native conversion. -/
def deltaBinderIndexConv (n : Nat) (Γ : LCtx) :
    ConvT deltaEqEnv n Γ deltaBinderIndex indexId indexFn :=
  .lam _ _ _ _ _ _ _ (.refl _ _ _ (.sort _ _))
    (.trans _ _ _ _ _
      (.app _ _ _ _ _ _ _ (deltaIndexConv n _) (.refl _ _ _ (.bvar _ 0 _ rfl)))
      (.beta _ _ _ _ _ _ (.sort _ _) (.bvar _ 0 _ rfl) (.bvar _ 0 _ rfl)))

/-- Moving the same delta below a binder makes it invisible to the WHNF schedule. -/
theorem delta_binder_schedule_stuck (Γ : LCtx) (ys : List (Expr Nat)) :
    ¬ FirstWhnfMismatch deltaEqEnv Γ [deltaBinderIndex] [indexId] ys := by
  apply firstWhnfMismatch_false_of_normal
  intro x hx
  have heq : x = deltaBinderIndex := by simpa using hx
  subst x
  exact fun _ h => whStepCK_lam_false_aux h rfl

/-- Delta control: the same checked definition succeeds at the head and fails below a binder. -/
theorem delta_index_control (n : Nat) :
    Nonempty (EnvWfT deltaEqEnv) ∧
    Nonempty (ConvT deltaEqEnv n [] (.const 66 []) indexId indexFn) ∧
    FirstWhnfMismatch deltaEqEnv [] [.const 66 []] [indexId] [indexId] ∧
    Nonempty (ConvT deltaEqEnv n [] deltaBinderIndex indexId indexFn) ∧
    deltaBinderIndex ≠ indexId ∧
    ∀ ys, ¬ FirstWhnfMismatch deltaEqEnv [] [deltaBinderIndex] [indexId] ys :=
  ⟨⟨deltaEqEnvWf⟩, ⟨deltaIndexConv n []⟩, delta_index_schedule [],
    ⟨deltaBinderIndexConv n []⟩, by decide, delta_binder_schedule_stuck []⟩

/-- A beta redex in Eq's parameter, hence in the computed constructor index. -/
def computedBetaIndex : Expr Nat := .app (.lam indexFn (.bvar 0)) indexId

/-- Native typing of the non-normal computed constructor index. -/
def computedBetaIndexTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ computedBetaIndex indexFn :=
  .app _ _ _ _ _
    (.lam _ _ _ _ _ (indexFnTy E n Γ) (.bvar _ 0 _ rfl))
    (indexIdTy E n Γ)

/-- The computed constructor index contracts to the already-normal actual index. -/
def computedBetaIndexConv (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ConvT E n Γ computedBetaIndex indexId indexFn :=
  .beta _ _ _ _ _ _ (indexFnTy E n Γ) (.bvar _ 0 _ rfl) (indexIdTy E n Γ)

/-- The actual index is normal; the reducible term is in the parameter position. -/
def computedBetaEqCtx : LCtx :=
  [.assumption (foldApps (.const 63 []) [indexFn, computedBetaIndex, indexId])]

/-- Well-formed native Eq context for the computed-side obstruction. -/
def computedBetaEqCtxWf (n : Nat) : CtxWfT eqEnvT n computedBetaEqCtx :=
  .assumption _ _ _ .nil
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl)
          (indexFnTy eqEnvT n [])) (computedBetaIndexTy eqEnvT n []))
      (indexIdTy eqEnvT n []))

/-- Normalizing only actual indices cannot repair a reducible computed index. -/
theorem computed_beta_schedule_stuck (ys : List (Expr Nat)) :
    ¬ FirstWhnfMismatch eqEnvT computedBetaEqCtx [indexId] [computedBetaIndex] ys := by
  apply firstWhnfMismatch_false_of_normal
  intro x hx
  have heq : x = indexId := by simpa using hx
  subst x
  exact fun _ h => whStepCK_lam_false_aux h rfl

/-- This failure already occurs at head beta, without a binder-normalization issue. -/
theorem computed_beta_index_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n computedBetaEqCtx) ∧
    Nonempty (ConvT eqEnvT n computedBetaEqCtx indexId computedBetaIndex indexFn) ∧
    WhStepCK eqEnvT computedBetaEqCtx computedBetaIndex indexId ∧
    indexId ≠ computedBetaIndex ∧
    ∀ ys, ¬ FirstWhnfMismatch eqEnvT computedBetaEqCtx [indexId] [computedBetaIndex] ys :=
  ⟨⟨pinEqGroupWfT⟩, ⟨computedBetaEqCtxWf n⟩,
    ⟨.symm _ _ _ _ (computedBetaIndexConv eqEnvT n computedBetaEqCtx)⟩,
    .ctx (.beta _ _ _), by decide, computed_beta_schedule_stuck⟩

/-- The proposed completion obligation for one-sided weak-head index normalization. -/
def WhnfIndexComplete (E : ResolvedEnv) : Prop :=
  ∀ (n : Nat) (Γ : LCtx) (A a b : Expr Nat),
    CtxWfT E n Γ → HasTyT E n Γ A (.sort (.succ .zero)) →
    ConvT E n Γ a b A →
    FirstWhnfMismatchStar E Γ [b] [a] [b]

/-- A native kernel counterexample to completion by actual-side WHNF normalization. -/
theorem not_whnfIndexComplete_eqEnvT : ¬ WhnfIndexComplete eqEnvT := by
  intro h
  have hr := h 0 computedBetaEqCtx indexFn indexId computedBetaIndex
    (computedBetaEqCtxWf 0) (indexFnTy eqEnvT 0 computedBetaEqCtx)
    (.symm _ _ _ _ (computedBetaIndexConv eqEnvT 0 computedBetaEqCtx))
  have heq : [computedBetaIndex] = [indexId] :=
    firstWhnfMismatchStar_eq_of_normal (by
      intro x hx
      have hx' : x = indexId := by simpa using hx
      subst x
      exact fun _ hs => whStepCK_lam_false_aux hs rfl) hr
  exact (by decide : [computedBetaIndex] ≠ [indexId]) heq

/-- Even when the computed index is normal, the binder control cannot complete. -/
theorem binder_index_no_alignment :
    ¬ FirstWhnfMismatchStar eqEnvT binderEqCtx [indexId] [indexBinderBeta] [indexId] := by
  intro hr
  have heq : [indexId] = [indexBinderBeta] :=
    firstWhnfMismatchStar_eq_of_normal (by
      intro x hx
      have hx' : x = indexBinderBeta := by simpa using hx
      subst x
      exact (binder_indices_normal binderEqCtx).1) hr
  exact (by decide : [indexId] ≠ [indexBinderBeta]) heq

/-- Native eta remains distinct after any number of selected weak-head index steps. -/
theorem eta_index_no_alignment :
    ¬ FirstWhnfMismatchStar eqEnvT etaEqCtx [.bvar 1] [etaIndex] [.bvar 1] := by
  intro hr
  have heq : [.bvar 1] = [etaIndex] :=
    firstWhnfMismatchStar_eq_of_normal (by
      intro x hx
      have hx' : x = etaIndex := by simpa using hx
      subst x
      exact eta_indices_normal.1) hr
  exact (by decide : [Expr.bvar 1] ≠ [etaIndex]) heq

/-! ## The complete weak-head scheduler comparator -/

/-- The constructor indices computed by the same field-free/projection canon as CK. -/
def scheduledCanonIdx {E : ResolvedEnv} (w : IotaWitness E) (x : Expr Nat) :
    List (Expr Nat) :=
  resultIdxAt w (w.preMajor.take w.nparams)
    (if w.fields = [] then [] else projFields w x)

/-- Candidate (b), with its index strategy explicitly fixed to landed CK weak-head steps.
The original CK rules remain available; new index steps and their head/major contexts are
closed under the same scheduling restrictions.  Only non-constructor K majors admit an
index step, and ordinary recursor-major descent retains both original non-K guards. -/
inductive WhStepIndexCK2 (E : ResolvedEnv) (Γ : LCtx) : Expr Nat → Expr Nat → Prop
  | ck {a b : Expr Nat} (hs : WhStepCK E Γ a b) : WhStepIndexCK2 E Γ a b
  | index {w : IotaWitness E} {x : Expr Nat} {idxs : List (Expr Nat)}
      (hK : KFreeW w ∨ KFieldW w) (hnc : ¬ IsCtorSpine E x)
      (hs : FirstWhnfMismatch E Γ (redexIdx w) (scheduledCanonIdx w x) idxs) :
      WhStepIndexCK2 E Γ (recCall (.const w.recRef w.ls) w.preMajor x)
        (recCall (.const w.recRef w.ls)
          (w.preMajor.take (w.nparams + 1 + w.nMinors) ++ idxs) x)
  | recMajor {r : Nat} {m : CheckedMember} {ls : List Level} {pre : List (Expr Nat)}
      {x x' : Expr Nat}
      (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
      (hlen : pre.length + 1 = piCount m.mtype)
      (hnK : ¬ KFreeRec E r) (hnP : ¬ KProjRec E r)
      (hs : WhStepIndexCK2 E Γ x x') :
      WhStepIndexCK2 E Γ (recCall (.const r ls) pre x) (recCall (.const r ls) pre x')
  | appHead {f f' a : Expr Nat} (hs : WhStepIndexCK2 E Γ f f') :
      WhStepIndexCK2 E Γ (.app f a) (.app f' a)

/-- The original Eq-gap witness after its actual beta index contracts. -/
def indexEqGapAlignedW : IotaWitness eqEnvT :=
  { eqGapW with
    preMajor := [.bvar 2, .bvar 1, eqGapMot, .sort .zero, .bvar 1]
    hpre := rfl
    hminor := rfl
    hctorAfter := rfl }

/-- Positive control: candidate (b) repairs the original gap in exactly index-beta then K. -/
theorem redR_whStepIndexCK2_eqGap :
    RedR (WhStepIndexCK2 eqEnvT) eqGapCtx eqGapRedex (.sort .zero) := by
  refine .step (.index (w := eqGapW) (Or.inl ⟨rfl, rfl, rfl⟩)
    not_isCtorSpine_bvar firstWhnfMismatch_eqGap) ?_
  exact .step (.ck (.kStar (w := indexEqGapAlignedW) ⟨rfl, rfl, rfl⟩
    not_isCtorSpine_bvar rfl)) (.refl _)

/-- Source invariant for the new steps beyond the original CK relation. -/
def ScheduledRecSource (E : ResolvedEnv) (e : Expr Nat) : Prop :=
  ∃ (r : Nat) (ls : List Level) (xs : List (Expr Nat)) (m : CheckedMember),
    e = foldApps (.const r ls) xs ∧ E.members r = some m ∧
    m.mclass = .recursorM ∧ 0 < xs.length ∧ piCount m.mtype ≤ xs.length

/-- Appending an argument preserves the saturated-recursion source invariant. -/
theorem scheduledRecSource_app {f a : Expr Nat} (h : ScheduledRecSource E f) :
    ScheduledRecSource E (.app f a) := by
  obtain ⟨r, ls, xs, m, rfl, hm, hr, hp, hl⟩ := h
  exact ⟨r, ls, xs ++ [a], m, (foldApps_snoc _ _ _).symm, hm, hr,
    by simp, by simpa using Nat.le_trans hl (Nat.le_add_right xs.length 1)⟩

/-- Every step is either old CK or has a saturated recursor source. -/
theorem whStepIndexCK2_ck_or_saturated {a b : Expr Nat}
    (hs : WhStepIndexCK2 E Γ a b) : WhStepCK E Γ a b ∨ ScheduledRecSource E a := by
  induction hs with
  | ck hs => exact .inl hs
  | index hK hnc hs =>
      rename_i w x idxs
      refine .inr ⟨w.recRef, w.ls, w.preMajor ++ [x], w.recMember,
        ?_, w.hrec, w.hrecK, by simp, ?_⟩
      · rw [recCall_eq_app, foldApps_snoc]
      · have h₁ := w.hpre
        have h₂ := w.hnmin
        simp only [List.length_append, List.length_singleton]
        omega
  | @recMajor r m ls pre x x' hm hr hl _ _ _ _ =>
      refine .inr ⟨r, ls, pre ++ [x], m, ?_, hm, hr, by simp, ?_⟩
      · rw [recCall_eq_app, foldApps_snoc]
      · simpa using Nat.le_of_eq hl.symm
  | appHead _ ih =>
      exact ih.elim (fun hs => .inl (.appHead hs))
        (fun hs => .inr (scheduledRecSource_app hs))

/-- A scheduled-recursion source always has an outer application. -/
theorem scheduledRecSource_is_app {a : Expr Nat} (h : ScheduledRecSource E a) :
    ∃ f x, a = .app f x := by
  obtain ⟨r, ls, xs, m, he, _, _, hp, _⟩ := h
  rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
  · simp at hp
  · exact ⟨_, x, he.trans (foldApps_snoc _ _ _)⟩

/-- At a fixed constant spine the invariant pins its class and arity. -/
theorem scheduledRecSource_spine {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) {ls : List Level} {xs : List (Expr Nat)}
    (h : ScheduledRecSource E (foldApps (.const r ls) xs)) :
    m.mclass = .recursorM ∧ piCount m.mtype ≤ xs.length := by
  obtain ⟨s, us, ys, mm, he, hs, hr, _, hl⟩ := h
  obtain ⟨hhead, hargs⟩ := foldApps_const_inj he
  obtain ⟨rfl, rfl⟩ := Expr.const.inj hhead
  obtain rfl := Option.some.inj (hm.symm.trans hs)
  exact ⟨hr, hargs ▸ hl⟩

/-- Sorts remain normal for the entire candidate-(b) grammar. -/
theorem normalR_sortIndexCK2 (Γ : LCtx) (u : Level) :
    NormalR (WhStepIndexCK2 E) Γ (.sort u) := by
  intro e h
  rcases whStepIndexCK2_ck_or_saturated h with h | h
  · exact whStepCK_sort_false_aux h rfl
  · obtain ⟨f, a, he⟩ := scheduledRecSource_is_app h
    exact Expr.noConfusion he

/-- Pi types remain normal; index normalization does not become outer readback under binders. -/
theorem normalR_piIndexCK2 (Γ : LCtx) (A B : Expr Nat) :
    NormalR (WhStepIndexCK2 E) Γ (.pi A B) := by
  intro e h
  rcases whStepIndexCK2_ck_or_saturated h with h | h
  · exact whStepCK_pi_false_aux h rfl
  · obtain ⟨f, a, he⟩ := scheduledRecSource_is_app h
    exact Expr.noConfusion he

/-- Lambda abstractions remain normal in the complete comparator. -/
theorem normalR_lamIndexCK2 (Γ : LCtx) (A body : Expr Nat) :
    NormalR (WhStepIndexCK2 E) Γ (.lam A body) := by
  intro e h
  rcases whStepIndexCK2_ck_or_saturated h with h | h
  · exact whStepCK_lam_false_aux h rfl
  · obtain ⟨f, a, he⟩ := scheduledRecSource_is_app h
    exact Expr.noConfusion he

/-- Constructor spines remain normal, including under newly enabled recursor contexts. -/
theorem normalR_ctorIndexCK2 (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : m.mclass = .constructorM)
    (Γ : LCtx) (ls : List Level) (xs : List (Expr Nat)) :
    NormalR (WhStepIndexCK2 E) Γ (foldApps (.const r ls) xs) := by
  intro e h
  rcases whStepIndexCK2_ck_or_saturated h with h | h
  · exact whStepCK_ctorSpine_false_aux hW hm hr h xs rfl
  · exact MemberClass.noConfusion ((scheduledRecSource_spine hm h).1.symm.trans hr)

/-- Admitted family spines remain normal for the complete candidate. -/
theorem normalR_famAppIndexCK2 (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hr : m.mclass = .inductiveM)
    (Γ : LCtx) (ls : List Level) (xs : List (Expr Nat)) :
    NormalR (WhStepIndexCK2 E) Γ (foldApps (.const r ls) xs) := by
  intro e h
  rcases whStepIndexCK2_ck_or_saturated h with h | h
  · exact whStepCK_famApp_false_aux hW hm hr h rfl
  · exact MemberClass.noConfusion ((scheduledRecSource_spine hm h).1.symm.trans hr)

/-- The whole candidate-(b) relation supplies the unchanged landed readback interface. -/
theorem readbackLaws_whStepIndexCK2 (E : ResolvedEnv) :
    ReadbackLaws E (WhStepIndexCK2 E) where
  sort_normal := normalR_sortIndexCK2
  pi_normal := normalR_piIndexCK2
  famApp_normal := fun hW Γ _ _ hm hr ls xs => normalR_famAppIndexCK2 hW hm hr Γ ls xs
  appHead := fun _ _ _ _ hs => .appHead hs
  beta := fun _ A body arg => .ck (.ctx (.beta A body arg))

/-- The new index arm is saturated, so partial recursor prefixes still cannot step. -/
theorem whStepIndexCK2_recPrefix_false_aux {r : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
    {a e : Expr Nat} (h : WhStepIndexCK2 E Γ a e) :
    ∀ {ls : List Level} {xs : List (Expr Nat)}, a = foldApps (.const r ls) xs →
      xs.length + 1 ≤ piCount m.mtype → False := by
  induction h with
  | ck hs =>
      intro ls xs heq hlen
      exact whStepCK_recPrefix_false_aux hW hm hrec hs heq hlen
  | index hK hnc hs =>
      rename_i w x idxs
      intro ls xs heq hlen
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, hargs⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm' : w.recMember = m :=
        Option.some.inj (w.hrec.symm.trans (hrr.symm ▸ hm))
      have h1 := w.hpre
      have h2 := w.hnmin
      rw [hm'] at h2
      have hlenEq := congrArg List.length hargs
      simp only [List.length_append, List.length_singleton] at hlenEq
      omega
  | recMajor hm' hrec' hlen' hnK hnP hs' =>
      intro ls xs heq hlen
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, hargs⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm'' : _ = m := Option.some.inj (hm'.symm.trans (hrr.symm ▸ hm))
      subst hm''
      have hlenEq := congrArg List.length hargs
      simp only [List.length_append, List.length_singleton] at hlenEq
      omega
  | appHead hf ih =>
      intro ls xs heq hlen
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hf' _
        exact ih hf' (by
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen
          omega)

/-- A field-free Eq witness with arbitrary type, parameter, motive, and actual index.
The stored constructor substitution is written literally; its first family argument does
not affect the computed result index, which is always the parameter `a`. -/
def eqIndexW (A a mot b : Expr Nat) : IotaWitness eqEnvT :=
  { eqGapW with
    preMajor := [A, a, mot, .sort .zero, b]
    ctorParams := [A, a]
    hctorParams := rfl
    hpre := rfl
    hminor := rfl
    ctorAfterParams := foldApps (.const 63 []) [instantiate0 a (lift 0 1 A), a, a]
    hctorAfter := rfl
    hctorTel := rfl
    hfamTel := rfl
    hresTel := rfl }

/-- A field-free Eq witness at the controls' fixed function type. -/
def eqFnIndexW (a mot b : Expr Nat) : IotaWitness eqEnvT :=
  eqIndexW indexFn a mot b

/-- A saturated Eq recursor at a variable proof major. -/
def eqIndexRedex (A a mot b : Expr Nat) : Expr Nat :=
  recCall (.const 65 [.succ (.succ .zero)]) [A, a, mot, .sort .zero, b] (.bvar 0)

/-- The corresponding Eq recursor specialized to the controls' function index type. -/
def eqFnIndexRedex (a mot b : Expr Nat) : Expr Nat :=
  eqIndexRedex indexFn a mot b

/-- Every legacy Eq witness uses the actual admitted field-free constructor. -/
theorem eqWitnessCtorData (w : IotaWitness eqEnvT) (hr : w.recRef = 65) :
    w.ctorMember = eqReflT ∧ w.fields = [] := by
  obtain ⟨hnp, hni, hnm⟩ := eqWitnessIndexCut w hr
  have hfr : w.familyRef = 63 := by
    have h := w.hrecIdx
    rw [hr, hnm] at h
    omega
  have hci : w.ctorIdx = 0 := Nat.lt_one_iff.mp (hnm ▸ w.hidx)
  have hcr : w.ctorRef = 64 := by
    rw [w.hctorIdx, hfr, hci]
  have hcm : w.ctorMember = eqReflT := by
    have h := w.hctor
    rw [hcr] at h
    exact (Option.some.inj h).symm
  have hfl : w.fields.length = 0 := by
    have h := w.hnpar
    rw [hnp, hcm] at h
    change 2 + w.fields.length = 2 at h
    omega
  exact ⟨hcm, List.eq_nil_of_length_eq_zero hfl⟩

/-- CK is stuck on every such Eq redex whose actual and computed indices differ. -/
theorem whStepCK_eqIndex_false_aux {A a mot b s t : Expr Nat}
    (hne : b ≠ a) (hs : WhStepCK eqEnvT Γ s t) :
    s = eqIndexRedex A a mot b → False := by
  induction hs with
  | ctx hctx =>
      intro heq
      subst heq
      exact whStepCtx_recCall_nonCtorMajor_aux pinEqGroupWfT hctx
        (w := eqIndexW A a mot b) rfl not_isCtorSpine_bvar
  | kStar hK hnc hidx =>
      rename_i w x
      intro heq
      rw [eqIndexRedex, recCall_eq_app] at heq
      injection heq with hf _
      have hf0 : foldApps (.const w.recRef w.ls) w.preMajor =
          foldApps (.const 65 [.succ (.succ .zero)]) [A, a, mot, .sort .zero, b] := hf
      obtain ⟨hconst, hargs⟩ := foldApps_const_inj hf0
      injection hconst with hrr hll
      obtain ⟨hnp, hni, hnm⟩ := eqWitnessIndexCut w hrr
      obtain ⟨hcm, hfields⟩ := eqWitnessCtorData w hrr
      unfold redexIdx resultIdxAt at hidx
      rw [hargs, hnp, hnm, hcm, hll] at hidx
      have hidx' : [b] = [a] := hidx
      exact hne (List.cons.inj hidx').1
  | kProj hK hnc hf hidx =>
      rename_i w x
      intro heq
      rw [eqIndexRedex, recCall_eq_app] at heq
      injection heq with hf' _
      have hf0 : foldApps (.const w.recRef w.ls) w.preMajor =
          foldApps (.const 65 [.succ (.succ .zero)]) [A, a, mot, .sort .zero, b] := hf'
      obtain ⟨hconst, _⟩ := foldApps_const_inj hf0
      injection hconst with hrr _
      exact hK.1 (eqWitnessCtorData w hrr).2
  | recMajor hm hrec hlen hnK hnP hs =>
      intro heq
      rw [eqIndexRedex, recCall_eq_app] at heq
      injection heq with hf _
      have hf0 : foldApps (.const _ _) _ =
          foldApps (.const 65 [.succ (.succ .zero)]) [A, a, mot, .sort .zero, b] := hf
      obtain ⟨hconst, _⟩ := foldApps_const_inj hf0
      injection hconst with hrr _
      exact hnK (hrr.symm ▸ ⟨eqGapW, rfl, rfl, rfl, rfl⟩)
  | appHead hf ih =>
      intro heq
      rw [eqIndexRedex, recCall_eq_app] at heq
      injection heq with hf' _
      exact whStepCK_recPrefix_false pinEqGroupWfT
        (rfl : eqEnvT.members 65 = some eqRecT) rfl
        [A, a, mot, .sort .zero, b] (by change 6 ≤ 6; omega) _ (hf' ▸ hf)

/-- Function-index specialization of the generic old-CK source exclusion. -/
theorem whStepCK_eqFnIndex_false_aux {a mot b s t : Expr Nat}
    (hne : b ≠ a) (hs : WhStepCK eqEnvT Γ s t) :
    s = eqFnIndexRedex a mot b → False :=
  whStepCK_eqIndex_false_aux hne hs

/-- Candidate (b) cannot escape a mismatching Eq recursor with a WHNF actual index. -/
theorem whStepIndexCK2_eqIndex_false_aux {A a mot b s t : Expr Nat}
    (hne : b ≠ a) (hnormal : NormalR (WhStepCK eqEnvT) Γ b)
    (hs : WhStepIndexCK2 eqEnvT Γ s t) : s = eqIndexRedex A a mot b → False := by
  induction hs with
  | ck hck => exact whStepCK_eqIndex_false_aux hne hck
  | index hK hnc hidx =>
      rename_i w x idxs
      intro heq
      rw [eqIndexRedex, recCall_eq_app] at heq
      injection heq with hf _
      have hf0 : foldApps (.const w.recRef w.ls) w.preMajor =
          foldApps (.const 65 [.succ (.succ .zero)]) [A, a, mot, .sort .zero, b] := hf
      obtain ⟨hconst, hargs⟩ := foldApps_const_inj hf0
      injection hconst with hrr _
      obtain ⟨hnp, hni, hnm⟩ := eqWitnessIndexCut w hrr
      have hactual : redexIdx w = [b] := by
        unfold redexIdx
        rw [hargs, hnp, hnm]
        rfl
      rw [hactual] at hidx
      exact firstWhnfMismatch_false_of_normal (by
        intro z hz
        have hz' : z = b := by simpa using hz
        subst z
        exact hnormal) hidx
  | recMajor hm hrec hlen hnK hnP hs =>
      intro heq
      rw [eqIndexRedex, recCall_eq_app] at heq
      injection heq with hf _
      have hf0 : foldApps (.const _ _) _ =
          foldApps (.const 65 [.succ (.succ .zero)]) [A, a, mot, .sort .zero, b] := hf
      obtain ⟨hconst, _⟩ := foldApps_const_inj hf0
      injection hconst with hrr _
      exact hnK (hrr.symm ▸ ⟨eqGapW, rfl, rfl, rfl, rfl⟩)
  | appHead hf ih =>
      intro heq
      rw [eqIndexRedex, recCall_eq_app] at heq
      injection heq with hf' _
      exact whStepIndexCK2_recPrefix_false_aux pinEqGroupWfT
        (rfl : eqEnvT.members 65 = some eqRecT) rfl hf hf' (by change 6 ≤ 6; omega)

/-- Function-index specialization of the generic candidate-(b) source exclusion. -/
theorem whStepIndexCK2_eqFnIndex_false_aux {a mot b s t : Expr Nat}
    (hne : b ≠ a) (hnormal : NormalR (WhStepCK eqEnvT) Γ b)
    (hs : WhStepIndexCK2 eqEnvT Γ s t) : s = eqFnIndexRedex a mot b → False :=
  whStepIndexCK2_eqIndex_false_aux hne hnormal hs

/-- Generic full candidate-(b) normality for a mismatching Eq recursor with a WHNF actual index. -/
theorem normalR_whStepIndexCK2_eqIndex {A a mot b : Expr Nat}
    (hne : b ≠ a) (hnormal : NormalR (WhStepCK eqEnvT) Γ b) :
    NormalR (WhStepIndexCK2 eqEnvT) Γ (eqIndexRedex A a mot b) :=
  fun _ hs => whStepIndexCK2_eqIndex_false_aux hne hnormal hs rfl

/-- The full comparator redex is normal, not merely its selected index list. -/
theorem normalR_whStepIndexCK2_eqFnIndex {a mot b : Expr Nat}
    (hne : b ≠ a) (hnormal : NormalR (WhStepCK eqEnvT) Γ b) :
    NormalR (WhStepIndexCK2 eqEnvT) Γ (eqFnIndexRedex a mot b) :=
  fun _ hs => whStepIndexCK2_eqFnIndex_false_aux hne hnormal hs rfl

/-- The constant motive used at the binder control. -/
def binderIndexMot : Expr Nat :=
  .lam indexFn
    (.lam (foldApps (.const 63 []) [indexFn, indexId, .bvar 0]) (.sort (.succ .zero)))

/-- The constant motive used at the eta control; `f` is shifted by the index binder. -/
def etaIndexMot : Expr Nat :=
  .lam indexFn
    (.lam (foldApps (.const 63 []) [indexFn, .bvar 2, .bvar 0]) (.sort (.succ .zero)))

/-- Full Eq recursor with the internal-beta mismatch. -/
def binderIndexRedex : Expr Nat :=
  eqFnIndexRedex indexId binderIndexMot indexBinderBeta

/-- Full Eq recursor with the native eta mismatch. -/
def etaIndexRedex : Expr Nat := eqFnIndexRedex (.bvar 1) etaIndexMot etaIndex

/-- The complete candidate-(b) binder control has no readback step. -/
theorem binderIndexRedex_normal :
    NormalR (WhStepIndexCK2 eqEnvT) binderEqCtx binderIndexRedex :=
  normalR_whStepIndexCK2_eqFnIndex (by decide) (binder_indices_normal binderEqCtx).1

/-- The complete candidate-(b) eta control has no readback step. -/
theorem etaIndexRedex_normal :
    NormalR (WhStepIndexCK2 eqEnvT) etaEqCtx etaIndexRedex :=
  normalR_whStepIndexCK2_eqFnIndex (by decide) eta_indices_normal.1

/-- In particular, no finite binder readback reaches a sort. -/
theorem binderIndexRedex_not_sort (u : Level) :
    ¬ RedR (WhStepIndexCK2 eqEnvT) binderEqCtx binderIndexRedex (.sort u) := by
  intro hr
  exact Expr.noConfusion (redR_of_normal binderIndexRedex_normal hr)

/-- In particular, no finite eta readback reaches a sort. -/
theorem etaIndexRedex_not_sort (u : Level) :
    ¬ RedR (WhStepIndexCK2 eqEnvT) etaEqCtx etaIndexRedex (.sort u) := by
  intro hr
  exact Expr.noConfusion (redR_of_normal etaIndexRedex_normal hr)

/-! ## Native conversions of the complete recursor controls -/

/-- The binder control's Eq family at an arbitrary right index. -/
def binderIndexFamily (b : Expr Nat) : Expr Nat :=
  foldApps (.const 63 []) [indexFn, indexId, b]

/-- The literal reflexivity constructor used by the binder certificate. -/
def binderIndexCtor : Expr Nat := foldApps (.const 64 []) [indexFn, indexId]

/-- Native proposition typing of the binder family. -/
def binderIndexFamilyTy (n : Nat) (Γ : LCtx) {b : Expr Nat}
    (hb : HasTyT eqEnvT n Γ b indexFn) :
    HasTyT eqEnvT n Γ (binderIndexFamily b) (.sort .zero) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl)
        (indexFnTy eqEnvT n Γ)) (indexIdTy eqEnvT n Γ)) hb

/-- Native typing of the binder control's canon. -/
def binderIndexCtorTy (n : Nat) (Γ : LCtx) :
    HasTyT eqEnvT n Γ binderIndexCtor (binderIndexFamily indexId) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (.const _ 64 [] eqReflT rfl rfl rfl)
      (indexFnTy eqEnvT n Γ)) (indexIdTy eqEnvT n Γ)

/-- The inner constant-motive lambda in its actual bound context. -/
def binderIndexMotBodyTy (n : Nat) (Γ : LCtx) :
    HasTyT eqEnvT n (.assumption indexFn :: Γ)
      (.lam (binderIndexFamily (.bvar 0)) (.sort (.succ .zero)))
      (.pi (binderIndexFamily (.bvar 0)) (.sort (.succ (.succ .zero)))) :=
  .lam _ _ _ _ _
    (binderIndexFamilyTy n _ (.bvar (.assumption indexFn :: Γ) 0 indexFn rfl))
    (.sort _ _)

/-- Native typing of the full constant motive. -/
def binderIndexMotTy (n : Nat) (Γ : LCtx) :
    HasTyT eqEnvT n Γ binderIndexMot
      (.pi indexFn (.pi (binderIndexFamily (.bvar 0)) (.sort (.succ (.succ .zero))))) :=
  .lam _ _ _ _ _ (indexFnTy eqEnvT n Γ) (binderIndexMotBodyTy n Γ)

/-- The constant motive computes at every typed index and every typed proof. -/
def binderIndexMotAtConv (n : Nat) (Γ : LCtx) {b p : Expr Nat}
    (hb : HasTyT eqEnvT n Γ b indexFn)
    (hp : HasTyT eqEnvT n Γ p (binderIndexFamily b)) :
    ConvT eqEnvT n Γ (.app (.app binderIndexMot b) p)
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
  have hc : ConvT eqEnvT n Γ (.app binderIndexMot b)
      (.lam (binderIndexFamily b) (.sort (.succ .zero)))
      (.pi (binderIndexFamily b) (.sort (.succ (.succ .zero)))) :=
    .beta _ _ _ _ _ _ (indexFnTy eqEnvT n Γ) (binderIndexMotBodyTy n Γ) hb
  exact .trans _ _ _ _ _
    (.app _ _ _ _ _ _ _ hc (.refl _ _ _ hp))
    (.beta _ _ _ _ _ _ (binderIndexFamilyTy n Γ hb) (.sort _ _) hp)

/-- Native typing of the complete binder recursor at either variable or constructor proof. -/
def binderIndexRecTy (n : Nat) (Γ : LCtx) {p : Expr Nat}
    (hp : HasTyT eqEnvT n Γ p (binderIndexFamily indexBinderBeta)) :
    HasTyT eqEnvT n Γ
      (recCall (.const 65 [.succ (.succ .zero)])
        [indexFn, indexId, binderIndexMot, .sort .zero, indexBinderBeta] p)
      (.sort (.succ .zero)) := by
  have hminor : HasTyT eqEnvT n Γ (.sort .zero)
      (.app (.app binderIndexMot indexId) binderIndexCtor) :=
    .conv _ _ _ _ _ (.sort _ _)
      (.symm _ _ _ _ (binderIndexMotAtConv n Γ
        (indexIdTy eqEnvT n Γ) (binderIndexCtorTy n Γ)))
  have hpre : HasTyT eqEnvT n Γ
      (foldApps (.const 65 [.succ (.succ .zero)])
        [indexFn, indexId, binderIndexMot, .sort .zero, indexBinderBeta]) _ :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _
            (.app _ _ _ _ _ (.const _ 65 [.succ (.succ .zero)] eqRecT rfl rfl rfl)
              (indexFnTy eqEnvT n Γ)) (indexIdTy eqEnvT n Γ))
          (binderIndexMotTy n Γ)) hminor) (indexBinderBetaTy eqEnvT n Γ)
  exact .conv _ _ _ _ _ (.app _ _ _ _ _ hpre hp)
    (binderIndexMotAtConv n Γ (indexBinderBetaTy eqEnvT n Γ) hp)

/-- The complete stuck binder recursor is nevertheless natively convertible to `Sort 0`. -/
def binderIndexRedexConv (n : Nat) :
    ConvT eqEnvT n binderEqCtx binderIndexRedex (.sort .zero) (.sort (.succ .zero)) := by
  have hmajor : HasTyT eqEnvT n binderEqCtx (.bvar 0)
      (binderIndexFamily indexBinderBeta) := .bvar binderEqCtx 0 _ rfl
  have hfamily : ConvT eqEnvT n binderEqCtx (binderIndexFamily indexId)
      (binderIndexFamily indexBinderBeta) (.sort .zero) :=
    .app _ _ _ _ _ _ _
      (.app _ _ _ _ _ _ _
        (.app _ _ _ _ _ _ _ (.refl _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl))
          (.refl _ _ _ (indexFnTy eqEnvT n binderEqCtx)))
        (.refl _ _ _ (indexIdTy eqEnvT n binderEqCtx)))
      (.symm _ _ _ _ (indexBinderBetaConv eqEnvT n binderEqCtx))
  have hcanon : HasTyT eqEnvT n binderEqCtx binderIndexCtor
      (binderIndexFamily indexBinderBeta) :=
    .conv _ _ _ _ _ (binderIndexCtorTy n binderEqCtx) hfamily
  exact convT_iotaStarK_bvar (w := eqFnIndexW indexId binderIndexMot indexBinderBeta)
    hmajor hcanon (binderIndexFamilyTy n binderEqCtx (indexBinderBetaTy eqEnvT n binderEqCtx))
    (binderIndexRecTy n binderEqCtx hcanon) (.sort _ _)
    (binderIndexRecTy n binderEqCtx hmajor)

/-- The eta control's Eq family in its original context. -/
def etaIndexFamily (b : Expr Nat) : Expr Nat :=
  foldApps (.const 63 []) [indexFn, .bvar 1, b]

/-- The literal reflexivity constructor at the neutral function. -/
def etaIndexCtor : Expr Nat := foldApps (.const 64 []) [indexFn, .bvar 1]

/-- Native typing of the neutral-function index. -/
def etaIndexParamTy (n : Nat) : HasTyT eqEnvT n etaEqCtx (.bvar 1) indexFn :=
  .bvar etaEqCtx 1 indexFn rfl

/-- Native typing of its eta expansion. -/
def etaIndexTy (n : Nat) : HasTyT eqEnvT n etaEqCtx etaIndex indexFn :=
  .lam _ _ _ _ _ (.sort _ _)
    (.app _ _ _ _ _
      (.bvar (.assumption (.sort .zero) :: etaEqCtx) 2 indexFn rfl)
      (.bvar (.assumption (.sort .zero) :: etaEqCtx) 0 (.sort .zero) rfl))

/-- Native proposition typing of the eta family. -/
def etaIndexFamilyTy (n : Nat) {b : Expr Nat}
    (hb : HasTyT eqEnvT n etaEqCtx b indexFn) :
    HasTyT eqEnvT n etaEqCtx (etaIndexFamily b) (.sort .zero) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl)
        (indexFnTy eqEnvT n etaEqCtx)) (etaIndexParamTy n)) hb

/-- Native typing of the eta control's reflexivity constructor. -/
def etaIndexCtorTy (n : Nat) :
    HasTyT eqEnvT n etaEqCtx etaIndexCtor (etaIndexFamily (.bvar 1)) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (.const _ 64 [] eqReflT rfl rfl rfl)
      (indexFnTy eqEnvT n etaEqCtx)) (etaIndexParamTy n)

/-- The eta motive's inner lambda, where the original function is at slot 2. -/
def etaIndexMotBodyTy (n : Nat) :
    HasTyT eqEnvT n (.assumption indexFn :: etaEqCtx)
      (.lam (foldApps (.const 63 []) [indexFn, .bvar 2, .bvar 0]) (.sort (.succ .zero)))
      (.pi (foldApps (.const 63 []) [indexFn, .bvar 2, .bvar 0])
        (.sort (.succ (.succ .zero)))) :=
  .lam _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl)
          (indexFnTy eqEnvT n (.assumption indexFn :: etaEqCtx)))
        (.bvar (.assumption indexFn :: etaEqCtx) 2 indexFn rfl))
      (.bvar (.assumption indexFn :: etaEqCtx) 0 indexFn rfl))
    (.sort _ _)

/-- Native typing of the eta control's complete constant motive. -/
def etaIndexMotTy (n : Nat) :
    HasTyT eqEnvT n etaEqCtx etaIndexMot
      (.pi indexFn
        (.pi (foldApps (.const 63 []) [indexFn, .bvar 2, .bvar 0])
          (.sort (.succ (.succ .zero))))) :=
  .lam _ _ _ _ _ (indexFnTy eqEnvT n etaEqCtx) (etaIndexMotBodyTy n)

/-- The eta control's motive computes at arbitrary typed indices and proof arguments. -/
def etaIndexMotAtConv (n : Nat) {b p : Expr Nat}
    (hb : HasTyT eqEnvT n etaEqCtx b indexFn)
    (hp : HasTyT eqEnvT n etaEqCtx p (etaIndexFamily b)) :
    ConvT eqEnvT n etaEqCtx (.app (.app etaIndexMot b) p)
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
  have hc : ConvT eqEnvT n etaEqCtx (.app etaIndexMot b)
      (.lam (etaIndexFamily b) (.sort (.succ .zero)))
      (.pi (etaIndexFamily b) (.sort (.succ (.succ .zero)))) :=
    .beta _ _ _ _ _ _ (indexFnTy eqEnvT n etaEqCtx) (etaIndexMotBodyTy n) hb
  exact .trans _ _ _ _ _
    (.app _ _ _ _ _ _ _ hc (.refl _ _ _ hp))
    (.beta _ _ _ _ _ _ (etaIndexFamilyTy n hb) (.sort _ _) hp)

/-- Native typing of the complete eta recursor at either choice of proof major. -/
def etaIndexRecTy (n : Nat) {p : Expr Nat}
    (hp : HasTyT eqEnvT n etaEqCtx p (etaIndexFamily etaIndex)) :
    HasTyT eqEnvT n etaEqCtx
      (recCall (.const 65 [.succ (.succ .zero)])
        [indexFn, .bvar 1, etaIndexMot, .sort .zero, etaIndex] p)
      (.sort (.succ .zero)) := by
  have hminor : HasTyT eqEnvT n etaEqCtx (.sort .zero)
      (.app (.app etaIndexMot (.bvar 1)) etaIndexCtor) :=
    .conv _ _ _ _ _ (.sort _ _)
      (.symm _ _ _ _ (etaIndexMotAtConv n (etaIndexParamTy n) (etaIndexCtorTy n)))
  have hpre : HasTyT eqEnvT n etaEqCtx
      (foldApps (.const 65 [.succ (.succ .zero)])
        [indexFn, .bvar 1, etaIndexMot, .sort .zero, etaIndex]) _ :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _
            (.app _ _ _ _ _ (.const _ 65 [.succ (.succ .zero)] eqRecT rfl rfl rfl)
              (indexFnTy eqEnvT n etaEqCtx)) (etaIndexParamTy n))
          (etaIndexMotTy n)) hminor) (etaIndexTy n)
  exact .conv _ _ _ _ _ (.app _ _ _ _ _ hpre hp)
    (etaIndexMotAtConv n (etaIndexTy n) hp)

/-- The complete eta recursor has a native K conversion despite being stuck for candidate (b). -/
def etaIndexRedexConv (n : Nat) :
    ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) (.sort (.succ .zero)) := by
  have hmajor : HasTyT eqEnvT n etaEqCtx (.bvar 0)
      (etaIndexFamily etaIndex) := .bvar etaEqCtx 0 _ rfl
  have hfamily : ConvT eqEnvT n etaEqCtx (etaIndexFamily (.bvar 1))
      (etaIndexFamily etaIndex) (.sort .zero) :=
    .app _ _ _ _ _ _ _
      (.app _ _ _ _ _ _ _
        (.app _ _ _ _ _ _ _ (.refl _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl))
          (.refl _ _ _ (indexFnTy eqEnvT n etaEqCtx)))
        (.refl _ _ _ (etaIndexParamTy n)))
      (.symm _ _ _ _ (etaIndexConv n))
  have hcanon : HasTyT eqEnvT n etaEqCtx etaIndexCtor (etaIndexFamily etaIndex) :=
    .conv _ _ _ _ _ (etaIndexCtorTy n) hfamily
  exact convT_iotaStarK_bvar (w := eqFnIndexW (.bvar 1) etaIndexMot etaIndex)
    hmajor hcanon (etaIndexFamilyTy n (etaIndexTy n))
    (etaIndexRecTy n hcanon) (.sort _ _) (etaIndexRecTy n hmajor)

/-- Fully typed countermodel for candidate (b), at an admitted Eq environment and context. -/
theorem binder_readback_countermodel (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n binderEqCtx) ∧
    Nonempty (ConvT eqEnvT n binderEqCtx (.sort .zero) binderIndexRedex (.sort (.succ .zero))) ∧
    NormalR (WhStepIndexCK2 eqEnvT) binderEqCtx binderIndexRedex ∧
    ∀ u, ¬ RedR (WhStepIndexCK2 eqEnvT) binderEqCtx binderIndexRedex (.sort u) :=
  ⟨⟨pinEqGroupWfT⟩, ⟨binderEqCtxWf n⟩, ⟨.symm _ _ _ _ (binderIndexRedexConv n)⟩,
    binderIndexRedex_normal, binderIndexRedex_not_sort⟩

/-- Fully typed countermodel exposing the independent native eta boundary. -/
theorem eta_readback_countermodel (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx (.sort .zero) etaIndexRedex (.sort (.succ .zero))) ∧
    NormalR (WhStepIndexCK2 eqEnvT) etaEqCtx etaIndexRedex ∧
    ∀ u, ¬ RedR (WhStepIndexCK2 eqEnvT) etaEqCtx etaIndexRedex (.sort u) :=
  ⟨⟨pinEqGroupWfT⟩, ⟨etaEqCtxWf n⟩, ⟨.symm _ _ _ _ (etaIndexRedexConv n)⟩,
    etaIndexRedex_normal, etaIndexRedex_not_sort⟩

/-- The binder countermodel refutes the existing fundamental type-level chain interface. -/
theorem not_fundamentalLRST_whStepIndexCK2_binder (n : Nat) :
    ¬ FundamentalLRST (WhStepIndexCK2 eqEnvT) eqEnvT n := by
  intro F
  have hc : ConvT eqEnvT n binderEqCtx (.sort .zero) binderIndexRedex
      (.sort (.succ .zero)) := .symm _ _ _ _ (binderIndexRedexConv n)
  have h := F (binderEqCtxWf n) (.sort _ .zero) (.of _ _ _ _ hc) .sort (.sort _ .zero)
  rw [LRSCore.eq_def] at h
  obtain ⟨_, _, u', _, hr⟩ := h
  exact binderIndexRedex_not_sort u' hr

/-- The independent eta countermodel refutes the same unchanged interface. -/
theorem not_fundamentalLRST_whStepIndexCK2_eta (n : Nat) :
    ¬ FundamentalLRST (WhStepIndexCK2 eqEnvT) eqEnvT n := by
  intro F
  have hc : ConvT eqEnvT n etaEqCtx (.sort .zero) etaIndexRedex
      (.sort (.succ .zero)) := .symm _ _ _ _ (etaIndexRedexConv n)
  have h := F (etaEqCtxWf n) (.sort _ .zero) (.of _ _ _ _ hc) .sort (.sort _ .zero)
  rw [LRSCore.eq_def] at h
  obtain ⟨_, _, u', _, hr⟩ := h
  exact etaIndexRedex_not_sort u' hr

/-- The existing typed identity-substitution interface is inhabited at bottom in any
let-free native context.  This is used only to instantiate a claimed universal supplier. -/
theorem relSubstIdT_bot_of_noValue (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (hnone : ∀ i, lookupValue Γ i = none) (M : CtxModelT E) (R : Readback) :
    RelSubstIdT M R n Γ EnvT.bot := by
  have hT := typedSubstT_id (envClosed_of_envWfT hW) hΓ
  refine ⟨hT, hT, ?_, ?_, ?_⟩
  · intro i A hA
    exact ⟨by simpa only [substT_id] using
      (ConvT.refl Γ (.bvar i) A (.bvar Γ i A hA))⟩
  · intro i A _ c hc
    have hc' : c = .bot := hc.elim id id
    subst c
    exact ⟨lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _,
      lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _⟩
  · intro i v A hv _
    rw [hnone i] at hv
    exact Option.noConfusion hv

/-- The complete binder readback failure is already visible at the selected typed sort compact. -/
theorem not_lrSCoreS_index_binder_sort (n : Nat) :
    ¬ LRSCoreS (WhStepIndexCK2 eqEnvT) eqEnvT n binderEqCtx
      (.sort .zero) binderIndexRedex (.sort (.succ .zero)) .sort := by
  intro h
  obtain ⟨_, _, _, _, hr⟩ := (lrSCoreS_sort_iff _ _ _ _).mp h
  exact binderIndexRedex_not_sort _ hr

/-- The binder countermodel refutes full `FundConvAt`, including its quantified substitutions. -/
theorem not_fundConvAt_whStepIndexCK2_binder (n : Nat) :
    ¬ FundConvAt (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT) n binderEqCtx
      (.sort .zero) binderIndexRedex (.sort (.succ .zero)) := by
  intro hF
  have hnone : ∀ i, lookupValue binderEqCtx i = none := by
    intro i
    cases i with
    | zero => rfl
    | succ i => simp [binderEqCtx, lookupValue]
  apply not_lrSCoreS_index_binder_sort n
  apply (lrSCoreS_prop_iff_sort _ _ _ _).mp
  exact fundConvAt_ctx_of_id (binderEqCtxWf n)
    (relSubstIdT_bot_of_noValue pinEqGroupWfT (binderEqCtxWf n) hnone
      (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT)) hF .prop
    (Or.inl (approxT_sort_code eqEnvT EnvT.bot .zero))

/-- Native eta gives the same direct failure of the selected typed sort relation. -/
theorem not_lrSCoreS_index_eta_sort (n : Nat) :
    ¬ LRSCoreS (WhStepIndexCK2 eqEnvT) eqEnvT n etaEqCtx
      (.sort .zero) etaIndexRedex (.sort (.succ .zero)) .sort := by
  intro h
  obtain ⟨_, _, _, _, hr⟩ := (lrSCoreS_sort_iff _ _ _ _).mp h
  exact etaIndexRedex_not_sort _ hr

/-- The eta countermodel also refutes the complete quantified `FundConvAt` port. -/
theorem not_fundConvAt_whStepIndexCK2_eta (n : Nat) :
    ¬ FundConvAt (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT) n etaEqCtx
      (.sort .zero) etaIndexRedex (.sort (.succ .zero)) := by
  intro hF
  have hnone : ∀ i, lookupValue etaEqCtx i = none := by
    intro i
    cases i with
    | zero => rfl
    | succ i =>
        cases i with
        | zero => rfl
        | succ i => simp [etaEqCtx, lookupValue]
  apply not_lrSCoreS_index_eta_sort n
  apply (lrSCoreS_prop_iff_sort _ _ _ _).mp
  exact fundConvAt_ctx_of_id (etaEqCtxWf n)
    (relSubstIdT_bot_of_noValue pinEqGroupWfT (etaEqCtxWf n) hnone
      (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT)) hF .prop
    (Or.inl (approxT_sort_code eqEnvT EnvT.bot .zero))

/-- Candidate (b) cannot supply the full existing typed fundamental interface at admitted Eq. -/
theorem not_fundamentalSAtT_whStepIndexCK2_eqEnvT (n : Nat) :
    ¬ FundamentalSAtT (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT) n := by
  intro hF
  exact not_fundConvAt_whStepIndexCK2_binder n
    (hF.2 (binderEqCtxWf n) (.symm _ _ _ _ (binderIndexRedexConv n)))

-- BEGIN CK2 INDEX AUDIT ROOTS
#print axioms FirstWhnfMismatch
#print axioms FirstWhnfMismatch.here
#print axioms FirstWhnfMismatch.there
#print axioms firstWhnfMismatch_det
#print axioms firstWhnfMismatch_false_of_normal
#print axioms FirstWhnfMismatchStar
#print axioms FirstWhnfMismatchStar.refl
#print axioms FirstWhnfMismatchStar.step
#print axioms firstWhnfMismatchStar_eq_of_normal
#print axioms firstWhnfMismatch_eqGap
#print axioms eqGap_indexConv
#print axioms eqWitnessIndexCut
#print axioms indexFn
#print axioms indexId
#print axioms indexBinderBeta
#print axioms indexFnTy
#print axioms indexIdTy
#print axioms indexBinderBetaTy
#print axioms indexBinderBetaConv
#print axioms binderEqCtx
#print axioms binderEqCtxWf
#print axioms binder_indices_normal
#print axioms binder_index_schedule_stuck
#print axioms binder_index_control
#print axioms etaEqCtx
#print axioms etaIndex
#print axioms etaEqCtxWf
#print axioms etaIndexConv
#print axioms eta_indices_normal
#print axioms eta_index_schedule_stuck
#print axioms eta_index_control
#print axioms deltaEqMember
#print axioms deltaEqEnv
#print axioms deltaEqEnvWf
#print axioms deltaIndexConv
#print axioms delta_index_schedule
#print axioms deltaBinderIndex
#print axioms deltaBinderIndexConv
#print axioms delta_binder_schedule_stuck
#print axioms delta_index_control
#print axioms computedBetaIndex
#print axioms computedBetaIndexTy
#print axioms computedBetaIndexConv
#print axioms computedBetaEqCtx
#print axioms computedBetaEqCtxWf
#print axioms computed_beta_schedule_stuck
#print axioms computed_beta_index_control
#print axioms WhnfIndexComplete
#print axioms not_whnfIndexComplete_eqEnvT
#print axioms binder_index_no_alignment
#print axioms eta_index_no_alignment
#print axioms scheduledCanonIdx
#print axioms WhStepIndexCK2
#print axioms WhStepIndexCK2.ck
#print axioms WhStepIndexCK2.index
#print axioms WhStepIndexCK2.recMajor
#print axioms WhStepIndexCK2.appHead
#print axioms indexEqGapAlignedW
#print axioms redR_whStepIndexCK2_eqGap
#print axioms ScheduledRecSource
#print axioms scheduledRecSource_app
#print axioms whStepIndexCK2_ck_or_saturated
#print axioms scheduledRecSource_is_app
#print axioms scheduledRecSource_spine
#print axioms normalR_sortIndexCK2
#print axioms normalR_piIndexCK2
#print axioms normalR_lamIndexCK2
#print axioms normalR_ctorIndexCK2
#print axioms normalR_famAppIndexCK2
#print axioms readbackLaws_whStepIndexCK2
#print axioms whStepIndexCK2_recPrefix_false_aux
#print axioms eqIndexW
#print axioms eqFnIndexW
#print axioms eqIndexRedex
#print axioms eqFnIndexRedex
#print axioms eqWitnessCtorData
#print axioms whStepCK_eqIndex_false_aux
#print axioms whStepCK_eqFnIndex_false_aux
#print axioms whStepIndexCK2_eqIndex_false_aux
#print axioms whStepIndexCK2_eqFnIndex_false_aux
#print axioms normalR_whStepIndexCK2_eqIndex
#print axioms normalR_whStepIndexCK2_eqFnIndex
#print axioms binderIndexMot
#print axioms etaIndexMot
#print axioms binderIndexRedex
#print axioms etaIndexRedex
#print axioms binderIndexRedex_normal
#print axioms etaIndexRedex_normal
#print axioms binderIndexRedex_not_sort
#print axioms etaIndexRedex_not_sort
#print axioms binderIndexFamily
#print axioms binderIndexCtor
#print axioms binderIndexFamilyTy
#print axioms binderIndexCtorTy
#print axioms binderIndexMotBodyTy
#print axioms binderIndexMotTy
#print axioms binderIndexMotAtConv
#print axioms binderIndexRecTy
#print axioms binderIndexRedexConv
#print axioms etaIndexFamily
#print axioms etaIndexCtor
#print axioms etaIndexParamTy
#print axioms etaIndexTy
#print axioms etaIndexFamilyTy
#print axioms etaIndexCtorTy
#print axioms etaIndexMotBodyTy
#print axioms etaIndexMotTy
#print axioms etaIndexMotAtConv
#print axioms etaIndexRecTy
#print axioms etaIndexRedexConv
#print axioms binder_readback_countermodel
#print axioms eta_readback_countermodel
#print axioms not_fundamentalLRST_whStepIndexCK2_binder
#print axioms not_fundamentalLRST_whStepIndexCK2_eta
#print axioms relSubstIdT_bot_of_noValue
#print axioms not_lrSCoreS_index_binder_sort
#print axioms not_fundConvAt_whStepIndexCK2_binder
#print axioms not_lrSCoreS_index_eta_sort
#print axioms not_fundConvAt_whStepIndexCK2_eta
#print axioms not_fundamentalSAtT_whStepIndexCK2_eqEnvT
-- END CK2 INDEX AUDIT ROOTS

end Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
