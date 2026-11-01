import rcic.RcicF3BoundedPiSpine
import rcic.RcicF3BoundedBVarAttack

/-!
# Bounded Pi-spine extraction at AccR and an inhabited dependent depth three

The actual AccR row supplies its own bounded field derivation and its
actual normalized one-binder read. The selected AccR parameter from the
earlier fixture still has an empty child domain, retained in Witness.

The auxiliary three-binder expression is typed in the same admitted
family-only prefix. Its domains are `[Prop, P, P]`, with the latter two
depending on the first value, and its terminal family argument is the
complete parameter `P`. Choosing the true proposition gives an inhabited
domain tuple. An outer conversion from a nested imax sort to Prop tests
the Pi inversion through conversion wrappers. The public extraction and
original-context soundness composition are called directly.

The auxiliary expression is not declared as a new admitted constructor,
and no value of `AccR True` is asserted. This witnesses the precise
bounded-spine component, not normalization subject reduction, parameter
mirror alignment, domain erasure, or universal data-frame closure.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.BoundedPiSpineAttack
open Rcic.Declarative BoundedPiSpine
open NormRoleTableAttack (table)
open PropEvalAdmittedInputsAttack (bound)

def accDs : List (Expr Nat) := [.bvar 0]
def accArgs : List (Expr Nat) := [.bvar 1]
def accCtx : LCtx := [.assumption (.sort .zero)]

noncomputable def acc_typed :
    HasTyT accFamOnly 0 accCtx
      (policyPi accDs (foldApps (.const 0 []) accArgs))
      (.sort (.imax .zero .zero)) :=
  AccEnv.accFieldTyT accFamOnly rfl

theorem acc_bound (σ K : Nat → Nat) : LOKt σ 4 K acc_typed := by
  change 0 ≤ 4 ∧ 0 ≤ 4 ∧ True ∧
    ((∀ l, l ∈ ([] : List Level) → evalTotal σ l ≤ K 0) ∧ True)
  exact ⟨Nat.zero_le _, Nat.zero_le _, True.intro,
    (fun l hl => (List.not_mem_nil l hl).elim), True.intro⟩

theorem acc_read : piTelescopeFuel accFamOnly 8 accField =
    some (accDs, foldApps (.const 0 []) accArgs) := rfl

theorem acc_spine (σ K : Nat → Nat) :
    Domains (E := accFamOnly) (n := 0) σ 4 K accCtx accDs ∧
      ∃ (v : Level) (d : HasTyT accFamOnly 0 (context accCtx accDs)
        (foldApps (.const 0 []) accArgs) (.sort v)), LOKt σ 4 K d :=
  telescope σ 4 K accDs (foldApps (.const 0 []) accArgs)
    acc_typed (acc_bound σ K)

theorem acc_argument (σ K : Nat → Nat) :
    ∃ (A T : Expr Nat), lookupType (context accCtx accDs) 1 = some A ∧
      (∃ d : HasTyT accFamOnly 0 (context accCtx accDs) (.bvar 1) T,
        LOKt σ 4 K d) ∧
      ∃ c : TyConvT accFamOnly 0 (context accCtx accDs) A T,
        BoundedBVar.Bounded σ 4 K c :=
  variable_argument σ 4 K accDs accArgs (.const 0 [])
    acc_typed (acc_bound σ K) 1 (List.mem_cons_self _ _)

def threeDs : List (Expr Nat) := [.sort .zero, .bvar 0, .bvar 1]
def threeArgs : List (Expr Nat) := [.bvar 2]
def three : Expr Nat := policyPi threeDs (foldApps (.const 0 []) threeArgs)
def threeLevel : Level := .imax (.succ .zero) (.imax .zero (.imax .zero .zero))

noncomputable def three_base : HasTyT accFamOnly 0 [] three (.sort threeLevel) :=
  .pi [] (.sort .zero) (.succ .zero)
    (.pi (.bvar 0) (.pi (.bvar 1) (accApp (.bvar 2))))
    (.imax .zero (.imax .zero .zero))
    (.sort [] .zero)
    (.pi [.assumption (.sort .zero)] (.bvar 0) .zero
      (.pi (.bvar 1) (accApp (.bvar 2))) (.imax .zero .zero)
      (.bvar _ 0 _ rfl)
      (.pi [.assumption (.bvar 0), .assumption (.sort .zero)]
        (.bvar 1) .zero (accApp (.bvar 2)) .zero
        (.bvar _ 1 _ rfl)
        (.app _ (.const 0 []) (.bvar 2) (.sort .zero) (.sort .zero)
          (.const _ 0 [] accFamMember rfl rfl rfl)
          (.bvar _ 2 _ rfl))))

noncomputable def three_typed : HasTyT accFamOnly 0 [] three (.sort .zero) :=
  .conv [] three (.sort threeLevel) (.sort .zero) (.succ threeLevel)
    three_base (.sorts [] threeLevel .zero (fun _ => rfl))

theorem three_bound (σ K : Nat → Nat) : LOKt σ 4 K three_typed := by
  change (1 ≤ 4 ∧ 0 ≤ 4 ∧ 1 ≤ 4 ∧
    (0 ≤ 4 ∧ 0 ≤ 4 ∧ True ∧
      (0 ≤ 4 ∧ 0 ≤ 4 ∧ True ∧
        ((∀ l, l ∈ ([] : List Level) → evalTotal σ l ≤ K 0) ∧ True)))) ∧ 1 ≤ 4
  exact ⟨⟨by decide, Nat.zero_le _, by decide,
    Nat.zero_le _, Nat.zero_le _, True.intro,
    Nat.zero_le _, Nat.zero_le _, True.intro,
    (fun l hl => (List.not_mem_nil l hl).elim), True.intro⟩, by decide⟩

theorem three_read : piTelescopeFuel accFamOnly 12 three =
    some (threeDs, foldApps (.const 0 []) threeArgs) := rfl

theorem three_spine (σ K : Nat → Nat) :
    Domains (E := accFamOnly) (n := 0) σ 4 K [] threeDs ∧
      ∃ (v : Level) (d : HasTyT accFamOnly 0 (context [] threeDs)
        (foldApps (.const 0 []) threeArgs) (.sort v)), LOKt σ 4 K d :=
  telescope σ 4 K threeDs (foldApps (.const 0 []) threeArgs)
    three_typed (three_bound σ K)

theorem three_context (σ K : Nat → Nat) :
    Nonempty (CtxWfT accFamOnly 0 (context [] threeDs)) :=
  context_wf σ 4 K threeDs (three_spine σ K).1 .nil

def truthParameter : PSet.{4} := tyv (tv True)
def values : List PSet.{4} := [truthParameter, pempty, pempty]

theorem truth_mem (P : Premises4) : truthParameter ∈ U W4 0 :=
  mem_sImage_tyv.mpr ⟨tv True,
    mem_propSets.mpr (fun _ hz => (mem_tv.mp hz).2), Equiv.rfl⟩

theorem truth_inhabited (P : Premises4) :
    pempty ∈ Ed (mkM P (table P)) truthParameter :=
  mem_congr_right (ed_tyv (mkM P (table P)) (dich_tv True)).symm
    (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)

theorem values_fit (P : Premises4) (σ : Nat → Nat) :
    TelFits (mkM P (table P)) σ threeDs ρ0 values := by
  refine ⟨?_, truth_inhabited P, truth_inhabited P, True.intro⟩
  exact mem_congr_right (ed_tyv (mkM P (table P)) (U4_dich 0)).symm (truth_mem P)

theorem composition (P : Premises4) (σ : Nat → Nat) :
    ∃ (A T : Expr Nat), lookupType (context [] threeDs) 2 = some A ∧
      (∃ c : TyConvT accFamOnly 0 (context [] threeDs) A T,
        BoundedBVar.Bounded σ 4 bound c) ∧
      Equiv (den (mkM P (table P)) σ (push values ρ0) A)
        (den (mkM P (table P)) σ (push values ρ0) T) :=
  variable_argument_sound P (table P) σ bound (BoundedBVarAttack.prefix_sound P σ)
    threeDs threeArgs (.const 0 []) three_typed (three_bound σ bound)
    2 (List.mem_cons_self _ _) ρ0 values True.intro (values_fit P σ)

def Witness (P : Premises4) : Prop :=
  BoundedBVarAttack.Witness P ∧
  piTelescopeFuel accFamOnly 8 accField =
    some (accDs, foldApps (.const 0 []) accArgs) ∧
  (∀ σ K, Domains (E := accFamOnly) (n := 0) σ 4 K accCtx accDs ∧
    ∃ (v : Level) (d : HasTyT accFamOnly 0 (context accCtx accDs)
      (foldApps (.const 0 []) accArgs) (.sort v)), LOKt σ 4 K d) ∧
  (∀ σ K, ∃ (A T : Expr Nat), lookupType (context accCtx accDs) 1 = some A ∧
    (∃ d : HasTyT accFamOnly 0 (context accCtx accDs) (.bvar 1) T, LOKt σ 4 K d) ∧
    ∃ c : TyConvT accFamOnly 0 (context accCtx accDs) A T,
      BoundedBVar.Bounded σ 4 K c) ∧
  threeDs.length = 3 ∧ threeLevel ≠ .zero ∧
  piTelescopeFuel accFamOnly 12 three =
    some (threeDs, foldApps (.const 0 []) threeArgs) ∧
  (∀ σ K, LOKt σ 4 K three_typed) ∧
  Nonempty (CtxWfT accFamOnly 0 (context [] threeDs)) ∧
  (∀ σ, TelFits (mkM P (table P)) σ threeDs ρ0 values) ∧
  (∀ σ, Fits (mkM P (table P)) σ (context [] threeDs) (push values ρ0)) ∧
  (∀ σ, ∃ (A T : Expr Nat), lookupType (context [] threeDs) 2 = some A ∧
    (∃ c : TyConvT accFamOnly 0 (context [] threeDs) A T,
      BoundedBVar.Bounded σ 4 bound c) ∧
    Equiv (den (mkM P (table P)) σ (push values ρ0) A)
      (den (mkM P (table P)) σ (push values ρ0) T)) ∧
  Equiv (Ed (mkM P (table P)) PlanPropEndAttack.parameter) pempty

theorem component_witness (P : Premises4) : Witness P := by
  refine ⟨BoundedBVarAttack.component_witness P, acc_read, acc_spine, acc_argument,
    rfl, ?_, three_read, three_bound, three_context (fun _ => 0) bound,
    values_fit P, ?_, composition P, PlanPropEndAttack.parameter_empty P (table P)⟩
  · intro h
    cases h
  · intro σ
    exact context_fits (mkM P (table P)) σ threeDs ρ0 values True.intro (values_fit P σ)

theorem nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.BoundedPiSpineAttack
