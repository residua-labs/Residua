import rcic.RcicF3BoundedBVar
import rcic.RcicF3NormPropCtorAttack

/-!
# Bounded variable inversion at a hidden domain and the actual AccR prefix

The first variable starts at a syntactically beta-hidden parameter domain
and is typed at Prop by an explicit bounded conversion. Its original
context is inhabited at the actual normalized AccR table, and the newly
extracted chain is composed with soundness there. The hidden domain is a
local typed example in the admitted group's family-only prefix; it is not
claimed to be an original stored parameter of that group.

The second example is the actual parameter variable passed to AccR under
the recursive field's Pi binder. That variable has no conversion wrappers.
The same lookup is also interpreted in the inhabited original constructor
context. The actual recursive child domain remains empty. No strengthening
of either local context, normalized-spine producer, or general parameter
mirror theorem is asserted. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.BoundedBVarAttack
open Rcic.Declarative BoundedBVar
open NormRoleTableAttack (table)
open PropEvalAdmittedInputsAttack (bound)
open PlanPropEndAttack (parameter σ)

/-- A closed beta-hidden type of parameters, convertible to Prop. -/
def hidden : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)

def hiddenCtx : LCtx := [.assumption hidden]

noncomputable def hidden_typed (Γ : LCtx) :
    HasTyT accFamOnly 0 Γ hidden (.sort (.succ .zero)) :=
  .app Γ (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)
    (.sort (.succ .zero)) (.sort (.succ .zero))
    (.lam Γ (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort .zero) (.sort (.succ .zero))
      (.sort Γ (.succ .zero))
      (.sort (.assumption (.sort (.succ .zero)) :: Γ) .zero))
    (.sort Γ .zero)

noncomputable def hidden_beta (Γ : LCtx) :
    ConvT accFamOnly 0 Γ hidden (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.sort (.succ .zero)) (.sort .zero) (.sort .zero)
    (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort Γ (.succ .zero))
    (.sort (.assumption (.sort (.succ .zero)) :: Γ) .zero)
    (.sort Γ .zero)

theorem hidden_beta_bound (τ K : Nat → Nat) (Γ : LCtx) :
    LOKc τ 4 K (hidden_beta Γ) := by
  change 2 ≤ 4 ∧ 1 ≤ 4 ∧ 1 ≤ 4
  exact ⟨by decide, by decide, by decide⟩

noncomputable def hidden_variable :
    HasTyT accFamOnly 0 hiddenCtx (.bvar 0) (.sort .zero) :=
  .conv hiddenCtx (.bvar 0) hidden (.sort .zero) (.succ .zero)
    (.bvar hiddenCtx 0 hidden rfl) (hidden_beta hiddenCtx)

theorem hidden_variable_bound (τ K : Nat → Nat) :
    LOKt τ 4 K hidden_variable :=
  ⟨True.intro, hidden_beta_bound τ K hiddenCtx⟩

/-- This chain is obtained from the variable derivation, rather than passed
in as an independently assumed parameter mirror. -/
theorem hidden_chain (τ K : Nat → Nat) :
    ∃ c : TyConvT accFamOnly 0 hiddenCtx hidden (.sort .zero),
      Bounded τ 4 K c :=
  extract_of_lookup τ 4 K (Γ := hiddenCtx) (k := 0) (A := hidden)
    rfl hidden_variable (hidden_variable_bound τ K)

theorem prefix_sound (P : Premises4) (τ : Nat → Nat) :
    EnvSound (mkM P (table P)) τ bound accFamOnly 0 :=
  (NormPropCtorAttack.component_witness P).2.2.1.rawEnv τ 0

/-- The empty-context beta derivation produces this particular hidden
domain's meaning before any hidden-parameter fit is used. -/
theorem hidden_den (P : Premises4) (τ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    Equiv (den (mkM P (table P)) τ ρ hidden)
      (den (mkM P (table P)) τ ρ (.sort .zero)) :=
  (sound_conv (P.good _ rfl) (prefix_sound P τ)
    (hidden_beta []) (hidden_beta_bound τ bound []) ρ True.intro).1

theorem hidden_fit (P : Premises4) (τ : Nat → Nat) :
    Fits (mkM P (table P)) τ hiddenCtx (vcons parameter ρ0) := by
  refine ⟨True.intro, ?_⟩
  exact mem_congr_right
    (ed_congr (mkM P (table P)) (hidden_den P τ ρ0)).symm
    (tyv_pempty_mem_sort P (table P) τ ρ0 .zero)

/-- The public extraction-to-soundness composition is invoked in the
inhabited original hidden context at the actual normalized table. -/
theorem hidden_composition (P : Premises4) (τ : Nat → Nat) :
    Equiv (den (mkM P (table P)) τ (vcons parameter ρ0) hidden)
      (den (mkM P (table P)) τ (vcons parameter ρ0) (.sort .zero)) :=
  lookup_equiv P (table P) τ bound (Γ := hiddenCtx) (k := 0) (A := hidden)
    (prefix_sound P τ) rfl hidden_variable
    (hidden_variable_bound τ bound) (vcons parameter ρ0) (hidden_fit P τ)

/-- The context under the actual recursive field's single Pi binder. -/
def recursiveCtx : LCtx :=
  [.assumption (.bvar 0), .assumption (.sort .zero)]

noncomputable def recursive_argument :
    HasTyT accFamOnly 0 recursiveCtx (.bvar 1) (.sort .zero) :=
  .bvar recursiveCtx 1 (.sort .zero) rfl

/-- This is the complete family application in the actual AccR field row. -/
noncomputable def recursive_body :
    HasTyT accFamOnly 0 recursiveCtx (accApp (.bvar 1)) (.sort .zero) :=
  .app recursiveCtx (.const 0 []) (.bvar 1) (.sort .zero) (.sort .zero)
    (.const recursiveCtx 0 [] accFamMember rfl rfl rfl) recursive_argument

theorem recursive_body_bound (τ K : Nat → Nat) :
    LOKt τ 4 K recursive_body :=
  ⟨fun l hl => (List.not_mem_nil l hl).elim, True.intro⟩

theorem recursive_argument_chain (τ K : Nat → Nat) :
    ∃ c : TyConvT accFamOnly 0 recursiveCtx (.sort .zero) (.sort .zero),
      Bounded τ 4 K c :=
  extract_of_lookup τ 4 K (Γ := recursiveCtx) (k := 1) (A := .sort .zero)
    rfl recursive_argument True.intro

def constructorCtx : LCtx :=
  [.assumption accField, .assumption (.sort .zero)]

noncomputable def constructor_argument :
    HasTyT accFamOnly 0 constructorCtx (.bvar 1) (.sort .zero) :=
  .bvar constructorCtx 1 (.sort .zero) rfl

theorem constructor_fit (P : Premises4) :
    Fits (mkM P (table P)) σ constructorCtx
      (vcons pempty (vcons parameter ρ0)) := by
  have hfit := (NormPropCtorAttack.component_witness P).2.2.2.2.1
  exact ⟨⟨True.intro, hfit.1⟩, hfit.2.1⟩

theorem constructor_composition (P : Premises4) :
    Equiv (den (mkM P (table P)) σ (vcons pempty (vcons parameter ρ0))
      (.sort .zero))
      (den (mkM P (table P)) σ (vcons pempty (vcons parameter ρ0))
        (.sort .zero)) :=
  lookup_equiv P (table P) σ bound (Γ := constructorCtx) (k := 1) (A := .sort .zero)
    (prefix_sound P σ) rfl constructor_argument
    True.intro (vcons pempty (vcons parameter ρ0)) (constructor_fit P)

def Witness (P : Premises4) : Prop :=
  NormPropCtorAttack.Witness P ∧
  hidden ≠ .sort .zero ∧
  Nonempty (CtxWfT accFamOnly 0 hiddenCtx) ∧
  Nonempty (HasTyT accFamOnly 0 hiddenCtx (.bvar 0) (.sort .zero)) ∧
  (∀ τ K, LOKt τ 4 K hidden_variable) ∧
  (∀ τ K, ∃ c : TyConvT accFamOnly 0 hiddenCtx hidden (.sort .zero),
    Bounded τ 4 K c) ∧
  (∀ τ, Fits (mkM P (table P)) τ hiddenCtx (vcons parameter ρ0)) ∧
  (∀ τ, Equiv (den (mkM P (table P)) τ (vcons parameter ρ0) hidden)
    (den (mkM P (table P)) τ (vcons parameter ρ0) (.sort .zero))) ∧
  accField = .pi (.bvar 0) (accApp (.bvar 1)) ∧
  Nonempty (HasTyT accFamOnly 0 recursiveCtx (accApp (.bvar 1)) (.sort .zero)) ∧
  (∀ τ K, LOKt τ 4 K recursive_body) ∧
  (∀ τ K, ∃ c : TyConvT accFamOnly 0 recursiveCtx (.sort .zero) (.sort .zero),
    Bounded τ 4 K c) ∧
  Fits (mkM P (table P)) σ constructorCtx (vcons pempty (vcons parameter ρ0)) ∧
  Equiv (den (mkM P (table P)) σ (vcons pempty (vcons parameter ρ0)) (.sort .zero))
    (den (mkM P (table P)) σ (vcons pempty (vcons parameter ρ0)) (.sort .zero)) ∧
  Equiv (Ed (mkM P (table P)) parameter) pempty

theorem component_witness (P : Premises4) : Witness P := by
  refine ⟨NormPropCtorAttack.component_witness P, ?_, ?_, ⟨hidden_variable⟩,
    hidden_variable_bound, hidden_chain, hidden_fit P, hidden_composition P, rfl,
    ⟨recursive_body⟩, recursive_body_bound, recursive_argument_chain,
    constructor_fit P, constructor_composition P,
    PlanPropEndAttack.parameter_empty P (table P)⟩
  · intro h
    cases h
  · exact ⟨.assumption [] hidden (.succ .zero) .nil (hidden_typed [])⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.BoundedBVarAttack
