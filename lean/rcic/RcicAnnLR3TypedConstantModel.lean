import rcic.RcicAnnLR3TypedStatements
import rcic.RcicAnnLR3TruthAxiomBoundary

/-!
# A concrete non-IR code system witnessing the const-arm obstruction

The code relation is indexed by Option Nat, semantic value and PER.
Universes use exact noncumulative membership, with full-tag definedness;
the zero-constructor family's PER is empty. All CodeSystem laws are
supplied. The image is independent of source derivations.

This is a local counterinstance to the all-admitted constant supplier,
NOT a proposed full model of lambda/Pi/inductive syntax. It makes no
assumption of global source soundness. Even the const arm's immediate
type-formation IH is supplied, so the failed arm is not rejected merely
by an omitted upstream obligation. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TypedConstantModel
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements TruthAxiomBoundary

/-- A defined zero-level type value, independently of its empty carrier. -/
def emptyValue : Value := denI EnvI.bot (taggedTerm (some 0) (.const 20 []))

theorem emptyValue_member : SortMember (some 0) emptyValue := tagged_member _ _ _
theorem emptyValue_defined : TypeDefined emptyValue := tagged_defined _ _ _

theorem emptyValue_ne_universe (k : Option Nat) : emptyValue ≠ universeValue k := by
  intro he
  have hk : some 0 = k.map Nat.succ := by
    apply sortMember_unique emptyValue_member _ emptyValue_defined
    rw [he]
    exact sort_member _ _
  cases k with
  | none => cases hk
  | some n => exact Nat.noConfusion (Option.some.inj hk)

/-- Ordinary inductive relation, not an inductive-recursive El definition. -/
inductive Code : Option Nat → Value → Relation → Prop
  | empty : Code (some 0) emptyValue emptyCarrier
  | univ (k : Option Nat) :
      Code (k.map Nat.succ) (universeValue k) (SortPER k)

theorem code_lawful {k : Option Nat} {V : Value} {R : Relation} (h : Code k V R) : Laws R := by
  cases h with
  | empty => exact truthPER_laws _
  | univ k => exact sortPER_laws k

theorem code_defined {k : Option Nat} {V : Value} {R : Relation} (h : Code k V R) :
    TypeDefined V := by
  cases h with
  | empty => exact emptyValue_defined
  | univ k => exact sort_defined _ _

theorem code_level {k : Option Nat} {V : Value} {R : Relation} (h : Code k V R) :
    SortMember k V := by
  cases h with
  | empty => exact emptyValue_member
  | univ k => exact sort_member _ _

theorem code_shape {k : Option Nat} {V : Value} {R : Relation} (h : Code k V R) :
    (k = some 0 ∧ V = emptyValue ∧ R = emptyCarrier) ∨
    ∃ j, k = j.map Nat.succ ∧ V = universeValue j ∧ R = SortPER j := by
  cases h with
  | empty => exact .inl ⟨rfl, rfl, rfl⟩
  | univ j => exact .inr ⟨j, rfl, rfl, rfl⟩

theorem code_coherent {k l : Option Nat} {V : Value} {R S : Relation}
    (h : Code k V R) (g : Code l V S) : Same R S := by
  rcases code_shape h with ⟨_, hv, hr⟩ | ⟨i, _, hv, hr⟩
  · rcases code_shape g with ⟨_, hv', hs⟩ | ⟨j, _, hv', hs⟩
    · rw [hr, hs]; exact fun _ _ => Iff.rfl
    · exact False.elim (emptyValue_ne_universe j (hv.symm.trans hv'))
  · rcases code_shape g with ⟨_, hv', hs⟩ | ⟨j, _, hv', hs⟩
    · exact False.elim (emptyValue_ne_universe i (hv'.symm.trans hv))
    · have he : universeValue i = universeValue j := hv.symm.trans hv'
      have heV : ValueEq (universeValue i) (universeValue j) := by intro c; rw [he]
      have hij : i = j := sort_code_injective (ρ := EnvI.bot) heV
      rw [hr, hs, hij]; exact fun _ _ => Iff.rfl

theorem code_universe_elim {k l : Option Nat} {R : Relation} {x : Value}
    (hc : Code l (universeValue k) R) (hm : Member R x) :
    SortMember k x ∧ TypeDefined x := by
  rcases code_shape hc with ⟨_, hv, hr⟩ | ⟨j, _, hv, hr⟩
  · exact False.elim (emptyValue_ne_universe k hv.symm)
  · have hvV : ValueEq (universeValue k) (universeValue j) := by intro c; rw [hv]
    have hkj : k = j := sort_code_injective (ρ := EnvI.bot) hvV
    subst j
    rw [hr] at hm
    exact ⟨hm.1, hm.2.1⟩

def codeSystem : CodeSystem where
  Code := Code
  universePER := SortPER
  lawful := code_lawful
  defined := code_defined
  level := code_level
  coherent := code_coherent
  universe_code := Code.univ
  universe_member := fun _k => ⟨sort_member _ _, sort_defined _ _, ValueEq.refl _⟩
  universe_elim := code_universe_elim

def image (ν : Valuation) (_Γ : LCtxA) (ρ : EnvI) : ExprA → Value
  | .sort l => universeValue (eval ν l)
  | .const r ls =>
      if r = 80 then emptyValue else if r = 81 then unitValue EnvI.bot
      else UnitModel.denote ν ρ (.const r ls)
  | e => UnitModel.denote ν ρ e

def model : AnnSemantics where
  toCodeSystem := codeSystem
  image := image
  sort_image := fun _ _ _ _ => rfl

/-- Every code assigned to the actual empty-family image has empty PER. -/
theorem code_at_empty_no_member {k : Option Nat} {R : Relation}
    (h : Code k emptyValue R) (x : Value) : ¬ Member R x := by
  rcases code_shape h with ⟨_, _, hr⟩ | ⟨j, _, hv, _⟩
  · rw [hr]; exact emptyCarrier_no_member x
  · exact False.elim (emptyValue_ne_universe j hv)

/-- The actual const arm's type-formation IH, uniformly in valuation and
realisation. This source type image has genuine defined universe membership. -/
theorem emptyType_goal : TyGoal model badEnv (iotaIfaceA badEnv) 0 [] emptyType (.sort .zero) := by
  intro _ ν ρ _
  refine ⟨some 1, SortPER (some 0), ?_, sort_defined _ _, ?_⟩
  · exact Code.univ (some 0)
  · exact ⟨emptyValue_member, emptyValue_defined, ValueEq.refl _⟩

theorem badTerm_goal_false : ¬ TyGoal model badEnv (iotaIfaceA badEnv) 0 [] badTerm emptyType := by
  intro h
  obtain ⟨k, R, hc, _, hm⟩ := h .nil (fun _ => none) EnvI.bot (.nil EnvI.bot)
  exact code_at_empty_no_member hc _ hm

/-- With the requested source and empty-context quantifiers, this
particular full fundamental statement is false, already at const. -/
theorem fundamental_false : ¬ Fundamental model badEnv (iotaIfaceA badEnv) 0 :=
  fun h => badTerm_goal_false (h.1 (badTerm_typed _))

theorem inhabited_model_boundary :
    Nonempty (EnvWfA (iotaIfaceA badEnv) badEnv) ∧
    Nonempty (CtxWfA badEnv (iotaIfaceA badEnv) 0 []) ∧
    Nonempty (HasTyA badEnv (iotaIfaceA badEnv) 0 [] emptyType (.sort .zero)) ∧
    Nonempty (HasTyA badEnv (iotaIfaceA badEnv) 0 [] badTerm emptyType) ∧
    (∀ ν, Realises model ν [] EnvI.bot) ∧
    TyGoal model badEnv (iotaIfaceA badEnv) 0 [] emptyType (.sort .zero) ∧
    ¬ TyGoal model badEnv (iotaIfaceA badEnv) 0 [] badTerm emptyType ∧
    ¬ Fundamental model badEnv (iotaIfaceA badEnv) 0 :=
  ⟨⟨badEnv_admitted _⟩, ⟨.nil⟩, ⟨emptyType_typed rfl⟩, ⟨badTerm_typed _⟩,
    fun _ => .nil EnvI.bot, emptyType_goal, badTerm_goal_false, fundamental_false⟩

end Rcic.Declarative.Ann.LR3.TypedConstantModel
