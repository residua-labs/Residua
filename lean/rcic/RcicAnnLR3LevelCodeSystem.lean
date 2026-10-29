import rcic.RcicAnnLR3EqKLikeHook
import rcic.RcicAnnLR3CandidateReflection

/-!
# A level code system for sort membership, with `NeutralSupport`

Sort membership needs levels, not content. In this code system a raw value is
a type at level `k` exactly when it is a defined level-`k` sort member. The
element relation of a type (`relFor`) is chaotic on bottom-carrying values,
except that a universe type relates the defined, bottom-carrying type images
of its level. The universe relation (`UniversePER`) relates two such images
when they are the same universe or neither is a universe, so that related
types have the same element relation.

- `codeSystem`: every field of `CodeSystem`.
- `universeTransport`, `propIrrelevance`: the skeleton's `UniverseAlgebra`.
- `neutralSupport_target`: `NeutralSupport` on every Target
  `annSemantics codeSystem (view E) (hook hE F)`. A universe member decodes
  as a code at its level. Reflection is the observation-directed
  `ObservationReflection.reflV`: at a universe image it is the named neutral
  type `13` of that level, which is a type image and not a universe.

Every type here is inhabited and proofs of different propositions are
related. That is the point: it is the model in which the K-like evaluation
of AnySort Eq (`EqKLikeHook`) can transport values between apart indices,
while large eliminations stay type images of the right level. It is not a
consistency model. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.LevelCodeSystem

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open ObservationReflection

def IsUniv (V : Value) : Prop := ∃ i, ValueEq V (universeValue i)

/-- Defined, bottom-carrying type images of level `j`, related when they are
the same universe or neither is a universe. -/
def UniversePER (j : Option Nat) : Relation := fun x y =>
  x .bot ∧ y .bot ∧ SortMember j x ∧ TypeDefined x ∧ SortMember j y ∧ TypeDefined y ∧
    ((∃ i, ValueEq x (universeValue i) ∧ ValueEq y (universeValue i)) ∨ (¬ IsUniv x ∧ ¬ IsUniv y))

theorem universePER_laws (j : Option Nat) : Laws (UniversePER j) := by
  refine ⟨?_, ?_⟩
  · rintro x y ⟨a, b, c, d, e, f, ⟨i, hx, hy⟩ | ⟨hx, hy⟩⟩
    · exact ⟨b, a, e, f, c, d, .inl ⟨i, hy, hx⟩⟩
    · exact ⟨b, a, e, f, c, d, .inr ⟨hy, hx⟩⟩
  · rintro x y z ⟨a, _, c, d, _, _, h1⟩ ⟨_, b', _, _, e', f', h2⟩
    refine ⟨a, b', c, d, e', f', ?_⟩
    rcases h1 with ⟨i, hx, hy⟩ | ⟨hx, hy⟩ <;> rcases h2 with ⟨i', hy', hz⟩ | ⟨hy', hz⟩
    · exact .inl ⟨i, hx, hz.trans (hy'.symm.trans hy)⟩
    · exact (hy' ⟨i, hy⟩).elim
    · exact (hy ⟨i', hy'⟩).elim
    · exact .inr ⟨hx, hz⟩

/-- The element relation of a type image: bottom-carrying values, and type
images of the right level when the type is a universe. -/
def relFor (V : Value) : Relation := fun x y =>
  x .bot ∧ y .bot ∧ ∀ j, ValueEq V (universeValue j) → UniversePER j x y

theorem relFor_laws (V : Value) : Laws (relFor V) :=
  ⟨fun ⟨a, b, h⟩ => ⟨b, a, fun j hj => (universePER_laws j).symm (h j hj)⟩,
    fun ⟨a, _, h⟩ ⟨_, b', g⟩ => ⟨a, b', fun j hj => (universePER_laws j).trans (h j hj) (g j hj)⟩⟩

def Code (k : Option Nat) (V : Value) (R : Relation) : Prop :=
  SortMember k V ∧ TypeDefined V ∧ Same R (relFor V)

theorem universe_unique {j k : Option Nat} (h : ValueEq (universeValue k) (universeValue j)) :
    j = k := (sort_code_injective h).symm

theorem relFor_universe (k : Option Nat) : Same (relFor (universeValue k)) (UniversePER k) := by
  intro x y
  constructor
  · rintro ⟨_, _, h⟩
    exact h k (ValueEq.refl _)
  · intro h
    refine ⟨h.1, h.2.1, fun j hj => ?_⟩
    rw [universe_unique hj]
    exact h

theorem universe_isUniv (k : Option Nat) : IsUniv (universeValue k) := ⟨k, ValueEq.refl _⟩

def codeSystem : CodeSystem where
  Code := Code
  universePER := UniversePER
  lawful := fun h => NeutralControls.laws_of_same h.2.2 (relFor_laws _)
  defined := fun h => h.2.1
  level := fun h => h.1
  coherent := fun h g x y => (h.2.2 x y).trans (g.2.2 x y).symm
  universe_code := fun k => ⟨sort_member _ k, sort_defined _ k, fun x y => (relFor_universe k x y).symm⟩
  universe_member := fun k => ⟨.bot _ _, .bot _ _, sort_member _ k, sort_defined _ k,
    sort_member _ k, sort_defined _ k, .inl ⟨k, ValueEq.refl _, ValueEq.refl _⟩⟩
  universe_elim := by
    intro k l R x hc hx
    have hu := ((hc.2.2 x x).trans (relFor_universe k x x)).mp hx
    exact ⟨hu.2.2.1, hu.2.2.2.1⟩

theorem code_of_universe {k : Option Nat} {x y : Value} (h : UniversePER k x y) :
    codeSystem.Code k x (relFor x) :=
  ⟨h.2.2.1, h.2.2.2.1, fun _ _ => Iff.rfl⟩

theorem relFor_nonUniv {V : Value} (h : ¬ IsUniv V) (x y : Value) :
    relFor V x y ↔ (x .bot ∧ y .bot) :=
  ⟨fun ⟨a, b, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, fun j hj => (h ⟨j, hj⟩).elim⟩⟩

theorem universeTransport : UniverseTransport codeSystem where
  relate := by
    intro k V W h
    refine ⟨relFor V, relFor W, code_of_universe h,
      code_of_universe ((universePER_laws k).symm h), fun x y => ?_⟩
    rcases h.2.2.2.2.2.2 with ⟨i, hV, hW⟩ | ⟨hV, hW⟩
    · rw [NeutralCodes.valueEq_eq hV, NeutralCodes.valueEq_eq hW]
    · exact (relFor_nonUniv hV x y).trans (relFor_nonUniv hW x y).symm

theorem not_level_zero_univ {V : Value} (hV : SortMember (some 0) V) (hd : TypeDefined V)
    {i : Option Nat} (h : ValueEq V (universeValue i)) : False := by
  have hs := sortMember_unique hV (sortMember_congr h.symm (sort_member _ i)) hd
  cases i with
  | none => exact Option.noConfusion hs
  | some n => exact Nat.succ_ne_zero n (Option.some.inj hs).symm

theorem propIrrelevance : PropIrrelevance codeSystem where
  relate := by
    intro V R x y hc hx hy
    refine (hc.2.2 x y).mpr ⟨((hc.2.2 x x).mp hx).1, ((hc.2.2 y y).mp hy).1, fun j hj => ?_⟩
    exact (not_level_zero_univ hc.1 hc.2.1 hj).elim

/-! ## `NeutralSupport` -/

/-- A named neutral type is not a universe. -/
theorem named_not_univ (k : Option Nat) (name : Nat) (h11 : name ≠ 11) :
    ¬ IsUniv (NativeMemberValues.value k name) := by
  rintro ⟨i, h⟩
  have hU := universe_tagged i
  have hobs : universeValue i (.spine 10 [.spine (levelRef (i.map Nat.succ)) [], .spine 11 [.bot]]) := by
    rw [hU]
    exact Or.inr ⟨_, _, rfl, Or.inr rfl, .appSpine (args := []) (.const _ _ _) (.bot _ _)⟩
  have hv := (h _).mpr hobs
  have hv' := (InductiveCodes.taggedValue_denI EnvI.bot k (.const name []) _).mpr hv
  obtain ⟨_, hp⟩ := tagged_obs hv'
  rcases approxI_const_inv hp with hp | hp
  · cases hp
  · exact h11 (CptI.spine.inj hp).1.symm

def reflectAt (V : Value) (a : Nat) : Value := reflV V (NeutralPER.neutralAtom (a + 12))

theorem reflect_member {k : Option Nat} {V : Value} {R : Relation} (hc : codeSystem.Code k V R)
    (a : Nat) : Member R (reflectAt V a) := by
  refine (hc.2.2 _ _).mpr ⟨.bot _ _, .bot _ _, fun j hj => ?_⟩
  have hr : reflectAt V a = NativeMemberValues.value j 13 := by
    rw [reflectAt, NeutralCodes.valueEq_eq hj]
    exact NeutralCodes.valueEq_eq (refl_universe j _)
  rw [hr]
  have hn := named_not_univ j 13 (by decide)
  exact ⟨NativeMemberValues.value_bot _ _, NativeMemberValues.value_bot _ _,
    NativeMemberValues.value_level _ _, NativeMemberValues.value_defined _ _,
    NativeMemberValues.value_level _ _, NativeMemberValues.value_defined _ _, .inr ⟨hn, hn⟩⟩

theorem decode_universe {M : AnnSemantics} (hM : M.toCodeSystem = codeSystem)
    {k l : Option Nat} {R : Relation} {x : Value} (hc : M.Code l (universeValue k) R)
    (hx : Member R x) : ∃ S, M.Code k x S := by
  rw [hM] at hc ⊢
  have hu := ((hc.2.2 x x).trans (relFor_universe k x x)).mp hx
  exact ⟨_, code_of_universe hu⟩

/-- `NeutralSupport` on the skeleton's Target shape, for any hook. -/
def neutralSupport_target {E : ResolvedEnvA} (hE : EnvWfA (iotaIfaceA E) E)
    (F : EnvironmentEval.FamilySyntax) :
    NeutralExtraction.NeutralSupport
      (EnvironmentEval.annSemantics codeSystem (SemanticMemberEval.view E)
        (AdmissionUniverseReadback.hook hE F)) where
  decode := decode_universe rfl
  reflect := reflectAt
  reflect_member := fun hc a => reflect_member hc a

end Rcic.Declarative.Ann.LR3.LevelCodeSystem
