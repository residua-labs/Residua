import rcic.RcicAnnLR3UniverseDecoderBoundary

/-!
# Undefined universes: universal chaos versus exact tagged membership

The universal relation at `none` is a lawful, inhabited PER, and it allows
the undefined universe to contain itself without a recursive decoder.
It does not preserve the existing exact-sort extraction interface: the
same defined sort value becomes a member at `none` and at `some 1`.
Keeping distinct raw sort values does not repair this relation-level loss.

The second construction retains the exact tag and forgets only the
payload. It supplies a nonrecursive self-decoding undefined fragment,
with neutral type reflection and exact membership. It is not universal
chaos, a complete CodeSystem, or a source fundamental theorem. No admitted
source class is refuted. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.NoneUniverseBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

def Chaos : Relation := fun _ _ => True

theorem chaos_laws : Laws Chaos :=
  ⟨fun _ => True.intro, fun _ _ => True.intro⟩

theorem chaos_member (x : Value) : Member Chaos x := True.intro

theorem chaos_irrelevant {x y : Value} : Chaos x y := True.intro

/-- Precisely the suggested change to the old universe carriers. -/
def chaoticUniverse : Option Nat → Relation
  | none => Chaos
  | some k => NeutralCodes.UniversePER (some k)

theorem universe_laws (k : Option Nat) : Laws (chaoticUniverse k) := by
  cases k with
  | none => exact chaos_laws
  | some k => exact NeutralCodes.universePER_laws (some k)

theorem universe_member (k : Option Nat) :
    Member (chaoticUniverse (k.map Nat.succ)) (universeValue k) := by
  cases k with
  | none => exact chaos_member _
  | some k => exact NeutralCodes.universe_member (some k)

theorem undefined_self_member : Member (chaoticUniverse none) (universeValue none) :=
  chaos_member _

theorem undefined_unit_member : Member (chaoticUniverse none) (unitValue EnvI.bot) :=
  chaos_member _

theorem undefined_unit_not_exact : ¬ SortMember none (unitValue EnvI.bot) :=
  unit_not_sort_member _ _

/-- A concrete failure of the existing universe elimination conclusion. -/
theorem exact_elimination_fails :
    ¬ (∀ x : Value, Member (chaoticUniverse none) x → SortMember none x ∧ TypeDefined x) := by
  intro h
  exact undefined_unit_not_exact (h _ undefined_unit_member).1

/-- No change of the code predicate can attach universal chaos at `none`
while retaining every field of the old CodeSystem. -/
theorem no_chaotic_codeSystem (C : CodeSystem) :
    ¬ Same (C.universePER none) Chaos := by
  intro h
  have hm : Member (C.universePER none) (unitValue EnvI.bot) :=
    (h _ _).mpr (chaos_member _)
  exact undefined_unit_not_exact (C.universe_elim (C.universe_code none) hm).1

theorem distinct_sort_values (k : Nat) :
    ¬ ValueEq (universeValue none) (universeValue (some k)) := by
  intro h
  have he : (none : Option Nat) = some k := sort_code_injective h
  cases he

/-- Raw tag injectivity survives, although chaotic relatedness identifies
the two distinct values. Extraction uses membership, not raw equality. -/
theorem chaotic_sort_pair (k : Nat) :
    Chaos (universeValue none) (universeValue (some k)) ∧
    ¬ ValueEq (universeValue none) (universeValue (some k)) :=
  ⟨True.intro, distinct_sort_values k⟩

theorem overlap_inhabited :
    Member (chaoticUniverse none) (universeValue (some 0)) ∧
    Member (chaoticUniverse (some 1)) (universeValue (some 0)) ∧
    TypeDefined (universeValue (some 0)) ∧ (none : Option Nat) ≠ some 1 :=
  ⟨chaos_member _, NeutralCodes.universe_member (some 0), sort_defined _ _,
    fun h => Option.noConfusion h⟩

theorem membership_indices_not_unique :
    ¬ (∀ (i j : Option Nat) (x : Value), Member (chaoticUniverse i) x →
      Member (chaoticUniverse j) x → TypeDefined x → i = j) := by
  intro h
  obtain ⟨hn, hs, hd, hne⟩ := overlap_inhabited
  exact hne (h _ _ _ hn hs hd)

def source_defined_sort : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 []
    (.sort .zero) (.sort (.succ .zero)) := .sort [] .zero

theorem source_defined_image :
    ValueEq (UnitModel.denote UniverseDecoderBoundary.noneValuation EnvI.bot (.sort .zero))
      (universeValue (some 0)) := ValueEq.refl _

/-- Both source sort derivations, the admitted environment, the empty
context and its paired realization are actual supplied data. The overlap
is a counterexample to the semantic extraction law, not to source SortUniq. -/
theorem admitted_overlap_control :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 [] (.sort .zero)
      (.sort (.succ .zero))) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 [] UniverseDecoderBoundary.noneSort
      (.sort (.succ (.param 0)))) ∧
    PairedRealises (FunctionEval.annSemantics NeutralCodes.codeSystem)
      UniverseDecoderBoundary.noneValuation UniverseDecoderBoundary.noneValuation
      [] EnvI.bot EnvI.bot ∧
    Member (chaoticUniverse none) (universeValue (some 0)) ∧
    Member (chaoticUniverse (some 1)) (universeValue (some 0)) ∧
    TypeDefined (universeValue (some 0)) ∧ (none : Option Nat) ≠ some 1 :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨source_defined_sort⟩,
    ⟨UniverseDecoderBoundary.source_none_sort⟩, .nil _ _, overlap_inhabited⟩

/-- The actual source context affected by forgetting all information in
an undefined universe: its single variable is itself a type. -/
def undefinedContext : LCtxA := [.assumption (.sort (.param 0))]

def undefinedContext_wf :
    CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 undefinedContext :=
  .assumption .nil (.sort [] (.param 0))

def undefinedVariable_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 undefinedContext
      (.bvar 0) (.sort (.param 0)) :=
  .bvar _ 0 (.sort (.param 0)) (.succ (.param 0)) rfl (.sort _ (.param 0))

def unitEnvironment : EnvI := EnvI.cons (unitValue EnvI.bot) EnvI.bot

theorem unit_variable_image :
    ValueEq (UnitModel.denote UniverseDecoderBoundary.noneValuation unitEnvironment (.bvar 0))
      (unitValue EnvI.bot) := by
  change ValueEq (denI unitEnvironment (.bvar 0)) (unitValue EnvI.bot)
  intro c
  constructor
  · intro hc
    rcases approxI_bvar_inv hc with hc | hc
    · subst c
      exact ApproxI.bot _ _
    · exact hc
  · intro hc
    exact ApproxI.bvar hc

/-- A raw universe-membership clause admits this actual unit assignment.
Its variable image fails exact membership despite the source typing. -/
theorem raw_variable_control :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 undefinedContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 undefinedContext
      (.bvar 0) (.sort (.param 0))) ∧
    Member (chaoticUniverse none) (unitEnvironment 0) ∧
    ¬ SortMember none
      (UnitModel.denote UniverseDecoderBoundary.noneValuation unitEnvironment (.bvar 0)) := by
  refine ⟨⟨.empty⟩, ⟨undefinedContext_wf⟩, ⟨undefinedVariable_typed⟩,
    chaos_member _, ?_⟩
  intro h
  exact undefined_unit_not_exact (sortMember_congr unit_variable_image h)

theorem raw_lookup_extraction_refuted :
    ¬ (∀ ρ : EnvI, Member (chaoticUniverse none) (ρ 0) →
      SortMember none (UnitModel.denote UniverseDecoderBoundary.noneValuation ρ (.bvar 0))) := by
  intro h
  exact raw_variable_control.2.2.2.2 (h unitEnvironment (chaos_member _))

/-- Forget payloads only after retaining an exact level and definedness. -/
def TaggedChaos (k : Option Nat) (x y : Value) : Prop :=
  (SortMember k x ∧ TypeDefined x) ∧ (SortMember k y ∧ TypeDefined y)

theorem taggedChaos_laws (k : Option Nat) : Laws (TaggedChaos k) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h g => ⟨h.1, g.2⟩⟩

theorem taggedChaos_member_iff (k : Option Nat) (x : Value) :
    Member (TaggedChaos k) x ↔ SortMember k x ∧ TypeDefined x :=
  ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem taggedChaos_indices_unique {i j : Option Nat} {x : Value}
    (hi : Member (TaggedChaos i) x) (hj : Member (TaggedChaos j) x) : i = j :=
  sortMember_unique hi.1.1 hj.1.1 hi.1.2

theorem taggedChaos_not_universal (k : Option Nat) : ¬ Same (TaggedChaos k) Chaos := by
  intro h
  exact unit_not_sort_member EnvI.bot k ((h _ _).mpr (chaos_member _)).1.1

/-- A fixed, nonrecursive undefined code relation. This fragment assigns
one carrier to every defined type value with the undefined tag. -/
def NoneCode (V : Value) (R : Relation) : Prop :=
  SortMember none V ∧ TypeDefined V ∧ Same R (TaggedChaos none)

theorem noneCode_laws {V : Value} {R : Relation} (h : NoneCode V R) : Laws R :=
  ⟨fun hxy => (h.2.2 _ _).mpr ((taggedChaos_laws none).symm ((h.2.2 _ _).mp hxy)),
    fun hxy hyz => (h.2.2 _ _).mpr
      ((taggedChaos_laws none).trans ((h.2.2 _ _).mp hxy) ((h.2.2 _ _).mp hyz))⟩

theorem noneCode_coherent {V W : Value} {R S : Relation}
    (h : NoneCode V R) (g : NoneCode W S) : Same R S :=
  fun x y => (h.2.2 x y).trans (g.2.2 x y).symm

theorem none_universe_code : NoneCode (universeValue none) (TaggedChaos none) :=
  ⟨sort_member _ none, sort_defined _ none, fun _ _ => Iff.rfl⟩

theorem none_universe_member : Member (TaggedChaos none) (universeValue none) :=
  ⟨⟨sort_member _ none, sort_defined _ none⟩, ⟨sort_member _ none, sort_defined _ none⟩⟩

/-- Decoding does not consume a smaller derivation and includes the
universe's actual self-member. -/
theorem none_universe_decode {V : Value} (h : Member (TaggedChaos none) V) :
    NoneCode V (TaggedChaos none) := ⟨h.1.1, h.1.2, fun _ _ => Iff.rfl⟩

theorem none_code_reflection {V : Value} {R : Relation} (h : NoneCode V R) (name : Nat) :
    Member R (NeutralCodes.neutralTypeValue none name) := by
  apply (h.2.2 _ _).mpr
  have ht := NeutralCodes.reify_level (.neutralType none name)
  have hd := NeutralCodes.reify_defined (.neutralType none name)
  exact ⟨⟨ht, hd⟩, ⟨ht, hd⟩⟩

theorem none_code_elimination {V x : Value} {R : Relation}
    (h : NoneCode V R) (hx : Member R x) : SortMember none x ∧ TypeDefined x :=
  ((h.2.2 _ _).mp hx).1

theorem tagged_self_decode_control (name : Nat) :
    NoneCode (universeValue none) (TaggedChaos none) ∧
    Member (TaggedChaos none) (universeValue none) ∧
    Member (TaggedChaos none) (NeutralCodes.neutralTypeValue none name) :=
  ⟨none_universe_code, none_universe_member, none_code_reflection none_universe_code name⟩

end Rcic.Declarative.Ann.LR3.NoneUniverseBoundary
