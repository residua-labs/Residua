import rcic.RcicAnnLR3GuardedOpenEqCall
import rcic.RcicAnnLR3StratifiedCandidates

/-! The exact disjunctive guarded relation and its constructive boundary.
The relation itself and its PER laws need no decision of the guard. Any
relation witness, however, already proves the guard or its negation.
The source-bound results below use the previously constructed actual open
Eq call and all its input-image evidence. They do not define its output
interpreter or rule out other guarded relations. closure_claim = 0. -/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedDisjunction

universe u

/-- The disjunctive policy on a common carrier. -/
def rawRelation {A : Type u} (G : Prop) (Rm Rf : A → A → Prop) : A → A → Prop :=
  fun x y => (G ∧ Rm x y) ∨ (¬ G ∧ Rf x y)

theorem guard_or_not {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    {x y : A} (h : rawRelation G Rm Rf x y) : G ∨ ¬ G := by
  rcases h with ⟨hG, _⟩ | ⟨hG, _⟩
  · exact Or.inl hG
  · exact Or.inr hG

theorem of_guard {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    {x y : A} (hG : G) (h : Rm x y) : rawRelation G Rm Rf x y :=
  Or.inl ⟨hG, h⟩

theorem of_not_guard {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    {x y : A} (hG : ¬ G) (h : Rf x y) : rawRelation G Rm Rf x y :=
  Or.inr ⟨hG, h⟩

theorem guard_iff {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    {x y : A} (hG : G) : rawRelation G Rm Rf x y ↔ Rm x y := by
  constructor
  · intro h
    rcases h with ⟨_, hm⟩ | ⟨hn, _⟩
    · exact hm
    · exact False.elim (hn hG)
  · exact of_guard hG

theorem not_guard_iff {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    {x y : A} (hG : ¬ G) : rawRelation G Rm Rf x y ↔ Rf x y := by
  constructor
  · intro h
    rcases h with ⟨hg, _⟩ | ⟨_, hf⟩
    · exact False.elim (hG hg)
    · exact hf
  · exact of_not_guard hG

/-- Branch equalities can be used to transport any existing branch PER
structure or identity isomorphism; no new carrier isomorphism is postulated. -/
theorem relation_eq_of_guard {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    (hG : G) : rawRelation G Rm Rf = Rm := by
  funext x y
  exact propext (guard_iff hG)

theorem relation_eq_of_not_guard {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    (hG : ¬ G) : rawRelation G Rm Rf = Rf := by
  funext x y
  exact propext (not_guard_iff hG)

theorem symmetric {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    (hm : ∀ {x y : A}, Rm x y → Rm y x)
    (hf : ∀ {x y : A}, Rf x y → Rf y x)
    {x y : A} (h : rawRelation G Rm Rf x y) : rawRelation G Rm Rf y x := by
  rcases h with ⟨hG, hxy⟩ | ⟨hG, hxy⟩
  · exact of_guard hG (hm hxy)
  · exact of_not_guard hG (hf hxy)

theorem transitive {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    (hm : ∀ {x y z : A}, Rm x y → Rm y z → Rm x z)
    (hf : ∀ {x y z : A}, Rf x y → Rf y z → Rf x z)
    {x y z : A} (hxy : rawRelation G Rm Rf x y)
    (hyz : rawRelation G Rm Rf y z) : rawRelation G Rm Rf x z := by
  rcases hxy with ⟨hG, hxy⟩ | ⟨hG, hxy⟩
  · exact of_guard hG (hm hxy ((guard_iff hG).mp hyz))
  · exact of_not_guard hG (hf hxy ((not_guard_iff hG).mp hyz))

theorem lawful {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    (hm : NeutralDataFamily.RelLaws Rm) (hf : NeutralDataFamily.RelLaws Rf) :
    NeutralDataFamily.RelLaws (rawRelation G Rm Rf) := by
  constructor
  · intro x y hxy
    exact symmetric (Rm := Rm) (Rf := Rf) hm.symm hf.symm hxy
  · intro x y z hxy hyz
    exact transitive (Rm := Rm) (Rf := Rf) hm.trans hf.trans hxy hyz

theorem shared_pair_iff {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    {x y : A} (hm : Rm x y) (hf : Rf x y) :
    rawRelation G Rm Rf x y ↔ G ∨ ¬ G := by
  constructor
  · exact guard_or_not
  · intro h
    rcases h with hG | hG
    · exact of_guard hG hm
    · exact of_not_guard hG hf

theorem inhabited_iff {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    (hm : ∃ x, Rm x x) (hf : ∃ x, Rf x x) :
    (∃ x, rawRelation G Rm Rf x x) ↔ G ∨ ¬ G := by
  constructor
  · rintro ⟨x, hx⟩
    exact guard_or_not hx
  · intro h
    rcases h with hG | hG
    · obtain ⟨x, hx⟩ := hm
      exact ⟨x, of_guard hG hx⟩
    · obtain ⟨x, hx⟩ := hf
      exact ⟨x, of_not_guard hG hx⟩

/-- If both branches reflect an inhabited class of neutral points, reflection
of that class by the disjunctive relation is exactly guard decidability in Prop. -/
theorem reflection_iff {A : Type u} {G : Prop} {Rm Rf : A → A → Prop}
    (N : A → Prop) (hN : ∃ x, N x)
    (hm : ∀ x, N x → Rm x x) (hf : ∀ x, N x → Rf x x) :
    (∀ x, N x → rawRelation G Rm Rf x x) ↔ G ∨ ¬ G := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hN
    exact guard_or_not (h x hx)
  · intro h x hx
    exact (shared_pair_iff (hm x hx) (hf x hx)).mpr h

/-- The usual neutral-closure rule forces membership at a normal neutral.
For this exact disjunctive relation that already entails G ∨ ¬G. -/
theorem neutral_cr3_implies_guard_or_not {A : Type u} {G : Prop}
    {Rm Rf : A → A → Prop} {N : A → Prop} {step : A → A → Prop}
    {n : A} (hn : N n) (hnormal : ∀ y, ¬ step n y)
    (hcr3 : ∀ x, N x →
      (∀ y, step x y → rawRelation G Rm Rf y y) →
      rawRelation G Rm Rf x x) : G ∨ ¬ G := by
  apply guard_or_not (hcr3 n hn ?_)
  intro y hy
  exact False.elim (hnormal y hy)

/-- The actual PointedPER API requires a member at every name. Even its
name-zero member decides the guard when the relation is this disjunction. -/
theorem pointed_guard_or_not {A : Type u} {k : Nat} {G : Prop}
    {Rm Rf : A → A → Prop} (C : StratifiedCandidates.PointedPER k A)
    (h : C.relation = rawRelation G Rm Rf) : G ∨ ¬ G := by
  have hp := C.point_member 0
  rw [h] at hp
  exact guard_or_not hp

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TaggedSaturatedTower
open GuardedReaderSource GuardedOpenEqCall

/-- This property imposes guarded self-membership on the already interpreted
all-P source-input class. Rm and Rf are explicit common-carrier relations;
no source recursor-result image is included or assumed. -/
def InterpretedMemberTotal {A : Type u} (ν : Valuation)
    (Rm Rf : PolicyInput → A → A → Prop) : Prop :=
  ∀ P : Prop, ∃ (i : PolicyInput) (x : A),
    i.assignment = propositionAssignment P 0 ∧ InputImages ν i ∧
    rawRelation (guard i.assignment) (Rm i) (Rf i) x x

theorem interpreted_member_total_implies_em {A : Type u} {ν : Valuation}
    {Rm Rf : PolicyInput → A → A → Prop}
    (h : InterpretedMemberTotal ν Rm Rf) : ∀ P : Prop, P ∨ ¬ P := by
  intro P
  obtain ⟨i, x, hi, _, hx⟩ := h P
  have hg := guard_or_not hx
  rw [hi] at hg
  exact (or_congr (proposition_guard_iff P 0)
    (not_congr (proposition_guard_iff P 0))).mp hg

theorem interpreted_member_total_iff_em {A : Type u} (ν : Valuation)
    (Rm Rf : PolicyInput → A → A → Prop)
    (hm : ∀ i, InputImages ν i → ∃ x, Rm i x x)
    (hf : ∀ i, InputImages ν i → ∃ x, Rf i x x) :
    InterpretedMemberTotal ν Rm Rf ↔ (∀ P : Prop, P ∨ ¬ P) := by
  constructor
  · exact interpreted_member_total_implies_em
  · intro hem P
    obtain ⟨i, hi, himages⟩ := proposition_policy_images ν P
    have hg : guard i.assignment ∨ ¬ guard i.assignment := by
      rw [hi]
      exact (or_congr (proposition_guard_iff P 0)
        (not_congr (proposition_guard_iff P 0))).mpr (hem P)
    obtain ⟨x, hx⟩ := (inhabited_iff (hm i himages) (hf i himages)).mpr hg
    exact ⟨i, x, hi, himages, hx⟩

/-- A concrete certified branch on the common raw-value carrier. -/
def certifiedBranch (P : Prop) : Value → Value → Prop :=
  TaggedKClosure.Decoded (GuardDecision.propCode P)

theorem certified_branch_neutral_member (P : Prop) (name : Nat) :
    certifiedBranch P (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) := by
  apply (TaggedKClosure.decoded_member_iff (GuardDecision.propCode P) _).mpr
  refine ⟨⟨NeutralPER.neutralAtom name⟩,
    GuardDecision.propCode_neutral_member P name, ?_⟩
  intro c
  rfl

/-- Both certified endpoints have the same raw type image and contain the
same neutral. Disjunctively guarding them still demands the excluded middle
instance for that point. This control is not a new source output interpreter. -/
theorem certified_neutral_control (G : Prop) (name : Nat) :
    (GuardDecision.propCode True).view.value =
      (GuardDecision.propCode False).view.value ∧
    certifiedBranch True (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) ∧
    certifiedBranch False (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) ∧
    (rawRelation G (certifiedBranch True) (certifiedBranch False)
      (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) ↔ G ∨ ¬ G) :=
  ⟨rfl, certified_branch_neutral_member True name,
    certified_branch_neutral_member False name,
    shared_pair_iff (certified_branch_neutral_member True name)
      (certified_branch_neutral_member False name)⟩

def InterpretedNeutralTotal (ν : Valuation) : Prop :=
  ∀ P : Prop, ∃ i : PolicyInput,
    i.assignment = propositionAssignment P 0 ∧ InputImages ν i ∧
    rawRelation (guard i.assignment) (certifiedBranch True) (certifiedBranch False)
      (NeutralPER.neutralAtom 0) (NeutralPER.neutralAtom 0)

theorem interpreted_neutral_total_iff_em (ν : Valuation) :
    InterpretedNeutralTotal ν ↔ (∀ P : Prop, P ∨ ¬ P) := by
  constructor
  · intro h
    apply interpreted_member_total_implies_em (ν := ν)
      (Rm := fun _ => certifiedBranch True) (Rf := fun _ => certifiedBranch False)
    intro P
    obtain ⟨i, hi, himages, hx⟩ := h P
    exact ⟨i, NeutralPER.neutralAtom 0, hi, himages, hx⟩
  · intro hem P
    obtain ⟨i, hi, himages⟩ := proposition_policy_images ν P
    refine ⟨i, hi, himages, ?_⟩
    apply (shared_pair_iff (certified_branch_neutral_member True 0)
      (certified_branch_neutral_member False 0)).mpr
    rw [hi]
    exact (or_congr (proposition_guard_iff P 0)
      (not_congr (proposition_guard_iff P 0))).mpr (hem P)

end Rcic.Declarative.Ann.LR3.GuardedDisjunction
