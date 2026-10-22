import rcic.RcicAnnLR3UnitTypedEq

/-!
# Truth-valued proof PERs and legal-domain dependent function PERs

All relations are independent of source derivations. A true proposition
has exactly the nonbottom unit equivalence class; a false one has no
members. Function PERs quantify only over related domain arguments.
No universe decoder or global source soundness is assumed or supplied.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TypedPER
open UnitModel
open Rcic.Declarative.NativeValleys.PiModelIdealAudit

abbrev Relation := Value → Value → Prop
structure Laws (R : Relation) : Prop where
  symm : ∀ {x y}, R x y → R y x
  trans : ∀ {x y z}, R x y → R y z → R x z

def Member (R : Relation) (x : Value) : Prop := R x x

theorem left_member {R : Relation} (hR : Laws R) {x y : Value} (h : R x y) : Member R x :=
  hR.trans h (hR.symm h)
theorem right_member {R : Relation} (hR : Laws R) {x y : Value} (h : R x y) : Member R y :=
  hR.trans (hR.symm h) h

def Same (R S : Relation) : Prop := ∀ x y, R x y ↔ S x y

def TruthPER (truth : Prop) (x y : Value) : Prop :=
  truth ∧ ProofPER EnvI.bot x y

theorem truthPER_laws (truth : Prop) : Laws (TruthPER truth) where
  symm := fun h => ⟨h.1, proofPER_symm h.2⟩
  trans := fun h g => ⟨h.1, proofPER_trans h.2 g.2⟩

theorem truthPER_member_iff (truth : Prop) (x : Value) :
    Member (TruthPER truth) x ↔ truth ∧ ProofMember EnvI.bot x :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h.2⟩⟩

theorem truthPER_inhabited_iff (truth : Prop) :
    (∃ x : Value, Member (TruthPER truth) x) ↔ truth := by
  constructor
  · rintro ⟨x, hx⟩; exact hx.1
  · intro ht; exact ⟨unitValue EnvI.bot, ht, unit_member _, unit_member _⟩

theorem falsePER_empty (x y : Value) : ¬ TruthPER False x y := fun h => h.1

theorem truthPER_irrelevant {truth : Prop} {x y : Value}
    (hx : Member (TruthPER truth) x) (hy : Member (TruthPER truth) y) :
    TruthPER truth x y := ⟨hx.1, hx.2.1, hy.2.1⟩

def EqPER (R : Relation) (a b : Value) : Relation := TruthPER (R a b)

theorem eqPER_inhabited_iff (R : Relation) (a b : Value) :
    (∃ p : Value, Member (EqPER R a b) p) ↔ R a b := truthPER_inhabited_iff _

theorem eqPER_refl {R : Relation} {a : Value} (ha : Member R a) :
    Member (EqPER R a a) (unitValue EnvI.bot) :=
  ⟨ha, unit_member _, unit_member _⟩

/-- Exact universe membership plus equality, not cumulative membership. -/
def SortPER (k : Option Nat) (x y : Value) : Prop :=
  SortMember k x ∧ TypeDefined x ∧ ValueEq x y

theorem sortPER_laws (k : Option Nat) : Laws (SortPER k) where
  symm := fun h => ⟨sortMember_congr h.2.2 h.1,
    typeDefined_congr h.2.2 h.2.1, h.2.2.symm⟩
  trans := fun h g => ⟨h.1, h.2.1, h.2.2.trans g.2.2⟩

theorem sortPER_member_iff (k : Option Nat) (x : Value) :
    Member (SortPER k) x ↔ SortMember k x ∧ TypeDefined x :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ValueEq.refl _⟩⟩

theorem sortPER_indices_unique {i j : Option Nat} {x : Value}
    (hi : Member (SortPER i) x) (hj : Member (SortPER j) x) : i = j :=
  sortMember_unique hi.1 hj.1 hi.2.1

/-- Extensional family of PERs over the admitted domain, not over all raw
arguments. This law is independent of any source conversion judgment. -/
def FamilyCoherent (D : Relation) (C : Value → Relation) : Prop :=
  ∀ x y, D x y → Same (C x) (C y)

def FunctionPER (app : Value → Value → Value) (D : Relation)
    (C : Value → Relation) (f g : Value) : Prop :=
  ∀ x y, D x y → C x (app f x) (app g y)

theorem functionPER_laws (app : Value → Value → Value) {D : Relation}
    (hD : Laws D) {C : Value → Relation}
    (hC : ∀ x, Member D x → Laws (C x)) (hc : FamilyCoherent D C) :
    Laws (FunctionPER app D C) where
  symm := by
    intro f g h x y hxy
    have hyx := hD.symm hxy
    have hr := hC y (right_member hD hxy)
    exact (hc y x hyx _ _).mp (hr.symm (h y x hyx))
  trans := by
    intro f g h hfg hgh x y hxy
    have hx := left_member hD hxy
    have hy := right_member hD hxy
    have hmid := (hc y x (hD.symm hxy) _ _).mp (hgh y y hy)
    exact (hC x hx).trans (hfg x y hxy) hmid

/-- Impredicative truth of a proposition-valued product. The quantification
is in Lean Prop even when its domain is large or empty. -/
def ForallTruth (D : Relation) (truth : Value → Prop) : Prop :=
  ∀ x, Member D x → truth x

def PropFunctionPER (D : Relation) (truth : Value → Prop) : Relation :=
  TruthPER (ForallTruth D truth)

theorem propFunctionPER_laws (D : Relation) (truth : Value → Prop) :
    Laws (PropFunctionPER D truth) := truthPER_laws _

theorem propFunction_member_iff (D : Relation) (truth : Value → Prop) :
    (∃ p : Value, Member (PropFunctionPER D truth) p) ↔
      (∀ x, Member D x → truth x) := truthPER_inhabited_iff _

/-- A proof projection is a semantic operation, not source synthesis. Its
use in a full evaluator still needs the typing and application laws. -/
def proofProject (_ : Value) : Value := unitValue EnvI.bot

theorem proofProject_sound {truth : Prop} {x : Value}
    (h : Member (TruthPER truth) x) :
    Member (TruthPER truth) (proofProject x) :=
  ⟨h.1, unit_member _, unit_member _⟩

end Rcic.Declarative.Ann.LR3.TypedPER
