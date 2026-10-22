import rcic.RcicAnnLR3FamilyLabelQuotient

/-!
# Arbitrary finite dependent constructor labels

`Fields n` is explicit raw data. A telescope extends a prefix by a relation
indexed by those raw fields; it does not refer recursively to a decoding
function in its datatype. Local fibre laws and coherence compose into the
PER on every finite telescope. Legal labels retain all field values.

The next-field relation descends constructively to the prefix quotient.
The complete label quotient gives a nonrecursive constructor signature,
legal trees and their quotient, with forward field congruence. No value or
tree is selected from a proposition or a quotient.

This supplies the finite nonrecursive label algebra. It does not turn
source field typings into codes, identify evaluator constructor values,
or supply a generic source recursor. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.FiniteFamilyLabels

open Rcic.Declarative
open UnitModel TypedPER TypedInductive NeutralDataFamily

universe u

/-- Fields are in source order: a prefix followed by its latest value. -/
def Fields : Nat → Type
  | 0 => Unit
  | n + 1 => Fields n × Value

def Fields.toList : {n : Nat} → Fields n → List Value
  | 0, _ => []
  | _ + 1, xs => Fields.toList xs.1 ++ [xs.2]

theorem Fields.toList_length : {n : Nat} → (xs : Fields n) → xs.toList.length = n
  | 0, _ => rfl
  | n + 1, xs => by
      simp only [Fields.toList, List.length_append, List.length_singleton,
        Fields.toList_length xs.1]

/-- The fibre has a raw data index, so this is an ordinary positive datatype. -/
inductive Telescope : Nat → Type
  | empty : Telescope 0
  | snoc {n : Nat} (prior : Telescope n) (fibre : Fields n → Relation) : Telescope (n + 1)

def FieldRel : {n : Nat} → Telescope n → Fields n → Fields n → Prop
  | _, .empty, _, _ => True
  | _, .snoc T C, xs, ys => FieldRel T xs.1 ys.1 ∧ C xs.1 xs.2 ys.2

/-- Only legal prefixes need lawful fibres. Related prefixes have the
same fibre relation, even when their underlying field values differ. -/
def Coherent : {n : Nat} → Telescope n → Prop
  | _, .empty => True
  | _, .snoc T C => Coherent T ∧
      (∀ xs, FieldRel T xs xs → Laws (C xs)) ∧
      (∀ xs ys, FieldRel T xs ys → Same (C xs) (C ys))

theorem coherent_empty : Coherent .empty := True.intro

theorem coherent_snoc {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent T)
    (hC : ∀ xs, FieldRel T xs xs → Laws (C xs))
    (hcoh : ∀ xs ys, FieldRel T xs ys → Same (C xs) (C ys)) :
    Coherent (.snoc T C) := ⟨hT, hC, hcoh⟩

theorem fieldRel_laws {n : Nat} (T : Telescope n) (hT : Coherent T) :
    RelLaws (FieldRel T) := by
  induction T with
  | empty => exact ⟨fun _ => True.intro, fun _ _ => True.intro⟩
  | snoc T C ih =>
      have hp := ih hT.1
      refine ⟨?_, ?_⟩
      · intro xs ys hxy
        have hx : FieldRel T xs.1 xs.1 := hp.trans hxy.1 (hp.symm hxy.1)
        exact ⟨hp.symm hxy.1,
          (hT.2.2 xs.1 ys.1 hxy.1 _ _).mp ((hT.2.1 xs.1 hx).symm hxy.2)⟩
      · intro xs ys zs hxy hyz
        have hx : FieldRel T xs.1 xs.1 := hp.trans hxy.1 (hp.symm hxy.1)
        exact ⟨hp.trans hxy.1 hyz.1,
          (hT.2.1 xs.1 hx).trans hxy.2 ((hT.2.2 xs.1 ys.1 hxy.1 _ _).mpr hyz.2)⟩

theorem fieldRel_left {n : Nat} {T : Telescope n} (hT : Coherent T)
    {xs ys : Fields n} (h : FieldRel T xs ys) : FieldRel T xs xs :=
  (fieldRel_laws T hT).trans h ((fieldRel_laws T hT).symm h)

theorem fieldRel_right {n : Nat} {T : Telescope n} (hT : Coherent T)
    {xs ys : Fields n} (h : FieldRel T xs ys) : FieldRel T ys ys :=
  (fieldRel_laws T hT).trans ((fieldRel_laws T hT).symm h) h

abbrev Label {n : Nat} (T : Telescope n) := {xs : Fields n // FieldRel T xs xs}

def emptyLabel : Label .empty := ⟨(), True.intro⟩

def snocLabel {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (xs : Label T) (x : Value) (hx : Member (C xs.1) x) : Label (.snoc T C) :=
  ⟨(xs.1, x), xs.2, hx⟩

def prefixLabel {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (xs : Label (.snoc T C)) : Label T := ⟨xs.1.1, xs.2.1⟩

def lastValue {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (xs : Label (.snoc T C)) : Value := xs.1.2

theorem lastValue_member {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (xs : Label (.snoc T C)) : Member (C (prefixLabel xs).1) (lastValue xs) := xs.2.2

theorem prefix_snoc {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (xs : Label T) (x : Value) (hx : Member (C xs.1) x) :
    prefixLabel (snocLabel xs x hx) = xs := rfl

theorem snoc_prefix {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (xs : Label (.snoc T C)) :
    snocLabel (prefixLabel xs) (lastValue xs) (lastValue_member xs) = xs := by
  cases xs with
  | mk xs h => cases xs; rfl

def LabelRel {n : Nat} {T : Telescope n} (xs ys : Label T) : Prop :=
  FieldRel T xs.1 ys.1

theorem labelRel_refl {n : Nat} {T : Telescope n} (xs : Label T) : LabelRel xs xs := xs.2

theorem labelRel_laws {n : Nat} {T : Telescope n} (hT : Coherent T) :
    RelLaws (fun xs ys : Label T => LabelRel xs ys) :=
  ⟨(fieldRel_laws T hT).symm, (fieldRel_laws T hT).trans⟩

theorem snocLabel_related {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    {xs ys : Label T} (hxy : LabelRel xs ys)
    {x y : Value} (hx : Member (C xs.1) x) (hy : Member (C ys.1) y)
    (h : C xs.1 x y) : LabelRel (snocLabel xs x hx) (snocLabel ys y hy) := ⟨hxy, h⟩

def labelSetoid {n : Nat} {T : Telescope n} (hT : Coherent T) : Setoid (Label T) where
  r := LabelRel
  iseqv := ⟨labelRel_refl, (labelRel_laws hT).symm, (labelRel_laws hT).trans⟩

abbrev Class {n : Nat} {T : Telescope n} (hT : Coherent T) := Quotient (labelSetoid hT)

def classify {n : Nat} {T : Telescope n} (hT : Coherent T) (xs : Label T) : Class hT :=
  Quotient.mk _ xs

theorem classify_related {n : Nat} {T : Telescope n} (hT : Coherent T)
    {xs ys : Label T} (h : LabelRel xs ys) : classify hT xs = classify hT ys :=
  Quotient.sound h

/-- A next-field PER is decoded directly from the prefix quotient.
Coherence proves the lift; it does not choose a prefix representative. -/
def fibreOnClass {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) : Class hT.1 → Relation :=
  Quotient.lift (fun xs : Label T => C xs.1)
    (fun xs ys h => funext fun x => funext fun y => propext (hT.2.2 xs.1 ys.1 h x y))

theorem fibreOnClass_classify {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (xs : Label T) :
    fibreOnClass hT (classify hT.1 xs) = C xs.1 := rfl

theorem fibreOnClass_laws {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (q : Class hT.1) : Laws (fibreOnClass hT q) := by
  refine Quotient.inductionOn q ?_
  intro xs
  exact hT.2.1 xs.1 xs.2

theorem fibre_transport {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {xs ys : Label T} (h : LabelRel xs ys) :
    Same (C xs.1) (C ys.1) := hT.2.2 xs.1 ys.1 h

theorem fibre_member_transport {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {xs ys : Label T} (h : LabelRel xs ys)
    {x : Value} (hx : Member (C xs.1) x) : Member (C ys.1) x :=
  (fibre_transport hT h x x).mp hx

/-- Every constructor label uses the quotient of its complete finite telescope. -/
def signature {n : Nat} {T : Telescope n} (hT : Coherent T) : Signature Unit where
  Rule := fun _ => Class hT
  Premise := fun _ _ => Empty
  child := fun _ _ p => nomatch p

abbrev leafRel := FamilyLabelQuotient.leafRel
abbrev leaf_laws := FamilyLabelQuotient.leaf_laws

def nodeClass {n : Nat} {T : Telescope n} (hT : Coherent T) (q : Class hT) :
    LegalTree (signature hT) (fun _ => Nat) leafRel () :=
  legalNode (signature hT) (fun _ => Nat) leafRel () q (fun p => nomatch p)

def node {n : Nat} {T : Telescope n} (hT : Coherent T) (xs : Label T) :
    LegalTree (signature hT) (fun _ => Nat) leafRel () := nodeClass hT (classify hT xs)

theorem node_related {n : Nat} {T : Telescope n} (hT : Coherent T)
    {xs ys : Label T} (h : LabelRel xs ys) :
    Bisim (signature hT) (fun _ => Nat) leafRel (node hT xs).1 (node hT ys).1 := by
  have he := classify_related hT h
  change Bisim _ _ _ (nodeClass hT (classify hT xs)).1 (nodeClass hT (classify hT ys)).1
  rw [he]
  exact (nodeClass hT (classify hT ys)).2

abbrev Family {n : Nat} {T : Telescope n} (hT : Coherent T) :=
  DependentFamily.FamilyQuotient (S := signature hT) (Leaf := fun _ => Nat) leaf_laws ()

def decodeClass {n : Nat} {T : Telescope n} (hT : Coherent T) (q : Class hT) : Family hT :=
  DependentFamily.treeClass leaf_laws (nodeClass hT q)

def decode {n : Nat} {T : Telescope n} (hT : Coherent T) (xs : Label T) : Family hT :=
  decodeClass hT (classify hT xs)

theorem decode_related {n : Nat} {T : Telescope n} (hT : Coherent T)
    {xs ys : Label T} (h : LabelRel xs ys) : decode hT xs = decode hT ys :=
  Quotient.sound (node_related hT h)

theorem decode_transport {n : Nat} {T : Telescope n} (hT : Coherent T)
    {xs ys : Label T} (h : LabelRel xs ys)
    (M : Family hT → Type u) (values : ∀ q, M q) :
    DependentFamily.transport M (decode_related hT h) (values (decode hT xs)) =
      values (decode hT ys) := by
  have ht : ∀ (a b : Family hT) (he : a = b),
      DependentFamily.transport M he (values a) = values b := by
    intro a b he
    cases he
    rfl
  exact ht _ _ _

end Rcic.Declarative.Ann.LR3.FiniteFamilyLabels
