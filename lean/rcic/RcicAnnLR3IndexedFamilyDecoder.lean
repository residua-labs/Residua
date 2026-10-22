import rcic.RcicAnnLR3FunctionalLabelPositions

/-!
# Indexed signatures by constructive descent of retained data

Result indices and child-index functions are retained on explicit legal
labels. Their coherence supplies actual quotient lifts: ordinary descent
for results and dependent descent for the position-indexed child map.
The resulting indexed signature carries result equations in its rules.
No label, position, index or tree is selected from a proposition.

The construction accepts already supplied semantic index data. It does
not infer those data or their coherence from a source typing derivation.
Source extraction and admitted controls are separate. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.IndexedFamilyDecoder

open Rcic.Declarative
open UnitModel TypedInductive NeutralDataFamily

universe u v w l

/-- Transport of a function is determined by its action on transported inputs. -/
theorem function_transport {Q : Type u} {P : Q → Type v} {Index : Type w}
    {q r : Q} (h : q = r) (f : P q → Index) (g : P r → Index)
    (hf : ∀ p, f p = g (DependentFamily.transport P h p)) :
    DependentFamily.transport (fun z => P z → Index) h f = g := by
  cases h
  exact funext hf

/-- Both maps are actual data. The child map has the complete position
type over the label's class, and coherence transports that position. -/
structure RawData {A : Type u} (s : Setoid A)
    (Position : Quotient s → Type v) (Index : Type w) where
  result : A → Index
  result_coherent : ∀ a b, s.r a b → result a = result b
  child : ∀ a, Position (Quotient.mk s a) → Index
  child_coherent : ∀ a b (h : s.r a b) p,
    child a p = child b (DependentFamily.transport Position (Quotient.sound h) p)

def result {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) : Quotient s → Index :=
  Quotient.lift D.result D.result_coherent

theorem result_class {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) (a : A) : result D (Quotient.mk s a) = D.result a := rfl

theorem child_descent {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) (a b : A) (h : s.r a b) :
    DependentFamily.transport (fun q => P q → Index) (Quotient.sound h) (D.child a) =
      D.child b :=
  function_transport (Quotient.sound h) (D.child a) (D.child b) (D.child_coherent a b h)

/-- Dependent quotient descent constructs the child-index map on every
class. Its input position remains data throughout the construction. -/
def child {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) (q : Quotient s) : P q → Index :=
  DependentFamily.dependentQuotientLift s (fun q => P q → Index)
    D.child (child_descent D) q

theorem child_class {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) (a : A) (p : P (Quotient.mk s a)) :
    child D (Quotient.mk s a) p = D.child a p := rfl

theorem child_transport {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) {q r : Quotient s} (h : q = r) (p : P q) :
    child D q p = child D r (DependentFamily.transport P h p) := by
  cases h
  rfl

/-- The rule carries its actual result-index equation. The complete
dependent child-index map is read directly from the quotient class. -/
def signature {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) : Signature Index where
  Rule := fun i => {q : Quotient s // result D q = i}
  Premise := fun _ r => P r.1
  child := fun _ r p => child D r.1 p

def ruleClass {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) (q : Quotient s) : (signature D).Rule (result D q) := ⟨q, rfl⟩

def rule {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) (a : A) : (signature D).Rule (D.result a) :=
  ruleClass D (Quotient.mk s a)

theorem ruleClass_child {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) (q : Quotient s) (p : P q) :
    (signature D).child (result D q) (ruleClass D q) p = child D q p := rfl

theorem rule_child {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
    (D : RawData s P Index) (a : A) (p : P (Quotient.mk s a)) :
    (signature D).child (D.result a) (rule D a) p = D.child a p := rfl

section Trees

variable {A : Type u} {s : Setoid A} {P : Quotient s → Type v} {Index : Type w}
  (D : RawData s P Index) (Leaf : Index → Type l)
  (RN : ∀ i, Leaf i → Leaf i → Prop)

abbrev Legal (i : Index) := LegalTree (signature D) Leaf RN i

/-- Both positions and the child-index fibres are explicit in the input. -/
abbrev Children (q : Quotient s) := ∀ p : P q, Legal D Leaf RN (child D q p)

def nodeClass (q : Quotient s) (children : Children D Leaf RN q) :
    Legal D Leaf RN (result D q) :=
  legalNode (signature D) Leaf RN (result D q) (ruleClass D q) children

def node (a : A) (children : Children D Leaf RN (Quotient.mk s a)) :
    Legal D Leaf RN (D.result a) := nodeClass D Leaf RN (Quotient.mk s a) children

/-- Root-index transport and all dependent position/child transports are
the ordinary equality transports induced by equality of label classes. -/
theorem nodeClass_transport {q r : Quotient s} (h : q = r)
    (xs : Children D Leaf RN q) :
    DependentFamily.transport (Legal D Leaf RN) (congrArg (result D) h)
      (nodeClass D Leaf RN q xs) =
    nodeClass D Leaf RN r (DependentFamily.transport (Children D Leaf RN) h xs) := by
  cases h
  rfl

theorem nodeClass_related {q r : Quotient s} (h : q = r)
    (xs : Children D Leaf RN q) (ys : Children D Leaf RN r)
    (hc : ∀ p, Bisim (signature D) Leaf RN
      ((DependentFamily.transport (Children D Leaf RN) h xs) p).1 (ys p).1) :
    Bisim (signature D) Leaf RN
      (DependentFamily.transport (Legal D Leaf RN) (congrArg (result D) h)
        (nodeClass D Leaf RN q xs)).1 (nodeClass D Leaf RN r ys).1 := by
  cases h
  change Bisim (signature D) Leaf RN
    (.node (result D q) (ruleClass D q) (fun p => (xs p).1))
    (.node (result D q) (ruleClass D q) (fun p => (ys p).1))
  exact Bisim.node (S := signature D) (Leaf := Leaf) (RN := RN)
    (result D q) (ruleClass D q) _ _ hc

variable (hRN : ∀ i, RelLaws (RN i))

abbrev Family (i : Index) :=
  DependentFamily.FamilyQuotient (S := signature D) (Leaf := Leaf) hRN i

def decodeClass (q : Quotient s) (children : Children D Leaf RN q) :
    Family D Leaf RN hRN (result D q) :=
  DependentFamily.treeClass hRN (nodeClass D Leaf RN q children)

theorem treeClass_transport {i j : Index} (h : i = j) (t : Legal D Leaf RN i) :
    DependentFamily.transport (Family D Leaf RN hRN) h (DependentFamily.treeClass hRN t) =
    DependentFamily.treeClass hRN (DependentFamily.transport (Legal D Leaf RN) h t) := by
  cases h
  rfl

theorem decodeClass_related {q r : Quotient s} (h : q = r)
    (xs : Children D Leaf RN q) (ys : Children D Leaf RN r)
    (hc : ∀ p, Bisim (signature D) Leaf RN
      ((DependentFamily.transport (Children D Leaf RN) h xs) p).1 (ys p).1) :
    DependentFamily.transport (Family D Leaf RN hRN) (congrArg (result D) h)
      (decodeClass D Leaf RN hRN q xs) = decodeClass D Leaf RN hRN r ys := by
  rw [decodeClass, treeClass_transport]
  exact Quotient.sound (nodeClass_related D Leaf RN h xs ys hc)

end Trees

end Rcic.Declarative.Ann.LR3.IndexedFamilyDecoder
