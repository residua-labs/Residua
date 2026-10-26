import rcic.RcicF3Core
import rcic.RcicF3KTWG

/-!
# F3 S7 KT-2b-2: a function field's value is a graph over the quotient of its domain

A function-recursive field `f : Π y : A, F (idx y)` has its value in `piSet ⟦A⟧ B`.  In the
W-type of `RcicF3KTWG` its children are indexed by `FBr A`, the quotient of `A.Idx` by `≈` of the
elements: children are then automatically `≈`-respecting, so the decoded graph is functional.

- `graphOf A h`: the graph `{⟨A.Func i, h ⟦i⟧⟩}`;
- `graph_mem_piSet`: a graph of fibre-valued children is a member of `piSet A B`;
- `exists_graph_of_mem_piSet`: every member of `piSet A B` is `≈` to such a graph, with children
  chosen canonically (`sUnion` of the `≈`-class of `fapp`-values: no choice).

Theory-agnostic (ADR #8005 §7b).  closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u

namespace PSet

/-- Two indices of `A` are related when their elements are `≈`. -/
def FSetoid (A : PSet.{u}) : Setoid A.Idx where
  r i j := Equiv (A.Func i) (A.Func j)
  iseqv := ⟨fun _ => Equiv.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- The branching type of a function field with domain `A`. -/
def FBr (A : PSet.{u}) : Type u := Quotient (FSetoid A)

/-- The graph of a family of children indexed by the quotient. -/
def graphOf (A : PSet.{u}) (h : FBr A → PSet.{u}) : PSet.{u} :=
  mk A.Idx (fun i => ordPair (A.Func i) (h (Quotient.mk (FSetoid A) i)))

theorem graph_mem_piSet {A : PSet.{u}} {B : PSet.{u} → PSet.{u}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x')) (h : FBr A → PSet.{u})
    (hval : ∀ i : A.Idx, h (Quotient.mk (FSetoid A) i) ∈ B (A.Func i)) : graphOf A h ∈ piSet A B := by
  refine mem_piSet_of_dep hB ⟨fun a ⟨i, hi⟩ => ?_, fun p ⟨i, hi⟩ => ?_, fun a b b' ⟨i, hi⟩ ⟨j, hj⟩ => ?_⟩
  · exact ⟨h (Quotient.mk (FSetoid A) i), mem_congr_right (hB _ _ hi) (hval i),
      ⟨i, ordPair_congr hi Equiv.rfl⟩⟩
  · exact ⟨A.Func i, ⟨i, Equiv.refl _⟩, _, hval i, hi.symm⟩
  · obtain ⟨hai, hbi⟩ := ordPair_equiv hi
    obtain ⟨haj, hbj⟩ := ordPair_equiv hj
    have hq : Quotient.mk (FSetoid A) i = Quotient.mk (FSetoid A) j :=
      Quotient.sound (hai.trans haj.symm)
    have hbb : Equiv (h (Quotient.mk (FSetoid A) i)) (h (Quotient.mk (FSetoid A) j)) := by
      rw [hq]; exact Equiv.refl _
    exact hbi.symm.trans (hbb.trans hbj)

/-- The canonical child of class `q`: the union of the `≈`-class of `fapp`-values. -/
def childOf (A F : PSet.{u}) (q : FBr A) : PSet.{u} :=
  sUnion (mk {i : A.Idx // Quotient.mk (FSetoid A) i = q} (fun i => fapp F (A.Func i.1)))

theorem exists_graph_of_mem_piSet {A F : PSet.{u}} {B : PSet.{u} → PSet.{u}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x')) (hF : F ∈ piSet A B) :
    (∀ i : A.Idx, childOf A F (Quotient.mk (FSetoid A) i) ∈ B (A.Func i)) ∧
      Equiv F (graphOf A (childOf A F)) := by
  have hfun := isFuncOnDep_of_mem_piSet hB hF
  -- the child of the class of `i` is `≈` the application at `A.Func i`
  have hchild : ∀ i : A.Idx, Equiv (childOf A F (Quotient.mk (FSetoid A) i)) (fapp F (A.Func i)) := by
    intro i
    apply ext; intro z
    constructor
    · intro hz
      obtain ⟨t, ⟨⟨j, hj⟩, ht⟩, hzt⟩ := mem_sUnion.mp hz
      have hij : Equiv (A.Func j) (A.Func i) := Quotient.exact hj
      obtain ⟨b, hb, hab⟩ := hfun.1 (A.Func j) ⟨j, Equiv.refl _⟩
      have h1 : Equiv (fapp F (A.Func j)) b := fapp_eq_of_uniq hfun.2.2 hab
      have hab' : ordPair (A.Func i) b ∈ F :=
        mem_congr_left (ordPair_congr hij Equiv.rfl) hab
      have h2 : Equiv (fapp F (A.Func i)) b := fapp_eq_of_uniq hfun.2.2 hab'
      exact mem_congr_right (h1.trans h2.symm) (mem_congr_right ht.symm hzt)
    · intro hz
      exact mem_sUnion.mpr ⟨fapp F (A.Func i), ⟨⟨i, rfl⟩, Equiv.refl _⟩, hz⟩
  refine ⟨fun i => ?_, ?_⟩
  · have hmem := fapp_mem_piSet hB hF (⟨i, Equiv.refl _⟩ : A.Func i ∈ A)
    exact mem_congr_left (hchild i).symm hmem
  · apply ext; intro p
    constructor
    · intro hp
      obtain ⟨a, ⟨i, hi⟩, b, hb, hpe⟩ := hfun.2.1 p hp
      have hab : ordPair (A.Func i) b ∈ F :=
        mem_congr_left (hpe.trans (ordPair_congr hi.symm Equiv.rfl)) hp
      have h1 : Equiv (fapp F (A.Func i)) b := fapp_eq_of_uniq hfun.2.2 hab
      exact ⟨i, ((ordPair_congr Equiv.rfl ((hchild i).trans h1)).trans (ordPair_congr hi Equiv.rfl)).trans hpe.symm⟩
    · intro ⟨i, hi⟩
      obtain ⟨b, hb, hab⟩ := hfun.1 (A.Func i) ⟨i, Equiv.refl _⟩
      have h1 : Equiv (fapp F (A.Func i)) b := fapp_eq_of_uniq hfun.2.2 hab
      exact mem_congr_left ((ordPair_congr Equiv.rfl ((hchild i).trans h1)).symm.trans hi) hab

end PSet

end Rcic.F3
