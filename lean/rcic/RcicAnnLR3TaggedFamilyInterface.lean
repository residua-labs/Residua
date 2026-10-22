import rcic.RcicAnnLR3TaggedSaturatedTower

/-!
# Legal-tree operations exposed on the tagged family carrier

The per-index raw type image is an explicit input of familyCode; this
interface is not a general source-family attachment. All operations
consume actual retained legal trees. Membership, application, constructors,
tree/quotient decoding and fold equations compose the existing family
algebra. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TaggedFamilyInterface
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements TaggedSaturatedTower
universe u v

section Family
variable {Index : Type u}
variable (k : Nat) (S : TypedInductive.Signature.{u,u,u} Index)
variable (ctor : NeutralFamily.ConstructorOp S)
variable (V : Index → Value)
variable (hV : ∀ i, SortMember (some (k+1)) (V i))
variable (hdef : ∀ i, TypeDefined (V i))

abbrev code (i : Index) : Code.{u} (k+1) :=
  familyCode k S ctor i (V i) (hV i) (hdef i)

def familyReflect (i : Index) (x : Value) (hx : CandidatePi.Neutral x) :
    (code k S ctor V hV hdef i).Element :=
  SaturatedFamilyCode.reflect S ctor i x hx

theorem family_cr3 (i : Index) (x : (code k S ctor V hV hdef i).Element) :
    (code k S ctor V hV hdef i).view.relation x x := x.admitted

theorem familyReflect_member (i : Index) (x : Value) (hx : CandidatePi.Neutral x) :
    (code k S ctor V hV hdef i).view.relation
      (familyReflect k S ctor V hV hdef i x hx)
      (familyReflect k S ctor V hV hdef i x hx) :=
  SaturatedFamilyCode.reflect_member S ctor i x hx

theorem familyReflect_value (i : Index) (x : Value) (hx : CandidatePi.Neutral x) :
    (code k S ctor V hV hdef i).erase
      (familyReflect k S ctor V hV hdef i x hx) = x := rfl

theorem familyReflect_related (i : Index) (x y : Value)
    (hx : CandidatePi.Neutral x) (hy : CandidatePi.Neutral y) (hxy : ValueEq x y) :
    (code k S ctor V hV hdef i).view.relation
      (familyReflect k S ctor V hV hdef i x hx)
      (familyReflect k S ctor V hV hdef i y hy) :=
  SaturatedFamilyCode.reflect_related S ctor i hx hy hxy

def familyReflectApplication (i : Index) (f : Value) (hf : CandidatePi.Neutral f)
    (a : Value) (ha : CandidatePi.NonemptyValue a) :
    (code k S ctor V hV hdef i).Element :=
  SaturatedFamilyCode.reflectApplication S ctor i f hf a ha

theorem family_application (i : Index) (f : Value) (hf : CandidatePi.Neutral f)
    (a : Value) (ha : CandidatePi.NonemptyValue a) :
    (code k S ctor V hV hdef i).view.relation
      (familyReflectApplication k S ctor V hV hdef i f hf a ha)
      (familyReflectApplication k S ctor V hV hdef i f hf a ha) ∧
    (code k S ctor V hV hdef i).erase
      (familyReflectApplication k S ctor V hV hdef i f hf a ha) =
      NeutralPi.applyValue f a :=
  SaturatedFamilyCode.application_reflection S ctor i f hf a ha

def familyNode (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r,
      (code k S ctor V hV hdef (S.child i r p)).Element) :
    (code k S ctor V hV hdef i).Element :=
  SaturatedFamilyCode.node S ctor i r children

theorem familyNode_member (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r,
      (code k S ctor V hV hdef (S.child i r p)).Element) :
    (code k S ctor V hV hdef i).view.relation
      (familyNode k S ctor V hV hdef i r children)
      (familyNode k S ctor V hV hdef i r children) :=
  SaturatedFamilyCode.node_member S ctor i r children

theorem familyNode_value (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r,
      (code k S ctor V hV hdef (S.child i r p)).Element) :
    (code k S ctor V hV hdef i).erase (familyNode k S ctor V hV hdef i r children) =
      ctor i r (fun p => (code k S ctor V hV hdef (S.child i r p)).erase (children p)) :=
  SaturatedFamilyCode.node_value S ctor i r children

theorem familyNode_related (i : Index) (r : S.Rule i)
    (children children' : ∀ p : S.Premise i r,
      (code k S ctor V hV hdef (S.child i r p)).Element)
    (hchildren : ∀ p, (code k S ctor V hV hdef (S.child i r p)).view.relation
      (children p) (children' p)) :
    (code k S ctor V hV hdef i).view.relation
      (familyNode k S ctor V hV hdef i r children)
      (familyNode k S ctor V hV hdef i r children') :=
  SaturatedFamilyCode.node_related S ctor i r children children' hchildren

def familyTree (i : Index) (x : (code k S ctor V hV hdef i).Element) :
    NeutralDataFamily.Tree S (SaturatedFamilyCode.Leaf Index) i := x.tree

theorem familyTree_related (i : Index)
    (x y : (code k S ctor V hV hdef i).Element)
    (hxy : (code k S ctor V hV hdef i).view.relation x y) :
    NeutralDataFamily.Bisim S (SaturatedFamilyCode.Leaf Index) SaturatedFamilyCode.LeafRel
      (familyTree k S ctor V hV hdef i x) (familyTree k S ctor V hV hdef i y) := hxy

def familyDecode (i : Index) (x : (code k S ctor V hV hdef i).Element) :
    SaturatedFamilyCode.QuotientFamily S i :=
  SaturatedFamilyCode.decode (S := S) (ctor := ctor) x

theorem familyDecode_related (i : Index)
    (x y : (code k S ctor V hV hdef i).Element)
    (hxy : (code k S ctor V hV hdef i).view.relation x y) :
    familyDecode k S ctor V hV hdef i x = familyDecode k S ctor V hV hdef i y :=
  SaturatedFamilyCode.decode_related hxy

def familyTransport {i j : Index} (h : i = j)
    (x : (code k S ctor V hV hdef i).Element) :
    (code k S ctor V hV hdef j).Element := h ▸ x

theorem familyTransport_value {i j : Index} (h : i = j)
    (x : (code k S ctor V hV hdef i).Element) :
    (code k S ctor V hV hdef j).erase (familyTransport k S ctor V hV hdef h x) =
      (code k S ctor V hV hdef i).erase x := by cases h; rfl

theorem familyTransport_related {i j : Index} (h : i = j)
    (x y : (code k S ctor V hV hdef i).Element)
    (hxy : (code k S ctor V hV hdef i).view.relation x y) :
    (code k S ctor V hV hdef j).view.relation
      (familyTransport k S ctor V hV hdef h x) (familyTransport k S ctor V hV hdef h y) := by
  cases h
  exact hxy

theorem familyDecode_transport {i j : Index} (h : i = j)
    (x : (code k S ctor V hV hdef i).Element) :
    familyDecode k S ctor V hV hdef j (familyTransport k S ctor V hV hdef h x) =
      (h ▸ familyDecode k S ctor V hV hdef i x) := by cases h; rfl

variable {Result : Index → Type v}
variable (neutral : ∀ i, SaturatedFamilyCode.Leaf Index i → Result i)
variable (algebra : ∀ i (r : S.Rule i),
  (∀ p : S.Premise i r, Result (S.child i r p)) → Result i)

/-- Reuses the existing constructive nested tree recursor. -/
noncomputable def familyFold {i : Index}
    (x : (code k S ctor V hV hdef i).Element) : Result i :=
  NeutralDataFamily.fold neutral algebra x.tree

theorem familyFold_reflect (i : Index) (x : Value) (hx : CandidatePi.Neutral x) :
    familyFold k S ctor V hV hdef neutral algebra
      (familyReflect k S ctor V hV hdef i x hx) = neutral i ⟨x, hx⟩ := rfl

theorem familyFold_node (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r,
      (code k S ctor V hV hdef (S.child i r p)).Element) :
    familyFold k S ctor V hV hdef neutral algebra
      (familyNode k S ctor V hV hdef i r children) =
      algebra i r (fun p => familyFold k S ctor V hV hdef neutral algebra (children p)) := rfl

theorem familyFold_related
    (hn : ∀ i (a b : SaturatedFamilyCode.Leaf Index i),
      ValueEq a.val b.val → neutral i a = neutral i b)
    (i : Index) (x y : (code k S ctor V hV hdef i).Element)
    (hxy : (code k S ctor V hV hdef i).view.relation x y) :
    familyFold k S ctor V hV hdef neutral algebra x =
      familyFold k S ctor V hV hdef neutral algebra y :=
  NeutralDataFamily.fold_respects_eq neutral algebra hn hxy

end Family
end Rcic.Declarative.Ann.LR3.TaggedFamilyInterface
