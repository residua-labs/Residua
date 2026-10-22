import rcic.RcicAnnLR3CandidatePi
import rcic.RcicAnnLR3IndexedFamilyDecoder

/-!
# Application-saturated indexed family data for the recursor lane

All positive native neutrals, including applications to nonempty arguments,
are explicit legal leaves. Reflection retains both the value and its tree;
constructor formation and quotient descent reuse the existing family algebra.
No tree is selected from a membership proposition and no collision-adequate
raw decoder is assumed. The quotient retains its structural PER.

This supplies the saturated family-carrier interface. Source member/code
attachment and the admissible proof-family eliminator are separate obligations;
this module does not supply a generic source iota arm. closure_claim = 0.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.SaturatedFamilyCode

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedInductive NeutralDataFamily

universe u v w

abbrev Leaf (Index : Type u) (_ : Index) := {x : Value // CandidatePi.Neutral x}

def leafValue {Index : Type u} (_i : Index) (a : Leaf Index _i) : Value := a.1

def LeafRel {Index : Type u} (i : Index) (a b : Leaf Index i) : Prop :=
  ValueEq a.1 b.1

theorem leaf_laws {Index : Type u} (i : Index) : RelLaws (LeafRel i) :=
  ⟨ValueEq.symm, ValueEq.trans⟩

abbrev Element {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index) :=
  Paired S (Leaf Index) LeafRel leafValue ctor i

abbrev Relation {Index : Type u} {S : Signature.{u,v,w} Index}
    {ctor : NeutralFamily.ConstructorOp S} {i : Index}
    (x y : Element S ctor i) := PairPER x y

theorem relation_laws {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index) :
    RelLaws (fun x y : Element S ctor i => Relation x y) :=
  pairPER_laws leaf_laws i

def reflect {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (x : Value) (hx : CandidatePi.Neutral x) : Element S ctor i :=
  pair leafValue ctor (legalNeutral S (Leaf Index) LeafRel i ⟨x, hx⟩ (ValueEq.refl x))

theorem reflect_value {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (x : Value) (hx : CandidatePi.Neutral x) :
    (reflect S ctor i x hx).value = x := rfl

theorem reflect_member {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (x : Value) (hx : CandidatePi.Neutral x) :
    Relation (reflect S ctor i x hx) (reflect S ctor i x hx) :=
  (reflect S ctor i x hx).admitted

theorem reflect_related {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    {x y : Value} (hx : CandidatePi.Neutral x) (hy : CandidatePi.Neutral y)
    (hxy : ValueEq x y) :
    Relation (reflect S ctor i x hx) (reflect S ctor i y hy) :=
  Bisim.neutral (S := S) (Leaf := Leaf Index) (RN := LeafRel) i ⟨x, hx⟩ ⟨y, hy⟩ hxy

def reflectApplication {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (f : Value) (hf : CandidatePi.Neutral f)
    (a : Value) (ha : CandidatePi.NonemptyValue a) : Element S ctor i :=
  reflect S ctor i (NeutralPi.applyValue f a) (.app hf a ha)

theorem application_reflection {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (f : Value) (hf : CandidatePi.Neutral f)
    (a : Value) (ha : CandidatePi.NonemptyValue a) :
    Relation (reflectApplication S ctor i f hf a ha)
      (reflectApplication S ctor i f hf a ha) ∧
    (reflectApplication S ctor i f hf a ha).value = NeutralPi.applyValue f a :=
  ⟨(reflectApplication S ctor i f hf a ha).admitted, rfl⟩

def node {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, Element S ctor (S.child i r p)) :
    Element S ctor i :=
  pair leafValue ctor (legalNode S (Leaf Index) LeafRel i r
    (fun p => ⟨(children p).tree, (children p).admitted⟩))

theorem node_member {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, Element S ctor (S.child i r p)) :
    Relation (node S ctor i r children) (node S ctor i r children) :=
  (node S ctor i r children).admitted

theorem node_value {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, Element S ctor (S.child i r p)) :
    (node S ctor i r children).value = ctor i r (fun p => (children p).value) := by
  change ctor i r (fun p => interpret leafValue ctor (children p).tree) = _
  apply congrArg (ctor i r)
  funext p
  exact (children p).value_eq.symm

theorem node_related {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index) (r : S.Rule i)
    (xs ys : ∀ p : S.Premise i r, Element S ctor (S.child i r p))
    (h : ∀ p, Relation (xs p) (ys p)) :
    Relation (node S ctor i r xs) (node S ctor i r ys) :=
  .node i r _ _ h

abbrev QuotientFamily {Index : Type u} (S : Signature.{u,v,w} Index) (i : Index) :=
  DependentFamily.FamilyQuotient (S := S) (Leaf := Leaf Index) leaf_laws i

def decode {Index : Type u} {S : Signature.{u,v,w} Index}
    {ctor : NeutralFamily.ConstructorOp S} {i : Index}
    (p : Element S ctor i) : QuotientFamily S i := pairedClass leaf_laws p

theorem decode_related {Index : Type u} {S : Signature.{u,v,w} Index}
    {ctor : NeutralFamily.ConstructorOp S} {i : Index}
    {p q : Element S ctor i} (h : Relation p q) : decode p = decode q :=
  Quotient.sound h

theorem index_transport {Index : Type u} {S : Signature.{u,v,w} Index}
    {ctor : NeutralFamily.ConstructorOp S} {i j : Index} (h : i = j)
    (p : Element S ctor i) :
    (DependentFamily.transport (Element S ctor) h p).value = p.value := by
  cases h
  rfl

theorem decode_transport {Index : Type u} {S : Signature.{u,v,w} Index}
    {ctor : NeutralFamily.ConstructorOp S} {i j : Index} (h : i = j)
    (p : Element S ctor i) :
    decode (DependentFamily.transport (Element S ctor) h p) =
      DependentFamily.transport (QuotientFamily S) h (decode p) := by
  cases h
  rfl

/-- The retained carrier supplies common application-neutral erasures for
any two indexed family instances, without equating their constructors. -/
theorem shared_neutral_erasure {Index : Type u} (S : Signature.{u,v,w} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i j : Index)
    (x : Value) (hx : CandidatePi.Neutral x) :
    Relation (reflect S ctor i x hx) (reflect S ctor i x hx) ∧
    Relation (reflect S ctor j x hx) (reflect S ctor j x hx) ∧
    (reflect S ctor i x hx).value = (reflect S ctor j x hx).value :=
  ⟨reflect_member S ctor i x hx, reflect_member S ctor j x hx, rfl⟩

end Rcic.Declarative.Ann.LR3.SaturatedFamilyCode
