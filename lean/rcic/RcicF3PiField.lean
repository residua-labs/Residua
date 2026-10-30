import rcic.RcicF3PiTel
import rcic.RcicF3KTWSpecPhi

/-!
# Dependent recursive fields: set interpretation and logical relation

A `RecTel I m` has `m` dependent Pi binders and a recursive result index
in `I`. Domains are arbitrary small sets; quotient branch addresses make
all graph encodings functional without selecting representatives.

This module interprets semantic telescopes. It does not extract a
`RecTel` from raw syntax or identify the result with `famLim`.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet

universe u

/-- Extend a quotient-indexed family to all set arguments, with empty
fibre outside the domain. No representative is selected. -/
def classFiber (A : PSet.{u}) (B : FBr A → PSet.{u}) (a : PSet.{u}) : PSet.{u} :=
  sUnion (mk {i : A.Idx // Equiv (A.Func i) a}
    (fun i => B (Quotient.mk (FSetoid A) i.1)))

/-- On a domain representative, the extension is exactly its class fibre. -/
theorem classFiber_at (A : PSet.{u}) (B : FBr A → PSet.{u}) (i : A.Idx) :
    Equiv (classFiber A B (A.Func i)) (B (Quotient.mk (FSetoid A) i)) := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨b, ⟨⟨j, hji⟩, hjb⟩, hzb⟩ := mem_sUnion.mp hz
    have hq : Quotient.mk (FSetoid A) j = Quotient.mk (FSetoid A) i :=
      Quotient.sound hji
    have hz' := mem_congr_right hjb.symm hzb
    change z ∈ B (Quotient.mk (FSetoid A) j) at hz'
    rw [hq] at hz'
    exact hz'
  · intro hz
    exact mem_sUnion.mpr ⟨_, ⟨⟨i, Equiv.refl _⟩, Equiv.refl _⟩, hz⟩

/-- The extension respects equivalent set arguments. -/
theorem classFiber_congr (A : PSet.{u}) (B : FBr A → PSet.{u})
    {a a' : PSet.{u}} (h : Equiv a a') :
    Equiv (classFiber A B a) (classFiber A B a') := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨b, ⟨⟨i, hi⟩, hib⟩, hzb⟩ := mem_sUnion.mp hz
    exact mem_sUnion.mpr ⟨b, ⟨⟨i, hi.trans h⟩, hib⟩, hzb⟩
  · intro hz
    obtain ⟨b, ⟨⟨i, hi⟩, hib⟩, hzb⟩ := mem_sUnion.mp hz
    exact mem_sUnion.mpr ⟨b, ⟨⟨i, hi.trans h.symm⟩, hib⟩, hzb⟩

/-- Pointwise containment is retained by the extension. -/
theorem classFiber_mono (A : PSet.{u}) {B C : FBr A → PSet.{u}}
    (h : ∀ q, Sub (B q) (C q)) (a : PSet.{u}) :
    Sub (classFiber A B a) (classFiber A C a) := by
  intro z hz
  obtain ⟨b, ⟨⟨i, hi⟩, hib⟩, hzb⟩ := mem_sUnion.mp hz
  exact mem_sUnion.mpr ⟨_, ⟨⟨i, hi⟩, Equiv.refl _⟩,
    h _ _ (mem_congr_right hib.symm hzb)⟩

/-- An arbitrary finite dependent telescope ending at a recursive index. -/
inductive RecTel (I : Type u) : Nat → Type (u + 1) where
  | ret (i : I) : RecTel I 0
  | pi {m : Nat} (A : PSet.{u}) (B : FBr A → RecTel I m) : RecTel I (m + 1)

/-- The underlying dependent branch telescope. -/
def RecTel.tel {I : Type u} : {m : Nat} → RecTel I m → PiTel.{u} m
  | _, .ret _ => .nil
  | _, .pi A B => .cons (FBr A) (fun q => (B q).tel)

/-- Interpret every binder as a dependent product and each result as the
specified fibre of `X`. Later domains may depend on previous arguments. -/
def RecTel.denote {I : Type u} : {m : Nat} → RecTel I m →
    (I → PSet.{u}) → PSet.{u}
  | _, .ret i, X => X i
  | _, .pi A B, X => piSet A (classFiber A (fun q => (B q).denote X))

/-- Result index at a complete dependent path. -/
def RecTel.result {I : Type u} : {m : Nat} → (t : RecTel I m) → t.tel.Path → I
  | _, .ret i, _ => i
  | _, .pi _ B, p => (B p.1).result p.2

/-- Encode a nested assignment by nested extensional graphs. -/
def RecTel.encode {I : Type u} : {m : Nat} → (t : RecTel I m) →
    PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u}) → PSet.{u}
  | _, .ret _, f => f
  | _, .pi A B, f => graphOf A (fun q => (B q).encode (f q))

/-- Canonical readback of all child values, without a choice function. -/
def RecTel.read {I : Type u} : {m : Nat} → (t : RecTel I m) → PSet.{u} →
    PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u})
  | _, .ret _, f => f
  | _, .pi A B, f => fun q => (B q).read (childOf A f q)

/-- Logical relation between a nested field and its recursive-result fibres. -/
def RecTel.Rel {I : Type u} {m : Nat} (t : RecTel I m) (X : I → PSet.{u})
    (f : PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u})) : Prop :=
  PiTel.All.{u, u + 1} t.tel (fun p z => z ∈ X (t.result p)) f

/-- A related nested assignment encodes a member of its dependent product. -/
theorem RecTel.encode_mem {I : Type u} {m : Nat} (t : RecTel I m)
    (X : I → PSet.{u}) (f : PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u}))
    (hf : t.Rel X f) : t.encode f ∈ t.denote X := by
  induction t with
  | ret i => exact hf
  | pi A B ih =>
    apply graph_mem_piSet (fun _ _ h => classFiber_congr A _ h)
    intro i
    exact mem_congr_right (classFiber_at A _ i).symm
      (ih _ (f (Quotient.mk (FSetoid A) i)) (hf _))

/-- Membership supplies the canonical child relation AND graph readback.
The graph conjunct rules out junk fields, including on empty domains. -/
theorem RecTel.read_spec {I : Type u} {m : Nat} (t : RecTel I m)
    (X : I → PSet.{u}) {f : PSet.{u}} (hf : f ∈ t.denote X) :
    t.Rel X (t.read f) ∧ Equiv f (t.encode (t.read f)) := by
  induction t generalizing f with
  | ret i => exact ⟨hf, Equiv.refl _⟩
  | pi A B ih =>
    have hc := exists_graph_of_mem_piSet
      (fun _ _ h => classFiber_congr A (fun q => (B q).denote X) h) hf
    have hv : ∀ q, childOf A f q ∈ (B q).denote X := by
      intro q
      refine Quotient.inductionOn q ?_
      intro i
      exact mem_congr_right (classFiber_at A _ i) (hc.1 i)
    have hr := fun q => ih q (hv q)
    exact ⟨fun q => (hr q).1, hc.2.trans (graphOf_congr (fun q => (hr q).2))⟩

/-- Exact membership criterion. Testing only children is insufficient:
the field must also be its total functional graph. -/
theorem RecTel.mem_iff {I : Type u} {m : Nat} (t : RecTel I m)
    (X : I → PSet.{u}) (f : PSet.{u}) :
    f ∈ t.denote X ↔ t.Rel X (t.read f) ∧ Equiv f (t.encode (t.read f)) :=
  ⟨t.read_spec X, fun h => mem_congr_left h.2.symm (t.encode_mem X _ h.1)⟩

/-- Inhabitation of the product is exactly inhabitation of the nested
logical relation; canonical readback proves the forward direction. -/
theorem RecTel.inhabited_iff {I : Type u} {m : Nat} (t : RecTel I m)
    (X : I → PSet.{u}) :
    (∃ f, f ∈ t.denote X) ↔ ∃ g, t.Rel X g := by
  constructor
  · intro ⟨f, hf⟩; exact ⟨t.read f, (t.read_spec X hf).1⟩
  · intro ⟨g, hg⟩; exact ⟨t.encode g, t.encode_mem X g hg⟩

/-- Equivalent leaves encode equivalent fields at arbitrary depth. -/
theorem RecTel.encode_congr {I : Type u} {m : Nat} (t : RecTel I m)
    (f g : PiTel.Value.{u, u + 1} t.tel (fun _ => PSet.{u}))
    (h : ∀ p, Equiv (t.tel.flatten f p) (t.tel.flatten g p)) :
    Equiv (t.encode f) (t.encode g) := by
  induction t with
  | ret i => exact h .unit
  | pi A B ih => exact graphOf_congr (fun q => ih q (f q) (g q) (fun p => h ⟨q, p⟩))

/-- Product interpretation is monotone in every recursive result fibre. -/
theorem RecTel.denote_mono {I : Type u} {m : Nat} (t : RecTel I m)
    (X Y : I → PSet.{u}) (h : ∀ i, Sub (X i) (Y i)) :
    Sub (t.denote X) (t.denote Y) := by
  induction t with
  | ret i => exact h i
  | pi A B ih =>
    exact piSet_sub (fun _ _ e => classFiber_congr A _ e)
      (fun _ _ e => classFiber_congr A _ e)
      (fun a => classFiber_mono A ih a)

end Rcic.F3.PSet
