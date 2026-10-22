import rcic.RcicAnnLR3TaggedCodeKernel

/-!
# Constructor-certified carriers and per-constructor reflection

A tag alone cannot manufacture a code: Witness indexes each code by its
actual kernel producer. Pi elements retain run, erased application and
respect; data elements retain legal trees. Neutral elements are indexed by
their interpreted type and carry a semantic neutral derivation. The
universe constructor retains a typed-kernel decoder and requires relational
coherence and the actual native image of each reflection. No common element or raw erasure is required across tags.

The Pi producer composes the existing supplied positivePi. Its old
restricted domain is retained explicitly; a general heterogeneous Pi
constructor over all the new codes is a separate obligation.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TaggedSaturatedTower
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily StratifiedCandidates
open CandidateActionProducts

universe u

inductive ConstructorTag where
  | proposition | univ | pi | family | neutral
  deriving DecidableEq

/-- The type annotation is retained in the carrier index. Neutrality is
a derivation closed under actual application, not a raw-value classifier. -/
structure TypedNeutral (_type : Value) where
  value : Value
  neutral : CandidatePi.Neutral value

def neutralRelation (k : Nat) {A : Value} (x y : TypedNeutral A) : Prop :=
  k = 0 ∨ ValueEq x.value y.value

theorem neutralRelation_laws (k : Nat) (A : Value) :
    RelLaws (neutralRelation k (A := A)) := by
  constructor
  · intro x y h
    exact h.elim Or.inl (fun h => Or.inr h.symm)
  · intro x y z h g
    rcases h with h | h
    · exact Or.inl h
    · rcases g with g | g
      · exact Or.inl g
      · exact Or.inr (h.trans g)

def neutralKernel (k name : Nat) : Kernel.{u} k where
  Element := ULift.{u} (TypedNeutral (NativeMemberValues.value (some k) name))
  erase := fun x => x.down.value
  per := {
    value := NativeMemberValues.value (some k) name
    level := NativeMemberValues.value_level _ _
    defined := NativeMemberValues.value_defined _ _
    relation := fun x y => neutralRelation k x.down y.down
    lawful := ⟨fun h => (neutralRelation_laws k _).symm h,
      fun h g => (neutralRelation_laws k _).trans h g⟩
    point := fun j => ⟨⟨NeutralPER.neutralAtom j, .atom j⟩⟩
    point_member := fun _ => Or.inr (ValueEq.refl _)
    irrelevant := fun h _ _ _ _ => Or.inl h }

def propositionKernel (C : CandidatePi.Element) : Kernel.{u} 0 where
  Element := ULift.{u} Value
  erase := ULift.down
  per := {
    value := C.value
    level := C.level
    defined := C.defined
    relation := fun x y => CandidatePi.decode C x.down y.down
    lawful := ⟨fun h => (candidateView C).lawful.symm h,
      fun h g => (candidateView C).lawful.trans h g⟩
    point := fun name => ⟨NeutralPER.neutralAtom name⟩
    point_member := fun name => CandidatePi.decode_reflection C (.atom name)
    irrelevant := fun h x y hx hy => (candidateView C).irrelevant h x.down y.down hx hy }

def piKernel
    {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k n : Nat}
    (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
    (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
    (A : ExprA) (lA lB : Level)
    (hbody : eval ν lB = some (k + 1))
    (hlevel : eval ν (.imax lA lB) = some (n + 1)) : Kernel.{u} (n + 1) where
  Element := SaturatedPiElements.SourceElementAction b
  erase := fun f => f.value
  per := SaturatedPiElements.positivePi b hD hsat A lA lB hbody hlevel

def familyKernel {Index : Type u} (k : Nat)
    (S : TypedInductive.Signature.{u,u,u} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (V : Value) (hV : SortMember (some (k + 1)) V) (hdef : TypeDefined V) :
    Kernel.{u} (k + 1) where
  Element := SaturatedFamilyCode.Element S ctor i
  erase := fun x => x.value
  per := {
    value := V
    level := hV
    defined := hdef
    relation := SaturatedFamilyCode.Relation
    lawful := SaturatedFamilyCode.relation_laws S ctor i
    point := fun name => SaturatedFamilyCode.reflect S ctor i
      (NeutralPER.neutralAtom name) (.atom name)
    point_member := fun name => SaturatedFamilyCode.reflect_member S ctor i
      (NeutralPER.neutralAtom name) (.atom name)
    irrelevant := fun h => False.elim (Nat.noConfusion h) }

def universeKernel (k : Nat) (κ : Type u) (decode : κ → Kernel.{u} k)
    (R : κ → κ → Prop) (laws : RelLaws R) (q : Nat → κ)
    (all_members : ∀ x, R x x) : Kernel.{u} (k + 1) where
  Element := κ
  erase := fun c => (decode c).per.value
  per := {
    value := universeValue (some k)
    level := sort_member _ _
    defined := sort_defined _ _
    relation := R
    lawful := laws
    point := q
    point_member := fun name => all_members (q name)
    irrelevant := fun h => False.elim (Nat.noConfusion h) }

/-- No arbitrary-kernel constructor is available. Every public tag
certifies the complete interpreted carrier and PER definition. -/
inductive Witness : ConstructorTag → {k : Nat} → Kernel.{u} k → Type (u + 1) where
  | neutral (k name : Nat) : Witness .neutral (neutralKernel k name)
  | proposition (C : CandidatePi.Element) : Witness .proposition (propositionKernel C)
  | pi
      {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
      {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
      {ρ : EnvI} {B : ExprA} {k n : Nat}
      (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
      (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
      (A : ExprA) (lA lB : Level)
      (hbody : eval ν lB = some (k + 1))
      (hlevel : eval ν (.imax lA lB) = some (n + 1)) :
      Witness .pi (piKernel b hD hsat A lA lB hbody hlevel)
  /-- Certifies the semantic legal-tree carrier; the raw image remains an
  explicit input, not a general source-family provenance theorem. -/
  | family {Index : Type u} (k : Nat)
      (S : TypedInductive.Signature.{u,u,u} Index)
      (ctor : NeutralFamily.ConstructorOp S) (i : Index)
      (V : Value) (hV : SortMember (some (k + 1)) V) (hdef : TypeDefined V) :
      Witness .family (familyKernel k S ctor i V hV hdef)
  | univ (k : Nat) (κ : Type u) (decode : κ → Kernel.{u} k)
      (R : κ → κ → Prop) (laws : RelLaws R) (q : Nat → κ)
      (all_members : ∀ x, R x x)
      (coherent : ∀ x y, R x y → KernelRelated (decode x) (decode y))
      (reflection_image : ∀ name, ValueEq ((decode (q name)).per.value)
        (NativeMemberValues.value (some k) name)) :
      Witness .univ (universeKernel k κ decode R laws q all_members)

structure Code (k : Nat) where
  kernel : Kernel.{u} k
  tag : ConstructorTag
  witness : Witness tag kernel

abbrev Code.Element {k : Nat} (C : Code.{u} k) := C.kernel.Element
abbrev Code.erase {k : Nat} (C : Code.{u} k) := C.kernel.erase
abbrev Code.view {k : Nat} (C : Code.{u} k) := C.kernel.per

def Code.neutral (k name : Nat) : Code.{u} k :=
  ⟨neutralKernel k name, .neutral, .neutral k name⟩

def Code.proposition (C : CandidatePi.Element) : Code.{u} 0 :=
  ⟨propositionKernel C, .proposition, .proposition C⟩

def piCode
    {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k n : Nat}
    (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
    (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
    (A : ExprA) (lA lB : Level)
    (hbody : eval ν lB = some (k + 1))
    (hlevel : eval ν (.imax lA lB) = some (n + 1)) : Code.{u} (n + 1) :=
  ⟨piKernel b hD hsat A lA lB hbody hlevel, .pi,
    .pi b hD hsat A lA lB hbody hlevel⟩

def familyCode {Index : Type u} (k : Nat)
    (S : TypedInductive.Signature.{u,u,u} Index)
    (ctor : NeutralFamily.ConstructorOp S) (i : Index)
    (V : Value) (hV : SortMember (some (k + 1)) V) (hdef : TypeDefined V) :
    Code.{u} (k + 1) :=
  ⟨familyKernel k S ctor i V hV hdef, .family, .family k S ctor i V hV hdef⟩

/-- The neutral tag reflects every derivation of semantic neutrality. -/
def neutralReflect (k name : Nat) (x : Value) (hx : CandidatePi.Neutral x) :
    (Code.neutral.{u} k name).Element := ⟨⟨x, hx⟩⟩

theorem neutral_cr3 (k name : Nat) (x : Value) (hx : CandidatePi.Neutral x) :
    (Code.neutral.{u} k name).view.relation
      (neutralReflect k name x hx) (neutralReflect k name x hx) :=
  Or.inr (ValueEq.refl x)

theorem neutral_reflection_erasure (k name : Nat) (x : Value)
    (hx : CandidatePi.Neutral x) :
    (Code.neutral.{u} k name).erase (neutralReflect k name x hx) = x := rfl

def neutralApplication (k name : Nat) (f : Value) (hf : CandidatePi.Neutral f)
    (a : Value) (ha : CandidatePi.NonemptyValue a) : (Code.neutral.{u} k name).Element :=
  neutralReflect k name (NeutralPi.applyValue f a) (.app hf a ha)

theorem neutral_application_member (k name : Nat) (f : Value) (hf : CandidatePi.Neutral f)
    (a : Value) (ha : CandidatePi.NonemptyValue a) :
    (Code.neutral.{u} k name).view.relation
      (neutralApplication k name f hf a ha) (neutralApplication k name f hf a ha) :=
  neutral_cr3 k name _ _

theorem proposition_cr3 (C : CandidatePi.Element) (x : Value)
    (hx : CandidatePi.Neutral x) :
    (Code.proposition.{u} C).view.relation ⟨x⟩ ⟨x⟩ :=
  CandidatePi.decode_reflection C hx

/-- Function reflection is on the actual action carrier. Each action
already supplies a real application equation and cross-argument respect. -/
theorem pi_cr3
    {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k n : Nat}
    (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
    (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
    (A : ExprA) (lA lB : Level)
    (hbody : eval ν lB = some (k + 1))
    (hlevel : eval ν (.imax lA lB) = some (n + 1))
    (f : (piCode b hD hsat A lA lB hbody hlevel).Element) :
    (piCode b hD hsat A lA lB hbody hlevel).view.relation f f :=
  SaturatedPiElements.elementRel_refl f

end Rcic.Declarative.Ann.LR3.TaggedSaturatedTower
