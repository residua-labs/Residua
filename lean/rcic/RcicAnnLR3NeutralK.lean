import rcic.RcicAnnLR3TypedPER

/-!
# Constructive neutral K saturation and an inhabited exact-iff obstruction

The K computation rule below is a guarded generating edge. Its guard is a
proposition; constructing the relation never decides that proposition or
selects a semantic representative. Nonempty finite paths supply symmetry
and transitivity without giving unrelated raw values reflexivity.

The guard characterizes the distinguished K edge, not every equality in
the completed target PER. The constant-proposition witness at the end has
two inhabited unrelated source endpoints, an admitted neutral equality
proof, and an inhabited target containing the minor, stuck J and another
neutral proof. Proof irrelevance gives a same-target transitivity chain
from J to the minor even though the endpoint guard is false.

These are local relational constructions and an obstruction to the literal
global iff. They do not assert a Code/El construction, source fundamental
theorem, all-context realisation, or a normalization theorem. Typed motive
transport, neutral congruence and compatibility with the remaining type
constructors are separate obligations. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.NeutralK

universe u

abbrev Rel (A : Type u) := A → A → Prop

structure PERLaws {A : Type u} (R : Rel A) : Prop where
  symm : ∀ {x y : A}, R x y → R y x
  trans : ∀ {x y z : A}, R x y → R y z → R x z

def Member {A : Type u} (R : Rel A) (x : A) : Prop := R x x

def Same {A : Type u} (R S : Rel A) : Prop :=
  ∀ x y, R x y ↔ S x y

/-- Finite nonempty paths in an undirected generating graph. There is no
unconditional reflexivity constructor: this is a PER completion. -/
inductive Path {A : Type u} (E : Rel A) : A → A → Prop
  | forward {x y : A} : E x y → Path E x y
  | backward {x y : A} : E y x → Path E x y
  | append {x y z : A} : Path E x y → Path E y z → Path E x z

theorem path_symm {A : Type u} {E : Rel A} {x y : A}
    (h : Path E x y) : Path E y x := by
  induction h with
  | forward h => exact .backward h
  | backward h => exact .forward h
  | append _ _ ih ig => exact .append ig ih

theorem path_trans {A : Type u} {E : Rel A} {x y z : A}
    (h : Path E x y) (g : Path E y z) : Path E x z :=
  .append h g

theorem path_laws {A : Type u} (E : Rel A) : PERLaws (Path E) where
  symm := path_symm
  trans := path_trans

/-- The completion is the least PER containing the generating relation. -/
theorem path_least {A : Type u} {E R : Rel A} (hR : PERLaws R)
    (hinclude : ∀ {x y : A}, E x y → R x y) {x y : A}
    (h : Path E x y) : R x y := by
  induction h with
  | forward h => exact hinclude h
  | backward h => exact hR.symm (hinclude h)
  | append _ _ ih ig => exact hR.trans ih ig

theorem path_mono {A : Type u} {E F : Rel A}
    (hinclude : ∀ {x y : A}, E x y → F x y) {x y : A}
    (h : Path E x y) : Path F x y :=
  path_least (path_laws F) (fun he => Path.forward (hinclude he)) h

/-- Extensional equality of the entire typed generating graph transports
the completion. Supplying that equality for actual type conversion is a
separate semantic obligation. -/
theorem path_same {A : Type u} {E F : Rel A} (h : Same E F) :
    Same (Path E) (Path F) := by
  intro x y
  exact ⟨path_mono (fun he => (h _ _).mp he),
    path_mono (fun hf => (h _ _).mpr hf)⟩

/-- Direct adapter to the existing Value-carrier PER algebra. -/
theorem path_typed_laws (E : TypedPER.Relation) :
    TypedPER.Laws (Path E) where
  symm := path_symm
  trans := path_trans

/-- A call is represented as a neutral value, not chosen or evaluated by
testing its endpoint relation. The surrounding typed judgement supplies
the fixed target C b p at which this frame is admitted. -/
structure Frame (A : Type u) where
  source : Rel A
  left : A
  right : A
  major : A
  minor : A
  call : A

def Guard {A : Type u} (f : Frame A) : Prop :=
  f.source f.left f.right

/-- Only this distinguished generating edge has the exact guard iff. -/
def KEdge {A : Type u} (f : Frame A) (x y : A) : Prop :=
  x = f.call ∧ y = f.minor ∧ Guard f

theorem kEdge_iff {A : Type u} (f : Frame A) :
    KEdge f f.call f.minor ↔ Guard f :=
  ⟨fun h => h.2.2, fun h => ⟨rfl, rfl, h⟩⟩

/-- `AtTarget` is an explicit parameter for typed frames at one fixed
target. `core` includes the target's independent equality rules, including
proof irrelevance when this target is a proposition. -/
inductive Seed {A : Type u} (core : Rel A) (neutral : A → Prop)
    (AtTarget : Frame A → Prop) : A → A → Prop
  | core {x y : A} : core x y → Seed core neutral AtTarget x y
  | neutral {x : A} : neutral x → Seed core neutral AtTarget x x
  | k {f : Frame A} : AtTarget f → Guard f →
      Seed core neutral AtTarget f.call f.minor

def Saturated {A : Type u} (core : Rel A) (neutral : A → Prop)
    (AtTarget : Frame A → Prop) : Rel A :=
  Path (Seed core neutral AtTarget)

theorem saturated_laws {A : Type u} (core : Rel A) (neutral : A → Prop)
    (AtTarget : Frame A → Prop) : PERLaws (Saturated core neutral AtTarget) :=
  path_laws _

theorem saturated_typed_laws (core : TypedPER.Relation)
    (neutral : UnitModel.Value → Prop)
    (AtTarget : Frame UnitModel.Value → Prop) :
    TypedPER.Laws (Saturated core neutral AtTarget) :=
  path_typed_laws _

theorem saturated_core {A : Type u} {core : Rel A} {neutral : A → Prop}
    {AtTarget : Frame A → Prop} {x y : A} (h : core x y) :
    Saturated core neutral AtTarget x y :=
  .forward (.core h)

theorem saturated_neutral {A : Type u} {core : Rel A} {neutral : A → Prop}
    {AtTarget : Frame A → Prop} {x : A} (h : neutral x) :
    Member (Saturated core neutral AtTarget) x :=
  .forward (.neutral h)

theorem saturated_k {A : Type u} {core : Rel A} {neutral : A → Prop}
    {AtTarget : Frame A → Prop} {f : Frame A} (hf : AtTarget f) (h : Guard f) :
    Saturated core neutral AtTarget f.call f.minor :=
  .forward (.k hf h)

/-- Related endpoints preserve the guard under ordinary source PER
congruence. No decidability or equality reflection from a proof is used. -/
theorem guard_congr {A : Type u} {R : Rel A} (hR : PERLaws R)
    {a a' b b' : A} (ha : R a a') (hb : R b b') :
    R a b ↔ R a' b' :=
  ⟨fun h => hR.trans (hR.trans (hR.symm ha) h) hb,
   fun h => hR.trans (hR.trans ha h) (hR.symm hb)⟩

/-- The fibre transport needed before using a guarded K edge is named,
not inferred from the mere existence of an admitted equality proof. -/
theorem guarded_minor_member {A : Type u} {D B T : Rel A} {a b c : A}
    (hc : Member B c) (transport : D a b → Same B T) (hab : D a b) :
    Member T c :=
  (transport hab c c).mp hc

def ExactK {A : Type u} (R : Rel A) (f : Frame A) : Prop :=
  R f.call f.minor ↔ Guard f

/-- A sufficient, explicit separation invariant for the converse to
survive completion. A completed path cannot escape a containing PER.
Constructing this invariant for a proposed full typed model is additional
work; proof-irrelevant targets in the witness below do not admit it. -/
theorem saturated_exact_of_separator {A : Type u} {core R : Rel A}
    {neutral : A → Prop} {AtTarget : Frame A → Prop} {f : Frame A}
    (hR : PERLaws R)
    (hseed : ∀ {x y : A}, Seed core neutral AtTarget x y → R x y)
    (separate : R f.call f.minor → Guard f) (hf : AtTarget f) :
    ExactK (Saturated core neutral AtTarget) f :=
  ⟨fun h => separate (path_least hR hseed h), saturated_k hf⟩

/-- Any independently forced same-target chain defeats the reverse
implication when the source endpoints are unrelated. -/
theorem no_exactK_of_chain {A : Type u} {R : Rel A} (hR : PERLaws R)
    {f : Frame A} {q : A} (hjq : R f.call q) (hqc : R q f.minor)
    (apart : ¬ Guard f) : ¬ ExactK R f :=
  fun h => apart (h.mp (hR.trans hjq hqc))

/-- Proof irrelevance on an explicitly admitted proof domain. -/
def ProofPER {A : Type u} (proof : A → Prop) : Rel A :=
  fun x y => proof x ∧ proof y

theorem proofPER_laws {A : Type u} (proof : A → Prop) :
    PERLaws (ProofPER proof) where
  symm := fun h => ⟨h.2, h.1⟩
  trans := fun h g => ⟨h.1, g.2⟩

theorem proofPER_irrelevant {A : Type u} {proof : A → Prop} {x y : A}
    (hx : Member (ProofPER proof) x) (hy : Member (ProofPER proof) y) :
    ProofPER proof x y :=
  ⟨hx.1, hy.1⟩

namespace InhabitedObstruction

inductive Atom
  | left | right | minor | major | stuck | bridge

inductive Neutral : Atom → Prop
  | major : Neutral .major
  | stuck : Neutral .stuck
  | bridge : Neutral .bridge

/-- Every atom, including every neutral, is admitted at the source. The
two designated endpoints remain distinct equivalence classes. -/
def source : Rel Atom := Eq

theorem source_laws : PERLaws source where
  symm := Eq.symm
  trans := Eq.trans

theorem source_left_member : Member source .left := rfl
theorem source_right_member : Member source .right := rfl
theorem source_apart : ¬ source .left .right := by
  intro h
  cases h

theorem neutral_source_member {x : Atom} (_h : Neutral x) : Member source x := rfl

/-- The equality proof domain admits every neutral even at unrelated
endpoints. A canonical proof is additionally admitted when related. All
members of this domain, including the neutrals, are proof irrelevant. -/
def equalityProof (a b : Atom) : Rel Atom :=
  ProofPER (fun x => Neutral x ∨ (source a b ∧ x = .minor))

theorem equalityProof_laws (a b : Atom) : PERLaws (equalityProof a b) :=
  proofPER_laws _

theorem neutral_equality_member (a b : Atom) {x : Atom} (h : Neutral x) :
    Member (equalityProof a b) x :=
  ⟨.inl h, .inl h⟩

theorem major_member : Member (equalityProof .left .right) .major :=
  neutral_equality_member _ _ .major

theorem refl_member : Member (equalityProof .left .left) .minor :=
  ⟨.inr ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩⟩

/-- This is one inhabited proposition P. The motive below is literally
constant at P, so no conversion of unrelated endpoint fibres is assumed. -/
def target : Rel Atom := ProofPER (fun x => x = .minor ∨ Neutral x)

def motive (_b _p : Atom) : Rel Atom := target

theorem target_laws : PERLaws target := proofPER_laws _

theorem minor_member : Member target .minor :=
  ⟨.inl rfl, .inl rfl⟩

theorem neutral_target_member {x : Atom} (h : Neutral x) : Member target x :=
  ⟨.inr h, .inr h⟩

theorem call_member : Member (motive .right .major) .stuck :=
  neutral_target_member .stuck

def frame : Frame Atom where
  source := source
  left := .left
  right := .right
  major := .major
  minor := .minor
  call := .stuck

theorem guard_false : ¬ Guard frame := source_apart

theorem k_generator_absent : ¬ KEdge frame frame.call frame.minor :=
  fun h => guard_false ((kEdge_iff frame).mp h)

/-- Both premises inhabit exactly the same target proposition. -/
theorem call_bridge : target .stuck .bridge :=
  ⟨.inr .stuck, .inr .bridge⟩

theorem bridge_minor : target .bridge .minor :=
  ⟨.inr .bridge, .inl rfl⟩

theorem target_no_exactK : ¬ ExactK target frame :=
  no_exactK_of_chain target_laws call_bridge bridge_minor guard_false

def completed : Rel Atom :=
  Saturated target Neutral (fun f => f = frame)

theorem completed_laws : PERLaws completed := saturated_laws _ _ _

theorem completed_call_minor : completed .stuck .minor :=
  path_trans (saturated_core call_bridge) (saturated_core bridge_minor)

theorem completed_no_exactK : ¬ ExactK completed frame :=
  no_exactK_of_chain completed_laws (saturated_core call_bridge)
    (saturated_core bridge_minor) guard_false

/-- Every required source, proof and target carrier is inhabited. The
failure is the global reverse implication, not an empty-carrier artifact
and not a failure of the constructive PER completion. -/
theorem inhabited_exact_iff_obstruction :
    PERLaws source ∧
    Member source .left ∧ Member source .right ∧ ¬ source .left .right ∧
    PERLaws (equalityProof .left .right) ∧
    Member (equalityProof .left .right) .major ∧
    Member (equalityProof .left .left) .minor ∧
    PERLaws target ∧
    Member (motive .left .minor) .minor ∧
    Member (motive .right .major) .stuck ∧
    Member target .bridge ∧
    target .stuck .bridge ∧ target .bridge .minor ∧
    ¬ KEdge frame frame.call frame.minor ∧
    PERLaws completed ∧ completed .stuck .minor ∧
    ¬ ExactK completed frame :=
  ⟨source_laws, source_left_member, source_right_member, source_apart,
    equalityProof_laws _ _, major_member, refl_member, target_laws,
    minor_member, call_member, neutral_target_member .bridge,
    call_bridge, bridge_minor, k_generator_absent, completed_laws,
    completed_call_minor, completed_no_exactK⟩

end InhabitedObstruction

#print axioms path_laws
#print axioms path_least
#print axioms saturated_typed_laws
#print axioms guard_congr
#print axioms InhabitedObstruction.inhabited_exact_iff_obstruction

end Rcic.Declarative.Ann.LR3.NeutralK
