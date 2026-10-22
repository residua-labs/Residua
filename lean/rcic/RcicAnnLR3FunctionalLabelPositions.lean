import rcic.RcicAnnLR3FiniteFamilyLabelAdapters

/-!
# Functional recursive positions over a finite label quotient

The next-field PER has already descended to the prefix quotient. Its legal
members therefore give a position type directly over each label class.
The position PER is lawful, and transport preserves the raw value. This
constructs an unindexed functional-recursive signature without selecting a
label representative, an element from a proposition, or a major tree.

Constructor congruence compares the actual child trees at the transported
positions. The admitted W-shaped fixture supplies its actual functional
domain shape, a universe domain code and inhabited positions. Dependent
child indices, source field-code production and source iota/K remain open.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.FunctionalLabelPositions

open Rcic.Declarative
open UnitModel TypedPER TypedInductive NeutralDataFamily FiniteFamilyLabels

/-- The position type is defined on the class itself, not on a chosen label. -/
def Position {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (q : Class hT.1) :=
  {x : Value // Member (fibreOnClass hT q) x}

def PositionPER {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q : Class hT.1}
    (x y : Position hT q) : Prop := fibreOnClass hT q x.1 y.1

theorem positionPER_refl {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q : Class hT.1} (x : Position hT q) :
    PositionPER hT x x := x.2

theorem positionPER_laws {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (q : Class hT.1) :
    RelLaws (fun x y : Position hT q => PositionPER hT x y) :=
  ⟨(fibreOnClass_laws hT q).symm, (fibreOnClass_laws hT q).trans⟩

def positionSetoid {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (q : Class hT.1) : Setoid (Position hT q) where
  r := PositionPER hT
  iseqv := ⟨positionPER_refl hT, (positionPER_laws hT q).symm,
    (positionPER_laws hT q).trans⟩

/-- Equality transport is data-valued and keeps each actual position value. -/
def move {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q r : Class hT.1} (h : q = r)
    (x : Position hT q) : Position hT r := h ▸ x

theorem move_value {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q r : Class hT.1} (h : q = r)
    (x : Position hT q) : (move hT h x).1 = x.1 := by
  cases h
  rfl

theorem move_refl {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q : Class hT.1} (x : Position hT q) :
    move hT rfl x = x := rfl

theorem move_trans {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q r s : Class hT.1} (h : q = r) (g : r = s)
    (x : Position hT q) : move hT g (move hT h x) = move hT (h.trans g) x := by
  cases h
  cases g
  rfl

theorem move_related {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q r : Class hT.1} (h : q = r)
    {x y : Position hT q} (hxy : PositionPER hT x y) :
    PositionPER hT (move hT h x) (move hT h y) := by
  cases h
  exact hxy

def position {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (xs : Label T) (x : Value)
    (hx : Member (C xs.1) x) : Position hT (classify hT.1 xs) := ⟨x, hx⟩

/-- The canonical transport is exactly the same value with its membership
transported through fibre coherence. Proof irrelevance identifies the certificates. -/
theorem move_position {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {xs ys : Label T} (h : LabelRel xs ys)
    (x : Value) (hx : Member (C xs.1) x) :
    move hT (classify_related hT.1 h) (position hT xs x hx) =
      position hT ys x (fibre_member_transport hT h hx) := by
  apply Subtype.ext
  exact move_value hT (classify_related hT.1 h) _

/-- One unindexed functional recursive field, after any finite dependent
nonrecursive prefix. Its legal-domain position type lives on the quotient. -/
def signature {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) : Signature Unit where
  Rule := fun _ => Class hT.1
  Premise := fun _ q => Position hT q
  child := fun _ _ _ => ()

abbrev leafRel := FiniteFamilyLabels.leafRel
abbrev leaf_laws := FiniteFamilyLabels.leaf_laws

abbrev Legal {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) :=
  LegalTree (signature hT) (fun _ => Nat) leafRel ()

def neutral {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (name : Nat) : Legal hT :=
  legalNeutral (signature hT) (fun _ => Nat) leafRel () name rfl

def nodeClass {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (q : Class hT.1)
    (children : Position hT q → Legal hT) : Legal hT :=
  legalNode (signature hT) (fun _ => Nat) leafRel () q children

def node {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (xs : Label T)
    (children : Position hT (classify hT.1 xs) → Legal hT) : Legal hT :=
  nodeClass hT (classify hT.1 xs) children

theorem nodeClass_related {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q r : Class hT.1} (h : q = r)
    (xs : Position hT q → Legal hT) (ys : Position hT r → Legal hT)
    (hc : ∀ p, Bisim (signature hT) (fun _ => Nat) leafRel
      (xs p).1 (ys (move hT h p)).1) :
    Bisim (signature hT) (fun _ => Nat) leafRel
      (nodeClass hT q xs).1 (nodeClass hT r ys).1 := by
  cases h
  change Bisim (signature hT) (fun _ => Nat) leafRel
    (.node () q (fun p => (xs p).1)) (.node () q (fun p => (ys p).1))
  exact Bisim.node (S := signature hT) (Leaf := fun _ => Nat) (RN := leafRel)
    () q _ _ (fun p => by simpa only [move] using hc p)

theorem node_related {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {a b : Label T} (h : LabelRel a b)
    (xs : Position hT (classify hT.1 a) → Legal hT)
    (ys : Position hT (classify hT.1 b) → Legal hT)
    (hc : ∀ p, Bisim (signature hT) (fun _ => Nat) leafRel
      (xs p).1 (ys (move hT (classify_related hT.1 h) p)).1) :
    Bisim (signature hT) (fun _ => Nat) leafRel (node hT a xs).1 (node hT b ys).1 :=
  nodeClass_related hT (classify_related hT.1 h) xs ys hc

abbrev Family {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) :=
  DependentFamily.FamilyQuotient (S := signature hT) (Leaf := fun _ => Nat) leaf_laws ()

def decodeClass {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (q : Class hT.1)
    (children : Position hT q → Legal hT) : Family hT :=
  DependentFamily.treeClass leaf_laws (nodeClass hT q children)

theorem decodeClass_related {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q r : Class hT.1} (h : q = r)
    (xs : Position hT q → Legal hT) (ys : Position hT r → Legal hT)
    (hc : ∀ p, Bisim (signature hT) (fun _ => Nat) leafRel
      (xs p).1 (ys (move hT h p)).1) : decodeClass hT q xs = decodeClass hT r ys :=
  Quotient.sound (nodeClass_related hT h xs ys hc)

/-- An actual node, inhabited even for a nonempty or infinite position domain. -/
def neutralFan {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) (q : Class hT.1) (name : Nat) : Legal hT :=
  nodeClass hT q (fun _ => neutral hT name)

theorem neutralFan_related {n : Nat} {T : Telescope n} {C : Fields n → Relation}
    (hT : Coherent (.snoc T C)) {q r : Class hT.1} (h : q = r) (name : Nat) :
    Bisim (signature hT) (fun _ => Nat) leafRel
      (neutralFan hT q name).1 (neutralFan hT r name).1 := by
  refine nodeClass_related hT h (fun _ => neutral hT name) (fun _ => neutral hT name) ?_
  intro p
  change Bisim (signature hT) (fun _ => Nat) leafRel (.neutral () name) (.neutral () name)
  exact Bisim.neutral (S := signature hT) (Leaf := fun _ => Nat) (RN := leafRel)
    () name name rfl

namespace Controls

open AdmittedFamilyControls.RawLabels

def labelledCoherent :
    Coherent (.snoc (FiniteFamilyLabelAdapters.TwoField.telescope candidate (fun _ => candidate))
      (fun _ => candidate)) :=
  coherent_snoc FiniteFamilyLabelAdapters.Controls.andCoherent
    (fun _ _ => FamilyLabelQuotient.AndControl.domainLaws) (fun _ _ _ _ _ => Iff.rfl)

/-- Related but distinct explicit labels transport the same raw position. -/
theorem labelled_transport_control :
    move labelledCoherent
      (classify_related labelledCoherent.1 FiniteFamilyLabelAdapters.Controls.and_related)
      (position labelledCoherent FiniteFamilyLabelAdapters.Controls.andLeft x x_member) =
    position labelledCoherent FiniteFamilyLabelAdapters.Controls.andRight x x_member :=
  move_position labelledCoherent FiniteFamilyLabelAdapters.Controls.and_related x x_member

theorem labelled_constructor_control :
    Bisim (signature labelledCoherent) (fun _ => Nat) leafRel
      (neutralFan labelledCoherent
        (classify labelledCoherent.1 FiniteFamilyLabelAdapters.Controls.andLeft) 7).1
      (neutralFan labelledCoherent
        (classify labelledCoherent.1 FiniteFamilyLabelAdapters.Controls.andRight) 7).1 :=
  neutralFan_related labelledCoherent
    (classify_related labelledCoherent.1 FiniteFamilyLabelAdapters.Controls.and_related) 7

abbrev universeDomain : Relation := NeutralCodes.UniversePER (some 0)

def frecCoherent : Coherent (.snoc .empty (fun _ => universeDomain)) :=
  coherent_snoc coherent_empty (fun _ _ => NeutralCodes.universePER_laws (some 0))
    (fun _ _ _ _ _ => Iff.rfl)

def frecPosition (name : Nat) : Position frecCoherent (classify frecCoherent.1 emptyLabel) :=
  position frecCoherent emptyLabel (NeutralCodes.reflectDescriptor (.univ (some 0)) name)
    (NeutralCodes.reflectDescriptor_member (.univ (some 0)) name)

theorem frec_positions_related : PositionPER frecCoherent (frecPosition 0) (frecPosition 1) :=
  ⟨.neutralType (some 0) 0, .neutralType (some 0) 1, rfl, rfl,
    ValueEq.refl _, ValueEq.refl _⟩

/-- The actual admitted W-shaped functional domain is Sort 0. Its supplied
universe PER gives legal positions and an explicit neutral-child node.
This does not assert interpretation of the source constructor constant. -/
theorem frec_pattern_inhabited :
    Nonempty (EnvWfA noIotaA pinFrecGroupEnvA) ∧
    (pinFrecNodeViewA noIotaA).fields = [.frec (.sort .zero) (.succ .zero) [] []] ∧
    NeutralCodes.Code (some 1) (TypedStatements.universeValue (some 0)) universeDomain ∧
    PositionPER frecCoherent (frecPosition 0) (frecPosition 1) ∧
    Bisim (signature frecCoherent) (fun _ => Nat) leafRel
      (neutralFan frecCoherent (classify frecCoherent.1 emptyLabel) 7).1
      (neutralFan frecCoherent (classify frecCoherent.1 emptyLabel) 7).1 :=
  ⟨⟨pinFrecGroupWfA noIotaA⟩, rfl, NeutralCodes.code_universe (some 0),
    frec_positions_related, (neutralFan frecCoherent (classify frecCoherent.1 emptyLabel) 7).2⟩

end Controls

end Rcic.Declarative.Ann.LR3.FunctionalLabelPositions
