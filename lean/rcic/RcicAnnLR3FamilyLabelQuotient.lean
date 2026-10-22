import rcic.RcicAnnLR3AdmittedFamilyControls

/-!
# Legal quotients for a dependent two-field constructor telescope

The label carries two actual values and their membership certificates. Its
second field lives in a fibre over the first. The label PER uses the two
field relations, and its laws use legal-domain fibre coherence.

The constructor rule is the quotient of those legal labels. Thus related
fields give equal rule labels and hence bisimilar constructor trees. The
decoder constructs the corresponding legal-tree quotient directly from a
label class; it selects no representative. Actual field data remain in
the caller's `Label`, alongside its class.

The admitted And control repairs the previous raw-label counterexample.
This is a nonrecursive two-field producer, not a decoder for arbitrary
admitted families. Recursive-position transport, bare-Value encoding,
source constructor application and generic iota/K remain separate.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.FamilyLabelQuotient

open Rcic.Declarative
open UnitModel TypedPER TypedInductive NeutralDataFamily

universe u

/-- Explicit legal telescope data. The second membership is in the first
value's actual fibre; no value is selected from a membership proposition. -/
structure Label (D : Relation) (C : Value → Relation) where
  first : Value
  second : Value
  first_member : Member D first
  second_member : Member (C first) second

def LabelPER {D : Relation} {C : Value → Relation} (a b : Label D C) : Prop :=
  D a.first b.first ∧ C a.first a.second b.second

theorem labelPER_refl {D : Relation} {C : Value → Relation} (a : Label D C) :
    LabelPER a a := ⟨a.first_member, a.second_member⟩

theorem labelPER_symm {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    {a b : Label D C} (h : LabelPER a b) : LabelPER b a := by
  refine ⟨hD.symm h.1, ?_⟩
  exact (coh a.first b.first h.1 _ _).mp
    ((hC a.first a.first_member).symm h.2)

theorem labelPER_trans {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    {a b c : Label D C} (h : LabelPER a b) (g : LabelPER b c) : LabelPER a c := by
  refine ⟨hD.trans h.1 g.1, ?_⟩
  exact (hC a.first a.first_member).trans h.2
    ((coh a.first b.first h.1 _ _).mpr g.2)

theorem labelPER_laws {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C) :
    RelLaws (fun a b : Label D C => LabelPER a b) :=
  ⟨labelPER_symm hD hC coh, labelPER_trans hD hC coh⟩

def labelSetoid {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C) :
    Setoid (Label D C) where
  r := LabelPER
  iseqv := ⟨labelPER_refl, labelPER_symm hD hC coh, labelPER_trans hD hC coh⟩

abbrev Class {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C) :=
  Quotient (labelSetoid hD hC coh)

def classify {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    (a : Label D C) : Class hD hC coh := Quotient.mk _ a

theorem classify_related {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    {a b : Label D C} (h : LabelPER a b) : classify hD hC coh a = classify hD hC coh b :=
  Quotient.sound h

/-- The existing structural tree now sees equal labels for related fields. -/
def signature {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C) :
    Signature Unit where
  Rule := fun _ => Class hD hC coh
  Premise := fun _ _ => Empty
  child := fun _ _ p => nomatch p

def leafRel (_ : Unit) (a b : Nat) : Prop := a = b

theorem leaf_laws (i : Unit) : RelLaws (leafRel i) := ⟨Eq.symm, Eq.trans⟩

def nodeClass {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    (a : Class hD hC coh) :
    LegalTree (signature hD hC coh) (fun _ => Nat) leafRel () :=
  legalNode (signature hD hC coh) (fun _ => Nat) leafRel () a (fun p => nomatch p)

def node {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    (a : Label D C) :
    LegalTree (signature hD hC coh) (fun _ => Nat) leafRel () :=
  nodeClass hD hC coh (classify hD hC coh a)

theorem node_related {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    {a b : Label D C} (h : LabelPER a b) :
    Bisim (signature hD hC coh) (fun _ => Nat) leafRel
      (node hD hC coh a).1 (node hD hC coh b).1 := by
  have he := classify_related hD hC coh h
  change Bisim _ _ _ (nodeClass hD hC coh (classify hD hC coh a)).1
    (nodeClass hD hC coh (classify hD hC coh b)).1
  rw [he]
  exact (nodeClass hD hC coh (classify hD hC coh b)).2

abbrev Family {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C) :=
  DependentFamily.FamilyQuotient (S := signature hD hC coh)
    (Leaf := fun _ => Nat) leaf_laws ()

/-- Direct construction from the label quotient. There is no quotient
representative selection or raw-value projection in this decoder. -/
def decodeClass {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    (a : Class hD hC coh) : Family hD hC coh :=
  DependentFamily.treeClass leaf_laws (nodeClass hD hC coh a)

/-- The caller supplies the explicit legal label and can retain it. -/
def decode {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    (a : Label D C) : Family hD hC coh :=
  decodeClass hD hC coh (classify hD hC coh a)

theorem decode_related {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    {a b : Label D C} (h : LabelPER a b) : decode hD hC coh a = decode hD hC coh b :=
  Quotient.sound (node_related hD hC coh h)

/-- Motives on the legal-tree quotient have canonical equality transport. -/
theorem decode_transport {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (coh : FamilyCoherent D C)
    {a b : Label D C} (h : LabelPER a b)
    (M : Family hD hC coh → Type u) (sectionValue : ∀ q, M q) :
    DependentFamily.transport M (decode_related hD hC coh h)
      (sectionValue (decode hD hC coh a)) = sectionValue (decode hD hC coh b) := by
  have transport_section : ∀ (p q : Family hD hC coh) (he : p = q),
      DependentFamily.transport M he (sectionValue p) = sectionValue q := by
    intro p q he
    cases he
    rfl
  exact transport_section _ _ _

namespace AndControl

open AdmittedFamilyControls.RawLabels

def domainLaws : Laws candidate := NeutralCodes.code_lawful candidate_code
def fibreLaws : ∀ a, Member candidate a → Laws candidate := fun _ _ => domainLaws
def coherent : FamilyCoherent candidate (fun _ => candidate) := fun _ _ _ _ _ => Iff.rfl

def leftLabel : Label candidate (fun _ => candidate) := ⟨x, x, x_member, x_member⟩
def rightLabel : Label candidate (fun _ => candidate) := ⟨y, x, y_member, x_member⟩

theorem labels_related : LabelPER leftLabel rightLabel := fields_related

theorem constructor_related :
    Bisim (FamilyLabelQuotient.signature domainLaws fibreLaws coherent) (fun _ => Nat)
      FamilyLabelQuotient.leafRel
      (FamilyLabelQuotient.node domainLaws fibreLaws coherent leftLabel).1
      (FamilyLabelQuotient.node domainLaws fibreLaws coherent rightLabel).1 :=
  node_related domainLaws fibreLaws coherent labels_related

theorem decoded_equal :
    decode domainLaws fibreLaws coherent leftLabel =
      decode domainLaws fibreLaws coherent rightLabel :=
  decode_related domainLaws fibreLaws coherent labels_related

/-- The old raw-label failure and the repaired related constructor pair
are inhabited simultaneously in the actual admitted And field pattern. -/
theorem inhabited_repair :
    Nonempty (EnvWfA (iotaIfaceA pinAndEnvA) pinAndEnvA) ∧
    (pinAndMkViewA (iotaIfaceA pinAndEnvA)).fields =
      [.plain (.bvar 1) .zero, .plain (.bvar 1) .zero] ∧
    NeutralCodes.Code (some 0) (NeutralCodes.proofCodeValue False) candidate ∧
    LabelPER leftLabel rightLabel ∧
    (¬ Bisim AdmittedFamilyControls.RawLabels.signature (fun _ => Nat)
      AdmittedFamilyControls.RawLabels.leafRel
      (AdmittedFamilyControls.RawLabels.node x x) (AdmittedFamilyControls.RawLabels.node y x)) ∧
    Bisim (FamilyLabelQuotient.signature domainLaws fibreLaws coherent) (fun _ => Nat)
      FamilyLabelQuotient.leafRel
      (FamilyLabelQuotient.node domainLaws fibreLaws coherent leftLabel).1
      (FamilyLabelQuotient.node domainLaws fibreLaws coherent rightLabel).1 ∧
    decode domainLaws fibreLaws coherent leftLabel =
      decode domainLaws fibreLaws coherent rightLabel :=
  ⟨⟨pinAnd_wf⟩, rfl, candidate_code, labels_related, raw_label_not_related,
    constructor_related, decoded_equal⟩

end AndControl

end Rcic.Declarative.Ann.LR3.FamilyLabelQuotient
