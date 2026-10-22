import rcic.RcicAnnLR3FiniteFamilyLabels

/-!
# Finite-label adapters and inhabited controls

The earlier two-field dependent label algebra embeds and retracts exactly.
Repeated lawful PERs give actual legal labels and constructor congruence at
every finite length. Nat's nullary and And's two-field admitted patterns
instantiate the new interface. These are field-pattern controls; no source
constructor denotation or generic recursor is inferred from them.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.FiniteFamilyLabelAdapters

open Rcic.Declarative
open UnitModel TypedPER TypedInductive NeutralDataFamily FiniteFamilyLabels

namespace TwoField

def telescope (D : Relation) (C : Value → Relation) : Telescope 2 :=
  .snoc (.snoc .empty (fun _ => D)) (fun xs => C xs.2)

theorem coherent {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (hc : FamilyCoherent D C) :
    Coherent (telescope D C) :=
  coherent_snoc
    (coherent_snoc coherent_empty (fun _ _ => hD) (fun _ _ _ _ _ => Iff.rfl))
    (fun xs hx => hC xs.2 hx.2)
    (fun xs ys hxy => hc xs.2 ys.2 hxy.2)

def embed {D : Relation} {C : Value → Relation}
    (a : FamilyLabelQuotient.Label D C) : Label (telescope D C) :=
  ⟨(((), a.first), a.second), ⟨True.intro, a.first_member⟩, a.second_member⟩

def project {D : Relation} {C : Value → Relation}
    (a : Label (telescope D C)) : FamilyLabelQuotient.Label D C :=
  ⟨a.1.1.2, a.1.2, a.2.1.2, a.2.2⟩

theorem project_embed {D : Relation} {C : Value → Relation}
    (a : FamilyLabelQuotient.Label D C) : project (embed a) = a := rfl

theorem embed_project {D : Relation} {C : Value → Relation}
    (a : Label (telescope D C)) : embed (project a) = a := by
  rcases a with ⟨⟨⟨p, x⟩, y⟩, h⟩
  cases p
  rfl

theorem embed_related_iff {D : Relation} {C : Value → Relation}
    (a b : FamilyLabelQuotient.Label D C) :
    LabelRel (embed a) (embed b) ↔ FamilyLabelQuotient.LabelPER a b :=
  ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨True.intro, h.1⟩, h.2⟩⟩

theorem project_related {D : Relation} {C : Value → Relation}
    {a b : Label (telescope D C)} (h : LabelRel a b) :
    FamilyLabelQuotient.LabelPER (project a) (project b) := ⟨h.1.2, h.2⟩

/-- Actual quotient descent of the explicit label embedding. -/
def embedClass {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (hc : FamilyCoherent D C) :
    FamilyLabelQuotient.Class hD hC hc → Class (coherent hD hC hc) :=
  Quotient.lift (fun a => classify (coherent hD hC hc) (embed a))
    (fun a b h => classify_related (coherent hD hC hc) ((embed_related_iff a b).mpr h))

def projectClass {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (hc : FamilyCoherent D C) :
    Class (coherent hD hC hc) → FamilyLabelQuotient.Class hD hC hc :=
  Quotient.lift (fun a => FamilyLabelQuotient.classify hD hC hc (project a))
    (fun _ _ h => FamilyLabelQuotient.classify_related hD hC hc (project_related h))

theorem projectClass_embedClass {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (hc : FamilyCoherent D C)
    (q : FamilyLabelQuotient.Class hD hC hc) :
    projectClass hD hC hc (embedClass hD hC hc q) = q := by
  refine Quotient.inductionOn q ?_
  intro a
  rfl

theorem embedClass_projectClass {D : Relation} {C : Value → Relation}
    (hD : Laws D) (hC : ∀ x, Member D x → Laws (C x)) (hc : FamilyCoherent D C)
    (q : Class (coherent hD hC hc)) :
    embedClass hD hC hc (projectClass hD hC hc q) = q := by
  refine Quotient.inductionOn q ?_
  intro a
  change classify _ (embed (project a)) = classify _ a
  rw [embed_project]

end TwoField

namespace Repeated

def telescope (D : Relation) : (n : Nat) → Telescope n
  | 0 => .empty
  | n + 1 => .snoc (telescope D n) (fun _ => D)

theorem coherent {D : Relation} (hD : Laws D) : (n : Nat) → Coherent (telescope D n)
  | 0 => coherent_empty
  | n + 1 => coherent_snoc (coherent hD n) (fun _ _ => hD) (fun _ _ _ _ _ => Iff.rfl)

def label {D : Relation} (x : Value) (hx : Member D x) : (n : Nat) → Label (telescope D n)
  | 0 => emptyLabel
  | n + 1 => snocLabel (label x hx n) x hx

theorem label_related {D : Relation} {x y : Value}
    (hx : Member D x) (hy : Member D y) (hxy : D x y) :
    (n : Nat) → LabelRel (label x hx n) (label y hy n)
  | 0 => True.intro
  | n + 1 => snocLabel_related (label_related hx hy hxy n) hx hy hxy

theorem decoded_equal {D : Relation} (hD : Laws D) {x y : Value}
    (hx : Member D x) (hy : Member D y) (hxy : D x y) (n : Nat) :
    decode (coherent hD n) (label x hx n) = decode (coherent hD n) (label y hy n) :=
  decode_related (coherent hD n) (label_related hx hy hxy n)

end Repeated

namespace Controls

open AdmittedFamilyControls.RawLabels

/-- The general construction accepts the actual admitted nullary pattern. -/
theorem nat_zero_pattern :
    Nonempty (EnvWfA (iotaIfaceA pinNatBuiltEnvA) pinNatBuiltEnvA) ∧
    (pinNatZeroViewA (iotaIfaceA pinNatBuiltEnvA)).fields = [] ∧
    (emptyLabel : Label .empty).1.toList = [] ∧
    LabelRel emptyLabel emptyLabel :=
  ⟨⟨pinNatBuilt_wf⟩, rfl, rfl, labelRel_refl emptyLabel⟩

def andCoherent : Coherent (TwoField.telescope candidate (fun _ => candidate)) :=
  TwoField.coherent FamilyLabelQuotient.AndControl.domainLaws
    FamilyLabelQuotient.AndControl.fibreLaws FamilyLabelQuotient.AndControl.coherent

def andLeft : Label (TwoField.telescope candidate (fun _ => candidate)) :=
  TwoField.embed FamilyLabelQuotient.AndControl.leftLabel

def andRight : Label (TwoField.telescope candidate (fun _ => candidate)) :=
  TwoField.embed FamilyLabelQuotient.AndControl.rightLabel

theorem and_related : LabelRel andLeft andRight :=
  (TwoField.embed_related_iff _ _).mpr FamilyLabelQuotient.AndControl.labels_related

theorem and_decoded_equal :
    FiniteFamilyLabels.decode andCoherent andLeft =
      FiniteFamilyLabels.decode andCoherent andRight := decode_related andCoherent and_related

/-- All source admission premises and both related explicit labels are
inhabited. The statement does not identify source denotations with labels. -/
theorem and_pattern_inhabited :
    Nonempty (EnvWfA (iotaIfaceA pinAndEnvA) pinAndEnvA) ∧
    (pinAndMkViewA (iotaIfaceA pinAndEnvA)).fields =
      [.plain (.bvar 1) .zero, .plain (.bvar 1) .zero] ∧
    andLeft.1.toList = [x, x] ∧ andRight.1.toList = [y, x] ∧
    LabelRel andLeft andRight ∧
    FiniteFamilyLabels.decode andCoherent andLeft =
      FiniteFamilyLabels.decode andCoherent andRight :=
  ⟨⟨pinAnd_wf⟩, rfl, rfl, rfl, and_related, and_decoded_equal⟩

/-- The construction and distinct-related-value control have no fixed
arity bound. This is a semantic label control, not a new source admission. -/
theorem every_length_inhabited (n : Nat) :
    Coherent (Repeated.telescope candidate n) ∧
    (Repeated.label x x_member n).1.toList.length = n ∧
    (Repeated.label y y_member n).1.toList.length = n ∧
    LabelRel (Repeated.label x x_member n) (Repeated.label y y_member n) ∧
    FiniteFamilyLabels.decode (Repeated.coherent FamilyLabelQuotient.AndControl.domainLaws n)
      (Repeated.label x x_member n) =
    FiniteFamilyLabels.decode (Repeated.coherent FamilyLabelQuotient.AndControl.domainLaws n)
      (Repeated.label y y_member n) :=
  ⟨Repeated.coherent FamilyLabelQuotient.AndControl.domainLaws n,
    Fields.toList_length _, Fields.toList_length _,
    Repeated.label_related x_member y_member fields_related.1 n,
    Repeated.decoded_equal FamilyLabelQuotient.AndControl.domainLaws
      x_member y_member fields_related.1 n⟩

end Controls

end Rcic.Declarative.Ann.LR3.FiniteFamilyLabelAdapters
