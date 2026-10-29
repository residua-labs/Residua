import rcic.RcicAnnLR3ReflectiveConversionUniverse

/-!
# An inhabited extension from named types to complete neutral spines

The atom-only certified universe embeds into the new reflective universe,
preserving raw member images, its exact equality PER, and designated points.
The actual neutral-application reflection has a raw image outside this
embedding. This gives a concrete positive extension of the obstruction;
no minimality or universal property of the extension is asserted.

The conversion-based Pi actions also retain distinct neutral names in their
PER. Thus their relation does not inherit the older K minor's collapse of
all neutral-only candidate results. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.SemanticSpineCompletion

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

universe u

def embed (name : UniverseSpineBoundary.nameUniverse.Element) :
    ReflectiveConversionUniverse.zero.{u}.Element :=
  ReflectiveConversionUniverse.reflect (NeutralPER.neutralAtom name) (.atom name)

theorem embed_image (name : UniverseSpineBoundary.nameUniverse.Element) :
    ValueEq (ReflectiveConversionUniverse.zero.{u}.erase (embed name))
      (UniverseSpineBoundary.nameUniverse.erase name) :=
  UniverseSpineBoundary.tagged_atom_native (some 0) name

theorem embed_relation_iff (r s : UniverseSpineBoundary.nameUniverse.Element) :
    ReflectiveConversionUniverse.zero.{u}.view.relation (embed r) (embed s) ↔
      UniverseSpineBoundary.nameUniverse.view.relation r s := by
  constructor
  · intro h
    have ht := GuardedTaggedCode.converts_type_image h
    have hn := (embed_image.{u} r).symm.trans (ht.trans (embed_image.{u} s))
    exact TaggedSaturatedTower.native_value_name_injective (some 0) r s hn
  · intro h
    change r = s at h
    cases h
    exact ReflectiveConversionUniverse.reflect_member _ (.atom r)

theorem embed_point (name : Nat) :
    embed.{u} (UniverseSpineBoundary.nameUniverse.view.point name) =
      ReflectiveConversionUniverse.zero.{u}.view.point name := rfl

def spine : ReflectiveConversionUniverse.zero.{u}.Element :=
  ReflectiveConversionUniverse.reflect UniverseSpineBoundary.application
    UniverseSpineBoundary.application_neutral

theorem spine_member :
    ReflectiveConversionUniverse.zero.{u}.view.relation spine spine :=
  ReflectiveConversionUniverse.reflect_member _ UniverseSpineBoundary.application_neutral

theorem spine_image :
    ReflectiveConversionUniverse.zero.{u}.erase spine =
      InductiveCodes.taggedValue (some 0) UniverseSpineBoundary.application := rfl

theorem spine_outside_embedding (name : UniverseSpineBoundary.nameUniverse.Element) :
    ¬ ValueEq (ReflectiveConversionUniverse.zero.{u}.erase spine)
      (ReflectiveConversionUniverse.zero.{u}.erase (embed name)) := by
  intro h
  exact UniverseSpineBoundary.no_application_member name
    ((h.trans (embed_image.{u} name)).symm)

theorem inhabited_extension :
    (∀ name, ReflectiveConversionUniverse.zero.{u}.view.relation
      (embed name) (embed name)) ∧
    ReflectiveConversionUniverse.zero.{u}.view.relation spine spine ∧
    (∀ name, ¬ ValueEq (ReflectiveConversionUniverse.zero.{u}.erase spine)
      (ReflectiveConversionUniverse.zero.{u}.erase (embed name))) :=
  ⟨fun name => ReflectiveConversionUniverse.reflect_member _ (.atom name),
    spine_member, spine_outside_embedding⟩

/-- On every full extended Code j domain, reflected atom names are related
exactly when the names agree. The argument is an actual certified Code j. -/
theorem reflected_action_names (j r s : Nat) :
    SaturatedPiElements.ElementRel
      (CertifiedUniverseEta.reflectAction.{u} j (NeutralPER.neutralAtom r) (.atom r))
      (CertifiedUniverseEta.reflectAction.{u} j (NeutralPER.neutralAtom s) (.atom s)) ↔
      r = s := by
  constructor
  · intro h
    let A : GuardedTaggedCode.Code.{u} j :=
      .legacy (TaggedSaturatedTower.Code.neutral.{u} j 0)
    have hA : A.view.value .bot := NativeMemberValues.value_bot (some j) 0
    have he : ValueEq (NeutralPi.applyValue (NeutralPER.neutralAtom r) A.view.value)
        (NeutralPi.applyValue (NeutralPER.neutralAtom s) A.view.value) :=
      (CertifiedUniverseEta.reflect_converts_iff _ _
        (.app (.atom r) _ (CandidatePi.typeDefined_nonempty A.view.defined))
        (.app (.atom s) _ (CandidatePi.typeDefined_nonempty A.view.defined))).mp
          (h A (GuardedTaggedCode.converts_refl A))
    have hr : NeutralPi.applyValue (NeutralPER.neutralAtom r) A.view.value
        (.spine r [.bot]) :=
      Or.inr (Or.inr ⟨r, [], .bot, rfl, NeutralPER.neutralAtom_observed r, hA⟩)
    have hs := (NeutralPi.applyValue_atom s A.view.value (.spine r [.bot])).mp
      ((he _).mp hr)
    rcases hs with hbot | ⟨z, hz, heq⟩
    · cases hbot
    · exact (CptI.spine.inj heq).1
  · intro h
    cases h
    exact CertifiedUniverseEta.reflectAction_member j _ (.atom r)

end Rcic.Declarative.Ann.LR3.SemanticSpineCompletion
