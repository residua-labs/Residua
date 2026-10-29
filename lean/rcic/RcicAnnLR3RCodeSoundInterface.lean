import rcic.RcicAnnLR3EnvironmentEvalComposition
import rcic.RcicAnnLR3GuardedTaggedCode

/-!
# Contextual reflective codes for the soundness layer

This interface separates propositional source gluing from decidable
normal-form quotation. Its elements are self-members of an existing
certified pointed PER. A fixed source/raw world supplies actual typing
and the inherited evaluator; each retained interpretation supplies its
own fragment, exact erasure and same-source coherence. A raw type image
does not determine retained bindings, and coherence is an explicit
obligation rather than a consequence of equality of raw images.

Reflection covers every source-typed neutral image, including application
spines. It produces a member related to an actual evaluated representative
whose source is convertible to the input. It need not preserve the input's
raw graph: typed Pi eta expansion and tagged universe reflection are not
excluded by an exact-raw-reflection requirement.

ReadsBack is a source-indexed proposition containing semantic relatedness
and an actual source conversion witness. Conversion is Type-valued, so
the witness is wrapped in Nonempty. Readback is inhabited by the source
itself and is stable under source conversion; it is not normalization,
a choice of canonical syntax, or a decision procedure. No NF, DecidableEq,
quotation equality, or reflection of arbitrary ambient type bindings is
part of this interface. Generator closure and the Fundamental theorem
remain separate construction obligations. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeSoundInterface

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower

universe u v

/-- Admission fixes the source context and the raw environment. Retained
bindings belong to the interpretation instance; this record alone is
not a general semantic-context or retained-environment judgment. -/
structure World where
  env : ResolvedEnvA
  iota : IotaIfaceA
  levelCount : Nat
  context : LCtxA
  family : EnvironmentEval.FamilySyntax
  valuation : Valuation
  rawEnvironment : EnvI
  envWf : EnvWfA iota env
  contextWf : CtxWfA env iota levelCount context

def World.evaluate (W : World) (e : ExprA) : Value :=
  EnvironmentEval.denote W.env W.family W.valuation W.rawEnvironment e

structure Source (W : World) (A : ExprA) where
  term : ExprA
  typed : HasTyA W.env W.iota W.levelCount W.context term A

/-- Both source typing and the actual evaluator image are retained.
Semantic neutrality on its own is insufficient to construct this input. -/
structure Neutral (W : World) (A : ExprA) extends Source W A where
  value : Value
  image : ValueEq (W.evaluate term) value
  neutral : CandidatePi.Neutral value

/-- Actual source application extends a neutral spine. The result typing
is an ordinary HasTyA derivation, allowing a typed conversion of the result
type. Evaluator composition and positive neutrality are proved here. -/
def Neutral.app {W : World} {A B R : ExprA} {lA lB : Level}
    (f : Neutral W (.pi A lA B lB)) (a : Source W A)
    (ht : HasTyA W.env W.iota W.levelCount W.context (.app f.term a.term) R) :
    Neutral W R where
  term := .app f.term a.term
  typed := ht
  value := NeutralPi.applyValue f.value (W.evaluate a.term)
  image := (EnvironmentEval.denote_application W.env W.family W.valuation
    W.rawEnvironment f.term a.term).trans
      (NeutralPi.applyValue_congr f.image (ValueEq.refl _))
  neutral := .app f.neutral (W.evaluate a.term)
    (CandidatePi.environment_denote_nonempty W.env W.family W.valuation
      W.rawEnvironment a.term)

abbrev Member {k : Nat} (C : GuardedTaggedCode.Code.{u} k) :=
  {x : C.Element // C.view.relation x x}

def Related {k : Nat} {C : GuardedTaggedCode.Code.{u} k}
    (x y : Member C) : Prop := C.view.relation x.val y.val

theorem related_refl {k : Nat} {C : GuardedTaggedCode.Code.{u} k}
    (x : Member C) : Related x x := x.property

theorem related_symm {k : Nat} {C : GuardedTaggedCode.Code.{u} k}
    {x y : Member C} (h : Related x y) : Related y x := C.view.lawful.symm h

theorem related_trans {k : Nat} {C : GuardedTaggedCode.Code.{u} k}
    {x y z : Member C} (h : Related x y) (g : Related y z) : Related x z :=
  C.view.lawful.trans h g

/-- The common soundness specification. Exact erasure is required for
the retained evaluator outputs; reflection itself only needs a realized,
source-convertible representative. Realization is existential in Prop,
so the interface does not choose syntax for arbitrary members. -/
structure RCodeSound (W : World) (k : Nat) where
  code : GuardedTaggedCode.Code.{u} k
  sourceType : ExprA
  sourceLevel : Level
  typeTyped : HasTyA W.env W.iota W.levelCount W.context sourceType (.sort sourceLevel)
  level : eval W.valuation sourceLevel = some k
  typeImage : ValueEq (W.evaluate sourceType) code.view.value
  Fragment : Type v
  source : Fragment → Source W sourceType
  evalSem : Fragment → Member code
  erasure : ∀ s, ValueEq (code.erase (evalSem s).val) (W.evaluate (source s).term)
  source_coherence : ∀ s t, (source s).term = (source t).term →
    Related (evalSem s) (evalSem t)
  realization : ∀ x : Member code, ∃ s : Fragment, Related x (evalSem s)
  reflect : Neutral W sourceType → Member code
  reflection_source : ∀ n : Neutral W sourceType,
    ∃ s : Fragment, Related (reflect n) (evalSem s) ∧
      Nonempty (ConvA W.env W.iota W.levelCount W.context
        (source s).term n.term sourceType)

abbrev RCodeSound.Element {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) := Member C.code

def RCodeSound.erase {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) (x : C.Element) : Value := C.code.erase x.val

def RCodeSound.point {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) (name : Nat) : C.Element :=
  ⟨C.code.view.point name, C.code.view.point_member name⟩

/-- The input realization is explicit. A target source cannot be called
a readback merely because it has the same type or raw erasure. -/
def RCodeSound.ReadsBack {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) (s : C.Fragment) (x : C.Element)
    (t : Source W C.sourceType) : Prop :=
  Related x (C.evalSem s) ∧
    Nonempty (ConvA W.env W.iota W.levelCount W.context
      (C.source s).term t.term C.sourceType)

theorem RCodeSound.ReadsBack.semantic_sound {W : World} {k : Nat}
    {C : RCodeSound.{u,v} W k} {s : C.Fragment} {x : C.Element}
    {t : Source W C.sourceType} (h : C.ReadsBack s x t) :
    Related x (C.evalSem s) := h.1

theorem RCodeSound.ReadsBack.source_sound {W : World} {k : Nat}
    {C : RCodeSound.{u,v} W k} {s : C.Fragment} {x : C.Element}
    {t : Source W C.sourceType} (h : C.ReadsBack s x t) :
    Nonempty (ConvA W.env W.iota W.levelCount W.context
      (C.source s).term t.term C.sourceType) := h.2

/-- Every fragment evaluation has a readback, namely its actual source.
This is propositional gluing and does not assert source normalization. -/
theorem RCodeSound.readback_total {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) (s : C.Fragment) :
    C.ReadsBack s (C.evalSem s) (C.source s) :=
  ⟨related_refl _, ⟨.refl W.context (C.source s).term C.sourceType (C.source s).typed⟩⟩

theorem RCodeSound.member_readback {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) (x : C.Element) :
    ∃ s : C.Fragment, C.ReadsBack s x (C.source s) := by
  obtain ⟨s, hs⟩ := C.realization x
  exact ⟨s, hs, (C.readback_total s).2⟩

theorem RCodeSound.fragment_nonempty {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) : Nonempty C.Fragment := by
  obtain ⟨s, _⟩ := C.realization (C.point 0)
  exact ⟨s⟩

theorem RCodeSound.realized {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) (x : C.Element) :
    ∃ s : C.Fragment, Related x (C.evalSem s) ∧
      ValueEq (C.erase (C.evalSem s)) (W.evaluate (C.source s).term) := by
  obtain ⟨s, hs⟩ := C.realization x
  exact ⟨s, hs, C.erasure s⟩

theorem RCodeSound.reflected_readback {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) (n : Neutral W C.sourceType) :
    ∃ s : C.Fragment, C.ReadsBack s (C.reflect n) n.toSource :=
  C.reflection_source n

/-- Saturation includes every admitted source neutral and its actual
evaluator-backed representative. No equality of reflected raw graphs
with the neutral input is assumed or concluded. -/
theorem RCodeSound.neutral_saturation {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) (n : Neutral W C.sourceType) :
    ∃ s : C.Fragment, C.ReadsBack s (C.reflect n) n.toSource ∧
      ValueEq (C.erase (C.evalSem s)) (W.evaluate (C.source s).term) := by
  obtain ⟨s, hs⟩ := C.reflected_readback n
  exact ⟨s, hs, C.erasure s⟩

/-- Application-spine saturation uses an actual application derivation
and the inherited application evaluator law, not an atom-only domain. -/
theorem RCodeSound.application_saturation {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) {A B : ExprA} {lA lB : Level}
    (f : Neutral W (.pi A lA B lB)) (a : Source W A)
    (ht : HasTyA W.env W.iota W.levelCount W.context
      (.app f.term a.term) C.sourceType) :
    ∃ s : C.Fragment, C.ReadsBack s (C.reflect (Neutral.app f a ht))
      (Neutral.app f a ht).toSource :=
  C.reflected_readback (Neutral.app f a ht)

theorem RCodeSound.ReadsBack.related {W : World} {k : Nat}
    {C : RCodeSound.{u,v} W k} {s : C.Fragment} {x y : C.Element}
    {t : Source W C.sourceType} (h : C.ReadsBack s x t)
    (hyx : Related y x) : C.ReadsBack s y t :=
  ⟨related_trans hyx h.1, h.2⟩

theorem RCodeSound.ReadsBack.convert {W : World} {k : Nat}
    {C : RCodeSound.{u,v} W k} {s : C.Fragment} {x : C.Element}
    {t q : Source W C.sourceType} (h : C.ReadsBack s x t)
    (htq : Nonempty (ConvA W.env W.iota W.levelCount W.context
      t.term q.term C.sourceType)) : C.ReadsBack s x q := by
  obtain ⟨hst⟩ := h.2
  obtain ⟨htq⟩ := htq
  exact ⟨h.1, ⟨.trans W.context (C.source s).term t.term q.term
    C.sourceType hst htq⟩⟩

/-- Typed eta is compatible with propositional readback. This proves
the source-conversion part only; semantic Pi action and generator closure
must still be constructed. In particular no raw eta equality is asserted. -/
theorem RCodeSound.reflection_eta_readback {W : World} {k : Nat}
    (C : RCodeSound.{u,v} W k) (n : Neutral W C.sourceType)
    (A B : ExprA) (lA lB : Level) (hpi : C.sourceType = .pi A lA B lB)
    (heta : HasTyA W.env W.iota W.levelCount W.context
      (.lam A lA (.app (liftA 0 1 n.term) (.bvar 0))) C.sourceType) :
    ∃ s : C.Fragment, C.ReadsBack s (C.reflect n)
      ⟨.lam A lA (.app (liftA 0 1 n.term) (.bvar 0)), heta⟩ := by
  obtain ⟨s, hs⟩ := C.reflected_readback n
  refine ⟨s, hs.convert ?_⟩
  have hn : HasTyA W.env W.iota W.levelCount W.context
      n.term (.pi A lA B lB) := by
    rw [← hpi]
    exact n.typed
  have he : HasTyA W.env W.iota W.levelCount W.context
      (.lam A lA (.app (liftA 0 1 n.term) (.bvar 0))) (.pi A lA B lB) := by
    rw [← hpi]
    exact heta
  have h : ConvA W.env W.iota W.levelCount W.context n.term
      (.lam A lA (.app (liftA 0 1 n.term) (.bvar 0))) (.pi A lA B lB) :=
    .symm W.context _ _ _ (.eta W.context n.term A B lA lB hn he)
  rw [← hpi] at h
  exact ⟨h⟩

end Rcic.Declarative.Ann.LR3.RCodeSoundInterface
