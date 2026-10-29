import rcic.RcicAnnLR3OptionSoundUniverse
import rcic.RcicAnnLR3RCodeSoundInterface
import rcic.RcicAnnLR3RCodeProofReadback

/-!
# The soundness interface over Option-indexed codes

`RCodeSoundO W k` is the soundness-only interface of `RCodeSound`, with its
code taken from the one Option-indexed universe `OCode k` and its source level
evaluating to `k : Option Nat`. It has the same fields: actual source typing,
a retained evaluator with exact erasure, same-source coherence, propositional
realization, and source-typed neutral reflection with a convertible realized
representative. There is no normal form, no decidable equality and no
quotation equation.

At a finite level the two interfaces are equivalent: `ofNat` and `toNat` are
mutually inverse, so every existing Nat-indexed instance is an instance here
and nothing is lost or added at `some k`. At `none`, `chaotic` builds an
instance on an ordinary none code from one typed source point, with every
typed source of the type as a fragment. A concrete admitted world whose
valuation sends the level parameter to `none` inhabits it.

No universe instance, Pi closure, or recursive tower is claimed here; those
need source-realized universe carriers. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.OptionSoundInterface

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open RCodeSoundInterface (World Source Neutral)
open OptionSoundUniverse

universe u v

abbrev Member {k : Option Nat} (C : OCode.{u} k) :=
  {x : C.Element // C.kernel.relation x x}

def Related {k : Option Nat} {C : OCode.{u} k} (x y : Member C) : Prop :=
  C.kernel.relation x.val y.val

theorem related_refl {k : Option Nat} {C : OCode.{u} k} (x : Member C) : Related x x :=
  x.property

theorem related_symm {k : Option Nat} {C : OCode.{u} k} {x y : Member C}
    (h : Related x y) : Related y x := C.kernel.lawful.symm h

theorem related_trans {k : Option Nat} {C : OCode.{u} k} {x y z : Member C}
    (h : Related x y) (g : Related y z) : Related x z := C.kernel.lawful.trans h g

/-- `RCodeSound` with an Option-indexed code. -/
structure RCodeSoundO (W : World) (k : Option Nat) where
  code : OCode.{u} k
  sourceType : ExprA
  sourceLevel : Level
  typeTyped : HasTyA W.env W.iota W.levelCount W.context sourceType (.sort sourceLevel)
  level : eval W.valuation sourceLevel = k
  typeImage : ValueEq (W.evaluate sourceType) code.kernel.value
  Fragment : Type v
  source : Fragment → Source W sourceType
  evalSem : Fragment → Member code
  erasure : ∀ s, ValueEq (code.kernel.erase (evalSem s).val) (W.evaluate (source s).term)
  source_coherence : ∀ s t, (source s).term = (source t).term →
    Related (evalSem s) (evalSem t)
  realization : ∀ x : Member code, ∃ s : Fragment, Related x (evalSem s)
  reflect : Neutral W sourceType → Member code
  reflection_source : ∀ n : Neutral W sourceType,
    ∃ s : Fragment, Related (reflect n) (evalSem s) ∧
      Nonempty (ConvA W.env W.iota W.levelCount W.context
        (source s).term n.term sourceType)

abbrev RCodeSoundO.Element {W : World} {k : Option Nat}
    (C : RCodeSoundO.{u,v} W k) := Member C.code

def RCodeSoundO.ReadsBack {W : World} {k : Option Nat}
    (C : RCodeSoundO.{u,v} W k) (s : C.Fragment) (x : C.Element)
    (t : Source W C.sourceType) : Prop :=
  Related x (C.evalSem s) ∧
    Nonempty (ConvA W.env W.iota W.levelCount W.context
      (C.source s).term t.term C.sourceType)

theorem RCodeSoundO.readback_total {W : World} {k : Option Nat}
    (C : RCodeSoundO.{u,v} W k) (s : C.Fragment) :
    C.ReadsBack s (C.evalSem s) (C.source s) :=
  ⟨related_refl _, ⟨.refl W.context (C.source s).term C.sourceType (C.source s).typed⟩⟩

theorem RCodeSoundO.member_readback {W : World} {k : Option Nat}
    (C : RCodeSoundO.{u,v} W k) (x : C.Element) :
    ∃ s : C.Fragment, C.ReadsBack s x (C.source s) := by
  obtain ⟨s, hs⟩ := C.realization x
  exact ⟨s, hs, (C.readback_total s).2⟩

theorem RCodeSoundO.reflected_readback {W : World} {k : Option Nat}
    (C : RCodeSoundO.{u,v} W k) (n : Neutral W C.sourceType) :
    ∃ s : C.Fragment, C.ReadsBack s (C.reflect n) n.toSource :=
  C.reflection_source n

/-! ## Equivalence with the Nat-indexed interface at finite levels -/

/-- Every existing Nat-indexed instance, unchanged. -/
def ofNat {W : World} {k : Nat} (C : RCodeSoundInterface.RCodeSound.{u,v} W k) :
    RCodeSoundO.{u,v} W (some k) where
  code := .finite C.code
  sourceType := C.sourceType
  sourceLevel := C.sourceLevel
  typeTyped := C.typeTyped
  level := C.level
  typeImage := C.typeImage
  Fragment := C.Fragment
  source := C.source
  evalSem := C.evalSem
  erasure := C.erasure
  source_coherence := C.source_coherence
  realization := C.realization
  reflect := C.reflect
  reflection_source := C.reflection_source

/-- Every finite-level Option instance is a Nat-indexed instance. -/
def toNat {W : World} {k : Nat} : RCodeSoundO.{u,v} W (some k) →
    RCodeSoundInterface.RCodeSound.{u,v} W k
  | ⟨.finite D, sT, sL, tT, lv, tI, Fr, src, ev, er, sc, re, rf, rs⟩ =>
      ⟨D, sT, sL, tT, lv, tI, Fr, src, ev, er, sc, re, rf, rs⟩

theorem toNat_ofNat {W : World} {k : Nat} (C : RCodeSoundInterface.RCodeSound.{u,v} W k) :
    toNat (ofNat C) = C := rfl

theorem ofNat_toNat {W : World} {k : Nat} (C : RCodeSoundO.{u,v} W (some k)) :
    ofNat (toNat C) = C := by
  rcases C with ⟨code, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  cases code
  rfl

/-- Readback is the same proposition through the embedding. -/
theorem ofNat_readsBack_iff {W : World} {k : Nat}
    (C : RCodeSoundInterface.RCodeSound.{u,v} W k) (s : C.Fragment) (x : C.Element)
    (t : Source W C.sourceType) :
    (ofNat C).ReadsBack s x t ↔ C.ReadsBack s x t := Iff.rfl

/-! ## Chaotic instances at the none level -/

/-- One actual typed source point of a level-none type with an ordinary
image gives a Sound instance. Fragments are all typed sources of the type;
the evaluator is the actual source evaluator with exact erasure. -/
def chaotic (W : World) (V : NoneOrdinary) (A : ExprA) (l : Level)
    (hA : HasTyA W.env W.iota W.levelCount W.context A (.sort l))
    (hl : eval W.valuation l = none)
    (hImage : ValueEq (W.evaluate A) V.value) (s₀ : Source W A) :
    RCodeSoundO.{u,0} W none where
  code := .noneOrdinary V
  sourceType := A
  sourceLevel := l
  typeTyped := hA
  level := hl
  typeImage := hImage
  Fragment := Source W A
  source := id
  evalSem := fun s => ⟨⟨W.evaluate s.term⟩, True.intro⟩
  erasure := fun _ => ValueEq.refl _
  source_coherence := fun _ _ _ => True.intro
  realization := fun _ => ⟨s₀, True.intro⟩
  reflect := fun n => ⟨⟨n.value⟩, True.intro⟩
  reflection_source := fun n => ⟨n.toSource, True.intro,
    ⟨.refl W.context n.term A n.typed⟩⟩

/-- Reflection in a chaotic fibre keeps the exact raw neutral image. -/
theorem chaotic_reflect_image (W : World) (V : NoneOrdinary) (A : ExprA) (l : Level)
    (hA : HasTyA W.env W.iota W.levelCount W.context A (.sort l))
    (hl : eval W.valuation l = none)
    (hImage : ValueEq (W.evaluate A) V.value) (s₀ : Source W A)
    (n : Neutral W A) :
    ValueEq ((chaotic W V A l hA hl hImage s₀).code.kernel.erase
      ((chaotic W V A l hA hl hImage s₀).reflect n).val) n.value := ValueEq.refl _

/-! ### A concrete admitted world: `A : Sort u, p : A` with `u ↦ none` -/

abbrev noneTypeContext : LCtxA := [.assumption (.sort (.param 0))]

def noneTypeContextWf : CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 noneTypeContext :=
  .assumption .nil (.sort [] (.param 0))

def nonePointTypeTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 noneTypeContext (.bvar 0) (.sort (.param 0)) :=
  .bvar noneTypeContext 0 (.sort (.param 0)) (.succ (.param 0)) rfl
    (.sort noneTypeContext (.param 0))

abbrev noneContext : LCtxA := [.assumption (.bvar 0), .assumption (.sort (.param 0))]

def noneContextWf : CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 noneContext :=
  .assumption noneTypeContextWf nonePointTypeTyped

abbrev noneType : ExprA := .bvar 1

def noneTypeTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 noneContext noneType (.sort (.param 0)) :=
  .bvar noneContext 1 (.sort (.param 0)) (.succ (.param 0)) rfl
    (.sort noneContext (.param 0))

def nonePointTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 noneContext (.bvar 0) noneType :=
  .bvar noneContext 0 noneType (.param 0) rfl noneTypeTyped

def noneRawEnvironment (name : Nat) : EnvI :=
  EnvI.cons (NeutralPER.neutralAtom 0)
    (EnvI.cons (NoneOrdinary.named name).value EnvI.bot)

def noneWorld (F : EnvironmentEval.FamilySyntax) (name : Nat) : World where
  env := emptyEnvA
  iota := iotaIfaceA emptyEnvA
  levelCount := 1
  context := noneContext
  family := F
  valuation := UniverseDecoderBoundary.noneValuation
  rawEnvironment := noneRawEnvironment name
  envWf := .empty
  contextWf := noneContextWf

theorem noneWorld_type_image (F : EnvironmentEval.FamilySyntax) (name : Nat) :
    ValueEq ((noneWorld F name).evaluate noneType) (NoneOrdinary.named name).value :=
  RCodeProofReadback.environment_variable_image emptyEnvA F _
    (noneRawEnvironment name) 1 (NativeMemberValues.value_bot none name)

def nonePoint (F : EnvironmentEval.FamilySyntax) (name : Nat) :
    Source (noneWorld F name) noneType :=
  ⟨.bvar 0, nonePointTyped⟩

/-- A constructed none-level Sound instance in an admitted world. -/
def noneInstance (F : EnvironmentEval.FamilySyntax) (name : Nat) :
    RCodeSoundO.{u,0} (noneWorld F name) none :=
  chaotic (noneWorld F name) (NoneOrdinary.named name) noneType (.param 0)
    noneTypeTyped rfl (noneWorld_type_image F name) (nonePoint F name)

theorem noneInstance_level (F : EnvironmentEval.FamilySyntax) (name : Nat) :
    eval (noneWorld F name).valuation (noneInstance.{u} F name).sourceLevel = none := rfl

/-- The none instance's admission, source point and readback, all constructed. -/
theorem noneInstance_packet (F : EnvironmentEval.FamilySyntax) (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 noneContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 noneContext noneType (.sort (.param 0))) ∧
    eval UniverseDecoderBoundary.noneValuation (.param 0) = none ∧
    (∀ x : (noneInstance.{u} F name).Element,
      ∃ s, (noneInstance.{u} F name).ReadsBack s x ((noneInstance.{u} F name).source s)) :=
  ⟨⟨.empty⟩, ⟨noneContextWf⟩, ⟨noneTypeTyped⟩, rfl,
    fun x => (noneInstance F name).member_readback x⟩

end Rcic.Declarative.Ann.LR3.OptionSoundInterface
