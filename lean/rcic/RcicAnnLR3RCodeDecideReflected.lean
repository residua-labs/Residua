import rcic.RcicAnnLR3RCodeSoundZeroInstances
import rcic.RcicAnnLR3RCodeInterface

/-!
# An optional decision instance in an explicitly reflected proof world

This module depends on Sound; Sound does not depend on this module.
The only reused item from the older decision-interface module is its
source Normal predicate. No older RCode instance or decision API is used.

The public RCodeDecide entry is restricted to the admitted context
A : Prop, p : A, q : A. Its retained A binding is required to be exactly
legacy (Code.neutral 0 name). Its two proof bindings are actual reflected
atoms, and its raw environment is the already constructed SoundZero
environment. The three active slots are checked separately; no assertion
is made about unused variables in the EnvI.bot tail. The A binding also
agrees with the actual reflection point of the inherited universe.

Unit is the finite proof-erased normal-form format. Its decoder is the
newest actual typed proof variable, which satisfies Normal. Retained
evaluation, source conversion, faithful quotation and a PER decision are
constructed below. They decide the proof PER in this fixed zero-level
world, not code conversion in a universe.

Constructor tags prove that the retained A slot cannot be assigned an
arbitrary propCode P. This is a concrete retained-binding restriction,
not a consequence of raw neutrality. It neither proves the absence of
every future universe IndexEmbedding nor constructs a general Kripke,
Pi, or universe decision procedure. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeDecideReflected

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER GuardedTaggedCode RCodeSoundInterface

def reflectedCode (name : Nat) : Code.{0} 0 :=
  Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 0 name)

/-- The retained assignment is explicit data with a checked restriction.
The canonical raw/source world below is tied to it by retained_type. -/
structure ReflectedProofWorld where
  family : EnvironmentEval.FamilySyntax
  valuation : Valuation
  name : Nat
  retainedType : Code.{0} 0
  retained_type : retainedType = reflectedCode name

def ReflectedProofWorld.standard (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (name : Nat) : ReflectedProofWorld :=
  ⟨F, ν, name, reflectedCode name, rfl⟩

def ReflectedProofWorld.world (W : ReflectedProofWorld) : World :=
  RCodeSoundZeroInstances.world W.family W.valuation (reflectedCode W.name)

def ReflectedProofWorld.sound (W : ReflectedProofWorld) :
    RCodeSound.{0,0} W.world 0 :=
  RCodeSoundZeroInstances.neutral W.family W.valuation W.name

def ReflectedProofWorld.retainedBinding (W : ReflectedProofWorld) :
    Nat → Option (Code.{0} 0) :=
  RCodeSoundZeroInstances.retainedBinding W.retainedType

theorem ReflectedProofWorld.sound_code_retained (W : ReflectedProofWorld) :
    W.sound.code = W.retainedType := W.retained_type.symm

theorem ReflectedProofWorld.retained_type_slot (W : ReflectedProofWorld) :
    W.retainedBinding 2 = some (reflectedCode W.name) := by
  change some W.retainedType = some (reflectedCode W.name)
  exact congrArg some W.retained_type

theorem ReflectedProofWorld.raw_environment_retained (W : ReflectedProofWorld) :
    W.world.rawEnvironment = RCodeSoundZeroInstances.rawEnvironment W.retainedType := by
  rw [W.retained_type]
  rfl

/-- The active newest proof slot is q in the displayed A,p,q context. -/
theorem ReflectedProofWorld.raw_q (W : ReflectedProofWorld) :
    W.world.rawEnvironment 0 = NeutralPER.neutralAtom 0 := rfl

theorem ReflectedProofWorld.raw_p (W : ReflectedProofWorld) :
    W.world.rawEnvironment 1 = NeutralPER.neutralAtom 1 := rfl

theorem ReflectedProofWorld.raw_A (W : ReflectedProofWorld) :
    W.world.rawEnvironment 2 = NativeMemberValues.value (some 0) W.name := rfl

theorem ReflectedProofWorld.raw_A_retained (W : ReflectedProofWorld) :
    W.world.rawEnvironment 2 = W.retainedType.view.value := by
  rw [W.retained_type]
  rfl

/-- The restricted code is the inherited universe's actual reflection,
not an arbitrary code with a conveniently neutral raw image. -/
theorem ReflectedProofWorld.retained_from_universe_reflection (W : ReflectedProofWorld) :
    W.retainedType = Code.legacy
      ((TaggedSaturatedTower.universeCode.{0} 0).view.point W.name) := by
  calc
    W.retainedType = reflectedCode W.name := W.retained_type
    _ = Code.legacy ((TaggedSaturatedTower.universeCode.{0} 0).view.point W.name) :=
      congrArg Code.legacy (TaggedSaturatedTower.universe_reflection 0 W.name).symm

theorem ReflectedProofWorld.raw_type_reflection_image (W : ReflectedProofWorld) :
    ValueEq (W.world.rawEnvironment 2)
      ((TaggedSaturatedTower.universeCode.{0} 0).erase
        ((TaggedSaturatedTower.universeCode.{0} 0).view.point W.name)) := by
  rw [TaggedSaturatedTower.universe_reflection_erasure]
  exact ValueEq.refl _

theorem ReflectedProofWorld.type_evaluation (W : ReflectedProofWorld) :
    ValueEq (W.world.evaluate RCodeProofReadback.proofType) W.retainedType.view.value := by
  rw [W.retained_type]
  exact W.sound.typeImage

/-- Both proof bindings are retained members from actual source-variable
evaluation, not untyped raw values inserted into the environment. -/
def ReflectedProofWorld.proofBinding (W : ReflectedProofWorld)
    (v : RCodeProofReadback.ProofVariable) : W.sound.Element :=
  W.sound.evalSem (.neutral (RCodeSoundZeroInstances.proofNeutral
    W.family W.valuation (reflectedCode W.name) v))

theorem ReflectedProofWorld.proofBinding_image (W : ReflectedProofWorld)
    (v : RCodeProofReadback.ProofVariable) :
    ValueEq (W.sound.erase (W.proofBinding v))
      (NeutralPER.neutralAtom (RCodeProofReadback.proofIndex v)) :=
  (W.sound.erasure (.neutral (RCodeSoundZeroInstances.proofNeutral
    W.family W.valuation (reflectedCode W.name) v))).trans
      (RCodeSoundZeroInstances.raw_proof_image W.family W.valuation
        (reflectedCode W.name) v)

theorem ReflectedProofWorld.q_evaluation (W : ReflectedProofWorld) :
    ValueEq (W.world.evaluate (RCodeProofReadback.proofSource .newest))
      (NeutralPER.neutralAtom 0) :=
  RCodeSoundZeroInstances.raw_proof_image W.family W.valuation
    (reflectedCode W.name) .newest

theorem ReflectedProofWorld.p_evaluation (W : ReflectedProofWorld) :
    ValueEq (W.world.evaluate (RCodeProofReadback.proofSource .older))
      (NeutralPER.neutralAtom 1) :=
  RCodeSoundZeroInstances.raw_proof_image W.family W.valuation
    (reflectedCode W.name) .older

/-- This uses retained constructor identity, not a claim about arbitrary
semantic embeddings or about conversion after discarding constructor tags. -/
theorem ReflectedProofWorld.retainedType_not_propCode (W : ReflectedProofWorld)
    (P : Prop) : W.retainedType ≠ Code.legacy (GuardDecision.propCode P) := by
  intro h
  have ht := congrArg (fun C : Code.{0} 0 => C.tag) h
  rw [W.retained_type] at ht
  change (Tag.legacy .neutral) = Tag.legacy .proposition at ht
  cases ht

theorem ReflectedProofWorld.no_propCode_assignment (W : ReflectedProofWorld)
    (P : Prop) :
    W.retainedBinding 2 ≠ some (Code.legacy (GuardDecision.propCode P)) := by
  intro h
  change some W.retainedType = some (Code.legacy (GuardDecision.propCode P)) at h
  exact W.retainedType_not_propCode P (Option.some.inj h)

/-- An optional discrete layer, accessible only with the explicit
ReflectedProofWorld admission above. Every normal form selects an actual
fragment; its evaluator and erasure therefore come from Sound itself. -/
structure RCodeDecide (W : ReflectedProofWorld) where
  normalEq : DecidableEq Unit
  normalSource : Unit → W.sound.Fragment
  normal : ∀ nf, RCodeInterface.Normal W.world.env W.world.iota W.world.context
    (W.sound.source (normalSource nf)).term
  quote : W.sound.Element → Unit
  quote_respect : ∀ x y, Related x y → quote x = quote y
  quote_sound : ∀ x, Related x (W.sound.evalSem (normalSource (quote x)))
  source_conversion : ∀ s : W.sound.Fragment,
    Nonempty (ConvA W.world.env W.world.iota W.world.levelCount W.world.context
      (W.sound.source s).term
      (W.sound.source (normalSource (quote (W.sound.evalSem s)))).term
      W.sound.sourceType)

def RCodeDecide.decodeNF {W : ReflectedProofWorld} (D : RCodeDecide W)
    (nf : Unit) : Source W.world W.sound.sourceType := W.sound.source (D.normalSource nf)

def RCodeDecide.evalNF {W : ReflectedProofWorld} (D : RCodeDecide W)
    (nf : Unit) : W.sound.Element := W.sound.evalSem (D.normalSource nf)

theorem RCodeDecide.evalNF_image {W : ReflectedProofWorld} (D : RCodeDecide W)
    (nf : Unit) :
    ValueEq (W.sound.erase (D.evalNF nf)) (W.world.evaluate (D.decodeNF nf).term) :=
  W.sound.erasure (D.normalSource nf)

theorem RCodeDecide.decodeNF_normal {W : ReflectedProofWorld} (D : RCodeDecide W)
    (nf : Unit) :
    RCodeInterface.Normal W.world.env W.world.iota W.world.context (D.decodeNF nf).term :=
  D.normal nf

theorem RCodeDecide.source_readback {W : ReflectedProofWorld} (D : RCodeDecide W)
    (s : W.sound.Fragment) :
    W.sound.ReadsBack s (W.sound.evalSem s) (D.decodeNF (D.quote (W.sound.evalSem s))) :=
  ⟨(W.sound.evalSem s).property, D.source_conversion s⟩

theorem RCodeDecide.member_readback {W : ReflectedProofWorld} (D : RCodeDecide W)
    (x : W.sound.Element) :
    W.sound.ReadsBack (D.normalSource (D.quote x)) x (D.decodeNF (D.quote x)) :=
  ⟨D.quote_sound x, ⟨.refl W.world.context (D.decodeNF (D.quote x)).term
    W.sound.sourceType (D.decodeNF (D.quote x)).typed⟩⟩

theorem RCodeDecide.reflected_readback {W : ReflectedProofWorld} (D : RCodeDecide W)
    (n : Neutral W.world W.sound.sourceType) :
    W.sound.ReadsBack (.neutral n) (W.sound.reflect n)
      (D.decodeNF (D.quote (W.sound.reflect n))) :=
  D.source_readback (.neutral n)

theorem RCodeDecide.neutral_source_sound {W : ReflectedProofWorld} (D : RCodeDecide W)
    (n : Neutral W.world W.sound.sourceType) :
    Nonempty (ConvA W.world.env W.world.iota W.world.levelCount W.world.context
      n.term (D.decodeNF (D.quote (W.sound.reflect n))).term W.sound.sourceType) :=
  (D.reflected_readback n).2

/-- Faithfulness concerns the fixed proof PER on self-members. It does
not compare proposition codes as elements of a positive universe. -/
theorem RCodeDecide.quote_eq_iff {W : ReflectedProofWorld} (D : RCodeDecide W)
    (x y : W.sound.Element) : D.quote x = D.quote y ↔ Related x y := by
  constructor
  · intro h
    have hx := D.quote_sound x
    rw [h] at hx
    exact related_trans hx (related_symm (D.quote_sound y))
  · exact D.quote_respect x y

def RCodeDecide.relationDecision {W : ReflectedProofWorld} (D : RCodeDecide W)
    (x y : W.sound.Element) : Decidable (Related x y) := by
  letI : DecidableEq Unit := D.normalEq
  exact if h : D.quote x = D.quote y then
    isTrue ((D.quote_eq_iff x y).mp h)
  else
    isFalse (fun hxy => h ((D.quote_eq_iff x y).mpr hxy))

/-- The actual bounded instance: one normal proof marker, newest source
variable, its retained evaluator, and source proof irrelevance. -/
def build (W : ReflectedProofWorld) : RCodeDecide W where
  normalEq := inferInstance
  normalSource := fun _ => .basepoint
  normal := fun _ => .bvar rfl
  quote := fun _ => ()
  quote_respect := fun _ _ _ => rfl
  quote_sound := fun x => W.sound.code.view.irrelevant rfl _ _ x.property
    (W.sound.evalSem .basepoint).property
  source_conversion := fun s =>
    ⟨.irr W.world.context W.sound.sourceType (W.sound.source s).term
      (W.sound.source .basepoint).term W.sound.typeTyped
      (W.sound.source s).typed (W.sound.source .basepoint).typed⟩

theorem build_decode_newest (W : ReflectedProofWorld) (nf : Unit) :
    ((build W).decodeNF nf).term = RCodeProofReadback.proofSource .newest := rfl

theorem build_newest_normal (W : ReflectedProofWorld) :
    RCodeInterface.Normal W.world.env W.world.iota W.world.context
      (RCodeProofReadback.proofSource .newest) :=
  (build W).decodeNF_normal ()

theorem restricted_decider_inhabited (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (name : Nat) :
    Nonempty (RCodeDecide (ReflectedProofWorld.standard F ν name)) :=
  ⟨build (ReflectedProofWorld.standard F ν name)⟩

end Rcic.Declarative.Ann.LR3.RCodeDecideReflected
