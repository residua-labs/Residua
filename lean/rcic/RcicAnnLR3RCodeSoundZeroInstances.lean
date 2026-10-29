import rcic.RcicAnnLR3RCodeSoundInterface
import rcic.RcicAnnLR3RCodeProofReadback
import rcic.RcicAnnLR3GuardedPropControl

/-!
# Direct soundness-layer constructions at level zero

An existing certified Code 0, an exact neutral reflector, and one actual
typed source evaluation suffice to construct RCodeSound in any fixed
admitted world. The fragment contains that source and every source-typed
neutral input. Its erasure equations use the supplied actual evaluation
and the reflector image law. Level-zero irrelevance proves coherence and
realizes every member by the one supplied source. Reflection readback is
source reflexivity; arbitrary well-typed proof readback additionally uses
the actual source irrelevance constructor. No decidable reifier or older
RCode record is used.

The fixed context A : Prop, p : A, q : A supplies the required point by
literal variable evaluation. Concrete instances then cover proposition
codes, native neutral codes at zero, and the existing guarded proposition
control for every guard. The guard is not decided. The generic guarded
builder still requires its displayed common type image and branch
reflectors; guardedControl supplies all of them.

These zero instances also satisfy exact raw reflection. That stronger
property is proved here, rather than imposed on Sound at Pi/universe
types. Neither general dependent-Pi/universe closure nor a whole-language
retained evaluator is claimed. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeSoundZeroInstances

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER GuardedTaggedCode RCodeSoundInterface

universe u

/-- The source basepoint is supplied once; it is not selected separately
for each semantic member. Neutral inputs retain their source derivations. -/
inductive PointFragment (W : World) (A : ExprA) : Type where
  | basepoint
  | neutral (n : Neutral W A)

def pointSource {W : World} {A : ExprA} (s₀ : Source W A) :
    PointFragment W A → Source W A
  | .basepoint => s₀
  | .neutral n => n.toSource

def pointEvaluation {W : World} {A : ExprA} (C : Code.{u} 0)
    (r : GuardedKernel.Reflector C.kernel) (m₀ : Member C) :
    PointFragment W A → Member C
  | .basepoint => m₀
  | .neutral n => ⟨r.reflect n.value n.neutral, r.member n.value n.neutral⟩

theorem pointEvaluation_image {W : World} {A : ExprA} (C : Code.{u} 0)
    (r : GuardedKernel.Reflector C.kernel) (s₀ : Source W A) (m₀ : Member C)
    (hm₀ : ValueEq (C.erase m₀.val) (W.evaluate s₀.term))
    (s : PointFragment W A) :
    ValueEq (C.erase (pointEvaluation C r m₀ s).val)
      (W.evaluate (pointSource s₀ s).term) := by
  cases s with
  | basepoint => exact hm₀
  | neutral n => exact (r.image n.value n.neutral).trans n.image.symm

/-- A direct construction from one actual retained source evaluation.
The hypotheses do not assume readback, source realization, or any code
generator closure. Exact reflection is sufficient at zero and is not a
requirement of the common interface. -/
def ofPoint (W : World) (C : Code.{u} 0) (A : ExprA)
    (hA : HasTyA W.env W.iota W.levelCount W.context A (.sort .zero))
    (hImage : ValueEq (W.evaluate A) C.view.value)
    (r : GuardedKernel.Reflector C.kernel) (s₀ : Source W A)
    (m₀ : Member C) (hm₀ : ValueEq (C.erase m₀.val) (W.evaluate s₀.term)) :
    RCodeSound.{u,0} W 0 where
  code := C
  sourceType := A
  sourceLevel := .zero
  typeTyped := hA
  level := rfl
  typeImage := hImage
  Fragment := PointFragment W A
  source := pointSource s₀
  evalSem := pointEvaluation C r m₀
  erasure := pointEvaluation_image C r s₀ m₀ hm₀
  source_coherence := fun s t _ => C.view.irrelevant rfl _ _
    (pointEvaluation C r m₀ s).property (pointEvaluation C r m₀ t).property
  realization := fun x => ⟨.basepoint, C.view.irrelevant rfl _ _ x.property m₀.property⟩
  reflect := fun n => ⟨r.reflect n.value n.neutral, r.member n.value n.neutral⟩
  reflection_source := fun n => ⟨.neutral n, r.member n.value n.neutral,
    ⟨.refl W.context n.term A n.typed⟩⟩

/-- The stronger exact-reflection certificate is local to this builder.
It is not transported into Sound as a global requirement. -/
theorem ofPoint_reflect_image (W : World) (C : Code.{u} 0) (A : ExprA)
    (hA : HasTyA W.env W.iota W.levelCount W.context A (.sort .zero))
    (hImage : ValueEq (W.evaluate A) C.view.value)
    (r : GuardedKernel.Reflector C.kernel) (s₀ : Source W A)
    (m₀ : Member C) (hm₀ : ValueEq (C.erase m₀.val) (W.evaluate s₀.term))
    (n : Neutral W A) :
    ValueEq ((ofPoint W C A hA hImage r s₀ m₀ hm₀).erase
      ((ofPoint W C A hA hImage r s₀ m₀ hm₀).reflect n)) n.value :=
  r.image n.value n.neutral

/-- At a proposition, any actual typed proof source is an admissible
readback target. This derives a source ConvA witness by its irrelevance
constructor, without choosing a normal representative or deciding a PER. -/
theorem ofPoint_proof_readback (W : World) (C : Code.{u} 0) (A : ExprA)
    (hA : HasTyA W.env W.iota W.levelCount W.context A (.sort .zero))
    (hImage : ValueEq (W.evaluate A) C.view.value)
    (r : GuardedKernel.Reflector C.kernel) (s₀ : Source W A)
    (m₀ : Member C) (hm₀ : ValueEq (C.erase m₀.val) (W.evaluate s₀.term))
    (s : PointFragment W A) (x : Member C) (t : Source W A) :
    (ofPoint W C A hA hImage r s₀ m₀ hm₀).ReadsBack s x t :=
  ⟨C.view.irrelevant rfl _ _ x.property (pointEvaluation C r m₀ s).property,
    ⟨.irr W.context A (pointSource s₀ s).term t.term hA
      (pointSource s₀ s).typed t.typed⟩⟩

/-- The retained type binding is fixed by the interpretation, separately
from its raw environment. The latter alone does not identify the code. -/
def retainedBinding (C : Code.{u} 0) : Nat → Option (Code.{u} 0)
  | 2 => some C
  | _ => none

theorem retainedBinding_type (C : Code.{u} 0) : retainedBinding C 2 = some C := rfl

def rawEnvironment (C : Code.{u} 0) : EnvI :=
  EnvI.cons (NeutralPER.neutralAtom 0)
    (EnvI.cons (NeutralPER.neutralAtom 1)
      (EnvI.cons C.view.value EnvI.bot))

def world (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (C : Code.{u} 0) : World where
  env := emptyEnvA
  iota := iotaIfaceA emptyEnvA
  levelCount := 0
  context := RCodeProofReadback.proofContext
  family := F
  valuation := ν
  rawEnvironment := rawEnvironment C
  envWf := .empty
  contextWf := RCodeProofReadback.proofContextWf

theorem type_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (hbot : C.view.value .bot) :
    ValueEq ((world F ν C).evaluate RCodeProofReadback.proofType) C.view.value :=
  RCodeProofReadback.environment_variable_image emptyEnvA F ν
    (rawEnvironment C) 2 hbot

theorem raw_proof_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (v : RCodeProofReadback.ProofVariable) :
    ValueEq ((world F ν C).evaluate (RCodeProofReadback.proofSource v))
      (NeutralPER.neutralAtom (RCodeProofReadback.proofIndex v)) := by
  cases v with
  | newest =>
      exact RCodeProofReadback.environment_variable_image emptyEnvA F ν
        (rawEnvironment C) 0 (ApproxI.bot EnvI.bot (.const 0 []))
  | older =>
      exact RCodeProofReadback.environment_variable_image emptyEnvA F ν
        (rawEnvironment C) 1 (ApproxI.bot EnvI.bot (.const 1 []))

def proofNeutral (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (v : RCodeProofReadback.ProofVariable) :
    Neutral (world F ν C) RCodeProofReadback.proofType where
  term := RCodeProofReadback.proofSource v
  typed := RCodeProofReadback.proofSourceTyped v
  value := NeutralPER.neutralAtom (RCodeProofReadback.proofIndex v)
  image := raw_proof_image F ν C v
  neutral := .atom (RCodeProofReadback.proofIndex v)

def evaluateProof (C : Code.{u} 0) (r : GuardedKernel.Reflector C.kernel)
    (v : RCodeProofReadback.ProofVariable) : Member C :=
  ⟨r.reflect (NeutralPER.neutralAtom (RCodeProofReadback.proofIndex v))
      (.atom (RCodeProofReadback.proofIndex v)),
    r.member (NeutralPER.neutralAtom (RCodeProofReadback.proofIndex v))
      (.atom (RCodeProofReadback.proofIndex v))⟩

theorem evaluateProof_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (r : GuardedKernel.Reflector C.kernel)
    (v : RCodeProofReadback.ProofVariable) :
    ValueEq (C.erase (evaluateProof C r v).val)
      ((world F ν C).evaluate (RCodeProofReadback.proofSource v)) :=
  (r.image (NeutralPER.neutralAtom (RCodeProofReadback.proofIndex v))
    (.atom (RCodeProofReadback.proofIndex v))).trans (raw_proof_image F ν C v).symm

/-- The actual newest variable, q in A,p,q order, supplies the basepoint.
The same fixed world is used for every member realized by this instance. -/
def build (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (hbot : C.view.value .bot)
    (r : GuardedKernel.Reflector C.kernel) : RCodeSound.{u,0} (world F ν C) 0 :=
  ofPoint (world F ν C) C RCodeProofReadback.proofType
    RCodeProofReadback.proofTypeTyped (type_image F ν C hbot) r
    ⟨RCodeProofReadback.proofSource .newest, RCodeProofReadback.proofSourceTyped .newest⟩
    (evaluateProof C r .newest) (evaluateProof_image F ν C r .newest)

theorem build_closed (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (hbot : C.view.value .bot)
    (r : GuardedKernel.Reflector C.kernel) :
    Nonempty (RCodeSound.{u,0} (world F ν C) 0) :=
  ⟨build F ν C hbot r⟩

theorem build_reflect_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (hbot : C.view.value .bot)
    (r : GuardedKernel.Reflector C.kernel)
    (n : Neutral (world F ν C) RCodeProofReadback.proofType) :
    ValueEq ((build F ν C hbot r).erase ((build F ν C hbot r).reflect n)) n.value :=
  r.image n.value n.neutral

def proposition (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (P : Prop) :
    RCodeSound.{0,0} (world F ν (Code.legacy (GuardDecision.propCode P))) 0 :=
  build F ν (Code.legacy (GuardDecision.propCode P)) (Or.inl rfl)
    (GuardedKernel.propositionReflector.{0} (GuardDecision.propElement P))

def neutral (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    RCodeSound.{0,0}
      (world F ν (Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 0 name))) 0 :=
  build F ν (Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 0 name))
    (NativeMemberValues.value_bot (some 0) name)
    (GuardedKernel.nativeNeutralReflector.{0} 0 name)

def guarded (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (G : Prop) (M N : Code.{u} 0) (I : GuardedKernel.TypeImage G M.kernel N.kernel)
    (hbot : I.value .bot)
    (rM : GuardedKernel.Reflector M.kernel) (rN : GuardedKernel.Reflector N.kernel) :
    RCodeSound.{u,0} (world F ν (Code.guarded G M N I)) 0 :=
  build F ν (Code.guarded G M N I) hbot (GuardedKernel.reflector I rM rN)

/-- Every guard has this constructed zero-level instance. All type-image,
reflector and source-point premises are supplied here without a decision. -/
def guardedControl (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (G : Prop) :
    RCodeSound.{0,0} (world F ν (GuardedPropControl.control G)) 0 :=
  guarded F ν G GuardedPropControl.trueBranch GuardedPropControl.falseBranch
    (GuardedPropControl.typeImage G) (Or.inl rfl)
    GuardedPropControl.trueReflector GuardedPropControl.falseReflector

theorem guardedControl_closed (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (G : Prop) :
    Nonempty (RCodeSound.{0,0} (world F ν (GuardedPropControl.control G)) 0) :=
  ⟨guardedControl F ν G⟩

/-- Nonempty source-indexed readback for every actual guarded member,
with exact erasure of the chosen evaluator output. No syntax chooser is
extracted from the propositional realization. -/
theorem guardedControl_member_realized (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (G : Prop) (x : (guardedControl F ν G).Element) :
    ∃ s : (guardedControl F ν G).Fragment,
      (guardedControl F ν G).ReadsBack s x ((guardedControl F ν G).source s) ∧
      ValueEq ((guardedControl F ν G).erase ((guardedControl F ν G).evalSem s))
        ((world F ν (GuardedPropControl.control G)).evaluate
          ((guardedControl F ν G).source s).term) := by
  obtain ⟨s, hs⟩ := (guardedControl F ν G).member_readback x
  exact ⟨s, hs, (guardedControl F ν G).erasure s⟩

end Rcic.Declarative.Ann.LR3.RCodeSoundZeroInstances
