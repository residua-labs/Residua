import rcic.RcicAnnLR3RCodeInterface
import rcic.RcicAnnLR3GuardedPropControl

/-!
# Constructed level-zero instances of the common RCode specification

For any actual certified Code 0 whose type image contains bottom and
whose kernel has an exact neutral reflector, the same admitted source
context `A : Prop, p : A, q : A` supplies a full instance of the common
RCode record. Its retained type binding is fixed to that code, its two
proof bindings are reflected atoms, and its raw environment is fixed
before any member is realized. Literal variable evaluation supplies the
erasure laws. Level-zero irrelevance supplies sound proof readback and
one fixed source representative for every member.

The NF decoder is the newest normal proof variable, bvar 0. The source conversion law is
the actual source proof-irrelevance constructor, so it applies to every
well-typed neutral input and does not preserve irrelevant proof names.
Concrete instances below supply all hypotheses for proposition codes,
native neutral codes at level zero, and the existing guarded proposition
control for every guard, without deciding it.

This closes these level-zero instances, including a guarded instance.
It does not construct the universe or positive dependent-Pi generators,
nor a whole-language evaluator or semantic context theorem.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeZeroInstances

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER GuardedTaggedCode RCodeInterface

universe u

/-- The retained type-variable binding is supplied once, not recovered
from its raw image and not chosen separately for each realized member. -/
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

/-- Retained variable lookup supplies an actual semantic member. -/
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

/-- This construction uses only an existing code, bottom in its actual
type image, and the existing data-producing neutral reflector. None of
its inputs is an assumed reifier, source realization, or closure theorem. -/
def build (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (hbot : C.view.value .bot)
    (r : GuardedKernel.Reflector C.kernel) :
    RCode.{u,0,0} (world F ν C) 0 RCodeProofReadback.ProofNF where
  code := C
  sourceType := RCodeProofReadback.proofType
  sourceLevel := .zero
  typeTyped := RCodeProofReadback.proofTypeTyped
  level := rfl
  typeImage := type_image F ν C hbot
  normalEq := inferInstance
  decodeNF := fun _ =>
    ⟨RCodeProofReadback.proofSource .newest, RCodeProofReadback.proofSourceTyped .newest⟩
  decodeNF_normal := fun _ => .bvar rfl
  evalNF := fun _ => evaluateProof C r .newest
  evalNF_image := fun _ => evaluateProof_image F ν C r .newest
  reflect := fun n => ⟨r.reflect n.value n.neutral, r.member n.value n.neutral⟩
  readNeutral := fun _ => .proof
  neutral_conversion := fun n =>
    .irr RCodeProofReadback.proofContext RCodeProofReadback.proofType n.term
      (RCodeProofReadback.proofSource .newest) RCodeProofReadback.proofTypeTyped
      n.typed (RCodeProofReadback.proofSourceTyped .newest)
  reify := fun _ => .proof
  reify_respect := fun _ _ _ => rfl
  reify_sound := fun x => C.view.irrelevant rfl _ _ x.property
    (evaluateProof C r .newest).property
  roundtrip := fun _ => rfl
  Fragment := RCodeProofReadback.ProofVariable
  source := fun v =>
    ⟨RCodeProofReadback.proofSource v, RCodeProofReadback.proofSourceTyped v⟩
  evalSem := evaluateProof C r
  erasure := evaluateProof_image F ν C r
  representative := fun x => ⟨.newest,
    C.view.irrelevant rfl _ _ x.property (evaluateProof C r .newest).property⟩

theorem build_closed (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (hbot : C.view.value .bot)
    (r : GuardedKernel.Reflector C.kernel) :
    Nonempty (RCode.{u,0,0} (world F ν C) 0 RCodeProofReadback.ProofNF) :=
  ⟨build F ν C hbot r⟩

/-- These instances satisfy the stronger exact raw reflection property;
the common RCode interface uses a source-conversion-backed law so that
later Pi eta reflection need not satisfy raw identity. -/
theorem build_reflect_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (C : Code.{u} 0) (hbot : C.view.value .bot)
    (r : GuardedKernel.Reflector C.kernel)
    (n : Neutral (world F ν C) RCodeProofReadback.proofType) :
    ValueEq ((build F ν C hbot r).erase ((build F ν C hbot r).reflect n)) n.value :=
  r.image n.value n.neutral

def proposition (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (P : Prop) :
    RCode.{0,0,0} (world F ν (Code.legacy (GuardDecision.propCode P))) 0
      RCodeProofReadback.ProofNF :=
  build F ν (Code.legacy (GuardDecision.propCode P)) (Or.inl rfl)
    (GuardedKernel.propositionReflector.{0} (GuardDecision.propElement P))

def neutral (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    RCode.{0,0,0}
      (world F ν (Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 0 name))) 0
      RCodeProofReadback.ProofNF :=
  build F ν (Code.legacy (TaggedSaturatedTower.Code.neutral.{0} 0 name))
    (NativeMemberValues.value_bot (some 0) name)
    (GuardedKernel.nativeNeutralReflector.{0} 0 name)

/-- Exact branch reflectors construct the guarded level-zero instance.
Its source world binds A to the resulting guarded code before any member
is quoted or realized. The guard is not decided. -/
def guarded (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (G : Prop) (M N : Code.{u} 0) (I : GuardedKernel.TypeImage G M.kernel N.kernel)
    (hbot : I.value .bot)
    (rM : GuardedKernel.Reflector M.kernel) (rN : GuardedKernel.Reflector N.kernel) :
    RCode.{u,0,0} (world F ν (Code.guarded G M N I)) 0 RCodeProofReadback.ProofNF :=
  build F ν (Code.guarded G M N I) hbot (GuardedKernel.reflector I rM rN)

def guardedControl (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (G : Prop) :
    RCode.{0,0,0} (world F ν (GuardedPropControl.control G)) 0
      RCodeProofReadback.ProofNF :=
  guarded F ν G GuardedPropControl.trueBranch GuardedPropControl.falseBranch
    (GuardedPropControl.typeImage G) (Or.inl rfl)
    GuardedPropControl.trueReflector GuardedPropControl.falseReflector

theorem guardedControl_closed (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (G : Prop) :
    Nonempty (RCode.{0,0,0} (world F ν (GuardedPropControl.control G)) 0
      RCodeProofReadback.ProofNF) :=
  ⟨guardedControl F ν G⟩

/-- The actual guarded instance supplies the normal source decoder,
reification soundness, and its concrete retained variable evaluator. -/
theorem guardedControl_member_realized (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (G : Prop) (x : (guardedControl F ν G).Element) :
    Related x ((guardedControl F ν G).evalNF ((guardedControl F ν G).reify x)) ∧
    Normal emptyEnvA (iotaIfaceA emptyEnvA) RCodeProofReadback.proofContext
      (((guardedControl F ν G).decodeNF ((guardedControl F ν G).reify x)).term) ∧
    ValueEq
      ((guardedControl F ν G).erase
        ((guardedControl F ν G).evalNF ((guardedControl F ν G).reify x)))
      ((world F ν (GuardedPropControl.control G)).evaluate
        (((guardedControl F ν G).decodeNF ((guardedControl F ν G).reify x)).term)) :=
  ⟨(guardedControl F ν G).reify_sound x,
    (guardedControl F ν G).decodeNF_normal _,
    (guardedControl F ν G).evalNF_image _⟩

end Rcic.Declarative.Ann.LR3.RCodeZeroInstances
