import rcic.RcicAnnLR3RCodeSoundZeroInstances
import rcic.RcicAnnLR3RCodeDependentPi

/-!
# Dependent actions over contextual sound fibres

In the general Family interface, the domain and every fibre use Sound.
Source-context and raw-environment extension precede body evaluation; the
retained fibre interpretations are supplied separately.
A uniform section supplies one actual source term across those extensions;
its source typing and exact application image are derived below. Neither
pointwise existential realization nor one local readback is used as a
choice function for such a section.

The inhabited dependent control equips the previous two non-convertible
proposition fibres with actual RCodeSound instances. Their common body is
the typed open term h P. The finite Bool domain remains a raw kernel, not
a sound model of every Prop code. General contextual Pi code certification,
fresh-variable substitution/naturality and the recursive tower remain open.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeSoundPi

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower RCodeSoundInterface

universe u v w z

/-- Extending the source context and its retained raw environment together. -/
def extend {W : World} {a : Nat} (A : RCodeSound.{u,v} W a)
    (x : Member A.code) : World where
  env := W.env
  iota := W.iota
  levelCount := W.levelCount
  context := .assumption A.sourceType :: W.context
  family := W.family
  valuation := W.valuation
  rawEnvironment := EnvI.cons (A.code.erase x.val) W.rawEnvironment
  envWf := W.envWf
  contextWf := .assumption W.contextWf A.typeTyped

def anchor {W : World} {a : Nat} (A : RCodeSound.{u,v} W a) : Member A.code :=
  ⟨A.code.view.point 0, A.code.view.point_member 0⟩

/-- Fibres have their own carriers in the actual extended worlds.
Transport is retained data and is not recovered from raw image equality. -/
structure Family {W : World} {a : Nat} (A : RCodeSound.{u,v} W a)
    (b : Nat) (B : ExprA) (lB : Level) where
  fibre : (x : Member A.code) → RCodeSound.{w,z} (extend A x) b
  source_type : ∀ x, (fibre x).sourceType = B
  source_level : ∀ x, (fibre x).sourceLevel = lB
  transport : ∀ x y, Related x y →
    KernelIso (fibre x).code.kernel (fibre y).code.kernel

section Contextual

variable {W : World} {a b : Nat} {A : RCodeSound.{u,v} W a}
variable {B : ExprA} {lB : Level}

def Family.kernels (D : Family.{u,v,w,z} A b B lB)
    (x : RCodeDependentPi.KMember A.code.kernel) : Kernel.{w} b :=
  (D.fibre x).code.kernel

def Family.transports (D : Family.{u,v,w,z} A b B lB) :
    RCodeDependentPi.FibreTransport A.code.kernel D.kernels := D.transport

def Family.codomainTyped (D : Family.{u,v,w,z} A b B lB) :
    HasTyA W.env W.iota W.levelCount (.assumption A.sourceType :: W.context)
      B (.sort lB) := by
  have h := (D.fibre (anchor A)).typeTyped
  rw [D.source_type, D.source_level] at h
  exact h

theorem Family.codomainImage (D : Family.{u,v,w,z} A b B lB)
    (x : Member A.code) :
    ValueEq (EnvironmentEval.denote W.env W.family W.valuation
      (EnvI.cons (A.code.erase x.val) W.rawEnvironment) B)
      (D.kernels x).per.value := by
  have h := (D.fibre x).typeImage
  rw [D.source_type x] at h
  exact h

/-- This section is data for one evaluator body, not an existence claim
derived from the individual fibres' realization propositions. -/
structure Section (D : Family.{u,v,w,z} A b B lB) where
  body : ExprA
  fragment : (x : Member A.code) → (D.fibre x).Fragment
  source_eq : ∀ x, ((D.fibre x).source (fragment x)).term = body
  respect : ∀ x y (h : Related x y),
    (D.fibre y).code.view.relation
      ((D.transport x y h).forward ((D.fibre x).evalSem (fragment x)).val)
      ((D.fibre y).evalSem (fragment y)).val

def Section.bodyTyped {D : Family.{u,v,w,z} A b B lB} (s : Section D) :
    HasTyA W.env W.iota W.levelCount (.assumption A.sourceType :: W.context)
      s.body B := by
  have h := ((D.fibre (anchor A)).source (s.fragment (anchor A))).typed
  rw [s.source_eq, D.source_type] at h
  exact h

def Section.sourceBody {D : Family.{u,v,w,z} A b B lB} (s : Section D) :
    RCodeDependentPi.SourceBody A.code.kernel D.kernels D.transports
      W.env W.family W.valuation W.rawEnvironment where
  body := s.body
  run := fun x => (D.fibre x).evalSem (s.fragment x)
  image := fun x => by
    have h := ((D.fibre x).erasure (s.fragment x)).symm
    rw [s.source_eq x] at h
    exact h
  respect := s.respect

def Section.typedBody {D : Family.{u,v,w,z} A b B lB} (s : Section D) :
    RCodeDependentPi.TypedSourceBody A.code.kernel D.kernels D.transports
      W.env W.iota W.family W.valuation W.rawEnvironment W.levelCount W.context
      A.sourceType B A.sourceLevel lB where
  evaluator := s.sourceBody
  environment := W.envWf
  context := W.contextWf
  domain_typed := A.typeTyped
  codomain_typed := D.codomainTyped
  body_typed := s.bodyTyped
  domain_image := A.typeImage
  codomain_image := D.codomainImage

def Section.action {D : Family.{u,v,w,z} A b B lB} (s : Section D) :
    RCodeDependentPi.Action A.code.kernel D.kernels D.transports :=
  s.sourceBody.action A.sourceType A.sourceLevel

def Section.lambdaTyped {D : Family.{u,v,w,z} A b B lB} (s : Section D) :
    HasTyA W.env W.iota W.levelCount W.context
      (.lam A.sourceType A.sourceLevel s.body)
      (.pi A.sourceType A.sourceLevel B lB) := s.typedBody.lambdaTyped

theorem Section.application {D : Family.{u,v,w,z} A b B lB} (s : Section D)
    (x : Member A.code) :
    ValueEq (NeutralPi.applyValue s.action.value (A.code.erase x.val))
      ((D.fibre x).code.erase ((D.fibre x).evalSem (s.fragment x)).val) :=
  s.action.erased x

theorem Section.paired {D : Family.{u,v,w,z} A b B lB} (s t : Section D)
    (hst : RCodeDependentPi.ActionRel s.action t.action)
    (x y : Member A.code) (hxy : Related x y) :
    (D.fibre y).code.view.relation
      ((D.transport x y hxy).forward ((D.fibre x).evalSem (s.fragment x)).val)
      ((D.fibre y).evalSem (t.fragment y)).val :=
  RCodeDependentPi.paired_application hst hxy

theorem Section.eta {D : Family.{u,v,w,z} A b B lB} (s : Section D) :
    RCodeDependentPi.ActionRel (RCodeDependentPi.etaAction s.action) s.action :=
  RCodeDependentPi.etaAction_related s.action

/-- Every displayed section has actual inhabited propositional readback
in each extended world. There is no discrete quotation or comparison. -/
theorem Section.readback {D : Family.{u,v,w,z} A b B lB} (s : Section D)
    (x : Member A.code) :
    (D.fibre x).ReadsBack (s.fragment x) ((D.fibre x).evalSem (s.fragment x))
      ((D.fibre x).source (s.fragment x)) := by
  exact ⟨((D.fibre x).evalSem (s.fragment x)).property,
    ⟨.refl _ _ _ ((D.fibre x).source (s.fragment x)).typed⟩⟩

end Contextual

/-! ## Actual sound fibres for the inherited dependent source control -/

open RCodeDependentPi

def boolWorld (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x : KMember boolKernel) : World where
  env := emptyEnvA
  iota := iotaIfaceA emptyEnvA
  levelCount := 0
  context := boolExtendedContext
  family := F
  valuation := ν
  rawEnvironment := EnvI.cons (boolKernel.erase x.val) boolEnvironment
  envWf := .empty
  contextWf := .assumption boolContextWf (.sort boolContext .zero)

def boolSource (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x : KMember boolKernel) : Source (boolWorld F ν x) (.bvar 0) :=
  ⟨boolSourceBody, boolBodyTyped⟩

def boolSound (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x : KMember boolKernel) : RCodeSound.{0,0} (boolWorld F ν x) 0 :=
  RCodeSoundZeroInstances.ofPoint (boolWorld F ν x)
    (.legacy (GuardDecision.propCode (boolProposition x.val))) (.bvar 0)
    (localPropTyped boolContext) ((boolTypedBody F ν).codomain_image x)
    (GuardedKernel.propositionReflector (GuardDecision.propElement (boolProposition x.val)))
    (boolSource F ν x) (boolOutput x) ((boolBody emptyEnvA F ν).image x).symm

/-- The head is a real source variable with a native neutral image. -/
def boolHeadNeutral (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x : KMember boolKernel) : Neutral (boolWorld F ν x) allPropsType where
  term := .bvar 1
  typed := boolHeadTyped
  value := NeutralPER.neutralAtom 0
  image := RCodeProofReadback.environment_variable_image emptyEnvA F ν
    (EnvI.cons (boolKernel.erase x.val) boolEnvironment) 1
    (ApproxI.bot EnvI.bot (.const 0 []))
  neutral := .atom 0

def boolArgument (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x : KMember boolKernel) : Source (boolWorld F ν x) (.sort .zero) :=
  ⟨.bvar 0, localPropTyped boolContext⟩

/-- A constructed nontrivial typed-neutral spine, not an assumed input. -/
def boolSpine (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x : KMember boolKernel) : Neutral (boolWorld F ν x) (.bvar 0) :=
  Neutral.app (boolHeadNeutral F ν x) (boolArgument F ν x) boolBodyTyped

theorem boolSound_spine_saturation (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (x : KMember boolKernel) :
    ∃ s : (boolSound F ν x).Fragment,
      (boolSound F ν x).ReadsBack s
        ((boolSound F ν x).reflect (boolSpine F ν x))
        (boolSpine F ν x).toSource ∧
      ValueEq ((boolSound F ν x).erase ((boolSound F ν x).evalSem s))
        ((boolWorld F ν x).evaluate ((boolSound F ν x).source s).term) :=
  (boolSound F ν x).neutral_saturation (boolSpine F ν x)

theorem boolSound_kernel (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x : KMember boolKernel) : (boolSound F ν x).code.kernel = boolFibre x := rfl

def boolSoundBody (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    SourceBody boolKernel boolFibre boolTransport emptyEnvA F ν boolEnvironment where
  body := boolSourceBody
  run := fun x => (boolSound F ν x).evalSem .basepoint
  image := fun x => ((boolSound F ν x).erasure .basepoint).symm
  respect := boolOutput_respect

theorem boolSound_run (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x : KMember boolKernel) : (boolSoundBody F ν).run x = boolOutput x := rfl

def boolSoundTypedBody (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    TypedSourceBody boolKernel boolFibre boolTransport emptyEnvA
      (iotaIfaceA emptyEnvA) F ν boolEnvironment 0 boolContext
      (.sort .zero) (.bvar 0) (.succ .zero) .zero where
  evaluator := boolSoundBody F ν
  environment := .empty
  context := boolContextWf
  domain_typed := .sort boolContext .zero
  codomain_typed := localPropTyped boolContext
  body_typed := boolBodyTyped
  domain_image := (boolTypedBody F ν).domain_image
  codomain_image := fun x => (boolSound F ν x).typeImage

theorem boolSound_readback (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x : KMember boolKernel) :
    (boolSound F ν x).ReadsBack .basepoint ((boolSound F ν x).evalSem .basepoint)
      ((boolSound F ν x).source .basepoint) :=
  ⟨(boolOutput x).property, ⟨.refl _ _ _ boolBodyTyped⟩⟩

theorem boolSound_paired (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (x y : KMember boolKernel) (h : MemberRel boolKernel x y) :
    (boolFibre y).per.relation
      ((boolTransport x y h).forward ((boolSound F ν x).evalSem .basepoint).val)
      ((boolSound F ν y).evalSem .basepoint).val := boolOutput_respect x y h

theorem inhabited_sound_dependent_control (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) :
    (∀ x : KMember boolKernel, Nonempty (RCodeSound.{0,0} (boolWorld F ν x) 0)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 boolContext
      (.lam (.sort .zero) (.succ .zero) boolSourceBody) allPropsType) ∧
    ¬ KernelRelated (boolSound F ν falseIndex).code.kernel
      (boolSound F ν trueIndex).code.kernel :=
  ⟨fun x => ⟨boolSound F ν x⟩, ⟨(boolSoundTypedBody F ν).lambdaTyped⟩,
    bool_fibres_not_related⟩

end Rcic.Declarative.Ann.LR3.RCodeSoundPi
