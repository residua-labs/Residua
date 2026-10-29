import rcic.RcicAnnLR3RCodeProofReadback
import rcic.RcicAnnLR3UnifiedPi
import rcic.RcicAnnLR3EnvironmentEvalComposition

/-!
# Dependent retained actions and uniform source bodies

The result carrier really depends on the retained argument. Its transport
along the domain PER is supplied as KernelIso data; no isomorphism is
selected from a proposition. Pointwise function PERs, heterogeneous paired
application and semantic eta are constructed below.

A source-realized subcarrier retains one source lambda body with its
uniform evaluator agreement. It does not select a different body at each
argument. The finite retained-index example has two genuinely different
proposition fibres and an actual, typed open source body.

This is dependent action algebra. It does not establish RCode closure,
typed-neutral presheaf naturality, a general reader, universe membership
of the new action carrier, or a Fundamental theorem. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeDependentPi

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily TaggedSaturatedTower

universe u v

abbrev KMember {k : Nat} (A : Kernel.{u} k) :=
  {x : A.Element // A.per.relation x x}

def MemberRel {k : Nat} (A : Kernel.{u} k) (x y : KMember A) : Prop :=
  A.per.relation x.val y.val

def transportMember {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (e : KernelIso A B) (x : KMember A) : KMember B :=
  ⟨e.forward x.val, (e.relation x.val x.val).mp x.property⟩

theorem transportMember_image {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (e : KernelIso A B) (x : KMember A) :
    ValueEq (B.erase (transportMember e x).val) (A.erase x.val) :=
  e.element_image x.val

abbrev FibreTransport {a b : Nat} (A : Kernel.{u} a)
    (B : KMember A → Kernel.{v} b) :=
  ∀ x y : KMember A, MemberRel A x y → KernelIso (B x) (B y)

/-- Exact native application and a genuinely dependent retained result. -/
structure Action {a b : Nat} (A : Kernel.{u} a)
    (B : KMember A → Kernel.{v} b) (T : FibreTransport A B) where
  value : Value
  run : (x : KMember A) → KMember (B x)
  erased : ∀ x, ValueEq (NeutralPi.applyValue value (A.erase x.val))
    ((B x).erase (run x).val)
  respect : ∀ x y (h : MemberRel A x y),
    (B y).per.relation ((T x y h).forward (run x).val) (run y).val

section Algebra

variable {a b : Nat} {A : Kernel.{u} a} {B : KMember A → Kernel.{v} b}
variable {T : FibreTransport A B}

def ActionRel (f g : Action A B T) : Prop :=
  ∀ x, (B x).per.relation (f.run x).val (g.run x).val

theorem actionRel_refl (f : Action A B T) : ActionRel f f :=
  fun x => (f.run x).property

theorem actionRel_laws : RelLaws (fun f g : Action A B T => ActionRel f g) where
  symm := fun h x => (B x).per.lawful.symm (h x)
  trans := fun h j x => (B x).per.lawful.trans (h x) (j x)

/-- Paired application compares results in the right-hand fibre using
the retained isomorphism of those fibres. -/
theorem paired_application {f g : Action A B T} (hfg : ActionRel f g)
    {x y : KMember A} (hxy : MemberRel A x y) :
    (B y).per.relation ((T x y hxy).forward (f.run x).val) (g.run y).val :=
  (B y).per.lawful.trans
    (((T x y hxy).relation (f.run x).val (g.run x).val).mp (hfg x))
    (g.respect x y hxy)

/-- No reflexive-transport identity is needed here: each action already
respects the actual chosen transport on a diagonal domain edge. -/
theorem actionRel_iff_paired (f g : Action A B T) :
    ActionRel f g ↔
    ∀ x y (h : MemberRel A x y),
      (B y).per.relation ((T x y h).forward (f.run x).val) (g.run y).val := by
  constructor
  · intro h x y hxy
    exact paired_application h hxy
  · intro h x
    have hx : MemberRel A x x := x.property
    exact (B x).per.lawful.trans
      ((B x).per.lawful.symm (f.respect x x hx)) (h x x hx)

theorem application_image (f : Action A B T) (x : KMember A) :
    ValueEq (NeutralPi.applyValue f.value (A.erase x.val))
      ((B x).erase (f.run x).val) := f.erased x

/-- Native graph eta preserves every represented result and all dependent
transport laws. It is not a syntactic normal-form reifier. -/
def etaAction (f : Action A B T) : Action A B T where
  value := UnifiedPi.etaGraph (fun _ _ => True) f.value
  run := f.run
  erased := fun x =>
    (UnifiedPi.etaGraph_application (fun _ _ => True) f.value
      (x := A.erase x.val) True.intro).trans (f.erased x)
  respect := f.respect

theorem etaAction_run (f : Action A B T) (x : KMember A) :
    (etaAction f).run x = f.run x := rfl

theorem etaAction_related (f : Action A B T) : ActionRel (etaAction f) f :=
  actionRel_refl f

theorem etaAction_respects {f g : Action A B T} (h : ActionRel f g) :
    ActionRel (etaAction f) (etaAction g) := h

end Algebra

/-- ONE body is retained for the entire dependent action. This is stronger
than unrelated per-argument existential source representations. -/
structure SourceBody {a b : Nat} (A : Kernel.{u} a)
    (B : KMember A → Kernel.{v} b) (T : FibreTransport A B)
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) where
  body : ExprA
  run : (x : KMember A) → KMember (B x)
  image : ∀ x,
    ValueEq (EnvironmentEval.denote E F ν (EnvI.cons (A.erase x.val) ρ) body)
      ((B x).erase (run x).val)
  respect : ∀ x y (h : MemberRel A x y),
    (B y).per.relation ((T x y h).forward (run x).val) (run y).val

section SourceAlgebra

variable {a b : Nat} {A : Kernel.{u} a} {B : KMember A → Kernel.{v} b}
variable {T : FibreTransport A B} {E : ResolvedEnvA}
variable {F : EnvironmentEval.FamilySyntax} {ν : Valuation} {ρ : EnvI}

def SourceBody.action (s : SourceBody A B T E F ν ρ)
    (sourceA : ExprA) (lA : Level) : Action A B T where
  value := EnvironmentEval.denote E F ν ρ (.lam sourceA lA s.body)
  run := s.run
  erased := fun x =>
    (EnvironmentEval.denote_lambda_application E F ν ρ sourceA s.body lA
      (A.erase x.val)).trans (s.image x)
  respect := s.respect

theorem SourceBody.action_image (s : SourceBody A B T E F ν ρ)
    (sourceA : ExprA) (lA : Level) :
    (s.action sourceA lA).value =
      EnvironmentEval.denote E F ν ρ (.lam sourceA lA s.body) := rfl

theorem SourceBody.action_run (s : SourceBody A B T E F ν ρ)
    (sourceA : ExprA) (lA : Level) (x : KMember A) :
    (s.action sourceA lA).run x = s.run x := rfl

/-- A retained representative in Type, not a choice from an existential. -/
structure SourceWitness (sourceA : ExprA) (lA : Level) (f : Action A B T) where
  evaluator : SourceBody A B T E F ν ρ
  related : ActionRel f (evaluator.action sourceA lA)

abbrev SourceRealizedAction (sourceA : ExprA) (lA : Level) :=
  Σ f : Action A B T, SourceWitness (E := E) (F := F) (ν := ν) (ρ := ρ)
    sourceA lA f

def SourceBody.realized (s : SourceBody A B T E F ν ρ)
    (sourceA : ExprA) (lA : Level) :
    SourceRealizedAction (A := A) (B := B) (T := T)
      (E := E) (F := F) (ν := ν) (ρ := ρ) sourceA lA :=
  ⟨s.action sourceA lA, ⟨s, actionRel_refl _⟩⟩

theorem SourceRealizedAction.realization (sourceA : ExprA) (lA : Level)
    (f : SourceRealizedAction (A := A) (B := B) (T := T)
      (E := E) (F := F) (ν := ν) (ρ := ρ) sourceA lA) :
    ActionRel f.1 (f.2.evaluator.action sourceA lA) ∧
    (f.2.evaluator.action sourceA lA).value =
      EnvironmentEval.denote E F ν ρ (.lam sourceA lA f.2.evaluator.body) :=
  ⟨f.2.related, rfl⟩

end SourceAlgebra

/-- Optional source admission and the type-family image are retained with
the same uniform body evaluator. These are data for a source lambda
constructor, not a whole-language fundamental premise hidden in a field. -/
structure TypedSourceBody {a b : Nat} (A : Kernel.{u} a)
    (B : KMember A → Kernel.{v} b) (T : FibreTransport A B)
    (E : ResolvedEnvA) (I : IotaIfaceA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (n : Nat) (Γ : LCtxA)
    (sourceA sourceB : ExprA) (lA lB : Level) where
  evaluator : SourceBody A B T E F ν ρ
  environment : EnvWfA I E
  context : CtxWfA E I n Γ
  domain_typed : HasTyA E I n Γ sourceA (.sort lA)
  codomain_typed : HasTyA E I n (.assumption sourceA :: Γ) sourceB (.sort lB)
  body_typed : HasTyA E I n (.assumption sourceA :: Γ) evaluator.body sourceB
  domain_image : ValueEq (EnvironmentEval.denote E F ν ρ sourceA) A.per.value
  codomain_image : ∀ x,
    ValueEq (EnvironmentEval.denote E F ν (EnvI.cons (A.erase x.val) ρ) sourceB)
      (B x).per.value

def TypedSourceBody.lambdaTyped {a b : Nat}
    {A : Kernel.{u} a} {B : KMember A → Kernel.{v} b} {T : FibreTransport A B}
    {E : ResolvedEnvA} {I : IotaIfaceA} {F : EnvironmentEval.FamilySyntax}
    {ν : Valuation} {ρ : EnvI} {n : Nat} {Γ : LCtxA}
    {sourceA sourceB : ExprA} {lA lB : Level}
    (s : TypedSourceBody A B T E I F ν ρ n Γ sourceA sourceB lA lB) :
    HasTyA E I n Γ (.lam sourceA lA s.evaluator.body)
      (.pi sourceA lA sourceB lB) :=
  .lam Γ sourceA lA s.evaluator.body sourceB lB
    s.domain_typed s.codomain_typed s.body_typed

/-! ## A finite retained-index dependent example

The domain has two explicit retained proposition indices. This is a
finite algebra fixture, not the full carrier of the Prop universe. Its
fibres are the genuine old propCode False and propCode True; neither is
assumed inhabited by a closed proof. The source context supplies an open
neutral h : (P : Prop) → P, and one body `h P` realizes both fibres.
-/

def boolProposition : Bool → Prop
  | false => False
  | true => True

def boolKernel : Kernel.{0} 1 where
  Element := Bool
  erase := fun b => (GuardDecision.propCode (boolProposition b)).view.value
  per := {
    value := (universeCode.{0} 0).view.value
    level := (universeCode.{0} 0).view.level
    defined := (universeCode.{0} 0).view.defined
    relation := Eq
    lawful := ⟨fun h => h.symm, fun h j => h.trans j⟩
    point := fun _ => false
    point_member := fun _ => rfl
    irrelevant := fun h => False.elim (Nat.noConfusion h) }

def boolFibre (x : KMember boolKernel) : Kernel.{0} 0 :=
  (GuardDecision.propCode (boolProposition x.val)).kernel

def boolTransport : FibreTransport boolKernel boolFibre := by
  intro x y h
  have he : x = y := Subtype.ext h
  cases he
  exact KernelIso.refl _

def falseIndex : KMember boolKernel := ⟨false, rfl⟩
def trueIndex : KMember boolKernel := ⟨true, rfl⟩

theorem bool_fibres_not_related :
    ¬ KernelRelated (boolFibre falseIndex) (boolFibre trueIndex) := by
  intro h
  exact GuardDecision.propCode_false_true_not_related ⟨rfl, h⟩

theorem bool_argument_nonempty (x : KMember boolKernel) :
    CandidatePi.NonemptyValue (boolKernel.erase x.val) :=
  CandidatePi.typeDefined_nonempty (boolFibre x).per.defined

def boolOutput (x : KMember boolKernel) : KMember (boolFibre x) :=
  ⟨⟨NeutralPi.applyValue (NeutralPER.neutralAtom 0) (boolKernel.erase x.val)⟩,
    CandidatePi.decode_reflection _
      (.app (.atom 0) (boolKernel.erase x.val) (bool_argument_nonempty x))⟩

theorem boolOutput_respect (x y : KMember boolKernel) (h : MemberRel boolKernel x y) :
    (boolFibre y).per.relation
      ((boolTransport x y h).forward (boolOutput x).val) (boolOutput y).val := by
  have he : x = y := Subtype.ext h
  cases he
  exact (boolOutput x).property

def boolNeutralAction : Action boolKernel boolFibre boolTransport where
  value := NeutralPER.neutralAtom 0
  run := boolOutput
  erased := fun _ => ValueEq.refl _
  respect := boolOutput_respect

def boolEnvironment : EnvI := EnvI.cons (NeutralPER.neutralAtom 0) EnvI.bot

abbrev boolSourceBody : ExprA := .app (.bvar 1) (.bvar 0)

def boolBody (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    SourceBody boolKernel boolFibre boolTransport E F ν boolEnvironment where
  body := boolSourceBody
  run := boolOutput
  image := fun x =>
    (EnvironmentEval.denote_application E F ν
      (EnvI.cons (boolKernel.erase x.val) boolEnvironment) (.bvar 1) (.bvar 0)).trans
      (NeutralPi.applyValue_congr
        (RCodeProofReadback.environment_variable_image E F ν
          (EnvI.cons (boolKernel.erase x.val) boolEnvironment) 1
          (ApproxI.bot EnvI.bot (.const 0 [])))
        (RCodeProofReadback.environment_variable_image E F ν
          (EnvI.cons (boolKernel.erase x.val) boolEnvironment) 0 (Or.inl rfl)))
  respect := boolOutput_respect

theorem boolBody_related_to_neutral (E : ResolvedEnvA)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    ActionRel ((boolBody E F ν).action (.sort .zero) (.succ .zero))
      boolNeutralAction := actionRel_refl boolNeutralAction

abbrev allPropsType : ExprA :=
  .pi (.sort .zero) (.succ .zero) (.bvar 0) .zero

abbrev allPropsLevel : Level := .imax (.succ .zero) .zero

def localPropTyped (Γ : LCtxA) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0
      (.assumption (.sort .zero) :: Γ) (.bvar 0) (.sort .zero) :=
  .bvar _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ .zero)

def allPropsTyped (Γ : LCtxA) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 Γ allPropsType (.sort allPropsLevel) :=
  .pi Γ (.sort .zero) (.succ .zero) (.bvar 0) .zero
    (.sort Γ .zero) (localPropTyped Γ)

abbrev boolContext : LCtxA := [.assumption allPropsType]
abbrev boolExtendedContext : LCtxA := .assumption (.sort .zero) :: boolContext

def boolContextWf : CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 boolContext :=
  .assumption .nil (allPropsTyped [])

def boolHeadTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 boolExtendedContext
      (.bvar 1) allPropsType :=
  .bvar boolExtendedContext 1 allPropsType allPropsLevel rfl
    (allPropsTyped boolExtendedContext)

def boolBodyTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 boolExtendedContext
      boolSourceBody (.bvar 0) :=
  .app boolExtendedContext (.bvar 1) (.bvar 0) (.sort .zero) (.bvar 0)
    (.succ .zero) .zero .zero (localPropTyped boolExtendedContext)
    (localPropTyped boolContext) boolHeadTyped (localPropTyped boolContext)

def boolTypedBody (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    TypedSourceBody boolKernel boolFibre boolTransport emptyEnvA
      (iotaIfaceA emptyEnvA) F ν boolEnvironment 0 boolContext
      (.sort .zero) (.bvar 0) (.succ .zero) .zero where
  evaluator := boolBody emptyEnvA F ν
  environment := .empty
  context := boolContextWf
  domain_typed := .sort boolContext .zero
  codomain_typed := localPropTyped boolContext
  body_typed := boolBodyTyped
  domain_image :=
    (EnvironmentEval.denote_core emptyEnvA F ν boolEnvironment
      (e := .sort .zero) True.intro).trans
      (FunctionEval.sortTerm_environment boolEnvironment EnvI.bot (some 0))
  codomain_image := fun x =>
    RCodeProofReadback.environment_variable_image emptyEnvA F ν
      (EnvI.cons (boolKernel.erase x.val) boolEnvironment) 0 (Or.inl rfl)

theorem inhabited_dependent_source_control (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) :
    Nonempty (SourceRealizedAction (A := boolKernel) (B := boolFibre)
      (T := boolTransport) (E := emptyEnvA) (F := F) (ν := ν) (ρ := boolEnvironment)
      (.sort .zero) (.succ .zero)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 boolContext
      (.lam (.sort .zero) (.succ .zero) boolSourceBody) allPropsType) ∧
    ¬ KernelRelated (boolFibre falseIndex) (boolFibre trueIndex) :=
  ⟨⟨(boolBody emptyEnvA F ν).realized (.sort .zero) (.succ .zero)⟩,
    ⟨(boolTypedBody F ν).lambdaTyped⟩, bool_fibres_not_related⟩

end Rcic.Declarative.Ann.LR3.RCodeDependentPi
