import rcic.RcicAnnLR3RCodeProofReadback
import rcic.RcicAnnLR3GuardedTaggedCode

/-!
# A single contextual specification for reflective, realizable codes

Elements in this specification are PER self-members, not arbitrary values
of the old raw carrier. The source world is fixed before an element is
realized. A neutral retains its source typing and its actual evaluator
image; semantic neutrality alone is not renamed source typing.

Reification is parametrized by its normal-form format, with decidable
equality supplied as explicit data. The format has an actual typed source
decoder, a retained evaluator with the inherited raw image, and a PER
soundness law for reification. Neutral readback has a
source conversion witness. Thus reflection may perform Pi eta expansion
without pretending that its raw graph is identical to the neutral input.

The decoded source satisfies an explicit recursive normality predicate:
its head step is stuck and all immediate components are normal in their
appropriate binder contexts. The constructed instance uses the finite
proof-erased ProofNF format. Its decoded source is a normal variable, and
source proof irrelevance justifies that representative. No construction
of normal forms for the other generators is asserted. The source fragment
remains explicit: it evaluates actual open proof variables.

This is one common specification with a constructed proposition instance
and constructive transport. A recursively generated RCode tower, general
dependent-Pi closure and a whole-language retained evaluator remain separate
obligations. In particular no desired closure theorem is taken as an axiom.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeInterface

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower

universe u v w

/-- The source/raw world and its admission data are fixed here.
Retained bindings are fixed by each concrete interpretation instance;
this record is not a general retained semantic-environment judgment.
Realization cannot select a fresh environment carrying the target value. -/
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

/-- Finite source normal forms: no head step remains, including delta or
iota, and components are recursively normal. Binder bodies use the
extended source context. Reducible lets and literals are not constructors.
This predicate asserts normality, not an algorithm that constructs it. -/
inductive Normal (E : ResolvedEnvA) (I : IotaIfaceA) : LCtxA → ExprA → Prop where
  | bvar {Γ : LCtxA} {i : Nat}
      (stuck : hStepFnA E I.fn Γ (.bvar i) = none) : Normal E I Γ (.bvar i)
  | const {Γ : LCtxA} {r : Nat} {ls : List Level}
      (stuck : hStepFnA E I.fn Γ (.const r ls) = none) : Normal E I Γ (.const r ls)
  | sort {Γ : LCtxA} {l : Level}
      (stuck : hStepFnA E I.fn Γ (.sort l) = none) : Normal E I Γ (.sort l)
  | app {Γ : LCtxA} {f a : ExprA}
      (stuck : hStepFnA E I.fn Γ (.app f a) = none)
      (fn : Normal E I Γ f) (arg : Normal E I Γ a) : Normal E I Γ (.app f a)
  | pi {Γ : LCtxA} {A B : ExprA} {u v : Level}
      (stuck : hStepFnA E I.fn Γ (.pi A u B v) = none)
      (domain : Normal E I Γ A) (body : Normal E I (.assumption A :: Γ) B) :
      Normal E I Γ (.pi A u B v)
  | lam {Γ : LCtxA} {A b : ExprA} {u : Level}
      (stuck : hStepFnA E I.fn Γ (.lam A u b) = none)
      (domain : Normal E I Γ A) (body : Normal E I (.assumption A :: Γ) b) :
      Normal E I Γ (.lam A u b)

theorem Normal.head_stuck {E : ResolvedEnvA} {I : IotaIfaceA}
    {Γ : LCtxA} {e : ExprA} (h : Normal E I Γ e) :
    hStepFnA E I.fn Γ e = none := by
  cases h with
  | bvar h => exact h
  | const h => exact h
  | sort h => exact h
  | app h _ _ => exact h
  | pi h _ _ => exact h
  | lam h _ _ => exact h

/-- Every source-typed, semantically neutral spine image in this world is
in the reflection domain. No atom-only restriction is present. -/
structure Neutral (W : World) (A : ExprA) extends Source W A where
  value : Value
  image : ValueEq (W.evaluate term) value
  neutral : CandidatePi.Neutral value

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

/-- NF is an explicitly chosen source-backed readback format. Every NF
decodes to a typed source term and has a retained evaluation with its
actual raw image. Reification is sound in the element PER.

The source conversion of neutral readback permits typed eta expansion;
raw identity of the reflected value and the input neutral is not imposed.
Concrete proof erasure uses a fixed open proof variable as decoder, with
an actual source irrelevance derivation. Additional fragment representatives
remain Type-valued retained data, so no choice principle is used. -/
structure RCode (W : World) (k : Nat) (NF : Type v) where
  code : GuardedTaggedCode.Code.{u} k
  sourceType : ExprA
  sourceLevel : Level
  typeTyped : HasTyA W.env W.iota W.levelCount W.context sourceType (.sort sourceLevel)
  level : eval W.valuation sourceLevel = some k
  typeImage : ValueEq (W.evaluate sourceType) code.view.value
  normalEq : DecidableEq NF
  decodeNF : NF → Source W sourceType
  decodeNF_normal : ∀ nf, Normal W.env W.iota W.context (decodeNF nf).term
  evalNF : NF → Member code
  evalNF_image : ∀ nf,
    ValueEq (code.erase (evalNF nf).val) (W.evaluate (decodeNF nf).term)
  reflect : Neutral W sourceType → Member code
  readNeutral : Neutral W sourceType → NF
  neutral_conversion : ∀ n : Neutral W sourceType,
    ConvA W.env W.iota W.levelCount W.context n.term
      (decodeNF (readNeutral n)).term sourceType
  reify : Member code → NF
  reify_respect : ∀ x y, Related x y → reify x = reify y
  reify_sound : ∀ x, Related x (evalNF (reify x))
  roundtrip : ∀ n, reify (reflect n) = readNeutral n
  Fragment : Type w
  source : Fragment → Source W sourceType
  evalSem : Fragment → Member code
  erasure : ∀ s, ValueEq (code.erase (evalSem s).val) (W.evaluate (source s).term)
  representative : ∀ x : Member code, {s : Fragment // Related x (evalSem s)}

abbrev RCode.Element {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) := Member C.code

def RCode.erase {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (x : C.Element) : Value := C.code.erase x.val

/-- The reified result itself has a typed source representative and the
actual inherited evaluation image; an unrelated constant quote cannot
represent two PER-separated universe elements. -/
theorem RCode.reified_realized {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (x : C.Element) :
    Related x (C.evalNF (C.reify x)) ∧
      ValueEq (C.erase (C.evalNF (C.reify x)))
        (W.evaluate (C.decodeNF (C.reify x)).term) :=
  ⟨C.reify_sound x, C.evalNF_image (C.reify x)⟩

theorem RCode.reify_evaluate {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (x : C.Element) :
    C.reify (C.evalNF (C.reify x)) = C.reify x :=
  (C.reify_respect _ _ (C.reify_sound x)).symm

/-- Quotation reflects the PER because it has a sound fixed evaluator. -/
theorem RCode.quote_eq_related {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (x y : C.Element)
    (h : C.reify x = C.reify y) : Related x y := by
  have hx := C.reify_sound x
  rw [h] at hx
  exact related_trans hx (related_symm (C.reify_sound y))

theorem RCode.quote_eq_iff {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (x y : C.Element) :
    C.reify x = C.reify y ↔ Related x y :=
  ⟨C.quote_eq_related x y, C.reify_respect x y⟩

/-- Semantic reflection is related to the evaluated readback, while its
source is convertible to the supplied neutral term. This supports eta
without imposing raw identity on the reflected representation. -/
theorem RCode.reflection_readback_sound {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (n : Neutral W C.sourceType) :
    Related (C.reflect n) (C.evalNF (C.readNeutral n)) := by
  have h := C.reify_sound (C.reflect n)
  rw [C.roundtrip n] at h
  exact h

theorem RCode.reflection_source_sound {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (n : Neutral W C.sourceType) :
    Nonempty (ConvA W.env W.iota W.levelCount W.context n.term
      (C.decodeNF (C.readNeutral n)).term C.sourceType) ∧
    Related (C.reflect n) (C.evalNF (C.readNeutral n)) ∧
    ValueEq (C.erase (C.evalNF (C.readNeutral n)))
      (W.evaluate (C.decodeNF (C.readNeutral n)).term) :=
  ⟨⟨C.neutral_conversion n⟩, C.reflection_readback_sound n,
    C.evalNF_image (C.readNeutral n)⟩

theorem RCode.realized {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (x : C.Element) :
    ∃ s : C.Fragment, Related x (C.evalSem s) ∧
      ValueEq (C.erase (C.evalSem s)) (W.evaluate (C.source s).term) :=
  ⟨(C.representative x).val, (C.representative x).property,
    C.erasure (C.representative x).val⟩

theorem RCode.representative_readback {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (x : C.Element) :
    C.reify x = C.reify (C.evalSem (C.representative x).val) :=
  C.reify_respect _ _ (C.representative x).property

theorem RCode.reflected_realized {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (n : Neutral W C.sourceType) :
    ∃ s : C.Fragment, Related (C.reflect n) (C.evalSem s) ∧
      C.reify (C.evalSem s) = C.readNeutral n := by
  let s := C.representative (C.reflect n)
  exact ⟨s.val, s.property,
    (C.reify_respect _ _ s.property).symm.trans (C.roundtrip n)⟩

def transportMember {k : Nat} {C D : GuardedTaggedCode.Code.{u} k}
    (e : KernelIso C.kernel D.kernel) (x : Member C) : Member D :=
  ⟨e.forward x.val, (e.relation x.val x.val).mp x.property⟩

theorem transportMember_related {k : Nat} {C D : GuardedTaggedCode.Code.{u} k}
    (e : KernelIso C.kernel D.kernel) (x y : Member C) :
    Related (transportMember e x) (transportMember e y) ↔ Related x y :=
  (e.relation x.val y.val).symm

theorem transportMember_inverse {k : Nat} {C D : GuardedTaggedCode.Code.{u} k}
    (e : KernelIso C.kernel D.kernel) (x : Member C) :
    transportMember e.symm (transportMember e x) = x :=
  Subtype.ext (e.left_inv x.val)

/-- A real retained isomorphism transports the entire contextual package.
This does not select an isomorphism from a propositional Converts witness. -/
def RCode.transport {W : World} {k : Nat} {NF : Type v}
    (C : RCode.{u,v,w} W k NF) (D : GuardedTaggedCode.Code.{u} k)
    (e : KernelIso C.code.kernel D.kernel) : RCode.{u,v,w} W k NF where
  code := D
  sourceType := C.sourceType
  sourceLevel := C.sourceLevel
  typeTyped := C.typeTyped
  level := C.level
  typeImage := C.typeImage.trans e.type_image
  normalEq := C.normalEq
  decodeNF := C.decodeNF
  decodeNF_normal := C.decodeNF_normal
  evalNF := fun nf => transportMember e (C.evalNF nf)
  evalNF_image := fun nf => (e.element_image (C.evalNF nf).val).trans
    (C.evalNF_image nf)
  reflect := fun n => transportMember e (C.reflect n)
  readNeutral := C.readNeutral
  neutral_conversion := C.neutral_conversion
  reify := fun y => C.reify (transportMember e.symm y)
  reify_respect := fun y z h => C.reify_respect _ _
    ((transportMember_related e.symm y z).mpr h)
  reify_sound := fun y => by
    have h := (e.relation (e.backward y.val)
      (C.evalNF (C.reify (transportMember e.symm y))).val).mp
      (C.reify_sound (transportMember e.symm y))
    rw [e.right_inv y.val] at h
    exact h
  roundtrip := fun n => by
    change C.reify (transportMember e.symm (transportMember e (C.reflect n))) =
      C.readNeutral n
    rw [transportMember_inverse]
    exact C.roundtrip n
  Fragment := C.Fragment
  source := C.source
  evalSem := fun s => transportMember e (C.evalSem s)
  erasure := fun s => (e.element_image (C.evalSem s).val).trans (C.erasure s)
  representative := fun y => by
    let s := C.representative (transportMember e.symm y)
    refine ⟨s.val, ?_⟩
    have h := (e.relation (e.backward y.val) (C.evalSem s.val).val).mp s.property
    rw [e.right_inv y.val] at h
    exact h

/-- This world is actually source-admitted for every retained proposition.
It is open: A : Prop, p : A, q : A. No closed proof of arbitrary P is used. -/
def proofWorld (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (P : Prop) : World where
  env := emptyEnvA
  iota := iotaIfaceA emptyEnvA
  levelCount := 0
  context := RCodeProofReadback.proofContext
  family := F
  valuation := ν
  rawEnvironment := RCodeProofReadback.rawEnvironment P
  envWf := .empty
  contextWf := RCodeProofReadback.proofContextWf

/-- A constructed generator instance with all three requested obligations,
on self-members and the actual fixed-world variable evaluator. -/
def proposition (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (P : Prop) :
    RCode.{0,0,0} (proofWorld F ν P) 0 RCodeProofReadback.ProofNF where
  code := .legacy (GuardDecision.propCode P)
  sourceType := RCodeProofReadback.proofType
  sourceLevel := .zero
  typeTyped := RCodeProofReadback.proofTypeTyped
  level := rfl
  typeImage := RCodeProofReadback.retainedType_image F ν P
  normalEq := inferInstance
  decodeNF := fun _ =>
    ⟨RCodeProofReadback.proofSource .newest, RCodeProofReadback.proofSourceTyped .newest⟩
  decodeNF_normal := fun _ => .bvar rfl
  evalNF := fun _ =>
    ⟨RCodeProofReadback.evaluateProof P .newest,
      RCodeProofReadback.evaluateProof_member P .newest⟩
  evalNF_image := fun _ =>
    (RCodeProofReadback.evaluateProof_image F ν P .newest).symm
  reflect := fun n =>
    ⟨⟨n.value⟩, proposition_cr3.{0} (GuardDecision.propElement P) n.value n.neutral⟩
  readNeutral := fun _ => .proof
  neutral_conversion := fun n =>
    .irr RCodeProofReadback.proofContext RCodeProofReadback.proofType n.term
      (RCodeProofReadback.proofSource .newest) RCodeProofReadback.proofTypeTyped
      n.typed (RCodeProofReadback.proofSourceTyped .newest)
  reify := fun _ => .proof
  reify_respect := fun _ _ _ => rfl
  reify_sound := fun x =>
    (GuardDecision.propCode P).view.irrelevant rfl _ _ x.property
      (RCodeProofReadback.evaluateProof_member P .newest)
  roundtrip := fun _ => rfl
  Fragment := RCodeProofReadback.ProofVariable
  source := fun s => ⟨RCodeProofReadback.proofSource s, RCodeProofReadback.proofSourceTyped s⟩
  evalSem := fun s =>
    ⟨RCodeProofReadback.evaluateProof P s, RCodeProofReadback.evaluateProof_member P s⟩
  erasure := fun s => (RCodeProofReadback.evaluateProof_image F ν P s).symm
  representative := fun x => ⟨.newest,
    (GuardDecision.propCode P).view.irrelevant rfl _ _ x.property
      (RCodeProofReadback.evaluateProof_member P .newest)⟩

theorem proposition_closed (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (P : Prop) :
    Nonempty (RCode.{0,0,0} (proofWorld F ν P) 0 RCodeProofReadback.ProofNF) :=
  ⟨proposition F ν P⟩

theorem proposition_reflect_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (P : Prop) (n : Neutral (proofWorld F ν P) RCodeProofReadback.proofType) :
    (proposition F ν P).erase ((proposition F ν P).reflect n) = n.value := rfl

theorem proposition_erasure (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (P : Prop) (s : RCodeProofReadback.ProofVariable) :
    ValueEq ((proposition F ν P).erase ((proposition F ν P).evalSem s))
      ((proofWorld F ν P).evaluate (RCodeProofReadback.proofSource s)) :=
  (proposition F ν P).erasure s

/-- The sole proof normal form decodes to an actual source variable. -/
theorem proposition_decodeNF (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (P : Prop) (nf : RCodeProofReadback.ProofNF) :
    ((proposition F ν P).decodeNF nf).term = .bvar 0 := rfl

end Rcic.Declarative.Ann.LR3.RCodeInterface
