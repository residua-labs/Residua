import rcic.RcicAnnLR3GuardDecision
import rcic.RcicAnnLR3GuardedReaderSource
import rcic.RcicAnnLR3EnvironmentEval

/-!
# Proof readback and member realization for reflective codes

The old proposition generator is proof irrelevant on its self-members.
Consequently, PER-respecting readback into literal normal-form equality
must identify all reflected proof neutrals. This is a conditional boundary:
it rules out additionally separating two proof-neutral readbacks, not a
proof-erased normal form or the source language.

The old Element field is a raw carrier, not its subtype of PER members.
The actual propCode False contains a raw unit which is not a self-member.
Thus total realization on that raw carrier cannot be a property of every
old generator. The member-qualified version has a positive control below:
every proposition self-member is related to the retained evaluation of an
actual open proof variable, with its raw evaluator agreement proved.

These are interface qualifications and one explicit proposition fragment.
There is no whole-language evalSem, general normalization theorem, or
Fundamental theorem here. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeProofReadback

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower

universe u v w

/-- At proposition level, a PER-respecting literal reifier is constant
on self-members. This uses the actual proof-irrelevance field of Code. -/
theorem reify_members_equal (C : Code.{u} 0) {NF : Type v}
    (reify : C.Element → NF)
    (respect : ∀ x y, C.view.relation x y → reify x = reify y)
    (x y : C.Element) (hx : C.view.relation x x)
    (hy : C.view.relation y y) : reify x = reify y :=
  respect x y (C.view.irrelevant rfl x y hx hy)

/-- Neutral readback need not be injective. The conclusion records the
identification that proof irrelevance requires, without assuming otherwise. -/
theorem reflected_readbacks_equal (C : Code.{u} 0)
    {Spine : Type v} {NF : Type w}
    (reflect : Spine → C.Element)
    (reflect_member : ∀ n, C.view.relation (reflect n) (reflect n))
    (reify : C.Element → NF)
    (respect : ∀ x y, C.view.relation x y → reify x = reify y)
    (readback : Spine → NF)
    (roundtrip : ∀ n, reify (reflect n) = readback n)
    (m n : Spine) : readback m = readback n := by
  exact (roundtrip m).symm.trans
    ((reify_members_equal C reify respect (reflect m) (reflect n)
      (reflect_member m) (reflect_member n)).trans (roundtrip n))

/-- This no-go result has an explicit separation hypothesis. Dropping that
hypothesis, as proof-erased readback does, removes the contradiction. -/
theorem no_separating_proof_readback (C : Code.{u} 0)
    {Spine : Type v} {NF : Type w}
    (reflect : Spine → C.Element)
    (reflect_member : ∀ n, C.view.relation (reflect n) (reflect n))
    (readback : Spine → NF) (m n : Spine)
    (separate : readback m ≠ readback n) :
    ¬ ∃ reify : C.Element → NF,
      (∀ x y, C.view.relation x y → reify x = reify y) ∧
      (∀ n, reify (reflect n) = readback n) := by
  rintro ⟨reify, respect, roundtrip⟩
  exact separate (reflected_readbacks_equal C reflect reflect_member reify
    respect readback roundtrip m n)

def proofAtom (P : Prop) (name : Nat) : (GuardDecision.propCode P).Element :=
  ⟨NeutralPER.neutralAtom name⟩

theorem proofAtom_member (P : Prop) (name : Nat) :
    (GuardDecision.propCode P).view.relation
      (proofAtom P name) (proofAtom P name) :=
  GuardDecision.propCode_neutral_member P name

theorem proofAtoms_related (P : Prop) (m n : Nat) :
    (GuardDecision.propCode P).view.relation
      (proofAtom P m) (proofAtom P n) :=
  (GuardDecision.propCode P).view.irrelevant rfl _ _
    (proofAtom_member P m) (proofAtom_member P n)

/-- An actual generator instance: no literal natural-number readback can
preserve the names of all its reflected proof atoms. The generator is
inhabited even for False, by its admitted open neutrals. -/
theorem propCode_no_name_reifier (P : Prop) :
    ¬ ∃ reify : (GuardDecision.propCode P).Element → Nat,
      (∀ x y, (GuardDecision.propCode P).view.relation x y →
        reify x = reify y) ∧
      (∀ name, reify (proofAtom P name) = name) := by
  apply no_separating_proof_readback (GuardDecision.propCode P)
    (proofAtom P) (proofAtom_member P) (fun n : Nat => n) 0 1
  exact Nat.zero_ne_one

theorem propFalse_readback_boundary :
    (∃ a : (GuardDecision.propCode False).Element,
      (GuardDecision.propCode False).view.relation a a) ∧
    ¬ ∃ reify : (GuardDecision.propCode False).Element → Nat,
      (∀ x y, (GuardDecision.propCode False).view.relation x y →
        reify x = reify y) ∧
      (∀ name, reify (proofAtom False name) = name) :=
  ⟨GuardDecision.propCode_inhabited False, propCode_no_name_reifier False⟩

/-- Every edge of a PER starts at a self-member. -/
theorem related_implies_member {k : Nat} (C : Code.{u} k)
    {x y : C.Element} (h : C.view.relation x y) :
    C.view.relation x x :=
  C.view.lawful.trans h (C.view.lawful.symm h)

/-- Realization on all raw carrier values would force the PER to be total
on the diagonal. No evaluator property can repair a nonmember witness. -/
theorem total_realization_implies_all_members {k : Nat} (C : Code.{u} k)
    {Source : Type v} (evaluate : Source → C.Element)
    (realized : ∀ x : C.Element, ∃ e, C.view.relation x (evaluate e)) :
    ∀ x : C.Element, C.view.relation x x := by
  intro x
  obtain ⟨e, he⟩ := realized x
  exact related_implies_member C he

/-- For an inhabited proof-irrelevant code, member-wise realization is
equivalent to one evaluator output being a member. Context-sensitive
source admission remains in Source; this is not a closed inhabitation
theorem for arbitrary propositions. -/
theorem proof_member_realization_iff (C : Code.{u} 0)
    {Source : Type v} (evaluate : Source → C.Element) :
    (∀ x : C.Element, C.view.relation x x →
      ∃ e, C.view.relation x (evaluate e)) ↔
    (∃ e, C.view.relation (evaluate e) (evaluate e)) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := h (C.view.point 0) (C.view.point_member 0)
    exact ⟨e, related_implies_member C (C.view.lawful.symm he)⟩
  · rintro ⟨e, he⟩ x hx
    exact ⟨e, C.view.irrelevant rfl x (evaluate e) hx he⟩

def falseUnit : (GuardDecision.propCode False).Element :=
  ⟨GuardDecision.unit⟩

theorem falseUnit_not_member :
    ¬ (GuardDecision.propCode False).view.relation falseUnit falseUnit := by
  intro h
  exact (GuardDecision.propElement_unit_iff False).mp h

theorem falseUnit_unrelated (y : (GuardDecision.propCode False).Element) :
    ¬ (GuardDecision.propCode False).view.relation falseUnit y :=
  fun h => falseUnit_not_member (related_implies_member _ h)

/-- This failure concerns the actual old proposition carrier, independently
of how a retained source evaluator might be implemented. -/
theorem propFalse_no_total_carrier_realization
    {Source : Type v}
    (evaluate : Source → (GuardDecision.propCode False).Element) :
    ¬ ∀ x : (GuardDecision.propCode False).Element,
      ∃ e, (GuardDecision.propCode False).view.relation x (evaluate e) := by
  intro h
  exact falseUnit_not_member
    (total_realization_implies_all_members _ evaluate h falseUnit)

/-- A singleton proof normal form is compatible with proof irrelevance.
It is a normal form for proof terms only; proposition codes in their
universe retain their existing, nontrivial relation. -/
inductive ProofNF where
  | proof
  deriving DecidableEq

def reifyProof (P : Prop) (_x : (GuardDecision.propCode P).Element) : ProofNF :=
  .proof

def readbackProof (P : Prop)
    (_n : TypedNeutral (GuardDecision.propCode P).view.value) : ProofNF :=
  .proof

/-- This reflection covers every existing semantic neutral derivation,
including neutral application spines, and retains its actual raw image. -/
def reflectProof (P : Prop)
    (n : TypedNeutral (GuardDecision.propCode P).view.value) :
    (GuardDecision.propCode P).Element := ⟨n.value⟩

theorem reflectProof_member (P : Prop)
    (n : TypedNeutral (GuardDecision.propCode P).view.value) :
    (GuardDecision.propCode P).view.relation
      (reflectProof P n) (reflectProof P n) :=
  proposition_cr3.{0} (GuardDecision.propElement P) n.value n.neutral

theorem reflectProof_erasure (P : Prop)
    (n : TypedNeutral (GuardDecision.propCode P).view.value) :
    (GuardDecision.propCode P).erase (reflectProof P n) = n.value := rfl

theorem reifyProof_respect (P : Prop)
    (x y : (GuardDecision.propCode P).Element)
    (_h : (GuardDecision.propCode P).view.relation x y) :
    reifyProof P x = reifyProof P y := rfl

theorem proof_roundtrip (P : Prop)
    (n : TypedNeutral (GuardDecision.propCode P).view.value) :
    reifyProof P (reflectProof P n) = readbackProof P n := rfl

/-- Proof-term erasure does not identify distinct proposition codes. -/
theorem proof_erasure_preserves_code_separation :
    ¬ CodeRelated (GuardDecision.propCode False) (GuardDecision.propCode True) :=
  GuardDecision.propCode_false_true_not_related

/-! ## An admitted open proof-variable fragment

The source context is A : Prop, p : A, q : A, in de Bruijn order. Its
retained assignment binds A to the actual propCode P and both proof
variables to its reflected members. The retained evaluator below is the
literal lookup for these two source variables. Its erasure agrees with
EnvironmentEval, rather than being inferred from a reifier.
-/

abbrev typeContext : LCtxA := [.assumption (.sort .zero)]

def typeContextWf :
    CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 typeContext :=
  .assumption .nil (.sort [] .zero)

def firstTypeTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 typeContext
      (.bvar 0) (.sort .zero) :=
  .bvar typeContext 0 (.sort .zero) (.succ .zero) rfl
    (.sort typeContext .zero)

abbrev firstProofContext : LCtxA :=
  [.assumption (.bvar 0), .assumption (.sort .zero)]

def firstProofContextWf :
    CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 firstProofContext :=
  .assumption typeContextWf firstTypeTyped

def secondTypeTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 firstProofContext
      (.bvar 1) (.sort .zero) :=
  .bvar firstProofContext 1 (.sort .zero) (.succ .zero) rfl
    (.sort firstProofContext .zero)

abbrev proofContext : LCtxA :=
  [.assumption (.bvar 1), .assumption (.bvar 0), .assumption (.sort .zero)]

def proofContextWf :
    CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 proofContext :=
  .assumption firstProofContextWf secondTypeTyped

abbrev proofType : ExprA := .bvar 2

def proofTypeTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 proofContext
      proofType (.sort .zero) :=
  .bvar proofContext 2 (.sort .zero) (.succ .zero) rfl
    (.sort proofContext .zero)

inductive ProofVariable where
  | newest | older
  deriving DecidableEq

def proofIndex : ProofVariable → Nat
  | .newest => 0
  | .older => 1

def proofSource (v : ProofVariable) : ExprA := .bvar (proofIndex v)

def proofSourceTyped (v : ProofVariable) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 proofContext
      (proofSource v) proofType := by
  cases v with
  | newest => exact .bvar proofContext 0 proofType .zero rfl proofTypeTyped
  | older => exact .bvar proofContext 1 proofType .zero rfl proofTypeTyped

theorem source_proofs_distinct : proofSource .newest ≠ proofSource .older := by
  intro h
  cases h

theorem source_formation_packet :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 proofContext) ∧
    (∀ v, Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0
      proofContext (proofSource v) proofType)) :=
  ⟨⟨.empty⟩, ⟨proofContextWf⟩, fun v => ⟨proofSourceTyped v⟩⟩

def rawEnvironment (P : Prop) : EnvI :=
  EnvI.cons (NeutralPER.neutralAtom 0)
    (EnvI.cons (NeutralPER.neutralAtom 1)
      (EnvI.cons (GuardDecision.propCode P).view.value EnvI.bot))

/-- A retained type-variable binding; the code is supplied in the
environment and is not recovered from a raw value. -/
def retainedType (P : Prop) : Code.{0} 0 := GuardDecision.propCode P

theorem retainedType_member (P : Prop) :
    (universeCode.{0} 0).view.relation (retainedType P) (retainedType P) :=
  GuardDecision.propCode_universe_member P

def evaluateProof (P : Prop) (v : ProofVariable) :
    (GuardDecision.propCode P).Element := proofAtom P (proofIndex v)

theorem evaluateProof_member (P : Prop) (v : ProofVariable) :
    (GuardDecision.propCode P).view.relation
      (evaluateProof P v) (evaluateProof P v) :=
  proofAtom_member P (proofIndex v)

theorem environment_variable_image
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (i : Nat) (hb : ρ i .bot) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.bvar i)) (ρ i) := by
  apply (EnvironmentEval.denote_core E F ν ρ
    (e := .bvar i) True.intro).trans
  intro c
  change ApproxI ρ (.bvar i) c ↔ ρ i c
  constructor
  · intro h
    rcases approxI_bvar_inv h with he | hv
    · subst c
      exact hb
    · exact hv
  · exact ApproxI.bvar

theorem retainedType_image (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (P : Prop) :
    ValueEq (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment P) proofType)
      (retainedType P).view.value :=
  environment_variable_image emptyEnvA F ν (rawEnvironment P) 2 (Or.inl rfl)

theorem evaluateProof_image (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (P : Prop) (v : ProofVariable) :
    ValueEq
      (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment P) (proofSource v))
      ((GuardDecision.propCode P).erase (evaluateProof P v)) := by
  cases v with
  | newest =>
      exact environment_variable_image emptyEnvA F ν (rawEnvironment P) 0
        (ApproxI.bot EnvI.bot (.const 0 []))
  | older =>
      exact environment_variable_image emptyEnvA F ν (rawEnvironment P) 1
        (ApproxI.bot EnvI.bot (.const 1 []))

/-- The corrected member-qualified realization obligation holds for this
actual proposition generator and retained variable evaluator. The witness
is a well-typed open variable, not a closed proof of P. -/
theorem proposition_member_realized (P : Prop)
    (x : (GuardDecision.propCode P).Element)
    (hx : (GuardDecision.propCode P).view.relation x x) :
    ∃ v : ProofVariable,
      (GuardDecision.propCode P).view.relation x (evaluateProof P v) := by
  refine ⟨.newest, ?_⟩
  exact (GuardDecision.propCode P).view.irrelevant rfl _ _ hx
    (evaluateProof_member P .newest)

theorem proposition_member_realized_with_image
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (P : Prop)
    (x : (GuardDecision.propCode P).Element)
    (hx : (GuardDecision.propCode P).view.relation x x) :
    ∃ v : ProofVariable,
      (GuardDecision.propCode P).view.relation x (evaluateProof P v) ∧
      ValueEq
        (EnvironmentEval.denote emptyEnvA F ν (rawEnvironment P) (proofSource v))
        ((GuardDecision.propCode P).erase (evaluateProof P v)) := by
  obtain ⟨v, hv⟩ := proposition_member_realized P x hx
  exact ⟨v, hv, evaluateProof_image F ν P v⟩

/-- The separation hypothesis is witnessed by two distinct, well-typed
source proof variables in one admitted context. This still assumes literal
source readback; proof-erased readback deliberately omits that equation. -/
theorem no_literal_source_proof_reifier (P : Prop) :
    ¬ ∃ reify : (GuardDecision.propCode P).Element → ExprA,
      (∀ x y, (GuardDecision.propCode P).view.relation x y →
        reify x = reify y) ∧
      (∀ v, reify (evaluateProof P v) = proofSource v) :=
  no_separating_proof_readback (GuardDecision.propCode P)
    (evaluateProof P) (evaluateProof_member P) proofSource
    .newest .older source_proofs_distinct

theorem source_readback_boundary_packet (P : Prop) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 proofContext) ∧
    (∀ v, Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0
      proofContext (proofSource v) proofType)) ∧
    (∀ v, (GuardDecision.propCode P).view.relation
      (evaluateProof P v) (evaluateProof P v)) ∧
    ¬ ∃ reify : (GuardDecision.propCode P).Element → ExprA,
      (∀ x y, (GuardDecision.propCode P).view.relation x y →
        reify x = reify y) ∧
      (∀ v, reify (evaluateProof P v) = proofSource v) :=
  ⟨⟨.empty⟩, ⟨proofContextWf⟩, fun v => ⟨proofSourceTyped v⟩,
    evaluateProof_member P, no_literal_source_proof_reifier P⟩

end Rcic.Declarative.Ann.LR3.RCodeProofReadback
