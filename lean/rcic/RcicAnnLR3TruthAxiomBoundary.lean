import rcic.RcicAnnLR3TypedInductive

/-!
# An admitted empty proposition and an axiom at its empty carrier

`EnvWfA.axiomM` checks the axiom's type, not its semantic inhabitance.
The environment below is ordinary source syntax data. It introduces NO
Lean axiom. Every source premise, including the closed axiom typing and
concrete iota interface, is supplied.

A truth-valued least-fixed-point interpretation of the zero-constructor
family is empty. No choice of denotation for the axiom can lie in that
PER. Consequently all-EnvWfA model soundness cannot be obtained merely
by filling the 28 term/conversion arms. This does not refute sort
uniqueness, relative environment soundness, or the scoped Eq positives.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TruthAxiomBoundary
open Rcic.Declarative
open UnitModel TypedPER
open Rcic.Declarative.NativeValleys.PiModelIdealAudit

abbrev zero : Level := .zero
abbrev one : Level := .succ .zero

def emptyFamily : CheckedMemberA := ⟨.inductiveM, 0, .sort .zero, none, 0, none⟩
def familyEnv : ResolvedEnvA := extendEnvA emptyEnvA 80 emptyFamily
abbrev emptyType : ExprA := .const 80 []
def badAxiom : CheckedMemberA := ⟨.axiomM, 0, emptyType, none, 0, none⟩
def badEnv : ResolvedEnvA := extendEnvA familyEnv 81 badAxiom
abbrev badTerm : ExprA := .const 81 []

def emptyFamilyView : FamViewA emptyFamily where
  params := []
  indices := []
  sort := .zero
  stored := rfl
  nparams := rfl
  profile := .inl (fun _ => rfl)

def family_admitted (I : IotaIfaceA) : EnvWfA I familyEnv :=
  .group emptyEnvA 80 emptyFamily one .empty rfl rfl (fun _ => rfl)
    (.sort [] .zero) rfl emptyFamilyView [] rfl

def emptyType_typed {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (hm : E.members 80 = some emptyFamily) : HasTyA E I n Γ emptyType (.sort .zero) :=
  .const Γ 80 [] emptyFamily one hm rfl rfl (.sort Γ .zero)

def badEnv_admitted (I : IotaIfaceA) : EnvWfA I badEnv :=
  .axiomM familyEnv 81 emptyType .zero (family_admitted I) rfl
    (emptyType_typed rfl) (fun _ => rfl) rfl

def badTerm_typed (I : IotaIfaceA) : HasTyA badEnv I 0 [] badTerm emptyType :=
  .const [] 81 [] badAxiom .zero rfl rfl rfl (emptyType_typed rfl)

/-- The inductive evidence for the interpretation of an empty family. -/
abbrev EmptyEvidence : Prop := TypedInductive.Closure TypedInductive.emptySignature ()

/-- The least constructor closure for this family is empty. -/
theorem emptyEvidence_false (h : EmptyEvidence) : False := TypedInductive.emptyClosure_false h

def emptyCarrier : Relation := TruthPER EmptyEvidence

theorem emptyCarrier_no_member (x : Value) : ¬ Member emptyCarrier x :=
  fun h => emptyEvidence_false h.1

/-- The nonbottom unit itself cannot inhabit a false proposition. -/
theorem unit_not_in_empty : ¬ Member emptyCarrier (unitValue EnvI.bot) :=
  emptyCarrier_no_member _

/-- An environment interpreter is free to choose ANY image of the axiom;
none is a valid interpretation of this source declaration. -/
theorem no_axiom_denotation : ¬ ∃ x : Value, Member emptyCarrier x := by
  rintro ⟨x, hx⟩
  exact emptyCarrier_no_member x hx

/-- The exact constant-soundness leaf required by the source const arm,
with its lookup, type formation and source typing supplied separately. -/
def ConstantLeafSound (V : ExprA → Value) : Prop :=
  HasTyA badEnv (iotaIfaceA badEnv) 0 [] badTerm emptyType →
    Member emptyCarrier (V badTerm)

theorem constantLeafSound_false (V : ExprA → Value) : ¬ ConstantLeafSound V :=
  fun h => emptyCarrier_no_member _ (h (badTerm_typed (iotaIfaceA badEnv)))

/-- A relative environment realization may be empty. Admission alone
cannot supply such a realization when axioms must be genuine members. -/
def BadEnvRealises (interpretMember : Nat → Value) : Prop :=
  Member emptyCarrier (interpretMember 81)

theorem no_bad_environment_realization : ¬ ∃ μ, BadEnvRealises μ := by
  rintro ⟨μ, hμ⟩
  exact emptyCarrier_no_member _ hμ

theorem inhabited_constant_boundary :
    Nonempty (EnvWfA (iotaIfaceA badEnv) badEnv) ∧
    Nonempty (CtxWfA badEnv (iotaIfaceA badEnv) 0 []) ∧
    badEnv.members 80 = some emptyFamily ∧ badEnv.members 81 = some badAxiom ∧
    Nonempty (HasTyA badEnv (iotaIfaceA badEnv) 0 [] emptyType (.sort .zero)) ∧
    Nonempty (HasTyA badEnv (iotaIfaceA badEnv) 0 [] badTerm emptyType) ∧
    Laws emptyCarrier ∧
    (¬ ValueEq (unitValue EnvI.bot) bottom) ∧
    (∀ x : Value, ¬ Member emptyCarrier x) ∧
    (∀ V : ExprA → Value, ¬ ConstantLeafSound V) :=
  ⟨⟨badEnv_admitted _⟩, ⟨.nil⟩, rfl, rfl, ⟨emptyType_typed rfl⟩,
    ⟨badTerm_typed _⟩, truthPER_laws _, unit_nonbottom _,
    emptyCarrier_no_member, constantLeafSound_false⟩

end Rcic.Declarative.Ann.LR3.TruthAxiomBoundary
