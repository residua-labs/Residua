import rcic.RcicAnnLR3RCodeSoundZeroInstances
import rcic.RcicAnnLR3CandidateActionProducts
import rcic.RcicAnnLR3IotaLiftLaw
import rcic.RcicAnnLR3RCodeSoundPiControl

/-!
# The impredicative Pi probe: Prop codomain over a domain of any size

**Formation is size-correct.** For a domain of any size α (any `Sort w`,
for instance the carrier of a universe code) and any family of membership
predicates on Prop fibres, `impCode` is a level-zero certified proposition
code in every host universe `u`. Its members are the raw values containing
the bottom observation whose application to every domain member lands in
its fibre, together with all neutrals. The quantification is a Prop, so it
does not raise the host universe. In particular the code over the bot-closed
Prop codes of host universe `u` is itself such a code
(`impredicative_self_member`).

**Realizability by the retained evaluator holds at lambda.** If the body's
evaluation in every extended environment lies in its fibre, then the actual
evaluation of the lambda is a member (`lambda_member`). Application of a
member lands in the fibre (`application_member`).

**Boundary: quantification over all candidates.** The universe of all
certified level-zero codes contains a proposition code with a member lacking
the bottom observation. The evaluator always adds bottom to a variable's
image. So the actual evaluation of the typed closed identity
`λ (X : Prop) (x : X). x` is not a member of the impredicative product over
the full universe (`full_universe_identity_boundary`). All premises are
constructed: admitted source typing, the certified code and its member.
This is the variable-lookup residual `ImageBvarRel` of `PairedLookup`,
forced by impredicative quantification.

**Repair.** On the bot-closed sub-universe the residual is discharged, and
that sub-universe is closed under `impCode` for any domain size. The
identity is then realized. `identitySound` is an actual `RCodeSound`
instance for `∀ X : Prop, X → X`, with domain the bot-closed Prop universe
(a universe code) and its realizing point the actual evaluation of the typed
identity. Whether every source proposition's code is bot-closed is the
remaining obligation for the Prop universe of the model. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ImpredicativePiProbe

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements RCodeSoundInterface

universe u w

/-! ## Impredicative formation -/

/-- Membership in a Prop-valued product: bottom-containing values whose
applications land in the fibres, or neutrals. -/
def ImpMember {α : Sort w} (erase : α → Value) (D : α → Prop)
    (Fib : α → Value → Prop) (f : Value) : Prop :=
  (f .bot ∧ ∀ x, D x → Fib x (NeutralPi.applyValue f (erase x))) ∨ CandidatePi.Neutral f

def impElement {α : Sort w} (erase : α → Value) (D : α → Prop)
    (Fib : α → Value → Prop) (V : Value) (hV : SortMember (some 0) V)
    (hd : TypeDefined V) : CandidatePi.Element where
  value := V
  candidate := CandidateUniverse.predicateCandidate (ImpMember erase D Fib)
  level := hV
  defined := hd

/-- A certified level-zero code in every host universe `u`, for every domain
size `w`. -/
def impCode {α : Sort w} (erase : α → Value) (D : α → Prop)
    (Fib : α → Value → Prop) (V : Value) (hV : SortMember (some 0) V)
    (hd : TypeDefined V) : GuardedTaggedCode.Code.{u} 0 :=
  .legacy (TaggedSaturatedTower.Code.proposition (impElement erase D Fib V hV hd))

theorem impCode_member_iff {α : Sort w} (erase : α → Value) (D : α → Prop)
    (Fib : α → Value → Prop) (V : Value) (hV : SortMember (some 0) V)
    (hd : TypeDefined V) (f : Value) :
    (impCode.{u} erase D Fib V hV hd).view.relation ⟨f⟩ ⟨f⟩ ↔ ImpMember erase D Fib f := by
  change Member (CandidatePi.complete (CandidateUniverse.predicateCandidate
    (ImpMember erase D Fib))).relation f ↔ _
  rw [CandidatePi.complete_member_iff, CandidateUniverse.predicateCandidate_member]
  constructor
  · rintro (h | h)
    · exact h
    · exact Or.inr h
  · exact Or.inl

theorem impCode_value {α : Sort w} (erase : α → Value) (D : α → Prop)
    (Fib : α → Value → Prop) (V : Value) (hV : SortMember (some 0) V)
    (hd : TypeDefined V) : (impCode.{u} erase D Fib V hV hd).view.value = V := rfl

/-- Application of a member lands in the fibre. -/
theorem application_member {α : Sort w} {erase : α → Value} {D : α → Prop}
    {Fib : α → Value → Prop}
    (hneu : ∀ x, D x → ∀ v, CandidatePi.Neutral v → Fib x v)
    (hne : ∀ x, D x → CandidatePi.NonemptyValue (erase x))
    {f : Value} (hf : ImpMember erase D Fib f) {x : α} (hx : D x) :
    Fib x (NeutralPi.applyValue f (erase x)) := by
  rcases hf with ⟨_, h⟩ | hn
  · exact h x hx
  · exact hneu x hx _ (.app hn _ (hne x hx))

/-- Realizability at lambda: the body IH gives membership of the actual
evaluation of the lambda. -/
theorem lambda_member {α : Sort w} {erase : α → Value} {D : α → Prop}
    {Fib : α → Value → Prop}
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (A body : ExprA) (l : Level)
    (hbody : ∀ x, D x → Fib x (EnvironmentEval.denote E F ν (EnvI.cons (erase x) ρ) body)) :
    ImpMember erase D Fib (EnvironmentEval.denote E F ν ρ (.lam A l body)) := by
  refine Or.inl ⟨EnvironmentEval.denote_bot E F ν ρ _, fun x hx => ?_⟩
  rw [NeutralCodes.valueEq_eq
    (EnvironmentEval.denote_lambda_application E F ν ρ A body l (erase x))]
  exact hbody x hx

/-! ## Bot-closed level-zero codes -/

def BotClosed (X : GuardedTaggedCode.Code.{u} 0) : Prop :=
  ∀ a : X.Element, X.view.relation a a → X.erase a .bot

/-- Impredicative products are bot-closed, for every domain size. -/
theorem impCode_botClosed {α : Sort w} (erase : α → Value) (D : α → Prop)
    (Fib : α → Value → Prop) (V : Value) (hV : SortMember (some 0) V)
    (hd : TypeDefined V) : BotClosed (impCode.{u} erase D Fib V hV hd) := by
  intro a ha
  rcases (impCode_member_iff.{u} erase D Fib V hV hd a.down).mp ha with ⟨hb, _⟩ | hn
  · exact hb
  · exact RCodeSoundPiControl.neutral_bot hn

abbrev BotCode := {X : GuardedTaggedCode.Code.{u} 0 // BotClosed X}

theorem neutral_botClosed (name : Nat) :
    BotClosed (GuardedTaggedCode.Code.legacy (TaggedSaturatedTower.Code.neutral.{u} 0 name)) :=
  fun a _ => RCodeSoundPiControl.neutral_bot a.down.neutral

def botNeutral (name : Nat) : BotCode.{u} := ⟨_, neutral_botClosed name⟩

/-- The bot-closed Prop codes form an actual certified universe code at level
one, with conversion as its relation and native neutral points. -/
def botUniverseLegacy : TaggedSaturatedTower.Code.{u+1} 1 where
  kernel := TaggedSaturatedTower.universeKernel 0 BotCode.{u}
    (fun X => TaggedSaturatedTower.raiseKernel.{u, u+1} X.1.kernel)
    (fun X Y => GuardedTaggedCode.Converts X.1 Y.1)
    ⟨fun h => GuardedTaggedCode.converts_symm h, fun h g => GuardedTaggedCode.converts_trans h g⟩
    botNeutral (fun X => GuardedTaggedCode.converts_refl X.1)
  tag := .univ
  witness := .univ 0 BotCode.{u}
    (fun X => TaggedSaturatedTower.raiseKernel.{u, u+1} X.1.kernel)
    (fun X Y => GuardedTaggedCode.Converts X.1 Y.1)
    ⟨fun h => GuardedTaggedCode.converts_symm h, fun h g => GuardedTaggedCode.converts_trans h g⟩
    botNeutral (fun X => GuardedTaggedCode.converts_refl X.1)
    (fun _ _ h => TaggedSaturatedTower.kernelRelated_raise.{u, u, u+1} h)
    (fun _ => ValueEq.refl _)

def botUniverse : GuardedTaggedCode.Code.{u+1} 1 := .legacy botUniverseLegacy.{u}

theorem botUniverse_image : botUniverse.{u}.view.value = universeValue (some 0) := rfl

theorem botUniverse_erase (X : BotCode.{u}) : botUniverse.{u}.erase X = X.1.view.value := rfl

theorem botUniverse_member (X : BotCode.{u}) : botUniverse.{u}.view.relation X X :=
  GuardedTaggedCode.converts_refl X.1

def Good (X : GuardedTaggedCode.Code.{u} 0) (v : Value) : Prop :=
  GuardedTaggedCode.Good X.kernel v

/-- The fibre of `X → X` at a level-zero code `X`. -/
def selfFibre (X : GuardedTaggedCode.Code.{u} 0) : Value → Prop :=
  ImpMember (α := X.Element) X.erase (fun a => X.view.relation a a) (fun _ => Good X)

/-- The impredicative product over all bot-closed Prop codes of host universe
`u` is itself one of them. -/
theorem impredicative_self_member (V : Value) (hV : SortMember (some 0) V)
    (hd : TypeDefined V) :
    BotClosed (impCode.{u} (α := BotCode.{u}) (fun X => X.1.view.value) (fun _ => True)
      (fun X => selfFibre X.1) V hV hd) :=
  impCode_botClosed _ _ _ V hV hd

/-! ## The typed closed identity -/

abbrev innerType : ExprA := .pi (.bvar 0) .zero (.bvar 1) .zero
abbrev identityType : ExprA := .pi (.sort .zero) (.succ .zero) innerType (.imax .zero .zero)
abbrev innerLambda : ExprA := .lam (.bvar 0) .zero (.bvar 0)
abbrev identityTerm : ExprA := .lam (.sort .zero) (.succ .zero) innerLambda

abbrev ctx1 : LCtxA := [.assumption (.sort .zero)]
abbrev ctx2 : LCtxA := [.assumption (.bvar 0), .assumption (.sort .zero)]

def sortTyped : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort [] .zero

def xTyped : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 ctx1 (.bvar 0) (.sort .zero) :=
  .bvar ctx1 0 (.sort .zero) (.succ .zero) rfl (.sort ctx1 .zero)

def xTyped2 : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 ctx2 (.bvar 1) (.sort .zero) :=
  .bvar ctx2 1 (.sort .zero) (.succ .zero) rfl (.sort ctx2 .zero)

def innerTypeTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 ctx1 innerType (.sort (.imax .zero .zero)) :=
  .pi ctx1 (.bvar 0) .zero (.bvar 1) .zero xTyped xTyped2

def identityTypeTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] identityType
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) innerType (.imax .zero .zero) sortTyped innerTypeTyped

def innerLambdaTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 ctx1 innerLambda innerType :=
  .lam ctx1 (.bvar 0) .zero (.bvar 0) (.bvar 1) .zero xTyped xTyped2
    (.bvar ctx2 0 (.bvar 1) .zero rfl xTyped2)

def identityTermTyped :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] identityTerm identityType :=
  .lam [] (.sort .zero) (.succ .zero) innerLambda innerType (.imax .zero .zero)
    sortTyped innerTypeTyped innerLambdaTyped

/-- The identity's type is a proposition: its sort converts to `Sort 0`. -/
def identityTypeProp :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] identityType (.sort .zero) :=
  .conv [] identityType (.sort (.imax (.succ .zero) (.imax .zero .zero))) (.sort .zero)
    (.succ (.imax (.succ .zero) (.imax .zero .zero))) (.succ .zero)
    identityTypeTyped (.sort [] _) (fun _ => rfl) (.sort [] .zero)
    (.symm _ _ _ _ (.sorts [] .zero _ (fun _ => rfl)))

/-! ## Boundary over the full universe of certified Prop codes -/

def badMembers (v : Value) : Prop := v = CandidatePi.emptyValue

def badElement : CandidatePi.Element where
  value := NativeMemberValues.value (some 0) 0
  candidate := CandidateUniverse.predicateCandidate badMembers
  level := NativeMemberValues.value_level (some 0) 0
  defined := NativeMemberValues.value_defined (some 0) 0

/-- A certified level-zero code: an element of the conversion Prop universe. -/
def badCode : GuardedTaggedCode.Code.{0} 0 :=
  .legacy (TaggedSaturatedTower.Code.proposition badElement)

def badMember : badCode.Element := ⟨CandidatePi.emptyValue⟩

theorem badMember_member : badCode.view.relation badMember badMember := by
  change Member (CandidatePi.complete (CandidateUniverse.predicateCandidate
    badMembers)).relation CandidatePi.emptyValue
  rw [CandidatePi.complete_member_iff, CandidateUniverse.predicateCandidate_member]
  exact Or.inl rfl

theorem badCode_not_botClosed : ¬ BotClosed badCode := by
  intro h
  exact h badMember badMember_member

theorem bottom_not_good : ¬ Good badCode bottom := by
  rintro ⟨a, ha, he⟩
  have hm : Member (CandidatePi.complete (CandidateUniverse.predicateCandidate
      badMembers)).relation a.down := ha
  rw [CandidatePi.complete_member_iff, CandidateUniverse.predicateCandidate_member] at hm
  have he' : a.down = bottom := NeutralCodes.valueEq_eq he
  rcases hm with hm | hm
  · have hb : CandidatePi.emptyValue .bot := by
      rw [← hm, he']
      rfl
    exact hb
  · exact CandidatePi.bottom_not_neutral (he' ▸ hm)

theorem bvar_empty_image (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    EnvironmentEval.denote E F ν (EnvI.cons CandidatePi.emptyValue ρ) (.bvar 0) = bottom := by
  rw [IotaRecursor.denote_bvar]
  funext c
  apply propext
  constructor
  · intro h
    rcases approxI_bvar_inv h with h | h
    · exact h
    · exact h.elim
  · intro h
    rw [show c = .bot from h]
    exact .bot _ _

theorem lambda_not_neutral (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A body : ExprA) (l : Level) :
    ¬ CandidatePi.Neutral (EnvironmentEval.denote E F ν ρ (.lam A l body)) := by
  intro hn
  have hobs := (EnvironmentEval.denote_lambda_graph E F ν ρ A body l (.lam [])).mpr
    (UnifiedPi.legalGraph_observed _ _)
  rcases CandidatePi.neutral_spineOnly hn _ hobs with h | ⟨_, _, h⟩ <;> cases h

/-- Over all candidates, the actual evaluation of the typed closed identity
is not a member of the impredicative product. -/
theorem full_universe_identity_boundary (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] identityTerm identityType) ∧
    badCode.view.relation badMember badMember ∧
    ¬ BotClosed badCode ∧
    ¬ ImpMember (α := GuardedTaggedCode.Code.{0} 0) (fun X => X.view.value) (fun _ => True)
      (fun X => selfFibre X)
      (EnvironmentEval.denote emptyEnvA F ν EnvI.bot identityTerm) := by
  refine ⟨⟨.empty⟩, ⟨identityTermTyped⟩, badMember_member, badCode_not_botClosed, ?_⟩
  rintro (⟨_, h⟩ | hn)
  · have hf := h badCode True.intro
    rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application emptyEnvA F ν
      EnvI.bot (.sort .zero) innerLambda (.succ .zero) badCode.view.value)] at hf
    rcases hf with ⟨_, hg⟩ | hn
    · have hb := hg badMember badMember_member
      rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application emptyEnvA F ν
        _ (.bvar 0) (.bvar 0) .zero (badCode.erase badMember))] at hb
      have he : badCode.erase badMember = CandidatePi.emptyValue := rfl
      rw [he, bvar_empty_image] at hb
      exact bottom_not_good hb
    · exact lambda_not_neutral _ _ _ _ _ _ _ hn
  · exact lambda_not_neutral _ _ _ _ _ _ _ hn

/-! ## Repair: the bot-closed Prop universe -/

def identityWorld (F : EnvironmentEval.FamilySyntax) (ν : Valuation) : World where
  env := emptyEnvA
  iota := iotaIfaceA emptyEnvA
  levelCount := 0
  context := []
  family := F
  valuation := ν
  rawEnvironment := EnvI.bot
  envWf := .empty
  contextWf := .nil

theorem identityType_level (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    SortMember (some 0) ((identityWorld F ν).evaluate identityType) := by
  have h := CandidateActionProducts.source_pi_level emptyEnvA F ν EnvI.bot
    (.sort .zero) innerType (.succ .zero) (.imax .zero .zero)
  have he : eval ν (.imax (.succ .zero) (.imax .zero .zero)) = some 0 := rfl
  rw [he] at h
  exact h

theorem identityType_defined (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    TypeDefined ((identityWorld F ν).evaluate identityType) :=
  CandidateActionProducts.source_pi_defined emptyEnvA F ν EnvI.bot _ _ _ _

/-- The impredicative product over the bot-closed Prop universe, with the
actual evaluator image of the source type. -/
def identityCode (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    GuardedTaggedCode.Code.{0} 0 :=
  impCode.{0} (α := BotCode.{0}) (fun X => X.1.view.value) (fun _ => True)
    (fun X => selfFibre X.1) ((identityWorld F ν).evaluate identityType)
    (identityType_level F ν) (identityType_defined F ν)

/-- The identity's product quantifies over the elements of the certified
bot-closed universe code, and its own code is one of those elements. -/
theorem identityCode_in_universe (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    (∀ X : botUniverse.{0}.Element, botUniverse.{0}.erase X = X.1.view.value) ∧
    ∃ X : botUniverse.{0}.Element, X.1 = identityCode F ν ∧ botUniverse.view.relation X X :=
  ⟨fun _ => rfl, ⟨⟨identityCode F ν, impCode_botClosed _ _ _ _ _ _⟩, rfl,
    botUniverse_member _⟩⟩

/-- The repaired variable residual: a bot-closed member is its own image. -/
theorem botClosed_variable (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (X : BotCode.{0}) (a : X.1.Element)
    (ha : X.1.view.relation a a) :
    Good X.1 (EnvironmentEval.denote E F ν (EnvI.cons (X.1.erase a) ρ) (.bvar 0)) :=
  ⟨a, ha, (RCodeProofReadback.environment_variable_image E F ν
    (EnvI.cons (X.1.erase a) ρ) 0 (X.2 a ha)).symm⟩

/-- Realizability by the retained evaluator over every bot-closed Prop
code, including impredicative ones: two applications of `lambda_member`. -/
theorem identity_realized (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    ImpMember (α := BotCode.{0}) (fun X => X.1.view.value) (fun _ => True)
      (fun X => selfFibre X.1)
      ((identityWorld F ν).evaluate identityTerm) :=
  lambda_member emptyEnvA F ν EnvI.bot (.sort .zero) innerLambda (.succ .zero)
    (fun X _ => lambda_member emptyEnvA F ν _ (.bvar 0) (.bvar 0) .zero
      (fun a ha => botClosed_variable emptyEnvA F ν _ X a ha))

def identityPoint (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    Member (identityCode F ν) :=
  ⟨⟨(identityWorld F ν).evaluate identityTerm⟩,
    (impCode_member_iff _ _ _ _ _ _ _).mpr (identity_realized F ν)⟩

/-- An actual RCodeSound instance for `∀ X : Prop, X → X`, whose domain is
the bot-closed Prop universe and whose realizing point is the evaluator's
image of the typed identity. -/
def identitySound (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    RCodeSound.{0,0} (identityWorld F ν) 0 :=
  RCodeSoundZeroInstances.ofPoint (identityWorld F ν) (identityCode F ν) identityType
    identityTypeProp (ValueEq.refl _)
    (GuardedKernel.propositionReflector.{0} _) ⟨identityTerm, identityTermTyped⟩
    (identityPoint F ν) (ValueEq.refl _)

theorem identitySound_packet (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    BotClosed (identityCode F ν) ∧
    (identitySound F ν).ReadsBack .basepoint (identityPoint F ν)
      ⟨identityTerm, identityTermTyped⟩ ∧
    (∀ x : (identitySound F ν).Element,
      ∃ s, (identitySound F ν).ReadsBack s x ((identitySound F ν).source s)) :=
  ⟨impCode_botClosed _ _ _ _ _ _, (identitySound F ν).readback_total .basepoint,
    (identitySound F ν).member_readback⟩

end Rcic.Declarative.Ann.LR3.ImpredicativePiProbe
