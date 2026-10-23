import rcic.RcicAnnLR3TaggedPiControls

/-!
# A concrete positive Pi code for the large-K minor

The source type is Pi P : Prop, Prop. Its domain retains all closed
proposition codes, and its constant codomain is the saturated Prop
universe. Body image, relatedness, saturation and an inhabited argument
are all constructed. Every actual action produces a Prop-universe member
at that argument, excluding native typed points as function erasures.

This is the concrete minor needed for the K coherence test; the general
product over the entire heterogeneous Code 1 is not asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TaggedKPiFixture
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateActionProducts

abbrev one : Level := .succ .zero

private theorem sort_zero_image
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (σ : EnvI) :
    ValueEq (EnvironmentEval.denote E F ν σ (.sort .zero)) (universeValue (some 0)) := by
  rw [show EnvironmentEval.denote E F ν σ (.sort .zero) = universeValue (some 0) from
    (EnvironmentEval.annSemantics NeutralCodes.codeSystem E F).sort_image ν [] σ .zero]
  exact ValueEq.refl _

def codomainCode : CandidateAction.ClosedCode 1 :=
  ⟨(SaturatedTower.universeCode 0).1,
    ApproxI.bot EnvI.bot (sortTerm (some 0))⟩

def body (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    Body (CandidateAction.ClosedCode 0) CandidateAction.eraseCode CandidateAction.CodeRel
      E F ν ρ (.sort .zero) 1 where
  run := fun _ => codomainCode
  image := fun C => sort_zero_image E F ν (EnvI.cons (CandidateAction.eraseCode C) ρ)
  respect := fun _ _ _ => CandidateAction.codeRel_refl codomainCode

theorem body_closed
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (C : CandidateAction.ClosedCode 0) :
    SaturatedTower.Closed 1 ((body E F ν ρ).run C).code :=
  SaturatedTower.universe_closed 0

def code (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) : TaggedSaturatedTower.Code.{0} 1 :=
  TaggedSaturatedTower.piCode (k := 0) (n := 0) (body E F ν ρ)
    (CandidateAction.codeRel_laws 0) (body_closed E F ν ρ)
    (.sort .zero) one one (by rfl) (by rfl)

theorem code_image
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    (code E F ν ρ).view.value =
      EnvironmentEval.denote E F ν ρ EqLargeFixture.result := rfl

theorem code_tag
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) : (code E F ν ρ).tag = .pi := rfl

def argument : CandidateAction.ClosedCode 0 :=
  ⟨NativeMemberValues.neutralCode 0 0, NativeMemberValues.neutralCode_bot 0 0⟩

theorem argument_member : CandidateAction.CodeRel argument argument :=
  CandidateAction.codeRel_refl argument

theorem argument_bot : CandidateAction.eraseCode argument .bot := argument.bot

theorem reflection_member
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (name : Nat) :
    (code E F ν ρ).view.relation
      ((code E F ν ρ).view.point name) ((code E F ν ρ).view.point name) :=
  (code E F ν ρ).view.point_member name

theorem run_member
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (code E F ν ρ).Element)
    (C : CandidateAction.ClosedCode 0) :
    SaturatedTower.UniverseRel 0 (f.run C) (f.run C) :=
  f.respect C C (CandidateAction.codeRel_refl C)

theorem application_sort
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (code E F ν ρ).Element)
    (C : CandidateAction.ClosedCode 0) :
    SortMember (some 0)
      (NeutralPi.applyValue ((code E F ν ρ).erase f) (CandidateAction.eraseCode C)) :=
  sortMember_congr (f.erased C).symm
    (SaturatedTower.universe_elimination 0 (f.run C) (run_member E F ν ρ f C)).1

theorem no_native_element
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (f : (code E F ν ρ).Element)
    (i : Option Nat) (name : Nat) :
    ¬ ValueEq ((code E F ν ρ).erase f) (NativeMemberValues.value i name) := by
  intro hf
  have he := NeutralPi.applyValue_congr hf
    (ValueEq.refl (CandidateAction.eraseCode argument))
  have hs := sortMember_congr he (application_sort E F ν ρ f argument)
  exact SaturatedCandidatePiBoundary.native_typed_application_not_sort
    i (some 0) name (CandidateAction.eraseCode argument) argument_bot hs

theorem native_not_erased_member
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (i : Option Nat) (name : Nat) :
    ¬ ∃ f : (code E F ν ρ).Element,
      (code E F ν ρ).view.relation f f ∧
        ValueEq ((code E F ν ρ).erase f) (NativeMemberValues.value i name) := by
  rintro ⟨f, _, he⟩
  exact no_native_element E F ν ρ f i name he

theorem code_inhabited
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    ∃ f : (code E F ν ρ).Element, (code E F ν ρ).view.relation f f :=
  ⟨(code E F ν ρ).view.point 0, reflection_member E F ν ρ 0⟩

def source_formed {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} (Γ : LCtxA) :
    HasTyA E I n Γ EqLargeFixture.result (.sort one) :=
  EqLargeFixture.resultTyped

theorem source_application_premises :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0
      SaturatedCandidatePiBoundary.applicationContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0
      SaturatedCandidatePiBoundary.applicationContext
      (.app (.bvar 1) (.bvar 0)) (.sort .zero)) :=
  ⟨⟨.empty⟩, ⟨SaturatedCandidatePiBoundary.application_context_wf⟩,
    ⟨SaturatedCandidatePiBoundary.application_typed⟩⟩

theorem universe_member
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    (TaggedSaturatedTower.universeCode.{0} 1).view.relation
      (TaggedSaturatedTower.universeEncode 1 (code E F ν ρ))
      (TaggedSaturatedTower.universeEncode 1 (code E F ν ρ)) :=
  TaggedSaturatedTower.universe_member 1 (code E F ν ρ)

end Rcic.Declarative.Ann.LR3.TaggedKPiFixture
