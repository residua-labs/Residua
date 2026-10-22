import rcic.RcicAnnLR3SaturatedTower
import rcic.RcicAnnLR3CandidateActionProducts

/-!
# A typed-point tower is not full dependent-product saturation

The generated tower preserves universes and supplies common typed points.
Its level-only point policy is incompatible with the ordinary application
law for Pi P : Sort 0, Sort 0: applying the mandatory typed point yields a
third tag argument, outside every exact SortMember. Both universe
membership and mandatory target membership are supplied.

This diagnoses this completion policy only. Type-directed Pi reflection
can instead construct a function graph, as in SaturatedPiElements; that
repair is not refuted. No source Pi, SortUniq or ZSC counterexample is
claimed. closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SaturatedCandidatePiBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily

theorem native_typed_application_not_sort (i j : Option Nat) (name : Nat)
    (a : Value) (ha : a .bot) :
    ¬ SortMember j (NeutralPi.applyValue (NativeMemberValues.value i name) a) := by
  intro h
  have hf : NativeMemberValues.value i name (.spine 10 [.bot, .bot]) :=
    approxI_famApp 10 [] (.cons (.bot _ _) (.cons (.bot _ _) .nil))
  have ho : NeutralPi.applyValue (NativeMemberValues.value i name) a
      (.spine 10 [.bot, .bot, .bot]) :=
    Or.inr (Or.inr ⟨10, [.bot, .bot], .bot, rfl, hf, ha⟩)
  have ht := h _ ho
  cases ht

def domainCode : SaturatedTower.Code 0 :=
  SaturatedTower.completed 0 (NativeMemberValues.neutralCode 0 0)

def domainElement : StratifiedCandidates.Carrier 1 :=
  SaturatedTower.encode 0 domainCode

def rawArgument : Value := StratifiedCandidates.erase 1 domainElement

theorem rawArgument_bot : rawArgument .bot := NativeMemberValues.value_bot _ _

def UniverseMember (x : StratifiedCandidates.Carrier 1) : Prop :=
  (StratifiedCandidates.view 1 (SaturatedTower.universeCode 0).val).relation x x

theorem domain_member : UniverseMember domainElement :=
  SaturatedTower.universe_member 0 domainCode

/-- Only the ordinary unpaired application consequence is required. -/
def UniversePiApplication (P : SaturatedTower.Code 1) : Prop :=
  ∀ f x : StratifiedCandidates.Carrier 1,
    (StratifiedCandidates.view 1 P.val).relation f f →
    UniverseMember x →
    ∃ y : StratifiedCandidates.Carrier 1, UniverseMember y ∧
      ValueEq (NeutralPi.applyValue (StratifiedCandidates.erase 1 f)
        (StratifiedCandidates.erase 1 x)) (StratifiedCandidates.erase 1 y)

/-- Every target code has the offending point by its actual Closed proof.
The domain and codomain are both the generated universeCode 0. -/
theorem no_universe_pi_application (P : SaturatedTower.Code 1) :
    ¬ UniversePiApplication P := by
  intro h
  obtain ⟨y, hy, he⟩ := h (SaturatedTower.reflect 1 0) domainElement
    (P.property 0) domain_member
  have hs := (SaturatedTower.universe_elimination 0 y hy).1
  have happ := sortMember_congr he.symm hs
  rw [SaturatedTower.reflect_erasure] at happ
  exact native_typed_application_not_sort (some 0) (some 0) 0 rawArgument
    rawArgument_bot happ

def sourceImage (ν : Valuation) (ρ : EnvI) : Value :=
  EnvironmentEval.denote emptyEnvA EnvironmentEval.neutralFamilySyntax ν
    (EnvI.cons rawArgument
      (EnvI.cons (NativeMemberValues.value (some 0) 0) ρ))
    (.app (.bvar 1) (.bvar 0))

theorem source_image_application (ν : Valuation) (ρ : EnvI) :
    ValueEq (sourceImage ν ρ)
      (NeutralPi.applyValue (NativeMemberValues.value (some 0) 0) rawArgument) := by
  let σ := EnvI.cons rawArgument
    (EnvI.cons (NativeMemberValues.value (some 0) 0) ρ)
  apply (EnvironmentEval.denote_application emptyEnvA
    EnvironmentEval.neutralFamilySyntax ν σ (.bvar 1) (.bvar 0)).trans
  exact NeutralPi.applyValue_congr
    (CandidateAction.bound_image emptyEnvA EnvironmentEval.neutralFamilySyntax ν σ
      1 (NativeMemberValues.value (some 0) 0) rfl (NativeMemberValues.value_bot _ _))
    (CandidateAction.bound_image emptyEnvA EnvironmentEval.neutralFamilySyntax ν σ
      0 rawArgument rfl rawArgument_bot)

theorem source_image_not_sort (ν : Valuation) (ρ : EnvI) :
    ¬ SortMember (some 0) (sourceImage ν ρ) := by
  intro h
  exact native_typed_application_not_sort (some 0) (some 0) 0 rawArgument
    rawArgument_bot (sortMember_congr (source_image_application ν ρ) h)

/-- An actual source-Pi image at level one, before completion. -/
def sourcePiRaw (ν : Valuation) (ρ : EnvI) : StratifiedCandidates.Code 1 :=
  StratifiedCandidates.predicative 0
    (EnvironmentEval.denote emptyEnvA EnvironmentEval.neutralFamilySyntax ν ρ
      (CandidateActionSource.identityType 0))
    (CandidateActionProducts.source_pi_level emptyEnvA
      EnvironmentEval.neutralFamilySyntax ν ρ (.sort .zero) (.sort .zero)
      (.succ .zero) (.succ .zero))
    (CandidateActionProducts.source_pi_defined emptyEnvA
      EnvironmentEval.neutralFamilySyntax ν ρ (.sort .zero) (.sort .zero)
      (.succ .zero) (.succ .zero))
    (fun _ _ => False) ⟨False.elim, fun h _ => False.elim h⟩

def sourcePi (ν : Valuation) (ρ : EnvI) : SaturatedTower.Code 1 :=
  SaturatedTower.completed 1 (sourcePiRaw ν ρ)

theorem sourcePi_image (ν : Valuation) (ρ : EnvI) :
    (StratifiedCandidates.view 1 (sourcePi ν ρ).val).value =
      EnvironmentEval.denote emptyEnvA EnvironmentEval.neutralFamilySyntax ν ρ
        (CandidateActionSource.identityType 0) := rfl

abbrev one : Level := .succ .zero

def functionContext : LCtxA := [.assumption (CandidateActionSource.identityType 0)]

def function_context_wf :
    CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 functionContext :=
  .assumption .nil (CandidateActionSource.identity_formed [] 0)

def applicationContext : LCtxA := .assumption (.sort .zero) :: functionContext

def application_context_wf :
    CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext :=
  .assumption function_context_wf (.sort functionContext .zero)

def function_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext (.bvar 1)
      (CandidateActionSource.identityType 0) :=
  .bvar applicationContext 1 (CandidateActionSource.identityType 0)
    (.imax one one) rfl (CandidateActionSource.identity_formed applicationContext 0)

def argument_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext (.bvar 0)
      (.sort .zero) :=
  .bvar applicationContext 0 (.sort .zero) one rfl (.sort applicationContext .zero)

def application_typed :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext
      (.app (.bvar 1) (.bvar 0)) (.sort .zero) :=
  .app applicationContext (.bvar 1) (.bvar 0) (.sort .zero) (.sort .zero)
    one one one (.sort _ .zero) (.sort _ .zero) function_typed argument_typed

/-- The diagnosed contract has actual source admission and typing, an
actual generated target image, its mandatory point, and a legal universe
argument. No full semantic context or source rule is assumed. -/
theorem boundary_inhabited (ν : Valuation) (ρ : EnvI) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 applicationContext
      (.app (.bvar 1) (.bvar 0)) (.sort .zero)) ∧
    (StratifiedCandidates.view 1 (sourcePi ν ρ).val).value =
      EnvironmentEval.denote emptyEnvA EnvironmentEval.neutralFamilySyntax ν ρ
        (CandidateActionSource.identityType 0) ∧
    (StratifiedCandidates.view 1 (sourcePi ν ρ).val).relation
      (SaturatedTower.reflect 1 0) (SaturatedTower.reflect 1 0) ∧
    UniverseMember domainElement ∧
    (¬ UniversePiApplication (sourcePi ν ρ)) ∧
    (¬ SortMember (some 0) (sourceImage ν ρ)) :=
  ⟨⟨.empty⟩, ⟨application_context_wf⟩, ⟨application_typed⟩, sourcePi_image ν ρ,
    (sourcePi ν ρ).property 0, domain_member,
    no_universe_pi_application _, source_image_not_sort ν ρ⟩

end Rcic.Declarative.Ann.LR3.SaturatedCandidatePiBoundary
