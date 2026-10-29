import rcic.RcicAnnLR3RCodeSoundPi

/-!
# An inhabited uniform section with a sound domain and sound fibres

The native neutral proposition code supplies the domain. Each retained
extension has the same proposition code but its own actual source point:
the newly bound variable. Thus the common body is literally that variable,
its retained evaluation is the argument itself, and transport is identity.
The source type and the evaluator image are proved in the extended context.

This constructs the Family and Section data used by SoundPi with no
existence hypotheses, complementing its genuinely varying Bool fibres.
The present fibres are constant at the code level; this is not a general
Pi generator or a fresh-variable readback/naturality theorem.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RCodeSoundPiControl

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower RCodeSoundInterface RCodeSoundPi

/-- Every constructed neutral spine contains the inherited bottom observation.
This is a property of that constructed spine, not of arbitrary raw values. -/
theorem neutral_bot {x : Value} (h : CandidatePi.Neutral x) : x .bot := by
  cases h with
  | atom name => exact .bot _ _
  | app _ _ _ => exact Or.inl rfl

def domain (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :=
  RCodeSoundZeroInstances.neutral F ν name

abbrev codomain : ExprA := .bvar 3
abbrev body : ExprA := .bvar 0

def codomainTyped (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) (x : (domain F ν name).Element) :
    HasTyA (extend (domain F ν name) x).env (extend (domain F ν name) x).iota
      (extend (domain F ν name) x).levelCount (extend (domain F ν name) x).context
      codomain (.sort .zero) :=
  .bvar _ 3 (.sort .zero) (.succ .zero) rfl (.sort _ .zero)

def bodyTyped (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) (x : (domain F ν name).Element) :
    HasTyA (extend (domain F ν name) x).env (extend (domain F ν name) x).iota
      (extend (domain F ν name) x).levelCount (extend (domain F ν name) x).context
      body codomain :=
  .bvar _ 0 codomain .zero rfl (codomainTyped F ν name x)

theorem codomain_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) (x : (domain F ν name).Element) :
    ValueEq ((extend (domain F ν name) x).evaluate codomain)
      (domain F ν name).code.view.value :=
  RCodeProofReadback.environment_variable_image emptyEnvA F ν
    (extend (domain F ν name) x).rawEnvironment 3
    (NativeMemberValues.value_bot (some 0) name)

theorem body_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) (x : (domain F ν name).Element) :
    ValueEq ((extend (domain F ν name) x).evaluate body)
      ((domain F ν name).erase x) :=
  RCodeProofReadback.environment_variable_image emptyEnvA F ν
    (extend (domain F ν name) x).rawEnvironment 0 (neutral_bot x.val.down.neutral)

def fibre (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) (x : (domain F ν name).Element) :
    RCodeSound.{0,0} (extend (domain F ν name) x) 0 :=
  RCodeSoundZeroInstances.ofPoint (extend (domain F ν name) x)
    (domain F ν name).code codomain (codomainTyped F ν name x)
    (codomain_image F ν name x) (GuardedKernel.nativeNeutralReflector 0 name)
    ⟨body, bodyTyped F ν name x⟩ x (body_image F ν name x).symm

def family (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    Family (domain F ν name) 0 codomain .zero where
  fibre := fibre F ν name
  source_type := fun _ => rfl
  source_level := fun _ => rfl
  transport := fun _ _ _ => KernelIso.refl _

def uniformSection (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (name : Nat) :
    Section (family F ν name) where
  body := body
  fragment := fun _ => .basepoint
  source_eq := fun _ => rfl
  respect := fun _ _ h => h

theorem section_run (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) (x : (domain F ν name).Element) :
    ((uniformSection F ν name).sourceBody.run x).val = x.val := rfl

theorem section_erasure (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) (x : (domain F ν name).Element) :
    ValueEq (NeutralPi.applyValue (uniformSection F ν name).action.value
      ((domain F ν name).erase x)) ((domain F ν name).erase x) :=
  (uniformSection F ν name).application x

def section_lambda_typed (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 RCodeProofReadback.proofContext
      (.lam RCodeProofReadback.proofType .zero body)
      (.pi RCodeProofReadback.proofType .zero codomain .zero) :=
  (uniformSection F ν name).lambdaTyped

theorem section_readback (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) (x : (domain F ν name).Element) :
    (fibre F ν name x).ReadsBack .basepoint x ⟨body, bodyTyped F ν name x⟩ :=
  (uniformSection F ν name).readback x

theorem inhabited_sound_section (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (name : Nat) :
    Nonempty (Section (family F ν name)) ∧
    (∀ x : (domain F ν name).Element,
      Nonempty (RCodeSound.{0,0} (extend (domain F ν name) x) 0)) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 RCodeProofReadback.proofContext
      (.lam RCodeProofReadback.proofType .zero body)
      (.pi RCodeProofReadback.proofType .zero codomain .zero)) :=
  ⟨⟨uniformSection F ν name⟩, fun x => ⟨fibre F ν name x⟩,
    ⟨section_lambda_typed F ν name⟩⟩

end Rcic.Declarative.Ann.LR3.RCodeSoundPiControl
