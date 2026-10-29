import rcic.RcicAnnLR3ImpredicativePiProbe
import rcic.RcicAnnLR3CandidateTowerProbe
import rcic.RcicAnnLR3OptionSoundInterface

/-!
# Nonvacuity checks for the unpublished model conditions

Two conditions of this line have no published model: the bot-closed Prop
universe (with its Girard-style counterpart, saturated candidates) and the
chaotic none level. Each check pairs an inhabited instance with a mutant
that drops the condition, and shows the mutant fails.

**Bot-closed Prop universe** (`botClosed_nonvacuity`). Inhabited: the
certified universe code `botUniverse` has members, including a neutral code
and the impredicative identity product; the identity is realized and has an
actual `RCodeSound` instance. Mutant: drop bot-closure, i.e. quantify over all
certified Prop codes; then the same evaluator image is not realized.

**Saturated candidates** (`saturation_nonvacuity`). Inhabited: the Girard
reading of `∀ X : Prop, X → X` is realized by the typed identity.
Mutant: allow a non-saturated PER as the candidate; then the inner clause
of that reading fails for the same evaluator image.

**Chaotic none level** (`none_nonvacuity`). Inhabited: a none-level
`RCodeSoundO` instance in an admitted world, and the none universe with its
self member. Mutant 1: relate all none universe elements; this contradicts
the universe relation being conversion of the decoded codes. Mutant 2: admit
the universe's own image as an ordinary chaotic code; then two codes with
one raw image get different relations, so the raw algebra is incoherent.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.NonvacuityChecks

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements RCodeSoundInterface

/-! ## Bot-closed Prop universe -/

theorem botClosed_nonvacuity (F : EnvironmentEval.FamilySyntax) (ν : Valuation) :
    -- inhabited: members of the certified bot-closed universe
    (∃ X : ImpredicativePiProbe.botUniverse.{0}.Element,
      ImpredicativePiProbe.botUniverse.view.relation X X) ∧
    (∃ X : ImpredicativePiProbe.botUniverse.{0}.Element,
      X.1 = ImpredicativePiProbe.identityCode F ν) ∧
    Nonempty (RCodeSound.{0,0} (ImpredicativePiProbe.identityWorld F ν) 0) ∧
    ImpredicativePiProbe.ImpMember (α := ImpredicativePiProbe.BotCode.{0})
      (fun X => X.1.view.value) (fun _ => True) (fun X => ImpredicativePiProbe.selfFibre X.1)
      ((ImpredicativePiProbe.identityWorld F ν).evaluate ImpredicativePiProbe.identityTerm) ∧
    -- mutant: without bot-closure the same evaluator image is not realized
    ¬ ImpredicativePiProbe.ImpMember (α := GuardedTaggedCode.Code.{0} 0)
      (fun X => X.view.value) (fun _ => True) (fun X => ImpredicativePiProbe.selfFibre X)
      (EnvironmentEval.denote emptyEnvA F ν EnvI.bot ImpredicativePiProbe.identityTerm) :=
  ⟨⟨ImpredicativePiProbe.botNeutral 0, ImpredicativePiProbe.botUniverse_member _⟩,
    ⟨⟨_, ImpredicativePiProbe.impCode_botClosed _ _ _ _ _ _⟩, rfl⟩,
    ⟨ImpredicativePiProbe.identitySound F ν⟩,
    ImpredicativePiProbe.identity_realized F ν,
    (ImpredicativePiProbe.full_universe_identity_boundary F ν).2.2.2.2⟩

/-! ## Saturated candidates -/

/-- A PER relating only the bot-free empty value: not saturated. -/
def emptyPER : Relation := fun x y => x = CandidatePi.emptyValue ∧ y = CandidatePi.emptyValue

theorem emptyPER_laws : Laws emptyPER :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h g => ⟨h.1, g.2⟩⟩

theorem emptyPER_not_sat : ¬ CandidateTowerProbe.Sat emptyPER := by
  intro h
  exact h.2 _ _ ⟨rfl, rfl⟩

theorem saturation_nonvacuity (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (σ : CandidateTowerProbe.REnv) (ρ : CandidateTowerProbe.CEnv) (X : Value) :
    -- inhabited: the Girard reading is realized
    CandidateTowerProbe.El σ ρ CandidateTowerProbe.identityCode
      (EnvironmentEval.denote emptyEnvA F ν EnvI.bot ImpredicativePiProbe.identityTerm)
      (EnvironmentEval.denote emptyEnvA F ν EnvI.bot ImpredicativePiProbe.identityTerm) ∧
    -- mutant: a non-saturated PER breaks the inner clause for the same image
    Laws emptyPER ∧ ¬ CandidateTowerProbe.Sat emptyPER ∧
    ¬ (∀ x y, emptyPER x y → emptyPER
        (NeutralPi.applyValue (NeutralPi.applyValue
          (EnvironmentEval.denote emptyEnvA F ν EnvI.bot ImpredicativePiProbe.identityTerm) X) x)
        (NeutralPi.applyValue (NeutralPi.applyValue
          (EnvironmentEval.denote emptyEnvA F ν EnvI.bot ImpredicativePiProbe.identityTerm) X) y)) := by
  refine ⟨CandidateTowerProbe.identity_realized CandidateTowerProbe.satFor_laws F ν σ ρ,
    emptyPER_laws, emptyPER_not_sat, ?_⟩
  intro h
  have h1 := (h _ _ ⟨rfl, rfl⟩).1
  rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application emptyEnvA F ν
      EnvI.bot (.sort .zero) ImpredicativePiProbe.innerLambda (.succ .zero) X),
    NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_application emptyEnvA F ν
      _ (.bvar 0) (.bvar 0) .zero CandidatePi.emptyValue),
    ImpredicativePiProbe.bvar_empty_image] at h1
  have hb : bottom .bot := rfl
  rw [h1] at hb
  exact hb

/-! ## Chaotic none level -/

open OptionSoundUniverse in
theorem none_nonvacuity (F : EnvironmentEval.FamilySyntax) (name : Nat) :
    -- inhabited: a none-level sound instance and the self-containing universe
    Nonempty (OptionSoundInterface.RCodeSoundO.{0,0}
      (OptionSoundInterface.noneWorld F name) none) ∧
    (universeCode.{0} none).kernel.relation ⟨none⟩ ⟨none⟩ ∧
    decode none (⟨none⟩ : (universeCode.{0} none).Element) = OCode.noneUniverse ∧
    -- mutant 1: relating all none universe elements contradicts conversion
    ¬ (∀ x y : (universeCode.{0} none).Element, (universeCode.{0} none).kernel.relation x y) ∧
    -- mutant 2: a chaotic code at the universe's own image is incoherent
    ¬ Same NoneUniverseBoundary.Chaos NoneUniversePER := by
  refine ⟨⟨OptionSoundInterface.noneInstance F name⟩, rfl, rfl, ?_, ?_⟩
  · intro h
    have hc := (universe_relation_iff none ⟨none⟩ ⟨some (NoneOrdinary.named 0)⟩).mp
      (h ⟨none⟩ ⟨some (NoneOrdinary.named 0)⟩)
    have he := (none_converts_iff _ _).mp hc
    cases he
  · intro h
    obtain ⟨a, hx, _⟩ := (h bottom bottom).mp True.intro
    exact typeDefined_nonbottom (noneImage_defined a) hx.symm

end Rcic.Declarative.Ann.LR3.NonvacuityChecks
