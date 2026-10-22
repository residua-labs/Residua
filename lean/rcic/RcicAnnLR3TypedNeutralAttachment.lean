import rcic.RcicAnnLR3TypedNeutralProducer
import rcic.RcicAnnLR3EnvironmentTypedNeutralBoundary
import rcic.RcicAnnLR3EnvironmentEvalControls

/-!
# Matched semantic attachments for universe-typed neutral members

The environment lookup constructs data for an actual axiom or opaque
member whose stored type is a sort. Its level instantiation is retained,
and its reflected value has the corresponding universe tag. The result
stores the element relation and code explicitly; no tree, descriptor or
PER is selected from an existential proof.

The image at the end is explicitly a top-level override fixture. It
exhibits the admitted axiom and opaque controls under the new attachment.
It does not insert semantic members compositionally into nested source
terms, and it does not supply the general Ty_const contract or preserve
the earlier evaluator's full arm suite. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TypedNeutralAttachment

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open TypedNeutralProducer

/-- Actual source lookup, instantiated semantic type and reflected value
are retained together as ordinary data. -/
structure MemberInterpretation (E : ResolvedEnvA) (ν : Valuation)
    (r : Nat) (ls : List Level) where
  source : CheckedMemberA
  lookup : E.members r = some source
  neutral_class : source.mclass = .axiomM ∨ source.mclass = .opaqueM
  level : Option Nat
  typeValue : Value
  relation : Relation
  neutral : TypedNeutral level typeValue relation
  type_image : ∀ (F : EnvironmentEval.FamilySyntax) (ρ : EnvI),
    ValueEq (EnvironmentEval.denote E F ν ρ (instantiateLevelsA ls source.mtypeA)) typeValue

/-- The reflected member is constructed from the looked-up source sort.
This definition works at all partial valuations and level arguments. -/
def sortMemberInterpretation (E : ResolvedEnvA) (ν : Valuation)
    (r : Nat) (ls : List Level) (m : CheckedMemberA) (l : Level)
    (hm : E.members r = some m)
    (hc : m.mclass = .axiomM ∨ m.mclass = .opaqueM)
    (ht : m.mtypeA = .sort l) : MemberInterpretation E ν r ls where
  source := m
  lookup := hm
  neutral_class := hc
  level := (eval ν (instLevel ls l)).map Nat.succ
  typeValue := universeValue (eval ν (instLevel ls l))
  relation := NeutralCodes.UniversePER (eval ν (instLevel ls l))
  neutral := universeNeutral (eval ν (instLevel ls l)) r
  type_image := by
    intro F ρ
    rw [ht]
    change ValueEq (EnvironmentEval.denote E F ν ρ (.sort (instLevel ls l))) _
    have he := (EnvironmentEval.annSemantics InductiveCodes.legacyUniverseSystem E F).sort_image
      ν [] ρ (instLevel ls l)
    change EnvironmentEval.denote E F ν ρ (.sort (instLevel ls l)) = _ at he
    rw [he]
    exact ValueEq.refl _

/-- An environment-aware producer. Unsupported member types are left
unattached; this option is not a universal semantic member theorem. -/
def universeAttachment? (E : ResolvedEnvA) (ν : Valuation)
    (r : Nat) (ls : List Level) : Option (MemberInterpretation E ν r ls) :=
  match hm : E.members r with
  | none => none
  | some m =>
    match hc : m.mclass with
    | .axiomM =>
      match ht : m.mtypeA with
      | .sort l => some (sortMemberInterpretation E ν r ls m l hm (Or.inl hc) ht)
      | _ => none
    | .opaqueM =>
      match ht : m.mtypeA with
      | .sort l => some (sortMemberInterpretation E ν r ls m l hm (Or.inr hc) ht)
      | _ => none
    | _ => none

/-- A fixture exposing the attached member only at a top-level constant.
Nested terms still use the earlier evaluator, so compositionality is not
claimed for this fixture. -/
def topLevelImage (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) : ExprA → Value
  | .const r ls =>
    match universeAttachment? E ν r ls with
    | some a => a.neutral.value
    | none => EnvironmentEval.denote E F ν ρ (.const r ls)
  | e => EnvironmentEval.denote E F ν ρ e

def fixture (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) : AnnSemantics where
  toCodeSystem := InductiveCodes.legacyUniverseSystem
  image := fun ν _ ρ e => topLevelImage E F ν ρ e
  sort_image := by
    intro ν Γ ρ l
    exact (EnvironmentEval.annSemantics InductiveCodes.legacyUniverseSystem E F).sort_image
      ν Γ ρ l

theorem axiom_image {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m) (hc : m.mclass = .axiomM) (ht : m.mtypeA = .sort l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    topLevelImage E F ν ρ (.const r ls) = (universeNeutral (eval ν (instLevel ls l)) r).value := by
  rcases m with ⟨mc, ar, ty, body, np, norm⟩
  change mc = .axiomM at hc
  change ty = .sort l at ht
  subst mc
  subst ty
  have ha : universeAttachment? E ν r ls =
      some (sortMemberInterpretation E ν r ls
        ⟨.axiomM, ar, .sort l, body, np, norm⟩ l hm (Or.inl rfl) rfl) := by
    unfold universeAttachment?
    split
    · rename_i hnone
      cases hm.symm.trans hnone
    · rename_i m' hlookup
      have he : m' = ⟨.axiomM, ar, .sort l, body, np, norm⟩ :=
        Option.some.inj (hlookup.symm.trans hm)
      subst m'
      rfl
  simp only [topLevelImage, ha, sortMemberInterpretation]

theorem opaque_image {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m) (hc : m.mclass = .opaqueM) (ht : m.mtypeA = .sort l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    topLevelImage E F ν ρ (.const r ls) = (universeNeutral (eval ν (instLevel ls l)) r).value := by
  rcases m with ⟨mc, ar, ty, body, np, norm⟩
  change mc = .opaqueM at hc
  change ty = .sort l at ht
  subst mc
  subst ty
  have ha : universeAttachment? E ν r ls =
      some (sortMemberInterpretation E ν r ls
        ⟨.opaqueM, ar, .sort l, body, np, norm⟩ l hm (Or.inr rfl) rfl) := by
    unfold universeAttachment?
    split
    · rename_i hnone
      cases hm.symm.trans hnone
    · rename_i m' hlookup
      have he : m' = ⟨.opaqueM, ar, .sort l, body, np, norm⟩ :=
        Option.some.inj (hlookup.symm.trans hm)
      subst m'
      rfl
  simp only [topLevelImage, ha, sortMemberInterpretation]

theorem neutral_image {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m)
    (hc : m.mclass = .axiomM ∨ m.mclass = .opaqueM) (ht : m.mtypeA = .sort l)
    (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    topLevelImage E F ν ρ (.const r ls) = (universeNeutral (eval ν (instLevel ls l)) r).value := by
  rcases hc with hc | hc
  · exact axiom_image hm hc ht F ν ρ ls
  · exact opaque_image hm hc ht F ν ρ ls

/-- The restricted fixture goal follows from the constructed attachment.
It is not the general Ty_const arm: the stored type must be a sort, and
the model here is the explicitly named top-level fixture. -/
theorem sort_member_goal {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA} {l : Level}
    (hm : E.members r = some m)
    (hc : m.mclass = .axiomM ∨ m.mclass = .opaqueM) (ht : m.mtypeA = .sort l)
    (F : EnvironmentEval.FamilySyntax) (ls : List Level) :
    PairedTyGoal (fixture E F) E I n Γ (.const r ls) (instantiateLevelsA ls m.mtypeA) := by
  simp only [ht, instantiateLevelsA]
  intro _ ν μ ρ σ hν _
  let k := eval ν (instLevel ls l)
  refine ⟨k.map Nat.succ, NeutralCodes.UniversePER k, NeutralCodes.UniversePER k,
    ⟨?_, ?_, fun _ _ => Iff.rfl⟩, ?_⟩
  · rw [(fixture E F).sort_image]
    exact InductiveCodes.CodeI.old (NeutralCodes.code_universe k)
  · rw [(fixture E F).sort_image, ← eval_of_valuationRel hν (instLevel ls l)]
    exact InductiveCodes.CodeI.old (NeutralCodes.code_universe k)
  · change NeutralCodes.UniversePER k
      (topLevelImage E F ν ρ (.const r ls)) (topLevelImage E F μ σ (.const r ls))
    rw [neutral_image hm hc ht F ν ρ ls, neutral_image hm hc ht F μ σ ls,
      ← eval_of_valuationRel hν (instLevel ls l)]
    exact (universeNeutral k r).member

namespace Controls

open EnvironmentTypedNeutralBoundary

def axiomFixture (F : EnvironmentEval.FamilySyntax) : AnnSemantics := fixture env F

theorem axiom_type_ih (F : EnvironmentEval.FamilySyntax) :
    PairedTyGoal (axiomFixture F) env (iotaIfaceA env) 0 [] (.sort one) (.sort two) :=
  PairedArms.ty_sort_supplied (axiomFixture F) env (iotaIfaceA env) 0 [] one

theorem axiom_goal (F : EnvironmentEval.FamilySyntax) :
    PairedTyGoal (axiomFixture F) env (iotaIfaceA env) 0 [] (.const 92 []) (.sort one) :=
  sort_member_goal (m := member) rfl (Or.inl rfl) rfl F []

theorem axiom_attachment_actual (ν : Valuation) :
    ∃ a : MemberInterpretation env ν 92 [], universeAttachment? env ν 92 [] = some a :=
  ⟨sortMemberInterpretation env ν 92 [] member one rfl (Or.inl rfl) rfl, rfl⟩

theorem axiom_control_inhabited (F : EnvironmentEval.FamilySyntax) :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 []) ∧
    env.members 92 = some member ∧
    member.mclass = .axiomM ∧
    ([] : List Level).length = member.arity ∧
    levelsBounded 0 ([] : List Level) = true ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (.sort one) (.sort two)) ∧
    PairedTyGoal (axiomFixture F) env (iotaIfaceA env) 0 [] (.sort one) (.sort two) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 [] (.const 92 []) (.sort one)) ∧
    (∀ ν, ∃ a : MemberInterpretation env ν 92 [], universeAttachment? env ν 92 [] = some a) ∧
    PairedRealises (axiomFixture F) zeroValuation zeroValuation [] EnvI.bot EnvI.bot ∧
    PairedTyGoal (axiomFixture F) env (iotaIfaceA env) 0 [] (.const 92 []) (.sort one) :=
  ⟨⟨admitted⟩, ⟨.nil⟩, rfl, rfl, rfl, rfl, ⟨source_type⟩,
    axiom_type_ih F, ⟨source_member⟩, axiom_attachment_actual, .nil _ _, axiom_goal F⟩

def opaqueFixture (F : EnvironmentEval.FamilySyntax) : AnnSemantics :=
  fixture EnvironmentEvalControls.opaqueEnv F

def opaque_source_member :
    HasTyA EnvironmentEvalControls.opaqueEnv (iotaIfaceA EnvironmentEvalControls.opaqueEnv)
      0 [] (.const 91 []) (.sort one) :=
  .const [] 91 [] EnvironmentEvalControls.opaqueMember two rfl rfl rfl (.sort [] one)

theorem opaque_type_ih (F : EnvironmentEval.FamilySyntax) :
    PairedTyGoal (opaqueFixture F) EnvironmentEvalControls.opaqueEnv
      (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 [] (.sort one) (.sort two) :=
  PairedArms.ty_sort_supplied (opaqueFixture F) EnvironmentEvalControls.opaqueEnv
    (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 [] one

theorem opaque_goal (F : EnvironmentEval.FamilySyntax) :
    PairedTyGoal (opaqueFixture F) EnvironmentEvalControls.opaqueEnv
      (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 [] (.const 91 []) (.sort one) :=
  sort_member_goal (m := EnvironmentEvalControls.opaqueMember) rfl (Or.inr rfl) rfl F []

theorem opaque_attachment_actual (ν : Valuation) :
    ∃ a : MemberInterpretation EnvironmentEvalControls.opaqueEnv ν 91 [],
      universeAttachment? EnvironmentEvalControls.opaqueEnv ν 91 [] = some a :=
  ⟨sortMemberInterpretation EnvironmentEvalControls.opaqueEnv ν 91 []
    EnvironmentEvalControls.opaqueMember one rfl (Or.inr rfl) rfl, rfl⟩

theorem opaque_control_inhabited (F : EnvironmentEval.FamilySyntax) :
    Nonempty (EnvWfA (iotaIfaceA EnvironmentEvalControls.opaqueEnv)
      EnvironmentEvalControls.opaqueEnv) ∧
    Nonempty (CtxWfA EnvironmentEvalControls.opaqueEnv
      (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 []) ∧
    EnvironmentEvalControls.opaqueEnv.members 91 = some EnvironmentEvalControls.opaqueMember ∧
    EnvironmentEvalControls.opaqueMember.mclass = .opaqueM ∧
    ([] : List Level).length = EnvironmentEvalControls.opaqueMember.arity ∧
    levelsBounded 0 ([] : List Level) = true ∧
    Nonempty (HasTyA EnvironmentEvalControls.opaqueEnv
      (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 [] (.sort one) (.sort two)) ∧
    PairedTyGoal (opaqueFixture F) EnvironmentEvalControls.opaqueEnv
      (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 [] (.sort one) (.sort two) ∧
    Nonempty (HasTyA EnvironmentEvalControls.opaqueEnv
      (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 [] (.const 91 []) (.sort one)) ∧
    (∀ ν, ∃ a : MemberInterpretation EnvironmentEvalControls.opaqueEnv ν 91 [],
      universeAttachment? EnvironmentEvalControls.opaqueEnv ν 91 [] = some a) ∧
    PairedRealises (opaqueFixture F) zeroValuation zeroValuation [] EnvI.bot EnvI.bot ∧
    PairedTyGoal (opaqueFixture F) EnvironmentEvalControls.opaqueEnv
      (iotaIfaceA EnvironmentEvalControls.opaqueEnv) 0 [] (.const 91 []) (.sort one) :=
  ⟨⟨EnvironmentEvalControls.opaque_admitted⟩, ⟨.nil⟩, rfl, rfl, rfl, rfl,
    ⟨.sort [] one⟩, opaque_type_ih F, ⟨opaque_source_member⟩,
    opaque_attachment_actual, .nil _ _, opaque_goal F⟩

end Controls

end Rcic.Declarative.Ann.LR3.TypedNeutralAttachment
