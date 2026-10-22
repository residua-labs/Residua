import rcic.RcicAnnLR3SaturatedTower
import rcic.RcicAnnLR3SaturatedPiTransport
import rcic.RcicAnnLR3SaturatedCandidateControl

/-!
# Positive products in the restricted saturated tower

The proof-valued product constructor and its actual application law land
in the same restricted tower used by the repaired alias control.
The former positive-stage collision also has a common native realizer
for every admitted stage-one fibre in that tower.

This composes supplied producers. A retained body is still an explicit
input to the general product constructor; it is supplied for the forall
Prop control. No source Ty_pi, Conv_pi, or unified enriched model is
asserted. closure_claim = 0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SaturatedProducts

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open CandidateAction CandidateActionProducts
namespace S
abbrev Code := SaturatedTower.Code
end S
universe u

def propositionPi {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D) (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (A : ExprA) (v w : Level)
    (hw : eval ν w = some 0) (b : Body α erase D E F ν ρ B 0) : S.Code 0 :=
  SaturatedTower.completed 0
    (CandidateActionProducts.propositionPi hD hne A v w hw b).code

theorem propositionPi_image {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D) (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (A : ExprA) (v w : Level)
    (hw : eval ν w = some 0) (b : Body α erase D E F ν ρ B 0) :
    (StratifiedCandidates.view 0 (propositionPi hD hne A v w hw b).1).value =
      EnvironmentEval.denote E F ν ρ (.pi A v B w) := rfl

theorem propositionPi_saturated {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D) (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (A : ExprA) (v w : Level)
    (hw : eval ν w = some 0) (b : Body α erase D E F ν ρ B 0)
    {f : Value} (hf : CandidatePi.Neutral f) :
    Member (StratifiedCandidates.view 0 (propositionPi hD hne A v w hw b).1).relation f :=
  CandidateActionProducts.propositionPi_reflect hD hne A v w hw b hf

theorem propositionPi_apply {α : Type u} {erase : α → Value} {D : α → α → Prop}
    (hD : RelLaws D) (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} (A : ExprA) (v w : Level)
    (hw : eval ν w = some 0) (b : Body α erase D E F ν ρ B 0)
    {f g : Value} {x y : α}
    (hfg : (StratifiedCandidates.view 0 (propositionPi hD hne A v w hw b).1).relation f g)
    (hxy : D x y) :
    (StratifiedCandidates.view 0 (b.run x).code).relation
      (NeutralPi.applyValue f (erase x)) (NeutralPi.applyValue g (erase y)) :=
  CandidateActionProducts.propositionPi_apply hD hne A v w hw b hfg hxy

theorem propositionPi_transport {α : Type u} {erase : α → Value}
    {D : α → α → Prop} (hD : RelLaws D)
    (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    {E : ResolvedEnvA} {F G : EnvironmentEval.FamilySyntax} {ν μ : Valuation}
    {ρ σ : EnvI} {B B' : ExprA} (A A' : ExprA) (v w v' w' : Level)
    (hw : eval ν w = some 0) (hw' : eval μ w' = some 0)
    (b : Body α erase D E F ν ρ B 0) (c : Body α erase D E G μ σ B' 0)
    (hbc : ∀ x, D x x → CodeRel (b.run x) (c.run x)) :
    SaturatedTower.Relation 0 (propositionPi hD hne A v w hw b)
      (propositionPi hD hne A' v' w' hw' c) :=
  CandidateActionProducts.propositionPi_transport hD hne A A' v w v' w' hw hw' b c hbc

/-- This source instance supplies the body producer, not only its type. -/
def forallCode (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) : S.Code 0 :=
  SaturatedTower.completed 0 (CandidateActionProducts.forallCode E F ν ρ).code

theorem forall_source_control (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      EqLargeFixture.parameter (.sort .zero)) ∧
    ValueEq (EnvironmentEval.denote emptyEnvA F ν EnvI.bot EqLargeFixture.parameter)
      (StratifiedCandidates.view 0 (forallCode emptyEnvA F ν EnvI.bot).1).value ∧
    SaturatedTower.UniverseRel 0
      (SaturatedTower.encode 0 (forallCode emptyEnvA F ν EnvI.bot))
      (SaturatedTower.encode 0 (forallCode emptyEnvA F ν EnvI.bot)) ∧
    Member (StratifiedCandidates.view 0 (forallCode emptyEnvA F ν EnvI.bot).1).relation
      (NeutralPER.neutralAtom name) ∧
    (∀ C : StratifiedCandidates.Code 0,
      Member (StratifiedCandidates.view 0 (close 0 C).code).relation
        (NeutralPi.applyValue (NeutralPER.neutralAtom name) (eraseCode (close 0 C)))) := by
  have h := CandidateActionProducts.forall_source_control F ν name
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    SaturatedTower.universe_member 0 _, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Every admitted stage-one fibre admits a representative of the same
actual native application's output, with its exact typed erasure. -/
theorem every_stage_one_fibre (ν : Valuation) (ρ : EnvI) (name : Nat)
    (C : S.Code 1) :
    ∃ x : StratifiedCandidates.Carrier 1,
      (StratifiedCandidates.view 1 C.1).relation x x ∧
      ValueEq (NeutralPi.applyValue
        (SaturatedCandidateControl.nativeFunction ν ρ name) C.1.value)
        (StratifiedCandidates.erase 1 x) :=
  ⟨SaturatedTower.reflect 1 name, SaturatedTower.reflection_member 1 C name,
    SaturatedCandidateControl.native_application ν ρ name C.1⟩

theorem stage_one_source_application (ν : Valuation) (ρ : EnvI) (name : Nat)
    (C : S.Code 1) (hb : C.1.value .bot) :
    ∃ x : StratifiedCandidates.Carrier 1,
      (StratifiedCandidates.view 1 C.1).relation x x ∧
      ValueEq (SaturatedCandidateControl.sourceApplicationImage ν ρ name ⟨C.1, hb⟩)
        (StratifiedCandidates.erase 1 x) :=
  ⟨SaturatedTower.reflect 1 name, SaturatedTower.reflection_member 1 C name,
    SaturatedCandidateControl.source_application_image ν ρ name ⟨C.1, hb⟩⟩

end Rcic.Declarative.Ann.LR3.SaturatedProducts
