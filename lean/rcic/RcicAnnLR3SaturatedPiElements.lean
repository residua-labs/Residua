import rcic.RcicAnnLR3SaturatedTower
import rcic.RcicAnnLR3CandidateActionProducts

/-!
# Retained element actions for dependent positive products

Element actions retain an element of the result fibre, rather than only
an output type code. Constant reflection is an actual native lambda with
its represented result captured in the environment. The product
constructor uses the saturated tower's shared reflected elements.
This is an explicit new element carrier, not an embedding into the old
raw/sum carrier or a complete source Pi arm. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SaturatedPiElements
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateActionProducts
universe u v

structure ElementAction {α : Type u} {β : Type v}
    (eraseA : α → Value) (eraseB : β → Value)
    (D : α → α → Prop) (R : α → β → β → Prop) where
  value : Value
  run : α → β
  erased : ∀ x, ValueEq (NeutralPi.applyValue value (eraseA x)) (eraseB (run x))
  respect : ∀ x y, D x y → R x (run x) (run y)

section Algebra
variable {α : Type u} {β : Type v}
variable {eraseA : α → Value} {eraseB : β → Value}
variable {D : α → α → Prop} {R : α → β → β → Prop}

def ElementRel (f g : ElementAction eraseA eraseB D R) : Prop :=
  ∀ x, D x x → R x (f.run x) (g.run x)

theorem elementRel_refl (f : ElementAction eraseA eraseB D R) : ElementRel f f :=
  fun x hx => f.respect x x hx

theorem elementRel_laws (hR : ∀ x, D x x → RelLaws (R x)) :
    RelLaws (@ElementRel α β eraseA eraseB D R) := by
  constructor
  · intro f g h x hx
    exact (hR x hx).symm (h x hx)
  · intro f g h hfg hgh x hx
    exact (hR x hx).trans (hfg x hx) (hgh x hx)

theorem elementRel_paired (hD : RelLaws D)
    (hR : ∀ x, D x x → RelLaws (R x))
    {f g : ElementAction eraseA eraseB D R} (hfg : ElementRel f g)
    {x y : α} (hxy : D x y) : R x (f.run x) (g.run y) := by
  have hx := CandidatePi.domain_left_member hD hxy
  exact (hR x hx).trans (hfg x hx) (g.respect x y hxy)

theorem elementRel_iff_paired (hD : RelLaws D)
    (hR : ∀ x, D x x → RelLaws (R x))
    (f g : ElementAction eraseA eraseB D R) :
    ElementRel f g ↔ ∀ x y, D x y → R x (f.run x) (g.run y) :=
  ⟨fun h _ _ hxy => elementRel_paired hD hR h hxy,
    fun h x hx => h x x hx⟩

/-- A reflected result is represented by a real native constant lambda.
The resulting function's membership is constructed from the fibre data. -/
def constantElement (hD : RelLaws D)
    (p : β) (hp : ∀ x, D x x → R x p p) (hbot : eraseB p .bot)
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (A : ExprA) (l : Level) : ElementAction eraseA eraseB D R where
  value := EnvironmentEval.denote E F ν (EnvI.cons (eraseB p) ρ)
    (.lam A l (.bvar 1))
  run := fun _ => p
  erased := fun x =>
    (EnvironmentEval.denote_lambda_application E F ν (EnvI.cons (eraseB p) ρ)
      A (.bvar 1) l (eraseA x)).trans
      (CandidateAction.bound_image E F ν
        (EnvI.cons (eraseA x) (EnvI.cons (eraseB p) ρ))
        1 (eraseB p) rfl hbot)
  respect := fun x _ hxy => hp x (CandidatePi.domain_left_member hD hxy)

theorem constantElement_run (hD : RelLaws D)
    (p : β) (hp : ∀ x, D x x → R x p p) (hbot : eraseB p .bot)
    (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (A : ExprA) (l : Level) (x : α) :
    (constantElement (eraseA := eraseA) hD p hp hbot E F ν ρ A l).run x = p := rfl
end Algebra

end Rcic.Declarative.Ann.LR3.SaturatedPiElements


namespace Rcic.Declarative.Ann.LR3.SaturatedPiElements
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateActionProducts
universe u

abbrev SourceElementAction
    {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k : Nat}
    (b : Body α eraseA D E F ν ρ B k) :=
  ElementAction eraseA (StratifiedCandidates.erase k) D
    (fun x => (view k (b.run x).code).relation)

theorem positive_reflection_bot (k name : Nat) :
    StratifiedCandidates.erase (k + 1) (SaturatedTower.reflect (k + 1) name) .bot := by
  rw [SaturatedTower.reflect_erasure]
  exact NativeMemberValues.value_bot (some k) name

/-- Reflection has function shape: its actual native lambda returns the
tower's common reflected element at the fixed codomain stage. -/
def reflectSource
    {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k : Nat}
    (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
    (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
    (A : ExprA) (lA : Level) (name : Nat) : SourceElementAction b :=
  constantElement hD (SaturatedTower.reflect (k + 1) name)
    (fun x _ => hsat x name) (positive_reflection_bot k name) E F ν ρ A lA

/-- Positive products preserve the actual source Pi image and retain all
element-action data. This carrier has not been embedded in the tower. -/
def positivePi
    {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k n : Nat}
    (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
    (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
    (A : ExprA) (lA lB : Level)
    (_bodyLevel : eval ν lB = some (k + 1))
    (hlevel : eval ν (.imax lA lB) = some (n + 1)) :
    PointedPER (n + 1) (SourceElementAction b) where
  value := EnvironmentEval.denote E F ν ρ (.pi A lA B lB)
  level := hlevel ▸ source_pi_level E F ν ρ A B lA lB
  defined := source_pi_defined E F ν ρ A B lA lB
  relation := ElementRel
  lawful := elementRel_laws (fun x _ => (view (k + 1) (b.run x).code).lawful)
  point := reflectSource b hD hsat A lA
  point_member := fun name => elementRel_refl (reflectSource b hD hsat A lA name)
  irrelevant := fun h => False.elim (Nat.noConfusion h)

theorem positivePi_reflection_application
    {α : Type u} {eraseA : α → Value} {D : α → α → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k n : Nat}
    (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
    (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
    (A : ExprA) (lA lB : Level)
    (_bodyLevel : eval ν lB = some (k + 1))
    (hlevel : eval ν (.imax lA lB) = some (n + 1)) (name : Nat) (x : α) :
    ValueEq (NeutralPi.applyValue
      ((positivePi b hD hsat A lA lB _bodyLevel hlevel).point name).value (eraseA x))
      (NativeMemberValues.value (some k) name) := by
  have h := (reflectSource b hD hsat A lA name).erased x
  change ValueEq _ (StratifiedCandidates.erase (k + 1)
    (SaturatedTower.reflect (k + 1) name)) at h
  rw [SaturatedTower.reflect_erasure] at h
  exact h

end Rcic.Declarative.Ann.LR3.SaturatedPiElements
