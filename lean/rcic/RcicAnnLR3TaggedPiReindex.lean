import rcic.RcicAnnLR3TaggedSaturatedTower
import rcic.RcicAnnLR3SaturatedPiReindex

/-!
# Constructive reindexing of tagged positive function actions

Both inverse maps act on the retained run field and preserve the real
native function value. The resulting KernelIso also preserves designated
function reflections. This is a data producer from a supplied
DomainReindex, not a choice of maps from CodeRelated. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TaggedPiReindex
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateActionProducts
open SaturatedPiElements SaturatedPiReindex TaggedSaturatedTower
universe u v

section Actions
variable {α : Type u} {β : Type v}
variable {eraseA : α → Value} {eraseB : β → Value}
variable {D : α → α → Prop} {D' : β → β → Prop}
variable {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
variable {ρ : EnvI} {B : ExprA} {k : Nat}
variable (r : DomainReindex α β eraseA eraseB D D')
variable (b : Body α eraseA D E F ν ρ B k)

theorem sourceAction_ext {f g : SourceElementAction b}
    (hvalue : f.value = g.value) (hrun : f.run = g.run) : f = g := by
  cases f
  cases g
  cases hvalue
  cases hrun
  rfl

def reindexSourceAction (f : SourceElementAction b) :
    SourceElementAction (reindexBody r b) where
  value := f.value
  run := fun y => f.run (r.backward y)
  erased := fun y =>
    (NeutralPi.applyValue_congr (ValueEq.refl f.value)
      (backward_erasure r y).symm).trans (f.erased (r.backward y))
  respect := fun y z hyz =>
    f.respect (r.backward y) (r.backward z) ((backward_relation r y z).1 hyz)

def unreindexSourceAction (g : SourceElementAction (reindexBody r b)) :
    SourceElementAction b where
  value := g.value
  run := fun x => g.run (r.forward x)
  erased := fun x =>
    (NeutralPi.applyValue_congr (ValueEq.refl g.value)
      (r.erasure x)).trans (g.erased (r.forward x))
  respect := by
    intro x y hxy
    have h := g.respect (r.forward x) (r.forward y) ((r.relation x y).1 hxy)
    change (view k (b.run (r.backward (r.forward x))).code).relation
      (g.run (r.forward x)) (g.run (r.forward y)) at h
    simpa only [r.left_inv] using h

theorem reindexSourceAction_value (f : SourceElementAction b) :
    (reindexSourceAction r b f).value = f.value := rfl

theorem reindexSourceAction_run (f : SourceElementAction b) (y : β) :
    (reindexSourceAction r b f).run y = f.run (r.backward y) := rfl

theorem unreindex_reindex (f : SourceElementAction b) :
    unreindexSourceAction r b (reindexSourceAction r b f) = f := by
  apply sourceAction_ext b
  · rfl
  · funext x
    exact congrArg f.run (r.left_inv x)

theorem reindex_unreindex (g : SourceElementAction (reindexBody r b)) :
    reindexSourceAction r b (unreindexSourceAction r b g) = g := by
  apply sourceAction_ext (reindexBody r b)
  · rfl
  · funext y
    exact congrArg g.run (r.right_inv y)

theorem reindexSourceAction_relation (f g : SourceElementAction b) :
    ElementRel f g ↔ ElementRel (reindexSourceAction r b f) (reindexSourceAction r b g) := by
  constructor
  · intro h y hy
    exact h (r.backward y) ((backward_relation r y y).1 hy)
  · intro h x hx
    have hh := h (r.forward x) ((r.relation x x).1 hx)
    change (view k (b.run (r.backward (r.forward x))).code).relation
      (f.run (r.backward (r.forward x))) (g.run (r.backward (r.forward x))) at hh
    simpa only [r.left_inv] using hh
end Actions

theorem reindexDomainLaws
    {α : Type u} {β : Type v}
    {eraseA : α → Value} {eraseB : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β eraseA eraseB D D') (hD : RelLaws D) : RelLaws D' := by
  constructor
  · intro x y hxy
    exact (backward_relation r y x).2 (hD.symm ((backward_relation r x y).1 hxy))
  · intro x y z hxy hyz
    exact (backward_relation r x z).2
      (hD.trans ((backward_relation r x y).1 hxy) ((backward_relation r y z).1 hyz))

theorem reindexSourceAction_reflection
    {α : Type u} {β : Type v}
    {eraseA : α → Value} {eraseB : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k : Nat}
    (r : DomainReindex α β eraseA eraseB D D')
    (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
    (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
    (A : ExprA) (lA : Level) (name : Nat) :
    reindexSourceAction r b (reflectSource b hD hsat A lA name) =
      reflectSource (reindexBody r b) (reindexDomainLaws r hD)
        (fun y => hsat (r.backward y)) A lA name := by
  apply sourceAction_ext (reindexBody r b) rfl
  rfl

def piCode_reindexIso
    {α : Type u} {β : Type v}
    {eraseA : α → Value} {eraseB : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k n : Nat}
    (r : DomainReindex α β eraseA eraseB D D')
    (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
    (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
    (A : ExprA) (lA lB : Level)
    (hbody : eval ν lB = some (k + 1))
    (hlevel : eval ν (.imax lA lB) = some (n + 1)) :
    KernelIso
      (piCode b hD hsat A lA lB hbody hlevel).kernel
      (piCode (reindexBody r b) (reindexDomainLaws r hD)
        (fun y => hsat (r.backward y)) A lA lB hbody hlevel).kernel where
  forward := reindexSourceAction r b
  backward := unreindexSourceAction r b
  left_inv := unreindex_reindex r b
  right_inv := reindex_unreindex r b
  type_image := ValueEq.refl _
  element_image := fun _ => ValueEq.refl _
  point_image := reindexSourceAction_reflection r b hD hsat A lA
  relation := reindexSourceAction_relation r b

theorem piCode_reindex_related
    {α β : Type u} {eraseA : α → Value} {eraseB : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k n : Nat}
    (r : DomainReindex α β eraseA eraseB D D')
    (b : Body α eraseA D E F ν ρ B (k + 1)) (hD : RelLaws D)
    (hsat : ∀ x, SaturatedTower.Closed (k + 1) (b.run x).code)
    (A : ExprA) (lA lB : Level)
    (hbody : eval ν lB = some (k + 1))
    (hlevel : eval ν (.imax lA lB) = some (n + 1)) :
    TaggedSaturatedTower.CodeRelated (piCode b hD hsat A lA lB hbody hlevel)
      (piCode (reindexBody r b) (reindexDomainLaws r hD)
        (fun y => hsat (r.backward y)) A lA lB hbody hlevel) :=
  ⟨rfl, ⟨piCode_reindexIso r b hD hsat A lA lB hbody hlevel⟩⟩

end Rcic.Declarative.Ann.LR3.TaggedPiReindex
