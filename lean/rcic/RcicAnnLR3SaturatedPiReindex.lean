import rcic.RcicAnnLR3SaturatedPiTransport

/-!
Explicit transport between two retained argument carriers. The maps and
both inverses are data; no representative is selected from a quotient or
an existential. Retained actions keep their raw function value and their
result codes. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SaturatedPiReindex
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateAction CandidateActionProducts
universe u v

structure DomainReindex (α : Type u) (β : Type v)
    (erase : α → Value) (erase' : β → Value)
    (D : α → α → Prop) (D' : β → β → Prop) where
  forward : α → β
  backward : β → α
  left_inv : ∀ x, backward (forward x) = x
  right_inv : ∀ y, forward (backward y) = y
  relation : ∀ x y, D x y ↔ D' (forward x) (forward y)
  erasure : ∀ x, ValueEq (erase x) (erase' (forward x))

theorem backward_relation
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D') (x y : β) :
    D' x y ↔ D (r.backward x) (r.backward y) := by
  have h := (r.relation (r.backward x) (r.backward y)).symm
  simpa only [r.right_inv] using h

theorem backward_erasure
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D') (x : β) :
    ValueEq (erase (r.backward x)) (erase' x) := by
  simpa only [r.right_inv] using r.erasure (r.backward x)

/-- A supplied retained action is transported as data, including its
actual raw application equation. Its codomain level is arbitrary. -/
def reindexAction
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D') {k : Nat}
    (f : Action α erase D k) : Action β erase' D' k where
  value := f.value
  run := fun y => f.run (r.backward y)
  erased := fun y =>
    (NeutralPi.applyValue_congr (ValueEq.refl f.value)
      (backward_erasure r y).symm).trans (f.erased (r.backward y))
  respect := fun x y hxy => f.respect _ _ ((backward_relation r x y).mp hxy)

theorem reindexAction_value
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D') {k : Nat}
    (f : Action α erase D k) : (reindexAction r f).value = f.value := rfl

theorem reindexAction_run
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D') {k : Nat}
    (f : Action α erase D k) (x : β) :
    (reindexAction r f).run x = f.run (r.backward x) := rfl

/-- This is equality of the actual action PER after carrier transport,
not an equality inferred from the erased function values. -/
theorem reindexAction_relation
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D') {k : Nat}
    (f g : Action α erase D k) :
    ActionRel (reindexAction r f) (reindexAction r g) ↔ ActionRel f g := by
  constructor
  · intro h x y hxy
    have hp := h (r.forward x) (r.forward y) ((r.relation x y).mp hxy)
    change CodeRel (f.run (r.backward (r.forward x)))
      (g.run (r.backward (r.forward y))) at hp
    simpa only [r.left_inv] using hp
  · intro h x y hxy
    exact h (r.backward x) (r.backward y) ((backward_relation r x y).mp hxy)

theorem reindexAction_member
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D') {k : Nat}
    (f : Action α erase D k) :
    ActionRel (reindexAction r f) (reindexAction r f) :=
  (reindexAction_relation r f f).mpr (actionRel_refl f)

end Rcic.Declarative.Ann.LR3.SaturatedPiReindex


namespace Rcic.Declarative.Ann.LR3.SaturatedPiReindex
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily
open StratifiedCandidates CandidateAction CandidateActionProducts
universe u v

/-- Product PERs agree after an explicit erasure-compatible reindexing
of the retained domain and forward transport of the body fibres. -/
theorem functionPER_reindex
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D') (hD : RelLaws D)
    {C : α → Relation} {C' : β → Relation}
    (hC : ∀ x, D x x → Same (C x) (C' (r.forward x))) :
    Same (CandidatePi.FunctionPER erase D C)
      (CandidatePi.FunctionPER erase' D' C') := by
  intro f g
  constructor
  · intro h x y hxy
    have hd := (backward_relation r x y).mp hxy
    have hp := h (r.backward x) (r.backward y) hd
    have ht := (hC (r.backward x)
      (CandidatePi.domain_left_member hD hd) _ _).mp hp
    have ht' : C' x
        (NeutralPi.applyValue f (erase (r.backward x)))
        (NeutralPi.applyValue g (erase (r.backward y))) := by
      simpa only [r.right_inv] using ht
    simpa only [NeutralCodes.valueEq_eq (backward_erasure r x),
      NeutralCodes.valueEq_eq (backward_erasure r y)] using ht'
  · intro h x y hxy
    have hp := h (r.forward x) (r.forward y) ((r.relation x y).mp hxy)
    have ht := (hC x (CandidatePi.domain_left_member hD hxy) _ _).mpr hp
    simpa only [← NeutralCodes.valueEq_eq (r.erasure x),
      ← NeutralCodes.valueEq_eq (r.erasure y)] using ht

/-- The two codes retain their respective source product images while
their proof fibres are transported through the actual carrier maps. -/
theorem propositionPi_reindex_transport
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D')
    (hD : RelLaws D) (hD' : RelLaws D')
    (hne : ∀ x, D x x → CandidatePi.NonemptyValue (erase x))
    (hne' : ∀ x, D' x x → CandidatePi.NonemptyValue (erase' x))
    {E : ResolvedEnvA} {F G : EnvironmentEval.FamilySyntax} {ν μ : Valuation}
    {ρ σ : EnvI} {B B' : ExprA} (A A' : ExprA) (lA lB lA' lB' : Level)
    (hB : eval ν lB = some 0) (hB' : eval μ lB' = some 0)
    (b : Body α erase D E F ν ρ B 0)
    (c : Body β erase' D' E G μ σ B' 0)
    (hbc : ∀ x, D x x → CodeRel (b.run x) (c.run (r.forward x))) :
    CodeRel (propositionPi hD hne A lA lB hB b)
      (propositionPi hD' hne' A' lA' lB' hB' c) := by
  apply (zero_related_iff _ _).mpr
  have hfun := functionPER_reindex r hD
    (C := fun x => (view 0 (b.run x).code).relation)
    (C' := fun y => (view 0 (c.run y).code).relation)
    (fun x hx => (hbc x hx).transport)
  intro f g
  exact (propositionPi_el hD hne A lA lB hB b f g).trans
    ((hfun f g).trans
      (propositionPi_el hD' hne' A' lA' lB' hB' c f g).symm)

/-- Reindexing preserves the same source body evaluation and retains
its output code, uniformly at every finite output level. -/
def reindexBody
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D')
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k : Nat}
    (b : Body α erase D E F ν ρ B k) : Body β erase' D' E F ν ρ B k where
  run := fun y => b.run (r.backward y)
  image := by
    intro y
    rw [← NeutralCodes.valueEq_eq (backward_erasure r y)]
    exact b.image (r.backward y)
  respect := fun x y hxy => b.respect _ _ ((backward_relation r x y).mp hxy)

theorem reindexBody_run
    {α : Type u} {β : Type v} {erase : α → Value} {erase' : β → Value}
    {D : α → α → Prop} {D' : β → β → Prop}
    (r : DomainReindex α β erase erase' D D')
    {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {ρ : EnvI} {B : ExprA} {k : Nat}
    (b : Body α erase D E F ν ρ B k) (x : β) :
    (reindexBody r b).run x = b.run (r.backward x) := rfl

end Rcic.Declarative.Ann.LR3.SaturatedPiReindex
