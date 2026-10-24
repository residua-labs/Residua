import rcic.RcicF3Defs
import rcic.RcicUniverseClass

/-!
# F3: the instance bound on an admitted environment (definitions)

The bound the F3 consistency theorem takes as an antecedent, with no model and
no theorem about it, so that statements about the soundness tier can name it on
main ahead of the model. It is a predicate on the admission derivation
(`EnvWfT E`), not on the environment.

- `σOf vs`: the level valuation read from an instance vector.
- `RecNode E E' f rr rm`: what a group's admission walk finds at the group's
  recursor (its admission, the environment it is admitted in, and its typed
  views).
- `WalkB2 K hmem`: along a group's admission walk, each constructor's own
  domain typings (in the environment it is admitted in), at instances within
  `K`, satisfy the level bound `LOKt … 4 K`.
- `BoundG K hW`: every definition, theorem and opaque body typing satisfies
  `LOKt (fun _ => 0) 4 K`. In every group:
  - each constructor's stored type has a typing in the constructor scope
    within the bound;
  - `WalkB2` holds;
  - under `Prop` large elimination, each field has a typing at a uniformly
    `Prop` level, within the bound.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The level valuation read from an instance vector. -/
def σOf (vs : List Nat) : Nat → Nat := fun i => vs.getD i 0

/-- What the walk finds at the group's recursor. -/
structure RecNode (E E' : ResolvedEnv) (f rr : Nat) (rm : CheckedMember) : Type where
  E0 : ResolvedEnv
  a : RecursorEliminationAdmitted E0 rr rm
  h14 : IotaDescriptorClause E0 a
  fam : a.family.ref = f
  fresh : E0.members rr = none
  sub : ∀ r m, (extendEnv E0 rr rm).members r = some m → E'.members r = some m
  base : ∀ r m, E.members r = some m → E0.members r = some m
  h04 : CtorCensus E0 a.family.ref rr
  h07 : ∀ i, FieldUniverseAdmitted (a.constructorViews i)
  h12 : MinorPremisesMatch a
  famTyped : FamilyTypedT a.family
  ctorsTyped : ∀ i, CtorTypedT (a.constructorViews i)
  u : Level
  hT : HasTyT E0 rm.arity [] rm.mtype (.sort u)

/-- Bounded typings of each constructor's own domains, in the environment it is
admitted in, at instances within `K`. -/
def WalkB2 (K : Nat → Nat) {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → Prop
  | _, _, _, .nil _ => True
  | E, _, _, .cons _ r _ _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest =>
      (match hadm with
        | .constructor family view _ _ _ _ _ => ∀ vs : List Nat, vs.length = family.member.arity →
            (∀ v, v ∈ vs → v ≤ K r) → ∀ k : Fin (view.parameters ++ view.fields).length,
              ∃ d : HasTyT E family.member.arity (policyPrefixContext (view.parameters ++ view.fields) k.val)
                ((view.parameters ++ view.fields)[k.val]) (.sort (view.domainsTyped.levels k)), LOKt (σOf vs) 4 K d
        | _ => True) ∧ WalkB2 K hrest

/-- The level bounds on the derivations the proof uses: each constructor's
stored type in the constructor scope, each constructor's own admission domain
typings, and, under `Prop` large elimination, typings of the fields at a
uniformly `Prop` level in the constructor scope. -/
def BoundG (K : Nat → Nat) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => BoundG K hE
  | _, .definition _ _ _ _ _ hE _ _ hv _ _ _ _ => BoundG K hE ∧ LOKt (fun _ => 0) 4 K hv
  | _, .thm _ _ _ _ hE _ _ hp _ _ _ _ => BoundG K hE ∧ LOKt (fun _ => 0) 4 K hp
  | _, .opaque _ _ _ _ _ hE _ _ hv _ _ _ _ => BoundG K hE ∧ LOKt (fun _ => 0) 4 K hv
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem =>
      BoundG K hE ∧ (∀ node : RecNode E E' f rr rm, ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
        vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
        ∃ (u : Level) (d : HasTyT (extendEnv E f fm) node.a.family.member.arity []
            (node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d) ∧ WalkB2 K hmem ∧
      (∀ node : RecNode E E' f rr rm, UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
        ∀ (i : Fin node.a.constructors.length) (vs : List Nat), (∀ v, v ∈ vs → v ≤ K rr) →
        ∀ k : Fin (node.a.constructorViews i).fields.length, ∃ l : Level, UniformProp l ∧
          ∃ d : HasTyT (extendEnv E f fm) node.a.family.member.arity
            (policyPrefixContext (node.a.family.parameters ++ (node.a.constructorViews i).fields)
              (node.a.family.parameters.length + k.val))
            ((node.a.constructorViews i).fields[k]) (.sort l), LOKt (σOf vs) 4 K d)

/-- The bound is inhabited: the admitted `falseEnvU` satisfies it at every `K`
(its group has no constructor). -/
theorem falseEnvUWfT_boundG (K : Nat → Nat) : BoundG K falseEnvUWfT := by
  refine ⟨trivial, fun node i => ?_, ⟨trivial, trivial, trivial⟩, fun node _ _ i => ?_⟩
  · have h := node.a.recursorRef
    rw [node.fam] at h
    exact absurd i.isLt (by omega)
  · have h := node.a.recursorRef
    rw [node.fam] at h
    exact absurd i.isLt (by omega)

end PSet

end Rcic.F3
