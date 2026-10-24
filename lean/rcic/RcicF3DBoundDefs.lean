import rcic.RcicF3BoundDefs

/-!
# F3 class D: the second instance bound (definitions)

Definitions only, with no model and no theorem about the model, so that
statements about the soundness tier can name them on main ahead of the class-D
model (as `RcicF3BoundDefs` does for `BoundG`). Both are predicates on the
admission derivation (`EnvWfT E`).

- `BoundDG K hW`: in every group, each constructor's fields have a typing at a
  sort in the constructor scope (`extendEnv E f fm`), in the constructor's own
  telescope context (its parameters, then its earlier fields), bounded by
  `LOKt (σOf vs) 4 K` at every instance `vs` of the family's arity within the
  **recursor's** bound `K rr`. `BoundG` bounds a typing of each constructor's
  stored type only at the constructor's own instances (`K (f + 1 + i)`); the
  class-D model reads a δ-hidden field's denotation through its typing at the
  recursor's instances.
- `RecBelowCtors K hW`: in every group the recursor's bound is at most each
  constructor's (`K rr ≤ K r` for every `r` strictly between the family and the
  recursor). Under it `BoundDG` follows from `BoundG`
  (`boundDG_of_boundG`, `RcicF3DBoundBridge`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The fields' typings in the constructor scope, in the constructor's own
telescope context, bounded at every instance of the family's arity within the
recursor's bound. -/
def BoundDG (K : Nat → Nat) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => BoundDG K hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => BoundDG K hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => BoundDG K hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => BoundDG K hE
  | _, .group E f fm _ rr rm E' hE _ _ _ _ =>
      BoundDG K hE ∧
      ∀ node : RecNode E E' f rr rm, ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
        vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K rr) →
        ∀ k : Fin (node.a.constructorViews i).fields.length, ∃ l : Level,
          ∃ d : HasTyT (extendEnv E f fm) node.a.family.member.arity
            (policyPrefixContext ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields)
              ((node.a.constructorViews i).parameters.length + k.val))
            ((node.a.constructorViews i).fields[k]) (.sort l), LOKt (σOf vs) 4 K d

/-- The recursor's bound is at most each constructor's, in every group. -/
def RecBelowCtors (K : Nat → Nat) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => RecBelowCtors K hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => RecBelowCtors K hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => RecBelowCtors K hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => RecBelowCtors K hE
  | _, .group _ f _ _ rr _ _ hE _ _ _ _ =>
      RecBelowCtors K hE ∧ ∀ r, f < r → r < rr → K rr ≤ K r

/-- The bound is inhabited: the admitted `falseEnvU` satisfies it at every `K`
(its group has no constructor). -/
theorem falseEnvUWfT_boundDG (K : Nat → Nat) : BoundDG K falseEnvUWfT := by
  refine ⟨trivial, fun node i => ?_⟩
  have h := node.a.recursorRef
  rw [node.fam] at h
  exact absurd i.isLt (by omega)

/-- The condition is inhabited: `falseEnvU` at every `K` (no constructor). -/
theorem falseEnvUWfT_recBelowCtors (K : Nat → Nat) : RecBelowCtors K falseEnvUWfT :=
  ⟨trivial, fun _ h1 h2 => absurd h2 (by omega)⟩

end PSet

end Rcic.F3
