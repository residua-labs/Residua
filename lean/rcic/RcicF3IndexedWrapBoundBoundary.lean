import rcic.RcicF3IndexedWrapIotaAttack
import rcic.RcicF3AccBoundScopeAttack

/-!
# Wrap separates the indexed bound from the unchanged original bound

The admitted Wrap fixture has a revealed ordinary field of type Sort 1:
the field expression itself is Sort 0. The original BoundG clause would
instead require a bounded typing of that expression at a uniformly Prop
sort. The actual family-only prefix is sound, so that requirement is
contradictory at every K, relative to the same supplied Premises4.

This is an explicit domain boundary for the unchanged original root:
KernelSoundnessTierUncond retains BoundG, whereas the Wrap iota attack
supplies BoundGIndexed. Neither bound, IotaAt, PointwiseRole.GInv, nor
the original root statement is changed here. The existing not_gInv
counterexample is retained and is not claimed to refute that root.

The exact declaration inventory is checked by RcicF3AIndexedPropSeal. scope_closure_claim = 0; closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.IndexedWrapBoundBoundary

open Rcic.Declarative

/-- The family-only prefix has no dependence on the particular constant-one
bound used by the iota attack. Reapply the existing producer at arbitrary K. -/
theorem family_prefix_sound (P : Premises4) (K : Nat → Nat) : ∀ σ n,
    EnvSound (IndexedWrapIotaAttack.model P) σ K IndexedWrapFixture.famOnly n :=
  (PointwisePropPrefix.canonical_group_facts P K (IndexedWrapIotaAttack.table P)
    (f := 0) (fm := IndexedWrapFixture.famMember)
    (ctors := [(1, IndexedWrapFixture.introMember)])
    (rr := 2) (rm := IndexedWrapFixture.recMember)
    .empty rfl IndexedWrapIotaAttack.ctorClasses rfl IndexedWrapFixture.membersT
    (PointwiseRole.gInv_empty P K)
    (PointwiseRole.arities IndexedWrapFixture.env)
    (PointwiseRole.arities_agree IndexedWrapFixture.env)
    (NormRole.envCtx IndexedWrapFixture.envWfT)
    (EvalRole.envPlan IndexedWrapFixture.envWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (IndexedWrapIotaAttack.faithful P)
    IndexedWrapIotaAttack.uniform_prop).rawEnv

/-- Selecting the sole field of the literal admitted node exposes the old
all-Prop obligation. The empty level vector satisfies every K. -/
theorem boundG_field_obligation (K : Nat → Nat)
    (hB : BoundG K IndexedWrapFixture.envWfT) :
    ∃ l : Level, UniformProp l ∧
      ∃ d : HasTyT IndexedWrapFixture.famOnly 0 [] (.sort .zero) (.sort l),
        LOKt (fun _ => 0) 4 K d := by
  have h := hB.2.2.2 IndexedWrapFixture.node (fun _ => rfl) rfl
    ⟨0, by decide⟩ [] (fun _ hx => nomatch hx) ⟨0, by decide⟩
  change ∃ l : Level, UniformProp l ∧
    ∃ d : HasTyT IndexedWrapFixture.famOnly 0 [] (.sort .zero) (.sort l),
      LOKt (fun _ => 0) 4 K d at h
  exact h

/-- Wrap lies outside the original BoundG domain for every K. This uses
the existing bounded soundness contradiction at the actual family prefix. -/
theorem wrap_not_boundG (P : Premises4) (K : Nat → Nat) :
    ¬ BoundG K IndexedWrapFixture.envWfT := by
  intro hB
  obtain ⟨l, hl, d, hd⟩ := boundG_field_obligation K hB
  exact AccBoundScopeAttack.no_bounded_prop_sort P (IndexedWrapIotaAttack.table P)
    K (fun _ => 0) (family_prefix_sound P K (fun _ => 0) 0) l hl d hd

/-- The same admitted fixture satisfies the new indexed bound while failing
the unchanged original bound, at the same explicit K and Premises4. -/
theorem indexed_bound_strict_at_wrap (P : Premises4) (K : Nat → Nat) :
    IndexedFieldBounds.BoundGIndexed K IndexedWrapFixture.envWfT ∧
      ¬ BoundG K IndexedWrapFixture.envWfT :=
  ⟨IndexedWrapFixture.indexed_bound K, wrap_not_boundG P K⟩

end Rcic.F3.PSet.IndexedWrapBoundBoundary

#print axioms Rcic.F3.PSet.IndexedWrapBoundBoundary.family_prefix_sound
#print axioms Rcic.F3.PSet.IndexedWrapBoundBoundary.boundG_field_obligation
#print axioms Rcic.F3.PSet.IndexedWrapBoundBoundary.wrap_not_boundG
#print axioms Rcic.F3.PSet.IndexedWrapBoundBoundary.indexed_bound_strict_at_wrap
