import rcic.RcicF3DBoundDefs

/-!
# M0: standard-axiom admission boundary

The original singleton admission rule was monomorphic. This module measures
that restricted subjudgment before making a three-axiom consistency claim. It also
exhibits a bounded admitted environment in which an unrestricted axiom
proves the empty family. No extended consistency theorem is claimed.

`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative

/-- Every axiom already admitted in an environment is monomorphic. -/
def AxiomArityZero (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .axiomM → m.arity = 0

private theorem axiomArityZero_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hE : AxiomArityZero E) (hnew : m.mclass = .axiomM → m.arity = 0) :
    AxiomArityZero (extendEnv E r m) := by
  intro r' m' hm hax
  by_cases heq : r' = r
  · subst r'
    rw [members_extend_eq] at hm
    cases hm
    exact hnew hax
  · rw [members_extend_ne E r m r' heq] at hm
    exact hE r' m' hm hax

private theorem groupMembersT_axiomArityZero {S E : ResolvedEnv}
    {ms : List (Nat × CheckedMember)} {E' : ResolvedEnv}
    (hmem : GroupMembersT S E ms E') (hE : AxiomArityZero E)
    (hclasses : ∀ p ∈ ms, p.2.mclass ≠ .axiomM) : AxiomArityZero E' := by
  induction hmem with
  | nil => exact hE
  | @cons E₁ r m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      exact ih (axiomArityZero_extend hE
        (fun h => (hclasses (r, m) (List.mem_cons_self ..) h).elim))
        (fun p hp => hclasses p (List.mem_cons_of_mem _ hp))

/-- The original admission fragment: every bodyless axiom step has arity zero.
    Other steps retain exactly the current `EnvWfT` premises. -/
def MonomorphicAxiomAdmissions : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom (arity := arity) _ _ _ _ hE _ _ _ _ =>
      MonomorphicAxiomAdmissions hE ∧ arity = 0
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => MonomorphicAxiomAdmissions hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => MonomorphicAxiomAdmissions hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => MonomorphicAxiomAdmissions hE
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _ => MonomorphicAxiomAdmissions hE

/-- The original monomorphic admission fragment admits no parameterized axiom.
    This is deliberately restricted; current `EnvWfT` admits arbitrary arities. -/
theorem envWfT_axiomArityZero : {E : ResolvedEnv} → (hW : EnvWfT E) →
    MonomorphicAxiomAdmissions hW → AxiomArityZero E
  | _, .empty, _ => fun _ _ hm _ => by cases hm
  | _, .axiom _ _ _ _ hE _ _ _ _, hmono =>
      axiomArityZero_extend (envWfT_axiomArityZero hE hmono.1) (fun _ => hmono.2)
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hmono =>
      axiomArityZero_extend (envWfT_axiomArityZero hE hmono) (fun h => MemberClass.noConfusion h)
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hmono =>
      axiomArityZero_extend (envWfT_axiomArityZero hE hmono) (fun h => MemberClass.noConfusion h)
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hmono =>
      axiomArityZero_extend (envWfT_axiomArityZero hE hmono) (fun h => MemberClass.noConfusion h)
  | _, .group _ f fm ctors rr rm _ hE hfam hctors hrec hmem, hmono => by
      apply groupMembersT_axiomArityZero hmem (envWfT_axiomArityZero hE hmono)
      intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst p
        rw [hfam]
        decide
      · rcases List.mem_append.mp hp with hp | hp
        · rw [hctors p hp]
          decide
        · have hp' : p = (rr, rm) := List.mem_singleton.mp hp
          subst p
          rw [hrec]
          decide

/-- The exact polymorphic schemas lie outside the original monomorphic fragment,
    independently of their chosen stored type expressions. -/
theorem envWfT_no_polymorphic_axiom {E : ResolvedEnv} (hW : EnvWfT E)
    (hmono : MonomorphicAxiomAdmissions hW)
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m)
    (hc : m.mclass = .axiomM) (ha : m.arity = 1) : False := by
  have hz := envWfT_axiomArityZero hW hmono r m hm hc
  rw [ha] at hz
  cases hz

end Rcic.Declarative

namespace Rcic.F3.PSet.Ax3Boundary

open Rcic.Declarative

/-- An unrestricted object axiom, not a metatheoretic axiom. -/
def falseAxMember : CheckedMember := ⟨.axiomM, 0, .const 0 [], none⟩

/-- Keep the empty family and its recursor; append the unrestricted axiom. -/
def falseAxEnv : ResolvedEnv := extendEnv falseEnvU 2 falseAxMember

def falseAxEnvWfT : EnvWfT falseAxEnv :=
  .axiom falseEnvU 2 (.const 0 []) .zero falseEnvUWfT rfl
    (falseConstTyT rfl) (fun _ => rfl) rfl

theorem falseAxEnvWfT_monomorphic : MonomorphicAxiomAdmissions falseAxEnvWfT :=
  ⟨trivial, rfl⟩

def falseAxProof : HasTyT falseAxEnv 0 [] (.const 2 []) (.const 0 []) :=
  .const [] 2 [] falseAxMember rfl rfl rfl

theorem falseAxProof_below (K : Nat → Nat) : LevelsBelow 4 K falseAxProof := by
  intro _ h
  cases h

theorem falseAxEnv_boundG (K : Nat → Nat) : BoundG K falseAxEnvWfT :=
  falseEnvUWfT_boundG K

theorem falseAxEnv_boundDG (K : Nat → Nat) : BoundDG K falseAxEnvWfT :=
  falseEnvUWfT_boundDG K

/-- The arbitrary-axiom attack satisfies every other environment/derivation
premise of the height-4 consistency tier, at every instance bound. -/
theorem arbitrary_axiom_counterexample (K : Nat → Nat) :
    ∃ (E : ResolvedEnv) (hW : EnvWfT E),
      BoundG K hW ∧ BoundDG K hW ∧
      E.members 0 = some falseFamMember ∧ E.members 1 = some falseRecMemberU ∧
      ∃ (D : HasTyT E 0 [] (.const 2 []) (.const 0 [])), LevelsBelow 4 K D :=
  ⟨falseAxEnv, falseAxEnvWfT, falseAxEnv_boundG K, falseAxEnv_boundDG K,
    rfl, rfl, falseAxProof, falseAxProof_below K⟩

theorem falseAxEnv_not_axiomFree : ¬ AxiomFreeEnv' falseAxEnv := by
  intro h
  exact h 2 falseAxMember rfl rfl

end Rcic.F3.PSet.Ax3Boundary
