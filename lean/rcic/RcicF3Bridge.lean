import rcic.RcicF3NegControl

/-!
# F3: from `consistent4_G` to the target `RcicConsistentEmpty`

`rcicConsistentEmpty_of_class_bounds`: the target follows from
`consistent4_G` given two premises, stated as Lean hypotheses so that the
residual is exact:

- **class coverage**: every admitted axiom-free environment with the empty
  type at 0 and its recursor at 1 is in `ClassG`;
- **level bound**: every derivation of the type at 0 has, for some instance
  bound `K`, `BoundG K` and sort levels at most 4 (`LOKt`).

`axiomFree_of_classG`: the class is axiom-free, so coverage is about the
group conditions only.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- An environment in the class has no axioms. -/
theorem axiomFree_of_classG : {E : ResolvedEnv} → (hW : EnvWfT E) → ClassG hW → AxiomFreeEnv' E
  | _, .empty, _, r, m, h => by cases h
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _, _, _ => hC.elim
  | _, .definition E r' _ _ _ hE _ _ _ _ _ _ _, hC, r, m, h => by
      by_cases hr : r = r'
      · subst hr; rw [members_extend_eq] at h; cases h; exact fun h => MemberClass.noConfusion h
      · rw [members_extend_ne E r' _ r hr] at h; exact axiomFree_of_classG hE hC r m h
  | _, .thm E r' _ _ hE _ _ _ _ _ _ _, hC, r, m, h => by
      by_cases hr : r = r'
      · subst hr; rw [members_extend_eq] at h; cases h; exact fun h => MemberClass.noConfusion h
      · rw [members_extend_ne E r' _ r hr] at h; exact axiomFree_of_classG hE hC r m h
  | _, .opaque E r' _ _ _ hE _ _ _ _ _ _ _, hC, r, m, h => by
      by_cases hr : r = r'
      · subst hr; rw [members_extend_eq] at h; cases h; exact fun h => MemberClass.noConfusion h
      · rw [members_extend_ne E r' _ r hr] at h; exact axiomFree_of_classG hE hC r m h
  | _, .group E f fm ctors rr rm _ hE hfam hctors hrec hmem, hC, r, m, h => by
      rcases groupMembersT_cases hmem r m h with h1 | h1
      · exact axiomFree_of_classG hE hC.1 r m h1
      · rcases List.mem_cons.mp h1 with h2 | h2
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
          rw [hfam]; exact fun h => MemberClass.noConfusion h
        · rcases List.mem_append.mp h2 with h3 | h3
          · rw [hctors _ h3]; exact fun h => MemberClass.noConfusion h
          · rw [List.mem_singleton] at h3
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
            rw [hrec]; exact fun h => MemberClass.noConfusion h

/-- **The target from `consistent4_G`**, given class coverage and the level
bound. Relative to `Premises4`. -/
theorem rcicConsistentEmpty_of_class_bounds (P : Premises4)
    (hClass : ∀ (E : ResolvedEnv) (hW : EnvWfT E), AxiomFreeEnv' E → E.members 0 = some falseFamMember →
      E.members 1 = some falseRecMemberU → ClassG hW)
    (hBound : ∀ (E : ResolvedEnv) (hW : EnvWfT E) (n : Nat) (e : Expr Nat) (h : HasTyT E n [] e (.const 0 [])),
      ∃ K, BoundG K hW ∧ LOKt (fun _ => 0) 4 K h) :
    RcicConsistentEmpty := by
  intro E hW hax h0 h1 n e h
  obtain ⟨K, hB, hl⟩ := hBound E hW n e h
  exact consistent4_G P K hW (hClass E hW hax h0 h1) hB h1 n e h hl

end PSet

end Rcic.F3
