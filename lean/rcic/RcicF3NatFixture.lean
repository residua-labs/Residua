import rcic.RcicF3ClassFixtures
import rcic.RcicTypedGroupPins

/-!
# F3 S5b-6: the class contains a recursive group

`natEnvUWfT` (the admitted `Nat` block: family `Type` at 0, `zero` at 1,
`succ : Nat → Nat` at 2, recursor at 3) is in `ClassG` and in `BoundG K` for
every `K` (`natEnvUWfT_classG`), and the induction of `RcicF3MainG` gives a
sound model of it (`natEnvUWfT_envSound`). `succ`'s field is recursive: the
fixture exercises the family's fixed point, the recursor's stage induction
and ι with a recursive call.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The recursor node of the `Nat` block. -/
abbrev NatNode := RecNode emptyEnv natEnvU 0 3 natRecMemberU

theorem nat_fam (node : NatNode) : node.a.family.member = natFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

/-- The family view of the `Nat` block: no parameters, no indices, level 1. -/
theorem nat_family (node : NatNode) :
    node.a.family.parameters = [] ∧ node.a.family.indices = [] ∧ node.a.family.resultLevel = .succ .zero := by
  have hst := node.a.family.storedType
  rw [nat_fam node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [] _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  have h3 := List.append_eq_nil.mp h1.symm
  injection h2 with h4
  exact ⟨h3.1, h3.2, h4.symm⟩

theorem nat_ctor (node : NatNode) (i : Fin node.a.constructors.length) :
    (node.a.constructors[i.val] = natZeroMember ∧ i.val = 0) ∨
      (node.a.constructors[i.val] = natSuccMember ∧ i.val = 1) := by
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(1, natZeroMember), (2, natSuccMember)]) node rfl
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 2 := hlen ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact Or.inl ⟨(Option.some.inj (h.symm.trans rfl)), rfl⟩
  | 1, _, _, h => exact Or.inr ⟨(Option.some.inj (h.symm.trans rfl)), rfl⟩

/-- A constructor view of the `Nat` block: no parameters or result indices;
`zero` has no field, `succ` the one field `Nat`. -/
theorem nat_views (node : NatNode) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [] ∧ (node.a.constructorViews i).resultIndices = [] ∧
      (((node.a.constructorViews i).fields = [] ∧ i.val = 0) ∨
        ((node.a.constructorViews i).fields = [.const 0 []] ∧ i.val = 1)) := by
  obtain ⟨hP, hI, _⟩ := nat_family node
  have hp : (node.a.constructorViews i).parameters = [] := by
    have := (node.a.constructorViews i).parameterCount
    rw [hP] at this
    exact List.eq_nil_of_length_eq_zero this
  have hr : (node.a.constructorViews i).resultIndices = [] := by
    have := (node.a.constructorViews i).indexCount
    rw [hI] at this
    exact List.eq_nil_of_length_eq_zero this
  refine ⟨hp, hr, ?_⟩
  have hst := (node.a.constructorViews i).storedType
  rw [hp, List.nil_append] at hst
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals 0 (node.a.constructorViews i).fields.length ++
      (node.a.constructorViews i).resultIndices)
  rcases nat_ctor node i with ⟨e, h0⟩ | ⟨e, h1⟩
  · have hm : (node.a.constructors[i.val]).mtype = policyPi [] (.const 0 []) := by rw [e]; rfl
    have := (policyPi_split_eq [] _ (.const 0 []) _ (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    exact Or.inl ⟨this.symm, h0⟩
  · have hm : (node.a.constructors[i.val]).mtype = policyPi [.const 0 []] (.const 0 []) := by rw [e]; rfl
    have := (policyPi_split_eq [.const 0 []] _ (.const 0 []) _ (fun _ _ h => Expr.noConfusion h) hne
      (hm.symm.trans hst)).1
    exact Or.inr ⟨this.symm, h1⟩

/-- The `Nat` constructors' stored types, typed at instances within any bound. -/
theorem nat_ctor_typed (node : NatNode) (K : Nat → Nat) (σ : Nat → Nat) (i : Fin node.a.constructors.length) :
    ∃ (u : Level) (d : HasTyT (extendEnv emptyEnv 0 natFamMember) node.a.family.member.arity []
        (node.a.constructors[i.val]).mtype (.sort u)), LOKt σ 4 K d := by
  rcases nat_ctor node i with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e]
    exact ⟨.succ .zero, natConstTyT rfl, fun l hl => absurd hl (List.not_mem_nil _)⟩
  · rw [e]
    exact ⟨_, .pi [] _ _ _ _ (natConstTyT rfl) (natConstTyT rfl),
      (by decide : 1 ≤ 4), (by decide : 1 ≤ 4),
      fun l hl => absurd hl (List.not_mem_nil _), fun l hl => absurd hl (List.not_mem_nil _)⟩

/-- **The `Nat` block is in the class**, at every instance bound: a recursive
`Type` group. -/
theorem natEnvUWfT_classG : ClassG natEnvUWfT ∧ ∀ K, BoundG K natEnvUWfT := by
  refine ⟨⟨trivial, fun node => ⟨fun i => ?_,
    fun hu _ i => ?_⟩, fun node => ?_⟩,
    fun K => ⟨trivial, fun node i vs _ _ => nat_ctor_typed node K _ i, ?_, fun node hu _ _ _ _ _ => by
      rw [(nat_family node).2.2] at hu; exact absurd (hu fun _ => 0) (Nat.succ_ne_zero _)⟩⟩
  · obtain ⟨_, _, hF⟩ := nat_views node i
    rcases hF with ⟨hf, _⟩ | ⟨hf, _⟩
    · rw [hf]; trivial
    · rw [hf, (nat_family node).1]
      refine ⟨Or.inr ⟨[], ?_, by rw [(nat_family node).2.1], fun e he => absurd he (List.not_mem_nil _)⟩, trivial⟩
      show Expr.const 0 [] = foldApps (.const 0 ((List.range node.a.family.member.arity).map Level.param)) ([] ++ [])
      rw [nat_fam node]
      rfl
  · rw [(nat_family node).2.2] at hu
    exact absurd (hu fun _ => 0) (Nat.succ_ne_zero _)
  · rw [(nat_family node).1]
    exact ⟨trivial, rfl, rfl, rfl, trivial⟩
  · refine ⟨trivial, fun _ _ _ k => (Nat.not_lt_zero _ k.isLt).elim, fun vs _ _ k => ?_, trivial, trivial⟩
    obtain ⟨k, hk⟩ := k
    match k, hk with
    | 0, _ => exact ⟨natConstTyT rfl, fun l hl => absurd hl (List.not_mem_nil _)⟩

/-- The induction applied to the `Nat` block: its table is a sound model of it. -/
theorem natEnvUWfT_envSound (P : Premises4) (K : Nat → Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (envμR P (envCtx natEnvUWfT) natEnvUWfT)) σ K natEnvU n :=
  envSound_envμR_classG P K natEnvUWfT natEnvUWfT_classG.1 (natEnvUWfT_classG.2 K) σ n

end PSet

end Rcic.F3
