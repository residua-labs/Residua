import rcic.RcicF3AndFixture
import rcic.RcicG2AdmitOr

/-!
# F3 S6-4: the class contains a `Prop` family eliminating into `Prop`

`orWfT` is the admitted `Or` block (`Or : Prop → Prop → Prop` at 0, `inl`,
`inr` at 1 and 2, its recursor eliminating into `Prop` at 3), as one
`EnvWfT.group` step built from the in-tree admission chain
`Rcic.G2.orGroupChain`. `orWfT_classG`: it is in `ClassG` and in `BoundG K`
for every `K`; `orWfT_envSound`: the induction gives a sound model of it. Its
recursor is sound by the stage induction for `Prop` families
(`recVal_mem_recP`), whose value is the proof `∅`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The admitted `Or` block, as one group step. -/
def orWfT : EnvWfT Rcic.G2.orEnv :=
  .group emptyEnv 0 andFamMember [(1, Rcic.G2.orInlMember), (2, Rcic.G2.orInrMember)] 3 Rcic.G2.orRecMember
    Rcic.G2.orEnv .empty rfl (fun c hc => by
      rcases List.mem_cons.mp hc with rfl | hc
      · rfl
      · rcases List.mem_cons.mp hc with rfl | hc
        · rfl
        · exact absurd hc (List.not_mem_nil _))
    rfl (groupMembersT_of_chain Rcic.G2.orGroupChain)

/-- The recursor node of the `Or` block. -/
abbrev OrNode := RecNode emptyEnv Rcic.G2.orEnv 0 3 Rcic.G2.orRecMember

theorem or_fam (node : OrNode) : node.a.family.member = andFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

/-- The family view of the `Or` block: two `Prop` parameters, no index, level `0`. -/
theorem or_family (node : OrNode) :
    node.a.family.parameters = [.sort .zero, .sort .zero] ∧ node.a.family.indices = [] ∧
      node.a.family.resultLevel = .zero := by
  have hst := node.a.family.storedType
  rw [or_fam node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [.sort .zero, .sort .zero] _ _ _ (expr_not_pi_of_sort _)
    (expr_not_pi_of_sort _) hst
  injection h2 with hrl
  obtain ⟨_, hql⟩ := family_params_of_recType node _ h1
    [.sort .zero, .sort .zero, .pi (Rcic.G2.orApp 0 (.bvar 1) (.bvar 0)) (.sort .zero),
      .pi (.bvar 2) (.app (.bvar 1) (Rcic.G2.appsp 1 [.bvar 3, .bvar 2, .bvar 0])),
      .pi (.bvar 2) (.app (.bvar 2) (Rcic.G2.appsp 2 [.bvar 4, .bvar 3, .bvar 0])),
      Rcic.G2.orApp 0 (.bvar 4) (.bvar 3)] (.app (.bvar 3) (.bvar 0)) (fun _ _ h => Expr.noConfusion h) rfl 2
    (fun k hk hne e he => match k, hk, hne, he with
      | 0, _, _, he => by cases he; exact fun _ _ h => Expr.noConfusion h
      | 1, _, _, he => by cases he; exact fun _ _ h => Expr.noConfusion h
      | 2, _, hne, _ => absurd rfl hne
      | _ + 3, hk, _, _ => absurd hk (by rw [List.length_cons, List.length_cons, List.length_nil]; omega))
  have hq := List.eq_nil_of_length_eq_zero hql
  rw [hq, List.append_nil] at h1
  exact ⟨h1.symm, hq, hrl.symm⟩

theorem or_ctor (node : OrNode) (i : Fin node.a.constructors.length) :
    (node.a.constructors[i.val] = Rcic.G2.orInlMember ∧ i.val = 0) ∨
      (node.a.constructors[i.val] = Rcic.G2.orInrMember ∧ i.val = 1) := by
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(1, Rcic.G2.orInlMember), (2, Rcic.G2.orInrMember)]) node rfl
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 2 := hlen ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact Or.inl ⟨Option.some.inj (h.symm.trans rfl), rfl⟩
  | 1, _, _, h => exact Or.inr ⟨Option.some.inj (h.symm.trans rfl), rfl⟩

/-- A constructor view of `Or`: two `Prop` parameters, one proof field, no result index. -/
theorem or_view (node : OrNode) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [.sort .zero, .sort .zero] ∧
      ((node.a.constructorViews i).fields = [.bvar 1] ∨ (node.a.constructorViews i).fields = [.bvar 0]) ∧
      (node.a.constructorViews i).resultIndices = [] := by
  obtain ⟨hP, hI, _⟩ := or_family node
  have hst := (node.a.constructorViews i).storedType
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals (node.a.constructorViews i).parameters.length
      (node.a.constructorViews i).fields.length ++ (node.a.constructorViews i).resultIndices)
  have hpl : (node.a.constructorViews i).parameters.length = 2 := by
    rw [(node.a.constructorViews i).parameterCount, hP]; rfl
  have hri : (node.a.constructorViews i).resultIndices = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [(node.a.constructorViews i).indexCount, hI]; rfl
  rcases or_ctor node i with ⟨e, _⟩ | ⟨e, _⟩
  · have hm : (node.a.constructors[i.val]).mtype = policyPi [.sort .zero, .sort .zero, .bvar 1]
        (Rcic.G2.orApp 0 (.bvar 2) (.bvar 1)) := by rw [e]; rfl
    have hsp := (policyPi_split_eq _ _ _ _ (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    obtain ⟨h1, h2⟩ := List.append_inj (show ([.sort .zero, .sort .zero] : List (Expr Nat)) ++ [.bvar 1] = _
      from hsp) (by rw [hpl]; rfl)
    exact ⟨h1.symm, Or.inl h2.symm, hri⟩
  · have hm : (node.a.constructors[i.val]).mtype = policyPi [.sort .zero, .sort .zero, .bvar 0]
        (Rcic.G2.orApp 0 (.bvar 2) (.bvar 1)) := by rw [e]; rfl
    have hsp := (policyPi_split_eq _ _ _ _ (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1
    obtain ⟨h1, h2⟩ := List.append_inj (show ([.sort .zero, .sort .zero] : List (Expr Nat)) ++ [.bvar 0] = _
      from hsp) (by rw [hpl]; rfl)
    exact ⟨h1.symm, Or.inr h2.symm, hri⟩

/-- `Or` does not eliminate into every sort: two constructors in `Prop`. -/
theorem or_policy (node : OrNode) : node.a.policy ≠ .anySort := fun hpol => by
  have hs : EliminationSelection node.a.family.resultLevel node.a.constructors.length
      (∀ i, (node.a.constructorViews i).AllFieldsSafe) .anySort := by rw [← hpol]; exact node.a.selected
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(1, Rcic.G2.orInlMember), (2, Rcic.G2.orInrMember)]) node rfl
  rcases (EliminationSelection.anySort_iff _ _ _).mp hs with ht | ⟨_, hk0 | ⟨hk1, _⟩⟩
  · rw [(or_family node).2.2] at ht
    exact absurd (ht fun _ => 0) (Nat.lt_irrefl 0)
  · omega
  · omega

/-- The constructors' stored types, typed at instances within any bound. -/
theorem or_ctor_typed (node : OrNode) (K : Nat → Nat) (σ : Nat → Nat) (i : Fin node.a.constructors.length) :
    ∃ (u : Level) (d : HasTyT (extendEnv emptyEnv 0 andFamMember) node.a.family.member.arity []
        (node.a.constructors[i.val]).mtype (.sort u)), LOKt σ 4 K d := by
  rw [or_fam node]
  rcases or_ctor node i with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e]
    refine ⟨_, .pi [] _ _ _ _ (.sort [] .zero) (.pi _ _ _ _ _ (.sort _ .zero)
      (.pi _ _ _ _ _ (.bvar _ 1 _ rfl) (andOfTyT rfl (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl)))), ?_⟩
    simp [LOKt, LevelsOK, evalTotal, andOfTyT]
  · rw [e]
    refine ⟨_, .pi [] _ _ _ _ (.sort [] .zero) (.pi _ _ _ _ _ (.sort _ .zero)
      (.pi _ _ _ _ _ (.bvar _ 0 _ rfl) (andOfTyT rfl (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl)))), ?_⟩
    simp [LOKt, LevelsOK, evalTotal, andOfTyT]

theorem or_field_free (node : OrNode) (i : Fin node.a.constructors.length) :
    ∀ T, T ∈ (node.a.constructorViews i).fields → occursConst 0 T = false := by
  intro T hT
  rcases (or_view node i).2.1 with hf | hf <;> rw [hf] at hT <;>
    rcases List.mem_cons.mp hT with rfl | hT
  · rfl
  · exact absurd hT (List.not_mem_nil _)
  · rfl
  · exact absurd hT (List.not_mem_nil _)

/-- **The `Or` block is in the class**, at every instance bound. -/
theorem orWfT_classG : ClassG orWfT ∧ ∀ K, BoundG K orWfT := by
  refine ⟨⟨trivial, fun node => ⟨fun i => ?_,
    fun _ hpol _ => absurd hpol (or_policy node)⟩, fun node => ?_⟩,
    fun K => ⟨trivial, fun node i vs _ _ => or_ctor_typed node K _ i, ?_,
      fun node _ hpol => absurd hpol (or_policy node)⟩⟩
  · exact recFieldsDirect_of_free _ 0 (or_field_free node i)
  · rw [(or_family node).1]
    show WalkClass 2 (groupMembersT_of_chain Rcic.G2.orGroupChain)
    unfold Rcic.G2.orGroupChain
    simp only [groupMembersT_of_chain]
    repeat rw [walkClass_andRec]
    refine ⟨trivial, ?_⟩
    repeat rw [walkClass_andRec]
    refine ⟨rfl, ?_⟩
    repeat rw [walkClass_andRec]
    refine ⟨rfl, ?_⟩
    repeat rw [walkClass_andRec]
    exact ⟨rfl, trivial⟩
  · show WalkB2 K (groupMembersT_of_chain Rcic.G2.orGroupChain)
    unfold Rcic.G2.orGroupChain
    simp only [groupMembersT_of_chain]
    repeat rw [walkB2_andRec]
    refine ⟨trivial, ?_⟩
    repeat rw [walkB2_andRec]
    refine ⟨fun _ _ _ k => ?_, ?_⟩
    · match k with
      | ⟨0, _⟩ => exact ⟨.sort _ .zero, (by decide : 1 ≤ 4)⟩
      | ⟨1, _⟩ => exact ⟨.sort _ .zero, (by decide : 1 ≤ 4)⟩
      | ⟨2, _⟩ => exact ⟨.bvar _ 1 _ rfl, trivial⟩
    repeat rw [walkB2_andRec]
    refine ⟨fun _ _ _ k => ?_, ?_⟩
    · match k with
      | ⟨0, _⟩ => exact ⟨.sort _ .zero, (by decide : 1 ≤ 4)⟩
      | ⟨1, _⟩ => exact ⟨.sort _ .zero, (by decide : 1 ≤ 4)⟩
      | ⟨2, _⟩ => exact ⟨.bvar _ 0 _ rfl, trivial⟩
    repeat rw [walkB2_andRec]
    exact ⟨trivial, trivial⟩

/-- The induction applied to the `Or` block: its table is a sound model of it. -/
theorem orWfT_envSound (P : Premises4) (K : Nat → Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (envμR P (envCtx orWfT) orWfT)) σ K Rcic.G2.orEnv n :=
  envSound_envμR_classG P K orWfT orWfT_classG.1 (orWfT_classG.2 K) σ n

end PSet

end Rcic.F3
