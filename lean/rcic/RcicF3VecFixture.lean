import rcic.RcicF3OrFixture
import rcic.RcicTypedGroupPinsVec

/-!
# F3 S6-5: the class contains an indexed recursive family (`Vec`)

`vecEnvUWfT` is the admitted Nat block followed by `Vec : Sort 1 → N → Sort 1`
(`vnil : Π A, Vec A zero`, `vcons : Π A n (hd : A) (tl : Vec A n), Vec A (succ n)`,
the recursor eliminating into any sort), two `EnvWfT.group` steps
(`RcicTypedGroupPinsVec`). `vecEnvUWfT_classG`: it is in `ClassG` and in
`BoundG K` for every `K`; `vecEnvUWfT_envSound`: the induction gives a sound
model of it. `vcons`'s field `tl` is recursive at an index: the fixture
exercises the family's fixed point at indices, the recursor's stage induction
and ι with the recursive call's index read through the constructor telescope.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The recursor node of the `Vec` block. -/
abbrev VecNode := RecNode natEnvU vecEnvUT 4 7 vecRecMemberU

theorem vec_fam (node : VecNode) : node.a.family.member = vecFamMember :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

/-- The family view of `Vec`: one parameter `Sort 1`, one index `N`, level `1`. -/
theorem vec_family (node : VecNode) :
    node.a.family.parameters = [.sort (.succ .zero)] ∧ node.a.family.indices = [.const 0 []] ∧
      node.a.family.resultLevel = .succ .zero := by
  have hst := node.a.family.storedType
  rw [vec_fam node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [.sort (.succ .zero), .const 0 []] _ _ _ (expr_not_pi_of_sort _)
    (expr_not_pi_of_sort _) hst
  injection h2 with hrl
  have hR : vecRecMemberU.mtype = policyPi [.sort (.succ .zero),
      .pi (.const 0 []) (.pi (.app (.app (.const 4 []) (.bvar 1)) (.bvar 0)) (.sort (.param 0))),
      .app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1)),
      .pi (.const 0 []) (.pi (.bvar 3) (.pi (.app (.app (.const 4 []) (.bvar 4)) (.bvar 1))
        (.pi (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))
          (.app (.app (.bvar 5) (.app (.const 2 []) (.bvar 3)))
            (.app (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3)) (.bvar 2)) (.bvar 1)))))),
      .const 0 [], .app (.app (.const 4 []) (.bvar 4)) (.bvar 0)]
      (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0)) := rfl
  obtain ⟨hnp, hnq⟩ := family_params_of_recType node _ h1 _ _ (fun _ _ h => Expr.noConfusion h) hR 1
    (fun k hk hne e he => match k, hk, hne, he with
      | 0, _, _, he => by cases he; exact fun _ _ h => Expr.noConfusion h
      | 1, _, hne, _ => absurd rfl hne
      | 2, _, _, he => by cases he; exact fun _ _ h => Expr.noConfusion h
      | _ + 3, hk, _, _ => absurd hk (by rw [List.length_cons, List.length_cons, List.length_nil]; omega))
  obtain ⟨hp, hi⟩ := List.append_inj (show ([.sort (.succ .zero)] : List (Expr Nat)) ++ [.const 0 []] = _ from h1)
    (by rw [hnp]; rfl)
  exact ⟨hp.symm, hi.symm, hrl.symm⟩

theorem vec_ctor (node : VecNode) (i : Fin node.a.constructors.length) :
    (node.a.constructors[i.val] = vecNilMember ∧ i.val = 0) ∨
      (node.a.constructors[i.val] = vecConsMember ∧ i.val = 1) := by
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(5, vecNilMember), (6, vecConsMember)]) node rfl
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 2 := hlen ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact Or.inl ⟨Option.some.inj (h.symm.trans rfl), rfl⟩
  | 1, _, _, h => exact Or.inr ⟨Option.some.inj (h.symm.trans rfl), rfl⟩

theorem foldApps_const_args {r r' : Nat} {ls ls' : List Level} {as as' : List (Expr Nat)}
    (h : foldApps (.const r ls) as = foldApps (.const r' ls') as') : as = as' := by
  have := congrArg (fun e => (appsSpine e).2) h
  simpa only [appsSpine_foldApps, appsSpine, List.nil_append] using this

/-- The constructor views of `Vec`. -/
theorem vec_view (node : VecNode) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [.sort (.succ .zero)] ∧
      (((node.a.constructorViews i).fields = [] ∧ (node.a.constructorViews i).resultIndices = [.const 1 []]) ∨
       ((node.a.constructorViews i).fields = [.const 0 [], .bvar 1, .app (.app (.const 4 []) (.bvar 2)) (.bvar 1)] ∧
        (node.a.constructorViews i).resultIndices = [.app (.const 2 []) (.bvar 2)])) := by
  obtain ⟨hP, _, _⟩ := vec_family node
  have hst := (node.a.constructorViews i).storedType
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals (node.a.constructorViews i).parameters.length
      (node.a.constructorViews i).fields.length ++ (node.a.constructorViews i).resultIndices)
  have hpl : (node.a.constructorViews i).parameters.length = 1 := by
    rw [(node.a.constructorViews i).parameterCount, hP]; rfl
  rcases vec_ctor node i with ⟨e, _⟩ | ⟨e, _⟩
  · have hm : (node.a.constructors[i.val]).mtype = policyPi [.sort (.succ .zero)]
        (foldApps (.const 4 []) [.bvar 0, .const 1 []]) := by rw [e]; rfl
    obtain ⟨hsp, hb⟩ := policyPi_split_eq _ _ _ _ (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) hne
      (hm.symm.trans hst)
    obtain ⟨h1, h2⟩ := List.append_inj (show ([.sort (.succ .zero)] : List (Expr Nat)) ++ [] = _ from hsp)
      (by rw [hpl]; rfl)
    have hargs := foldApps_const_args hb
    rw [hpl, ← h2] at hargs
    exact ⟨h1.symm, Or.inl ⟨h2.symm, (List.append_cancel_left (show [Expr.bvar 0] ++ [.const 1 []] = _ from hargs)).symm⟩⟩
  · have hm : (node.a.constructors[i.val]).mtype = policyPi [.sort (.succ .zero), .const 0 [], .bvar 1,
        .app (.app (.const 4 []) (.bvar 2)) (.bvar 1)]
        (foldApps (.const 4 []) [.bvar 3, .app (.const 2 []) (.bvar 2)]) := by rw [e]; rfl
    obtain ⟨hsp, hb⟩ := policyPi_split_eq _ _ _ _ (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) hne
      (hm.symm.trans hst)
    obtain ⟨h1, h2⟩ := List.append_inj (show ([.sort (.succ .zero)] : List (Expr Nat)) ++
      [.const 0 [], .bvar 1, .app (.app (.const 4 []) (.bvar 2)) (.bvar 1)] = _ from hsp) (by rw [hpl]; rfl)
    have hargs := foldApps_const_args hb
    rw [hpl, ← h2] at hargs
    exact ⟨h1.symm, Or.inr ⟨h2.symm,
      (List.append_cancel_left (show [Expr.bvar 3] ++ [.app (.const 2 []) (.bvar 2)] = _ from hargs)).symm⟩⟩

/-- **The `Nat`-then-`Vec` environment is in the class**, at every instance bound. -/
theorem vecEnvUWfT_classG : ClassG vecEnvUWfT ∧ ∀ K, BoundG K vecEnvUWfT := by
  refine ⟨⟨natEnvUWfT_classG.1, fun node => ⟨fun i => ?_,
    fun hu _ _ => ?_⟩, fun node => ?_⟩,
    fun K => ⟨natEnvUWfT_classG.2 K, fun node i vs _ _ => ?_, ?_, fun node hu _ _ _ _ _ => ?_⟩⟩
  · rw [(vec_family node).1, (vec_family node).2.1]
    rcases (vec_view node i).2 with ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf]
    · trivial
    · refine ⟨Or.inl rfl, Or.inl rfl, Or.inr ⟨[.bvar 1], ?_, rfl, fun e he => ?_⟩, trivial⟩
      · show Expr.app (.app (.const 4 []) (.bvar 2)) (.bvar 1) =
          foldApps (.const 4 ((List.range node.a.family.member.arity).map Level.param))
            (policyParameterLocals 1 2 ++ [.bvar 1])
        rw [vec_fam node]
        rfl
      · rcases List.mem_cons.mp he with rfl | he
        · rfl
        · exact absurd he (List.not_mem_nil _)
  · rw [(vec_family node).2.2] at hu
    exact absurd (hu fun _ => 0) (Nat.succ_ne_zero _)
  · rw [(vec_family node).1]
    exact ⟨trivial, rfl, rfl, rfl, trivial⟩
  · rw [vec_fam node]
    rcases vec_ctor node i with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
    · refine ⟨_, vecNilTyT rfl rfl, ?_⟩
      simp [LOKt, LevelsOK, evalTotal, vecNilTyT, vecOfTyT, vecConstTyT]
    · refine ⟨_, vecConsTyT rfl rfl rfl, ?_⟩
      simp [LOKt, LevelsOK, evalTotal, vecConsTyT, vecOfTyT, vecConstTyT, natConstTyT]
  · refine ⟨trivial, fun _ _ _ k => ?_, fun _ _ _ k => ?_, trivial, trivial⟩
    · match k with
      | ⟨0, _⟩ => exact ⟨.sort _ (.succ .zero), (by decide : 2 ≤ 4)⟩
    · match k with
      | ⟨0, _⟩ => exact ⟨.sort _ (.succ .zero), (by decide : 2 ≤ 4)⟩
      | ⟨1, _⟩ => exact ⟨natConstTyT rfl, fun l hl => absurd hl (List.not_mem_nil _)⟩
      | ⟨2, _⟩ => exact ⟨.bvar _ 1 _ rfl, trivial⟩
      | ⟨3, _⟩ =>
          refine ⟨vecOfTyT rfl (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl), ?_⟩
          simp [LOKt, LevelsOK, vecOfTyT, vecConstTyT]
  · rw [(vec_family node).2.2] at hu
    exact absurd (hu fun _ => 0) (Nat.succ_ne_zero _)

/-- The induction applied to the `Nat`-then-`Vec` environment: its table is a sound model of it. -/
theorem vecEnvUWfT_envSound (P : Premises4) (K : Nat → Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (envμR P (envCtx vecEnvUWfT) vecEnvUWfT)) σ K vecEnvUT n :=
  envSound_envμR_classG P K vecEnvUWfT vecEnvUWfT_classG.1 (vecEnvUWfT_classG.2 K) σ n

end PSet

end Rcic.F3
